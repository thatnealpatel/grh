package main

import (
	"context"
	"fmt"
	"slices"
	"unicode/utf8"
)

// prepare waits while idle. A nil scope and nil error means a
// stored finding needs publication, not another review.
func (a *auditor) prepare(ctx context.Context) (*scope, error) {
	for {
		ahead, err := a.acceptedAhead(ctx)
		if err != nil {
			return nil, err
		}
		if a.fresh {
			if err := a.save(ctx, a.state); err != nil {
				return nil, err
			}
		}
		if p := a.state.Pending; p != nil {
			landed, err := a.findPublication(ctx, ahead)
			if err != nil || landed == "" {
				return nil, err
			}
			if err := a.finishReview(ctx, *p, landed); err != nil {
				return nil, err
			}
			// A recovered publication completed
			// the pass and waited. Read the tip
			// again: work may have landed during
			// that interval.
			continue
		}
		for len(ahead) != 0 {
			i := slices.IndexFunc(a.state.Findings, func(f finding) bool { return f.Note == ahead[0] })
			if i < 0 {
				break
			}
			// The standalone note was already
			// checked at publication. Keep the
			// most recent substantive review,
			// not a new clean verdict.
			j := a.state
			j.Findings = slices.Clone(j.Findings)
			j.Findings[i].Covered = true
			j.Examined = ahead[0]
			if err := a.save(ctx, j); err != nil {
				return nil, err
			}
			ahead = ahead[1:]
		}
		if len(ahead) == 0 {
			if err := a.wait(ctx); err != nil {
				return nil, err
			}
			continue
		}
		s := scope{Base: a.state.Examined, Target: ahead[0]}
		changes, err := a.repo.changes(ctx, s.Base, s.Target)
		if err != nil {
			return nil, err
		}
		for _, ch := range changes {
			if !utf8.ValidString(ch.path) {
				return nil, fmt.Errorf("audit: invalid UTF-8 path at %s", s.Target)
			}
			s.Paths = append(s.Paths, ch.path)
			s.Lean = s.Lean || leanPath(ch.path)
		}
		return &s, ctx.Err()
	}
}

func (a *auditor) acceptedAhead(ctx context.Context) ([]string, error) {
	tip, err := a.repo.tip(ctx)
	if err != nil {
		return nil, err
	}
	ahead, err := a.repo.between(ctx, a.state.Examined, tip)
	if err != nil {
		return nil, err
	}
	for _, f := range a.state.Findings {
		if slices.Contains(ahead, f.Note) == f.Covered {
			return nil, fmt.Errorf("audit: accepted note %s disagrees with checkpoint at %s", f.Note, a.state.Examined)
		}
	}
	return ahead, nil
}

func (a *auditor) acceptReview(ctx context.Context, s scope, text string) error {
	if s.Base != a.state.Examined || a.state.Pending != nil {
		return fmt.Errorf("audit: report is not for the next uncovered commit")
	}
	var r reply
	if err := decode([]byte(text), &r); err != nil {
		return fmt.Errorf("audit: invalid reviewer reply: %w", err)
	}
	if err := r.validate(s); err != nil {
		return err
	}
	ahead, err := a.acceptedAhead(ctx)
	if err != nil {
		return err
	}
	if len(ahead) == 0 || ahead[0] != s.Target {
		return fmt.Errorf("audit: pinned commit %s no longer immediately follows checkpoint", s.Target)
	}
	rec := record{Scope: s, Reply: r}
	if r.Verdict == "finding" {
		j := a.state
		j.Pending = &rec
		return a.save(ctx, j)
	}
	return a.finishReview(ctx, rec, "")
}

// findPublication recognizes a crash after adoption, without confusing a
// candidate, existing path, or mixed producer patch with an accepted note.
func (a *auditor) findPublication(ctx context.Context, ahead []string) (string, error) {
	p := a.state.Pending
	if len(ahead) == 0 || ahead[0] != p.Scope.Target {
		return "", fmt.Errorf("audit: pending target %s no longer immediately follows checkpoint", p.Scope.Target)
	}
	parent, path, data := p.Scope.Target, notePath(p.Scope.Target), p.note()
	for _, rev := range ahead[1:] {
		changes, err := a.repo.changes(ctx, parent, rev)
		if err != nil {
			return "", err
		}
		for _, ch := range changes {
			if ch.path != path {
				continue
			}
			if ch.status == "A" && len(changes) == 1 {
				ok, err := a.repo.matchesNote(ctx, rev, path, data)
				if err != nil {
					return "", err
				}
				if ok {
					return rev, nil
				}
			}
			return "", fmt.Errorf("audit: unexpected handoff patch at %s:%s", rev, path)
		}
		parent = rev
	}
	return "", nil
}

func (a *auditor) acceptPublication(ctx context.Context, text string) error {
	var e struct {
		Target string `json:"target"`
		Note   string `json:"accepted_revision"`
	}
	if err := decode([]byte(text), &e); err != nil {
		return fmt.Errorf("audit: invalid publication reply: %w", err)
	}
	p := a.state.Pending
	if p == nil || e.Target != p.Scope.Target || !commitID(e.Note) {
		return fmt.Errorf("audit: publication reply is not for the pending handoff")
	}
	ahead, err := a.acceptedAhead(ctx)
	if err != nil {
		return err
	}
	landed, err := a.findPublication(ctx, ahead)
	if err != nil {
		return err
	}
	if landed != e.Note {
		return fmt.Errorf("audit: handoff %s is not verified in accepted history", e.Note)
	}
	return a.finishReview(ctx, *p, landed)
}

func (a *auditor) finishReview(ctx context.Context, r record, note string) error {
	j := a.state
	if note != "" {
		j.Findings = append(slices.Clone(j.Findings), finding{Note: note, Path: notePath(r.Scope.Target)})
	}
	j.Examined, j.Latest, j.Pending = r.Scope.Target, &r, nil
	if err := a.save(ctx, j); err != nil {
		return err
	}
	// The pass is durable even if the
	// process stops during this wait.
	return a.wait(ctx)
}
