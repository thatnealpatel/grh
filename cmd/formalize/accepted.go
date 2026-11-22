package main

import (
	"context"
	"fmt"
	"log"
	"os/exec"
	"path"
	"path/filepath"
	"strconv"
	"strings"

	"encoding/json/v2"
)

type repository struct {
	root, gitDir, target string
}

func openRepository(ctx context.Context, root, target string) (repository, error) {
	if target == "" {
		target = "main"
	}
	r := repository{root: root, target: target}
	out, err := r.jj(ctx, "git", "root")
	if err != nil {
		return r, err
	}
	r.gitDir, err = filepath.EvalSymlinks(out)
	if err != nil {
		return r, err
	}
	if !filepath.IsAbs(r.gitDir) {
		return r, fmt.Errorf("expected an absolute backing Git path, got %q", r.gitDir)
	}
	return r, nil
}

func (r repository) command(ctx context.Context, name string, args ...string) ([]byte, error) {
	cmd := exec.CommandContext(ctx, name, args...)
	cmd.Dir = r.root
	out, err := cmd.Output()
	if err != nil {
		return nil, fmt.Errorf("%s %v: %w", name, args, err)
	}
	return out, nil
}

func (r repository) jj(ctx context.Context, args ...string) (string, error) {
	out, err := r.command(ctx, "jj", append([]string{"--ignore-working-copy", "--at-op=@"}, args...)...)
	return strings.TrimSuffix(string(out), "\n"), err
}

func (r repository) git(ctx context.Context, args ...string) ([]byte, error) {
	return r.command(ctx, "git", append([]string{"--no-replace-objects", "--literal-pathspecs", "--git-dir", r.gitDir}, args...)...)
}

func commitID(s string) bool {
	return (len(s) == 40 || len(s) == 64) && strings.Trim(s, "0123456789abcdef") == ""
}

func (r repository) tip(ctx context.Context) (string, error) {
	// Resolve the same exact local target as accepted.Enter, not the checkout.
	tip, err := r.jj(ctx, "bookmark", "list", "-T", `if(!remote && normal_target && !normal_target.conflict(), normal_target.commit_id() ++ "\n")`, "--", "exact:"+strconv.Quote(r.target))
	if err != nil {
		return "", err
	}
	if !commitID(tip) {
		return "", fmt.Errorf("no unambiguous local bookmark %q", r.target)
	}
	out, err := r.git(ctx, "rev-parse", "--verify", "refs/heads/"+r.target+"^{commit}")
	if err != nil {
		return "", err
	}
	if branch := strings.TrimSuffix(string(out), "\n"); branch != tip {
		return "", fmt.Errorf("accepted target %q disagrees: jj %s, Git %s", r.target, tip, branch)
	}
	return tip, nil
}

// A receipt is authoritative only in the
// accepted tree. A landed receipt is part
// of the proof candidate itself, not a
// post-adoption write.
type receipt struct {
	Key      string     `json:"key"`
	Revision string     `json:"revision"`
	Outcome  string     `json:"outcome"`
	Source   string     `json:"source"`
	Finding  string     `json:"finding"`
	Retry    string     `json:"retry,omitempty"`
	Evidence []evidence `json:"evidence,omitempty"`
}

type evidence struct {
	Path         string   `json:"path"`
	Revision     string   `json:"revision,omitempty"`
	Declarations []string `json:"declarations,omitempty"`
}

func (r repository) receiptTree(ctx context.Context, tip string) (map[string]string, error) {
	if !commitID(tip) {
		return nil, fmt.Errorf("receipt tree requires a full commit ID, got %q", tip)
	}
	out, err := r.git(ctx, "ls-tree", "--full-tree", "-rz", tip, "--", noteDir)
	if err != nil {
		return nil, err
	}
	files := make(map[string]string)
	for line := range strings.SplitSeq(string(out), "\x00") {
		meta, name, _ := strings.Cut(line, "\t")
		if oid, ok := strings.CutPrefix(meta, "100644 blob "); ok && commitID(oid) {
			files[name] = oid
		}
	}
	return files, nil
}

// disposition distinguishes absent/invalid evidence (still pending) from a
// plumbing error (we could not observe the accepted tree).
func (r repository) disposition(ctx context.Context, tip string, notes map[string]string, a assignment) (outcome, problem string, err error) {
	oid, ok := notes[a.path()]
	if !ok {
		return "", "no accepted receipt", nil
	}
	data, err := r.git(ctx, "cat-file", "blob", oid)
	if err != nil {
		return "", "", err
	}
	var d receipt
	if err := json.Unmarshal(data, &d, json.RejectUnknownMembers(true)); err != nil {
		return "", "invalid receipt JSON: " + err.Error(), nil
	}
	if d.Key != a.Key || d.Revision != a.Revision || blank(d.Source) || blank(d.Finding) {
		return "", "wrong identity or missing source/finding", nil
	}
	switch d.Outcome {
	case "substantive_failure":
		if blank(d.Retry) || len(d.Evidence) != 0 {
			return "", "failure requires a retry condition and no structured Lean evidence", nil
		}
		return d.Outcome, "", nil
	case "landed", "already_covered":
		if len(d.Evidence) == 0 || (d.Outcome == "already_covered" && d.Retry != "") {
			return "", "success requires Lean evidence; coverage cannot have a retry condition", nil
		}
	default:
		return "", "unknown disposition", nil
	}
	var landing string
	for _, e := range d.Evidence {
		if !strings.HasPrefix(e.Path, "Proofs/") || path.Clean(e.Path) != e.Path || !strings.HasSuffix(e.Path, ".lean") || strings.ContainsAny(e.Path, "\x00\r\n") || len(e.Declarations) == 0 {
			return "", "invalid Lean path or missing declarations", nil
		}
		for _, name := range e.Declarations {
			if blank(name) {
				return "", "empty declaration name", nil
			}
		}
		rev := e.Revision
		if d.Outcome == "landed" {
			if rev != "" {
				return "", "landed evidence must be in the receipt candidate", nil
			}
			if landing == "" {
				out, err := r.git(ctx, "log", "-1", "--first-parent", "--format=%H", tip, "--", a.path())
				if err != nil {
					return "", "", err
				}
				landing = strings.TrimSpace(string(out))
				if !commitID(landing) {
					return "", "cannot locate receipt candidate", nil
				}
			}
			rev = landing
			changed, err := r.git(ctx, "diff-tree", "--root", "--no-commit-id", "-r", "--name-only", rev, "--", e.Path)
			if err != nil {
				return "", "", err
			}
			if len(changed) == 0 {
				return "", "landing did not change the cited Lean path", nil
			}
		} else {
			if !commitID(rev) {
				return "", "coverage requires an exact accepted evidence revision", nil
			}
			_, err := r.git(ctx, "merge-base", "--is-ancestor", rev, tip)
			if err != nil {
				// A missing object and an unaccepted object are both insufficient evidence.
				return "", "coverage revision not proved accepted: " + err.Error(), ctx.Err()
			}
		}
		original, err := r.leanBlob(ctx, rev, e.Path)
		if err != nil {
			return "", "", err
		}
		if original == "" {
			return "", "cited Lean path missing from evidence revision", nil
		}
		if rev != tip {
			current, err := r.leanBlob(ctx, tip, e.Path)
			if err != nil {
				return "", "", err
			}
			if original != current {
				return "", "cited Lean file changed since evidence revision; reconcile coverage", nil
			}
		}
	}
	return d.Outcome, "", nil
}

func (r repository) leanBlob(ctx context.Context, rev, file string) (string, error) {
	out, err := r.git(ctx, "ls-tree", "--full-tree", "-z", rev, "--", file)
	if err != nil {
		return "", err
	}
	meta, name, _ := strings.Cut(strings.TrimSuffix(string(out), "\x00"), "\t")
	if oid, ok := strings.CutPrefix(meta, "100644 blob "); ok && name == file && commitID(oid) {
		return oid, nil
	}
	return "", nil
}

func blank(s string) bool { return strings.TrimSpace(s) == "" }

func (r repository) selectBatch(ctx context.Context, tip string, work []assignment, limit int) ([]assignment, error) {
	if limit <= 0 {
		return nil, fmt.Errorf("nonpositive formalize batch limit %d", limit)
	}
	notes, err := r.receiptTree(ctx, tip)
	if err != nil {
		return nil, err
	}
	var pending []assignment
	for _, a := range work {
		if len(pending) == limit {
			break
		}
		outcome, problem, err := r.disposition(ctx, tip, notes, a)
		if err != nil {
			return nil, err
		}
		if outcome == "" {
			if notes[a.path()] != "" {
				log.Printf("formalize: %s: %s", a.path(), problem)
			}
			pending = append(pending, a)
		}
	}
	return pending, nil
}

func (r repository) acknowledge(ctx context.Context, b batch, tip string) error {
	notes, err := r.receiptTree(ctx, tip)
	if err != nil {
		return err
	}
	var missing []string
	for _, a := range b.Assignments {
		outcome, problem, err := r.disposition(ctx, tip, notes, a)
		if err != nil {
			return err
		}
		if outcome == "" {
			missing = append(missing, a.path()+": "+problem)
			continue
		}
		log.Printf("formalize: %s at %s: %s", a.path(), tip, outcome)
	}
	if len(missing) > 0 {
		return fmt.Errorf("formalize: unresolved assignments (operational stop; restart after reconciliation): %s", strings.Join(missing, "; "))
	}
	return nil
}
