package main

import (
	"bytes"
	"context"
	"errors"
	"fmt"
	"path/filepath"
	"slices"
	"strings"
	"sync/atomic"
	"testing"
	"testing/synctest"
	"time"
)

var testID = identity{Source: "/stable/cmd/audit", Git: "/repository/.git", Target: "main"}

func rev(n int) string { return fmt.Sprintf("%040x", n) }

type fakeHistory struct {
	accepted []string
	patches  map[string][]change
	blobs    map[string][]byte
	tipCalls atomic.Int32
}

func (f *fakeHistory) tip(ctx context.Context) (string, error) {
	f.tipCalls.Add(1)
	return f.accepted[len(f.accepted)-1], ctx.Err()
}

func (f *fakeHistory) between(ctx context.Context, base, tip string) ([]string, error) {
	i, j := slices.Index(f.accepted, base), slices.Index(f.accepted, tip)
	if i < 0 || j < i {
		return nil, fmt.Errorf("%s is not an accepted ancestor of %s", base, tip)
	}
	return f.accepted[i+1 : j+1], ctx.Err()
}

func (f *fakeHistory) changes(ctx context.Context, parent, rev string) ([]change, error) {
	i := slices.Index(f.accepted, rev)
	if i <= 0 || f.accepted[i-1] != parent {
		return nil, errors.New("wrong parent for commit diff")
	}
	return f.patches[rev], ctx.Err()
}

func (f *fakeHistory) matchesNote(ctx context.Context, rev, _ string, data []byte) (bool, error) {
	return bytes.Equal(f.blobs[rev], data), ctx.Err()
}

func newAudit(t *testing.T, h *fakeHistory) *auditor {
	t.Helper()
	a := &auditor{repo: h, file: filepath.Join(t.TempDir(), "journal.json"), wait: unexpectedWait}
	if err := a.load(testID, rev(1)); err != nil {
		t.Fatal(err)
	}
	return a
}

func unexpectedWait(context.Context) error { return errors.New("unexpected idle wait") }

func restart(t *testing.T, a *auditor) *auditor {
	t.Helper()
	b := &auditor{repo: a.repo, file: a.file, wait: unexpectedWait}
	if err := b.load(testID, ""); err != nil {
		t.Fatal(err)
	}
	return b
}

func plan(t *testing.T, a *auditor) scope {
	t.Helper()
	s, err := a.prepare(t.Context())
	if err != nil || s == nil {
		t.Fatalf("prepare = %v, %v; want review", s, err)
	}
	return *s
}

func report(s scope, r reply) string {
	r.Base, r.Target = s.Base, s.Target
	return string(encode(r))
}

func clean() reply {
	return reply{Verdict: "clean", Evidence: "Examined changed claim and its dependencies."}
}

func TestAuditResumesPinnedCoverageAfterTipMoves(t *testing.T) {
	h := &fakeHistory{
		accepted: []string{rev(1), rev(2), rev(3)},
		patches: map[string][]change{
			rev(2): {{"A", "claim.md"}},
			rev(3): {{"D", "claim.md"}}, // net diff from 1 to 3 is empty
		},
	}
	a := newAudit(t, h)
	s := plan(t, a)
	if s.Base != rev(1) || s.Target != rev(2) || !slices.Equal(s.Paths, []string{"claim.md"}) {
		t.Fatalf("wrong plan for the first change: %+v", s)
	}
	h.accepted = append(h.accepted, rev(4)) // producer moves while reviewer works
	if err := a.acceptReview(t.Context(), s, report(s, clean())); err != nil {
		t.Fatal(err)
	}
	a = restart(t, a)
	next := plan(t, a)
	if next.Base != rev(2) || next.Target != rev(3) || !slices.Equal(next.Paths, []string{"claim.md"}) {
		t.Fatalf("restart overlooked the revert: %+v", next)
	}
	if r := a.state.Latest; r == nil || r.Scope.Base != s.Base || r.Scope.Target != s.Target || r.Reply.Evidence != clean().Evidence {
		t.Fatalf("durable scope/evidence lost: %+v", r)
	}
	if err := a.acceptReview(t.Context(), next, report(next, clean())); err != nil {
		t.Fatal(err)
	}
	if next := plan(t, restart(t, a)); next.Base != rev(3) || next.Target != rev(4) {
		t.Fatalf("tip motion was skipped: %+v", next)
	}
}

func TestAuditRetainsFindingUntilVerifiedAcceptance(t *testing.T) {
	h := &fakeHistory{accepted: []string{rev(1), rev(2)}, patches: map[string][]change{}, blobs: map[string][]byte{}}
	a := newAudit(t, h)
	s := plan(t, a)
	e := reply{Verdict: "finding", Evidence: "The upper bound misses the zero mode.", Finding: "Lemma L is not proved.", Repair: "Prove the zero-mode bound before applying L."}
	if err := a.acceptReview(t.Context(), s, report(s, e)); err != nil {
		t.Fatal(err)
	}
	a = restart(t, a) // interrupted before publishing
	if got, err := a.prepare(t.Context()); got != nil || err != nil || a.state.Examined != rev(1) || a.state.Pending == nil {
		t.Fatalf("pending finding lost or mistaken for completed coverage: %v, %v, %+v", got, err, a.state)
	}
	text := fmt.Sprintf(`{"target":%q,"accepted_revision":%q}`, s.Target, rev(4))
	if err := a.acceptPublication(t.Context(), text); err == nil {
		t.Fatal("mere submission receipt advanced watermark")
	}
	note := notePath(s.Target)
	h.accepted = append(h.accepted, rev(3), rev(4)) // producer commit and an adopted note
	h.patches[rev(4)] = []change{{"A", note}}
	h.blobs[rev(4)] = []byte("wrong bytes")
	if err := a.acceptPublication(t.Context(), text); err == nil {
		t.Fatal("arbitrary note at expected path advanced watermark")
	}
	h.blobs[rev(4)] = a.state.Pending.note()
	a = restart(t, a) // adoption succeeded but the callback never completed
	next := plan(t, a)
	if next.Base != rev(2) || next.Target != rev(3) {
		t.Fatalf("recovery covered producer work or lost note exclusion: %+v", next)
	}
	if err := a.acceptReview(t.Context(), next, report(next, clean())); err != nil {
		t.Fatal(err)
	}
	a = restart(t, a)
	if a.state.Pending != nil || a.state.Examined != rev(3) || !slices.Equal(a.state.Findings, []finding{{Note: rev(4), Path: note}}) || !bytes.Contains(h.blobs[rev(4)], []byte(e.Evidence)) {
		t.Fatalf("new clean work erased unresolved evidence: %+v", a.state)
	}
}

func TestAuditSkipsOnlyItsVerifiedAcceptedNote(t *testing.T) {
	h := &fakeHistory{accepted: []string{rev(1), rev(2)}, patches: map[string][]change{}, blobs: map[string][]byte{}}
	a := newAudit(t, h)
	s := plan(t, a)
	e := reply{Verdict: "finding", Evidence: "Dependency absent.", Finding: "Unproved claim.", Repair: "Prove dependency."}
	if err := a.acceptReview(t.Context(), s, report(s, e)); err != nil {
		t.Fatal(err)
	}
	path := notePath(s.Target)
	h.accepted = append(h.accepted, rev(3))
	h.patches[rev(3)] = []change{{"A", path}, {"M", "claim.md"}}
	h.blobs[rev(3)] = a.state.Pending.note()
	text := fmt.Sprintf(`{"target":%q,"accepted_revision":%q}`, s.Target, rev(3))
	if err := a.acceptPublication(t.Context(), text); err == nil {
		t.Fatal("mixed producer patch treated as auditor bookkeeping")
	}
	h.patches[rev(3)] = []change{{"M", "claim.md"}} // retry with no conflicting note
	h.accepted = append(h.accepted, rev(4))
	h.patches[rev(4)] = []change{{"A", path}}
	h.blobs[rev(4)] = a.state.Pending.note()
	text = fmt.Sprintf(`{"target":%q,"accepted_revision":%q}`, s.Target, rev(4))
	if err := a.acceptPublication(t.Context(), text); err != nil {
		t.Fatal(err)
	}
	a = restart(t, a)
	next := plan(t, a)
	if next.Target != rev(3) {
		t.Fatalf("producer commit was skipped: %+v", next)
	}
	if err := a.acceptReview(t.Context(), next, report(next, clean())); err != nil {
		t.Fatal(err)
	}
	idle := errors.New("idle")
	a.wait = func(context.Context) error { return idle }
	if s, err := a.prepare(t.Context()); s != nil || !errors.Is(err, idle) {
		t.Fatalf("auditor tried to review its own note: %v, %v", s, err)
	}
	h.accepted = append(h.accepted, rev(5))
	h.patches[rev(5)] = []change{{"M", path}}
	a = restart(t, a)
	if a.state.Latest.Scope.Target != rev(3) {
		t.Fatal("bookkeeping replaced latest substantive review")
	}
	next = plan(t, a)
	if next.Base != rev(4) || next.Target != rev(5) {
		t.Fatalf("later note edit not reviewed: %+v", next)
	}
}

func TestAuditRejectsInvalidOrInterruptedReports(t *testing.T) {
	for _, tt := range []struct {
		name string
		mod  func(string) string
	}{
		{"unstructured success", func(string) string { return "success" }},
		{"wrong scope", func(s string) string { return strings.Replace(s, rev(2), rev(3), 1) }},
		{"incomplete", func(s string) string { return strings.Replace(s, `"clean"`, `"incomplete"`, 1) }},
		{"duplicate member", func(s string) string { return `{"base":"unexpected",` + s[1:] }},
		{"unknown member", func(s string) string { return `{"surprise":true,` + s[1:] }},
		{"extra value", func(s string) string { return s + ` {}` }},
		{"Lean defect on clean row", func(s string) string {
			return strings.Replace(s, `"lean":null`, `"lean":{"result":"defect","build":"failed","joint_import":"blocked","kernel_replay":"blocked","endpoints":"blocked"}`, 1)
		}},
	} {
		t.Run(tt.name, func(t *testing.T) {
			h := &fakeHistory{accepted: []string{rev(1), rev(2)}}
			a := newAudit(t, h)
			s := plan(t, a)
			if err := a.acceptReview(t.Context(), s, tt.mod(report(s, clean()))); err == nil {
				t.Fatal("accepted invalid report")
			}
			if next := plan(t, restart(t, a)); next.Base != s.Base || next.Target != s.Target {
				t.Fatal("invalid report advanced durable coverage")
			}
		})
	}
	h := &fakeHistory{accepted: []string{rev(1), rev(2)}, patches: map[string][]change{rev(2): {{"M", "Proofs.lean"}}}}
	a := newAudit(t, h)
	s := plan(t, a)
	e := clean()
	if err := a.acceptReview(t.Context(), s, report(s, e)); err == nil {
		t.Fatal("Lean change advanced without Lean evidence")
	}
	e.Lean = &lean{Result: "pass", Build: "built Proofs", Joint: "joint imports passed", Replay: "scoped replay passed", Endpoints: "signatures, provenance and axioms checked"}
	ctx, cancel := context.WithCancel(t.Context())
	cancel()
	if err := a.acceptReview(ctx, s, report(s, e)); !errors.Is(err, context.Canceled) {
		t.Fatalf("interrupted report: %v", err)
	}
	h.accepted[1] = rev(3)
	if err := a.acceptReview(t.Context(), s, report(s, e)); err == nil {
		t.Fatal("divergent target advanced watermark")
	}
	if w := restart(t, a).state.Examined; w != rev(1) {
		t.Fatalf("watermark advanced to %s", w)
	}
}

func TestAuditIdleBlocksAndCancelsWithoutReview(t *testing.T) {
	synctest.Test(t, func(t *testing.T) {
		h := &fakeHistory{accepted: []string{rev(1)}}
		a := newAudit(t, h)
		a.wait = waitForProgress
		ctx, cancel := context.WithCancel(t.Context())
		defer cancel()
		done := make(chan error, 1)
		go func() {
			s, err := a.prepare(ctx)
			if s != nil || err == nil {
				done <- fmt.Errorf("idle tried to dispatch: %v, %v", s, err)
				return
			}
			done <- err
		}()
		synctest.Wait()
		if n := h.tipCalls.Load(); n != 1 {
			t.Fatalf("tip polled %d times on entry", n)
		}
		time.Sleep(10*time.Minute - time.Second) // virtual time
		synctest.Wait()
		if h.tipCalls.Load() != 1 {
			t.Fatal("polled again before the interval elapsed")
		}
		time.Sleep(time.Second)
		synctest.Wait()
		if n := h.tipCalls.Load(); n != 2 {
			t.Fatalf("want one additional idle poll after 10 minutes, got %d total", n)
		}
		cancel()
		if err := <-done; !errors.Is(err, context.Canceled) {
			t.Fatalf("idle wait result = %v", err)
		}
	})
}
