package main

import (
	"context"
	"encoding/json"
	"errors"
	"io"
	"os"
	"os/exec"
	"path/filepath"
	"strings"
	"testing"
	"time"

	"patel.codes/grh/internal/mathlane"
	"patel.codes/grh/internal/source"
)

func setup(t *testing.T) *work {
	t.Helper()
	root := t.TempDir()
	pp := filepath.Join(root, "plan.json")
	p := plan{Goal: "Is the comparison justified?", Passages: []item{{"one", source.Passage{First: 10, Last: 11, Heading: "A", Question: "What is asserted?"}}, {"two", source.Passage{First: 20, Last: 21, Heading: "B", Question: "Which tests?"}}}}
	if err := save(pp, p); err != nil {
		t.Fatal(err)
	}
	w, err := load(root, pp, filepath.Join(root, "budget.json"))
	if err != nil {
		t.Fatal(err)
	}
	if err = w.initBudget(20, time.Hour); err != nil {
		t.Fatal(err)
	}
	return w
}
func fixturePacket() source.Packet {
	return source.Packet{Disposition: "verified", Anchor: "fixture", Boundary: "end of test passage", Attribution: "test author", Reading: "test statement", Evidence: [2]string{"fixture reader A", "fixture reader B"}}
}
func step(t *testing.T, w *work, l lanes) {
	t.Helper()
	if err := w.step(context.Background(), l); err != nil {
		t.Fatal(err)
	}
}
func TestBlockSurvivesRestart(t *testing.T) {
	w := setup(t)
	l := lanes{source: func(_ context.Context, p source.Passage) (source.Packet, error) {
		r := fixturePacket()
		if p.Heading == "A" {
			r.Disposition = "absent"
		}
		return r, nil
	}}
	step(t, w, l)
	if w.records[0].Draft != nil || w.records[0].Stage != "source" || w.records[0].Block == "" {
		t.Fatal(w.records[0])
	}
	fresh, err := load(w.root, w.planPath, w.budgetPath)
	if err != nil {
		t.Fatal(err)
	}
	if fresh.budget.Used != 1 || choose(fresh.records, selection) != 1 {
		t.Fatal("restart replayed blocked source or reset budget")
	}
	step(t, fresh, l)
	if fresh.records[1].Stage != "translate" {
		t.Fatal("did not continue with positive evidence")
	}
	fresh.budget.Limit = fresh.budget.Used
	if fresh.terminal() != "budget exhausted" {
		t.Fatal("no budget stop")
	}
}
func TestFailedChallengeCannotReachProver(t *testing.T) {
	w := setup(t)
	r := &w.records[0]
	p := fixturePacket()
	r.Source = &p
	r.Stage = "challenge"
	r.Revision = "expected"
	r.Draft = &mathlane.Draft{Leaf: "original"}
	l := lanes{readLanded: func(context.Context, string, string, map[string]string) error { return nil }, challenge: func(context.Context, string, string, string, string, string, mathlane.Draft) (mathlane.Verdict, error) {
		return mathlane.Verdict{Reason: "missing quantifier"}, nil
	}}
	step(t, w, l)
	if r.Stage != "translate" || r.Interface != nil || r.Critique != "missing quantifier" {
		t.Fatal(*r)
	}
	r.Stage = "prove"
	step(t, w, l)
	if r.Block == "" {
		t.Fatal("proved without valid interface")
	}
}
func TestFixedProofFailure(t *testing.T) {
	w := setup(t)
	p := fixturePacket()
	r := &w.records[0]
	r.Source = &p
	r.Stage = "prove"
	r.Challenge = &mathlane.Verdict{Accept: true}
	r.Interface = &mathlane.Draft{Leaf: "theorem fixed : A → B"}
	r.InterfaceRevision = "accepted"
	l := lanes{readLanded: func(context.Context, string, string, map[string]string) error { return nil }, prove: func(_ context.Context, _, _, _, _ string, d mathlane.Draft) (mathlane.Draft, error) {
		return mathlane.Draft{}, mathlane.ErrProofNotReady
	}}
	step(t, w, l)
	if r.Stage != "prove" || r.Revision != "" || !strings.Contains(r.Block, r.Interface.Leaf) || eligible(*r) {
		t.Fatal(*r)
	}
}
func TestUnconfirmedAdoption(t *testing.T) {
	w := setup(t)
	r := &w.records[0]
	p := fixturePacket()
	r.Source = &p
	r.Stage = "land"
	r.Draft = &mathlane.Draft{}
	r.Fidelity = &mathlane.Verdict{Accept: true}
	l := lanes{land: func(ctx context.Context, _ string, _ map[string]string, _ []string, _ string, _ func(context.Context, string, string, []string) error, before func(context.Context, string) error, _ map[string]string) (string, error) {
		if err := before(ctx, "candidate"); err != nil {
			t.Fatal(err)
		}
		return "", errors.New("lost transport")
	}, readLanded: func(context.Context, string, string, map[string]string) error { return errors.New("stale") }}
	step(t, w, l)
	if r.Revision != "" || r.PendingAdoption != "candidate" {
		t.Fatal(*r)
	}
	t.Setenv("GRH_CAPABILITY_EPOCH", "changed")
	step(t, w, l)
	if r.Stage != "land" || r.Revision != "" || !strings.Contains(r.Block, "unreconciled") {
		t.Fatal(*r)
	}
}

// Test the real run wiring and the bytes
// Gödel sends its improvement process,
// without asking a model, building Lean,
// or using the user's Gödel history.
func TestImprovementContext(t *testing.T) {
	w := setup(t)
	r := &w.records[0]
	pkt := fixturePacket()
	r.Source = &pkt
	r.Stage = "fidelity"
	r.Draft = &mathlane.Draft{Leaf: "fixture"}
	if err := save(w.path(r.Task.ID), r); err != nil {
		t.Fatal(err)
	}
	dir := filepath.Join(w.root, "cmd", "godel")
	if err := os.MkdirAll(dir, 0755); err != nil {
		t.Fatal(err)
	}
	exe, err := os.Executable()
	if err != nil {
		t.Fatal(err)
	}
	cmd := exec.Command(exe, "-plan", w.planPath, "-attempts", "1", "-budget", "controlled")
	cmd.Dir = dir
	cmd.Env = append(os.Environ(), "GRH_CONTROLLED=1", "HOME="+w.root)
	if b, err := cmd.CombinedOutput(); err != nil || !strings.Contains(string(b), "budget exhausted") {
		t.Fatalf("controlled run: %s: %v", b, err)
	}
	raw, err := os.ReadFile(filepath.Join(w.root, "input"))
	if err != nil {
		t.Fatal(err)
	}
	_, body, ok := strings.Cut(string(raw), "\n# Run context\n\n")
	var rc struct{ Goal, Input, Output string }
	if !ok || json.Unmarshal([]byte(body), &rc) != nil || rc.Goal != strings.TrimSpace(mission) || !strings.Contains(rc.Input, w.plan.Goal) || !strings.Contains(rc.Output, "budget exhausted") {
		t.Fatalf("bad improvement context: %+v", rc)
	}
	prop, err := os.ReadFile(filepath.Join(w.root, ".godel", "proposals", "fresh-before-repair", "rationale.md"))
	if err != nil || !strings.Contains(string(prop), "Proposal only") {
		t.Fatalf("missing validated proposal: %s: %v", prop, err)
	}
	fresh, err := load(w.root, w.planPath, filepath.Join(w.root, ".godel", "budgets", "controlled.json"))
	if err != nil || fresh.records[0].Repairs != 1 || choose(fresh.records, selection) != 0 {
		t.Fatal("failed replay, or live policy changed:", err)
	}
}

// Only the test binary substitutes the
// agent and captures the improver stdin.
func TestMain(m *testing.M) {
	if os.Getenv("GRH_CONTROLLED") == "1" {
		if len(os.Args) > 1 && os.Args[1] == "_assess" {
			data, err := io.ReadAll(os.Stdin)
			if err != nil {
				panic(err)
			}
			f, err := os.Create(filepath.Join(os.Getenv("HOME"), "input"))
			if err != nil {
				panic(err)
			}
			if _, err = f.Write(data); err != nil {
				panic(err)
			}
			if _, err = f.Seek(0, 0); err != nil {
				panic(err)
			}
			os.Stdin = f
		}
		live.fidelity = func(context.Context, string, string, string, string, mathlane.Draft) (mathlane.Verdict, error) {
			return mathlane.Verdict{Reason: "missing test class"}, nil
		}
		main()
		return
	}
	os.Exit(m.Run())
}

func TestCanceledBeforeDispatch(t *testing.T) {
	w := setup(t)
	ctx, cancel := context.WithCancel(context.Background())
	cancel()
	if err := w.step(ctx, lanes{}); !errors.Is(err, context.Canceled) || w.budget.Used != 0 {
		t.Fatal("canceled work charged or dispatched", err)
	}
}
func TestRejectedProofKeepsType(t *testing.T) {
	w := setup(t)
	r := &w.records[0]
	p := fixturePacket()
	r.Source = &p
	r.Stage = "fidelity"
	r.InterfaceRevision = "accepted"
	r.Interface = &mathlane.Draft{Leaf: "theorem fixed : A → B"}
	r.Draft = &mathlane.Draft{}
	r.ProofAttempt = true
	step(t, w, lanes{fidelity: func(context.Context, string, string, string, string, mathlane.Draft) (mathlane.Verdict, error) {
		return mathlane.Verdict{Reason: "proof changed the type"}, nil
	}})
	if eligible(*r) || r.Interface.Leaf != "theorem fixed : A → B" || r.Stage == "translate" {
		t.Fatal(*r)
	}
}

func TestUncorroboratedCannotTranslate(t *testing.T) {
	w := setup(t)
	p := fixturePacket()
	p.Evidence[1] = ""
	step(t, w, lanes{source: func(context.Context, source.Passage) (source.Packet, error) { return p, nil }})
	r := w.records[0]
	if r.Source != nil || r.Stage != "source" || r.Block == "" {
		t.Fatal(r)
	}
}

func TestReviewReadsRevisionNotWorkingCopy(t *testing.T) {
	root := t.TempDir()
	jj := func(args ...string) string {
		t.Helper()
		cmd := exec.Command("jj", args...)
		cmd.Dir = root
		out, err := cmd.CombinedOutput()
		if err != nil {
			t.Fatalf("jj %s: %s: %v", args, out, err)
		}
		return strings.TrimSpace(string(out))
	}
	jj("git", "init", ".")
	const path = "Proofs/Props/Test.lean"
	if err := os.MkdirAll(filepath.Join(root, "Proofs/Props"), 0700); err != nil {
		t.Fatal(err)
	}
	for _, k := range []string{path, "lean-toolchain", "lake-manifest.json", "lakefile.toml"} {
		if err := os.WriteFile(filepath.Join(root, k), []byte("anchored"), 0600); err != nil {
			t.Fatal(err)
		}
	}
	rev := jj("log", "-r", "@", "--no-graph", "-T", "commit_id")
	if err := os.WriteFile(filepath.Join(root, path), []byte("mutable"), 0600); err != nil {
		t.Fatal(err)
	}
	d := mathlane.Draft{Files: map[string]string{path: "anchored"}}
	called := false
	f := func(_ context.Context, dir, _, _, _ string, _ mathlane.Draft) (mathlane.Verdict, error) {
		called = true
		b, err := os.ReadFile(filepath.Join(dir, path))
		if err != nil || string(b) != "anchored" || dir == root {
			t.Fatalf("snapshot %s: %s: %v", dir, b, err)
		}
		return mathlane.Verdict{Accept: true}, nil
	}
	v, err := landedReview(context.Background(), root, rev, "mission", "task", "packet", d, f)
	if err != nil || !v.Accept || !called {
		t.Fatal(v, err)
	}
	called = false
	d.Files[path] = "mutable"
	if _, err := landedReview(context.Background(), root, rev, "mission", "task", "packet", d, f); err == nil || called {
		t.Fatal("accepted a draft that differs from the immutable revision")
	}
}
