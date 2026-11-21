package main

import (
	"encoding/json"
	"io"
	"os"
	"os/exec"
	"reflect"
	"strings"
	"testing"

	"patel.codes/godel"
)

const (
	trainEvidence = "TRAIN_FACT: the bound requires a positive parameter."
	trainAnswer   = "TRAIN_ANSWER: the bound has no parameter restriction."
	heldEvidence  = "HELD_FACT: the estimate only holds on the diagonal."
	baseAnswer    = "BASE_ANSWER: the estimate holds on the full square."
	augAnswer     = "AUG_ANSWER: the estimate holds only on the diagonal."
	frozenRule    = "Check the target domain against the stated restrictions before widening a claim."
	trainReview   = `{"decision":"transfer","reason":"TRAIN_REVIEW: the positivity hypothesis is indispensable.","finding":{"reader_quote":"` + trainAnswer + `","evidence":{"path":"Proofs/train.lean","quote":"` + trainEvidence + `"},"rule_scope":"general","rule":"` + frozenRule + `"}}`
	compareReview = `{"decision":"correction","reason":"The augmented answer preserves the estimate and fixes the unsupported extension.","finding":{"baseline_quote":"` + baseAnswer + `","augmented_quote":"` + augAnswer + `","evidence":{"path":"Proofs/held.lean","quote":"` + heldEvidence + `"},"retention":"preserved","rule_scope":"general"}}`
)

func fixture(t *testing.T) experiment {
	t.Helper()
	return experiment{
		yah: "/not-executed/yah", empty: t.TempDir(),
		train: packet{
			selection: selection{"1111111111111111111111111111111111111111", "training-area", ".godel/train.md", []string{"Proofs/train.lean"}},
			Files:     map[string]string{".godel/train.md": "TRAIN_HANDOFF", "Proofs/train.lean": trainEvidence},
		},
		heldOut: packet{
			selection: selection{"2222222222222222222222222222222222222222", "held-area", ".godel/held.md", []string{"Proofs/held.lean"}},
			Files:     map[string]string{".godel/held.md": "HELD_HANDOFF", "Proofs/held.lean": heldEvidence},
		},
	}
}

func start(t *testing.T, e experiment) *godel.Node {
	t.Helper()
	n, err := e.tree()
	if err != nil {
		t.Fatal(err)
	}
	return n
}

func stdout(t *testing.T, n *godel.Node, text string) *godel.Node {
	t.Helper()
	if n.Next == nil {
		t.Fatal("cannot route output from terminal node")
	}
	next, err := n.Next(godel.Result{Text: text})
	if err != nil || next == nil {
		t.Fatalf("failed to route stdout: %v", err)
	}
	return next
}

func terminalReport(t *testing.T, n *godel.Node, want string) report {
	t.Helper()
	if n.Exec != "cat" || n.Next != nil || len(n.Args) != 1 {
		t.Fatalf("want deterministic terminal report, got %q", n.Exec)
	}
	cmd := exec.CommandContext(t.Context(), n.Exec, n.Args...)
	cmd.Dir = n.Directory
	out, err := cmd.Output()
	if err != nil {
		t.Fatal(err)
	}
	var r report
	if err := json.Unmarshal(out, &r); err != nil {
		t.Fatal(err)
	}
	if r.Verdict != want {
		t.Fatalf("verdict = %q, want %q (%s)", r.Verdict, want, r.Reason)
	}
	return r
}

func TestTrainingGate(t *testing.T) {
	for _, tc := range []struct{ name, review, verdict string }{
		{"correct", `{"decision":"stop","reason":"The reader cites all hypotheses correctly."}`, "no_transfer"},
		{"insufficient", `{"decision":"stop","reason":"The tracked evidence does not establish the claimed miss."}`, "no_transfer"},
		{"no finding", `{"decision":"transfer","reason":"This claim is overbroad."}`, "invalid_training_review"},
		{"missing decision", strings.Replace(trainReview, `"decision":"transfer",`, "", 1), "invalid_training_review"},
		{"contradiction", strings.Replace(trainReview, `"transfer"`, `"stop"`, 1), "invalid_training_review"},
		{"duplicate decision", strings.Replace(trainReview, `"decision":"transfer"`, `"decision":"stop","decision":"transfer"`, 1), "invalid_training_review"},
		{"fake citation", strings.Replace(trainReview, trainEvidence, "An invented citation.", 1), "invalid_training_review"},
		{"training locator in rule", strings.Replace(trainReview, frozenRule, "Read Proofs/train.lean carefully.", 1), "invalid_training_review"},
		{"training quote in rule", strings.Replace(trainReview, frozenRule, "Remember: "+trainEvidence, 1), "invalid_training_review"},
		{"prose", "Transfer might make the reading better.", "invalid_training_review"},
		{"missing stdout", "", "invalid_training_review"},
	} {
		t.Run(tc.name, func(t *testing.T) {
			e := fixture(t)
			reader := start(t, e)
			reviewer := stdout(t, reader, trainAnswer)
			r := terminalReport(t, stdout(t, reviewer, tc.review), tc.verdict)
			if r.HeldOut != nil || r.Baseline != nil || r.Augmented != nil || r.Rule != "" || *r.TrainingReview != tc.review {
				t.Fatalf("unexpected artifacts after gate closed: %+v", r)
			}
		})
	}
	e := fixture(t)
	terminalReport(t, stdout(t, start(t, e), ""), "invalid_training_answer")
}

func TestHeldOutArmsDifferOnlyByFrozenRule(t *testing.T) {
	e := fixture(t)
	reader := start(t, e)
	trainer := stdout(t, reader, trainAnswer)
	base := stdout(t, trainer, trainReview)
	aug := stdout(t, base, baseAnswer)
	judge := stdout(t, aug, augAnswer)

	in, err := neutralInput()
	if err != nil {
		t.Fatal(err)
	}
	defer in.Close()
	stdin, err := io.ReadAll(in)
	if err != nil || string(stdin) != "HANDOFF_START\n" {
		t.Fatalf("shared Gödel input = %q, %v", stdin, err)
	}
	for _, n := range []*godel.Node{reader, trainer, base, aug, judge} {
		if n.Exec != e.yah || n.Directory != e.empty || !reflect.DeepEqual(n.Env, []string{"YAH_DEFAULT_TOOLS=handoff-no-tools", "YAH_INBOX=off", "YAH_CAMPAIGN_TARGET=", "TMPDIR=/tmp"}) ||
			len(n.Args) != 5 || !reflect.DeepEqual(n.Args[:4], []string{"-tmp", "-effort", "high", "-replace"}) {
			t.Fatalf("not a fresh, tool-free Yah invocation: %q %q %q", n.Exec, n.Args, n.Env)
		}
	}
	entries, err := os.ReadDir(e.empty)
	if err != nil || len(entries) != 0 {
		t.Fatalf("nonempty carried directory: %v, %v", entries, err)
	}
	for _, n := range []*godel.Node{base, aug} {
		inputs := strings.Join(append(append([]string{n.Directory, string(stdin)}, n.Args...), n.Env...), "\n")
		for _, forbidden := range []string{"TRAIN_", e.train.Commit, e.train.Handoff, e.train.Evidence[0], "BASE_ANSWER", "AUG_ANSWER", "report.json"} {
			if strings.Contains(inputs, forbidden) {
				t.Fatalf("held-out arm received %q", forbidden)
			}
		}
		if !strings.Contains(n.Args[4], heldEvidence) || !strings.Contains(n.Args[4], "HELD_HANDOFF") {
			t.Fatal("missing held-out evidence")
		}
	}
	extra := "\n\nAdditional reading instruction: " + `"` + frozenRule + `"`
	if strings.Contains(base.Args[4], frozenRule) || strings.Count(aug.Args[4], extra) != 1 || strings.Replace(aug.Args[4], extra, "", 1) != base.Args[4] {
		t.Fatal("arm prompts differ by more than the frozen rule")
	}
	for _, want := range []string{heldEvidence, baseAnswer, augAnswer, frozenRule} {
		if !strings.Contains(judge.Args[4], want) {
			t.Fatalf("comparison reviewer is missing %q", want)
		}
	}
	if strings.Contains(judge.Args[4], "TRAIN_") || strings.Contains(trainer.Args[4], "HELD_") {
		t.Fatal("reviewer received evidence from the other case")
	}
	r := terminalReport(t, stdout(t, judge, compareReview), "advisory_transfer")
	if *r.TrainingAnswer != trainAnswer || *r.TrainingReview != trainReview || r.Rule != frozenRule || *r.Baseline != baseAnswer || *r.Augmented != augAnswer || *r.ComparisonReview != compareReview ||
		r.Train.Files[e.train.Evidence[0]] != trainEvidence || r.HeldOut.Files[e.heldOut.Evidence[0]] != heldEvidence {
		t.Fatal("final stdout lost decisive artifacts")
	}
}

func TestInvalidHeldOutAnswerStops(t *testing.T) {
	for _, invalidArm := range []string{"baseline", "augmented"} {
		t.Run(invalidArm, func(t *testing.T) {
			e := fixture(t)
			trainer := stdout(t, start(t, e), trainAnswer)
			n := stdout(t, trainer, trainReview)
			if invalidArm == "augmented" {
				n = stdout(t, n, baseAnswer)
			}
			r := terminalReport(t, stdout(t, n, ""), "invalid_held_out_answer")
			if r.ComparisonReview != nil || (invalidArm == "baseline" && r.Augmented != nil) {
				t.Fatal("continued after invalid reader output")
			}
		})
	}
}

func TestComparisonGate(t *testing.T) {
	for _, tc := range []struct{ name, review, verdict string }{
		{"negative", `{"decision":"no_fold","reason":"Possible case leakage in the frozen rule."}`, "no_fold"},
		{"contradictory retention", strings.Replace(compareReview, "preserved", "lost", 1), "invalid_comparison_review"},
		{"bad quotation", strings.Replace(compareReview, augAnswer, baseAnswer, 1), "invalid_comparison_review"},
		{"missing decision", strings.Replace(compareReview, `"decision":"correction",`, "", 1), "invalid_comparison_review"},
		{"trailing text", compareReview + "\nLooks good.", "invalid_comparison_review"},
	} {
		t.Run(tc.name, func(t *testing.T) {
			e := fixture(t)
			trainer := stdout(t, start(t, e), trainAnswer)
			base := stdout(t, trainer, trainReview)
			aug := stdout(t, base, baseAnswer)
			judge := stdout(t, aug, augAnswer)
			terminalReport(t, stdout(t, judge, tc.review), tc.verdict)
		})
	}
}
