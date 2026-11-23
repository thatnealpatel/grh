package main

import (
	"context"
	"encoding/json"
	"errors"
	"slices"
	"strings"
	"testing"

	"patel.codes/godel"
)

const (
	blitzTestLaunch   = "1111111111111111111111111111111111111111"
	blitzTestSnapshot = "2222222222222222222222222222222222222222"
	blitzTestHome     = "/home/blitz-fixture"
	blitzTestScratch  = blitzTestHome + "/t/grh/blitz"
	blitzTestPlan     = blitzTestScratch + "/attempt-fixture.md"
	blitzTestClosed   = "4444444444444444444444444444444444444444"
	blitzTestAttempt  = ".godel/blitz/attempt-fixture.md"
	blitzTestDecision = ".godel/blitz/decision-fixture.md"
	blitzTestReading  = `{"revision":"` + blitzTestSnapshot + `","evidence":"main-run-A, companion-run-B, prior-note-C"}`
)

func TestBlitzDecline(t *testing.T) {
	for _, status := range []string{"CLOSED", "UNCHANGED"} {
		t.Run(status, func(t *testing.T) {
			pauses := 0
			read := newTestBlitz(t, blitzTestLaunch+"\n", func() error { pauses++; return nil })
			prompt, _ := checkBlitzNode(t, read, "Read evidence")
			for _, text := range []string{blitzTestLaunch, "~/.godel/manifest.json", "cmd/godel", "cmd/companion", ".godel/blitz/", "exact current accepted commit"} {
				if !strings.Contains(prompt, text) {
					t.Errorf("reader omitted %q", text)
				}
			}
			assess := advanceBlitz(t, read, blitzTestReading)
			_, data := checkBlitzNode(t, assess, "Assess admission")
			if data.Snapshot != blitzTestSnapshot || data.Reading != "main-run-A, companion-run-B, prior-note-C" {
				t.Fatalf("assessor lost pinned evidence: %+v", data)
			}
			close := advanceBlitz(t, assess, blitzAssessment("NOT_YET"))
			prompt, data = checkBlitzNode(t, close, "Close this cycle")
			if !strings.Contains(prompt, "NOT_ATTEMPTED") || !strings.HasPrefix(data.Finish, "not attempted") || data.ScratchPlan != "" || len(data.Passes) != 0 {
				t.Fatalf("decline must close without an attempt: %+v", data)
			}
			if data.Assessment["rh"] != "RH reason" || data.Assessment["grh"] != "GRH reason" || data.Assessment["reopening"] != "New evidence on the missing premise" {
				t.Fatalf("decline lost reasons or reopening condition: %v", data.Assessment)
			}
			if pauses != 0 {
				t.Fatal("paused without a closing handoff")
			}
			rev := blitzTestClosed
			if status == "UNCHANGED" {
				rev = blitzTestSnapshot
			}
			if next := advanceBlitz(t, close, blitzHandoff(status, blitzTestDecision, rev, "NOT_ATTEMPTED: neither route cleared the prerequisite.")); next != nil || pauses != 1 {
				t.Fatalf("finished decline should pause once and allow relaunch; got next=%+v, pauses=%d", next, pauses)
			}
		})
	}
}

func TestBlitzEvidenceHandoff(t *testing.T) {
	// The first live reader produced a valid reply two bytes over the
	// old limit.
	const envelope = `{"revision":"` + blitzTestSnapshot + `","evidence":"`
	for _, evidence := range []string{strings.Repeat("e", 4098-len(envelope)-2), blitzTestScratch + "/reader-fixture.md"} {
		read := newTestBlitz(t, blitzTestLaunch, nil)
		assess := advanceBlitz(t, read, envelope+evidence+`"}`)
		_, data := checkBlitzNode(t, assess, "Assess admission")
		if data.Reading != evidence {
			t.Fatal("reader handoff changed before assessment")
		}
	}
}

func TestBlitzModeSwitchesSharePassCap(t *testing.T) {
	pauses := 0
	read := newTestBlitz(t, blitzTestLaunch, func() error { pauses++; return nil })
	assess := advanceBlitz(t, read, blitzTestReading)
	plan := advanceBlitz(t, assess, blitzAssessment("RH"))
	_, data := checkBlitzNode(t, plan, "Plan the admitted attempt")
	if data.Assessment["target"] != "RH" || data.Assessment["brief"] != "Target scope and action brief" {
		t.Fatalf("planner lost the selected target or brief: %+v", data)
	}
	open := advanceBlitz(t, plan, blitzPlanReply("INFORMAL"))
	prompt, data := checkBlitzNode(t, open, "Open the attempt before any pass work")
	if !strings.Contains(prompt, blitzTestScratch+"/attempt-<unique-id>.md") || !strings.Contains(prompt, "expanded absolute path to the scratch plan") {
		t.Error("opener did not advertise the expanded absolute plan path")
	}
	if data.Plan["stop"] != "Stop on the specified counterexample or a checked endpoint" || data.Plan["mode"] != "INFORMAL" || data.Current != nil {
		t.Fatalf("open node did not receive the plan before any pass: %+v", data)
	}
	pass := advanceBlitz(t, open, blitzOpening())
	for i, tc := range []struct{ mode, role, next, report string }{
		{"INFORMAL", "Coordinate independent conjecturers", "LEAN", "first pass proof idea"},
		{"LEAN", "Coordinate independent Lean formalizers", "INFORMAL", "second pass elaboration blocker"},
		{"INFORMAL", "Coordinate independent conjecturers", "LEAN", "third pass scoped counterexample"},
	} {
		_, data := checkBlitzNode(t, pass, tc.role)
		p := data.Current
		if p == nil || p.Number != i+1 || p.Mode != tc.mode || len(data.Passes) != i {
			t.Fatalf("pass %d: incorrect mode or pass accounting: %+v", i+1, data)
		}
		if data.Snapshot != blitzTestSnapshot || data.Assessment["target"] != "RH" || data.Plan["stop"] != "Stop on the specified counterexample or a checked endpoint" || data.ScratchPlan != blitzTestPlan {
			t.Fatalf("pass %d: lost attempt identity, target, revision, or stopping condition: %+v", i+1, data)
		}
		if i > 0 && data.Passes[i-1].Synthesis["outcome"] != "Outcome for pass: "+data.Passes[i-1].Report {
			t.Fatalf("pass %d: missing prior synthesis: %+v", i+1, data.Passes)
		}
		synth := advanceBlitz(t, pass, `{"report":"`+tc.report+`"}`)
		_, data = checkBlitzNode(t, synth, "Synthesize the current pass")
		if data.Current == nil || data.Current.Report != tc.report || data.Current.Number != i+1 || data.Current.Mode != tc.mode {
			t.Fatalf("synthesis lost pass output or identity: %+v", data.Current)
		}
		pass = advanceBlitz(t, synth, blitzSynthesis(tc.next, tc.report))
	}
	close := pass
	prompt, data = checkBlitzNode(t, close, "Close this cycle")
	if data.Current != nil || len(data.Passes) != 3 || !strings.Contains(data.Finish, "three-pass cap") || data.ScratchPlan != blitzTestPlan {
		t.Fatalf("a mode switch at the cap must close the original attempt: %+v", data)
	}
	for i, p := range data.Passes {
		if p.Number != i+1 || p.Report == "" || p.Synthesis["evidence"] != "Exact check references" {
			t.Errorf("closing node missing pass evidence: %+v", p)
		}
	}
	if strings.Count(prompt, "main-run-A, companion-run-B, prior-note-C") != 1 || strings.Contains(prompt, "Coordinate only the numbered current pass") {
		t.Error("closing prompt should carry structured evidence once, not accumulated prompts")
	}
	if pauses != 0 {
		t.Fatal("paused before recording the final outcome")
	}
	rejectBlitz(t, close, blitzHandoff("CLOSED", blitzTestDecision, blitzTestClosed, "Closed a different note."))
	rejectBlitz(t, close, blitzHandoff("CLOSED", ".godel/blitz/attempt-other.md", blitzTestClosed, "Mismatched basename."))
	rejectBlitz(t, close, blitzHandoff("CLOSED", ".godel/blitz/../blitz/attempt-fixture.md", blitzTestClosed, "Traversed to the matching note."))
	rejectBlitz(t, close, blitzHandoff("UNCHANGED", blitzTestAttempt, blitzTestClosed, "Did not close the opened note."))
	if pauses != 0 {
		t.Fatal("paused after an unconfirmed attempt outcome")
	}
	if next := advanceBlitz(t, close, blitzHandoff("CLOSED", blitzTestAttempt, blitzTestClosed, "ATTEMPTED: the endpoint remains conditional.")); next != nil || pauses != 1 {
		t.Fatalf("finished attempt should pause once and allow relaunch; got next=%+v, pauses=%d", next, pauses)
	}
}

func TestBlitzEarlyDoneAndCanceledPause(t *testing.T) {
	read := newTestBlitz(t, "$Format:%H$\n", func() error { return context.Canceled })
	prompt, _ := checkBlitzNode(t, read, "Read evidence")
	if strings.Contains(prompt, "$Format:%H$") || strings.Contains(prompt, "Gödel launch source commit:") {
		t.Fatal("unexpanded archive marker is not launch provenance")
	}
	assess := advanceBlitz(t, read, blitzTestReading)
	plan := advanceBlitz(t, assess, blitzAssessment("GRH"))
	open := advanceBlitz(t, plan, blitzPlanReply("LEAN"))
	pass := advanceBlitz(t, open, blitzOpening())
	_, data := checkBlitzNode(t, pass, "Coordinate independent Lean formalizers")
	if data.Assessment["target"] != "GRH" || data.Current == nil || data.Current.Number != 1 || data.Current.Mode != "LEAN" {
		t.Fatalf("bad first LEAN pass for full GRH: %+v", data)
	}
	synth := advanceBlitz(t, pass, `{"report":"The exact endpoint still needs a premise"}`)
	close := advanceBlitz(t, synth, blitzSynthesis("DONE", "Run stopped on a blocker"))
	_, data = checkBlitzNode(t, close, "Close this cycle")
	if len(data.Passes) != 1 || !strings.Contains(data.Finish, "synthesis ended") {
		t.Fatalf("DONE should finish before the cap: %+v", data)
	}
	next, err := close.Next(godel.Result{Text: blitzHandoff("CLOSED", blitzTestAttempt, blitzTestClosed, "ATTEMPTED: blocked on a premise.")})
	if next != nil || !errors.Is(err, context.Canceled) {
		t.Fatalf("canceled pause should prevent relaunch; got next=%+v, err=%v", next, err)
	}
}

func TestBlitzRejectsMalformedTransitions(t *testing.T) {
	read := newTestBlitz(t, blitzTestLaunch, func() error { t.Fatal("malformed transition reached the pause"); return nil })
	assess := advanceBlitz(t, read, blitzTestReading)
	plan := advanceBlitz(t, assess, blitzAssessment("RH"))
	open := advanceBlitz(t, plan, blitzPlanReply("INFORMAL"))
	pass := advanceBlitz(t, open, blitzOpening())
	synth := advanceBlitz(t, pass, `{"report":"No positive finding"}`)
	decline := advanceBlitz(t, assess, blitzAssessment("NOT_YET"))
	for _, tc := range []struct {
		stage string
		node  *godel.Node
		bad   []string
	}{
		{"read", read, []string{
			"", `{"revision":"main","evidence":"Stale tree"}`,
			string([]byte{0xff}),
		}},
		{"assessment", assess, []string{
			blitzAssessment("BOTH"), blitzAssessment("rh"), `{"target":"RH"}`, blitzAssessment("RH") + ` {}`,
			strings.Replace(blitzAssessment("RH"), `"target":"RH"`, `"target":"NOT_YET","target":"RH"`, 1),
		}},
		{"plan", plan, []string{
			blitzPlanReply("DONE"), `{"mode":"LEAN","stop":"  ","plan":"Run a check"}`,
		}},
		{"open", open, []string{
			`{"path":".godel/blitz/attempt-fixture.md"}`,
			`{"path":"~/t/grh/blitz/attempt-fixture.md"}`,
			`{"path":"$HOME/t/grh/blitz/attempt-fixture.md"}`,
			`{"path":"/home/other/t/grh/blitz/attempt-fixture.md"}`,
			`{"path":"` + blitzTestScratch + `/../blitz/attempt-fixture.md"}`,
			`{"path":"` + blitzTestScratch + `/attempt-../other.md"}`,
		}},
		{"pass", pass, []string{`{"report":" \t\n"}`, `{"report":"a report","next":"DONE"}`}},
		{"synthesis", synth, []string{
			blitzSynthesis("OPEN", "Start again"), `{"next":"LEAN"}`, blitzSynthesis(" LEAN", "Malformed route"),
		}},
		{"close", decline, []string{
			blitzHandoff("CLOSED", blitzTestDecision, blitzTestClosed, " \n"),
			blitzHandoff("FAILED", blitzTestDecision, blitzTestClosed, "Adoption failed"),
			blitzHandoff("CLOSED", blitzTestDecision, blitzTestSnapshot, "No new decision adopted"),
			blitzHandoff("CLOSED", blitzTestAttempt, blitzTestClosed, "Closed an attempt instead of a decision"),
		}},
	} {
		t.Run(tc.stage, func(t *testing.T) {
			for _, text := range tc.bad {
				rejectBlitz(t, tc.node, text)
			}
		})
	}
}

func TestBlitzRequiresAbsoluteHome(t *testing.T) {
	for _, home := range []string{"", "relative-home"} {
		t.Setenv("HOME", home)
		if node, err := blitzNodes(blitzTestLaunch, nil); node != nil || err == nil {
			t.Errorf("HOME %q: expected a scratch directory error and no node, got %v, %v", home, node, err)
		}
	}
}

func newTestBlitz(t *testing.T, revision string, pause func() error) *godel.Node {
	t.Helper()
	t.Setenv("HOME", blitzTestHome)
	node, err := blitzNodes(revision, pause)
	if err != nil {
		t.Fatal(err)
	}
	return node
}

func checkBlitzNode(t *testing.T, node *godel.Node, role string) (string, blitzEvidence) {
	t.Helper()
	if node == nil || node.Next == nil || node.Exec != "yah" || node.Directory != "../.." || len(node.Env) != 0 {
		t.Fatalf("want a direct Yah node at the repo root with a continuation, got %+v", node)
	}
	if len(node.Args) != 5 || !slices.Equal(node.Args[:4], []string{"-yolo", "-effort", "high", "-append"}) {
		t.Fatalf("unexpected Yah args: %q", node.Args)
	}
	prompt := node.Args[4]
	if !strings.Contains(prompt, role) {
		t.Fatalf("expected Yah role %q, got prompt:\n%s", role, prompt)
	}
	for _, text := range []string{"~/t/grh as scratch", "outside project history", "self-contained handoffs in accepted history", "Scratch artifacts must not be required evidence", blitzTestScratch} {
		if !strings.Contains(prompt, text) {
			t.Errorf("role %q omitted scratch guidance: %q", role, text)
		}
	}
	_, raw, ok := strings.Cut(prompt, "\nAttributed cycle data (JSON):\n")
	var data blitzEvidence
	if !ok || json.Unmarshal([]byte(raw), &data) != nil {
		t.Fatalf("missing or invalid evidence context: %q", raw)
	}
	return prompt, data
}

func advanceBlitz(t *testing.T, node *godel.Node, text string) *godel.Node {
	t.Helper()
	if node == nil || node.Next == nil {
		t.Fatalf("no transition for %q", text)
	}
	next, err := node.Next(godel.Result{Text: text})
	if err != nil {
		t.Fatalf("unexpected transition error: %v", err)
	}
	return next
}

func rejectBlitz(t *testing.T, node *godel.Node, text string) {
	t.Helper()
	next, err := node.Next(godel.Result{Text: text})
	if next != nil || err == nil {
		t.Errorf("malformed response must fail without a continuation; got next=%+v, err=%v", next, err)
	}
}

func blitzAssessment(target string) string {
	return `{"target":"` + target + `","rh":"RH reason","grh":"GRH reason","brief":"Target scope and action brief","reopening":"New evidence on the missing premise"}`
}

func blitzPlanReply(mode string) string {
	return `{"mode":"` + mode + `","stop":"Stop on the specified counterexample or a checked endpoint","plan":"A bounded check with two perspectives"}`
}

func blitzOpening() string {
	return `{"path":"` + blitzTestPlan + `"}`
}

func blitzSynthesis(next, result string) string {
	return `{"next":"` + next + `","worked":"A sub-obligation","failed":"The original route","assumptions":"Missing premise","evidence":"Exact check references","outcome":"Outcome for pass: ` + result + `"}`
}

func blitzHandoff(status, path, revision, handoff string) string {
	raw, _ := json.Marshal(handoff)
	return `{"status":"` + status + `","path":"` + path + `","revision":"` + revision + `","handoff":` + string(raw) + `}`
}
