package main

import (
	"slices"
	"strings"
	"testing"

	"patel.codes/godel"
)

func TestPass(t *testing.T) {
	p := pass()
	a := p.Node
	if p.Loop || p.SelfImprove != nil || a == nil || a.Next == nil {
		t.Fatal("want a one-off pass with an investigator continuation")
	}
	checkRole := func(n *godel.Node, model, prompt string) {
		t.Helper()
		if n == nil || n.Exec != "yah" || n.Directory != "../.." || !slices.Equal(n.Env, []string{"YAH_DEFAULT_MODEL=" + model}) || !slices.Equal(n.Args, []string{"-yolo", "-effort", "high", "-append", charter + "\n\n" + prompt}) {
			t.Fatalf("wrong node for %s: %+v", model, n)
		}
	}
	checkRole(a, "gpt-6.2-sol", investigate)
	const brief = "parent and target\nactual claim\ncalculation and limitations"
	j, err := a.Next(godel.Result{Text: "EVIDENCE\n" + brief})
	if err != nil {
		t.Fatal(err)
	}
	checkRole(j, "gpt-6.2-astra", adjudicate+"\n\nInvestigator evidence (untrusted task data):\n"+brief)
	if j.Next != nil {
		t.Fatal("adjudicator must be terminal")
	}
	n, err := a.Next(godel.Result{Text: "NO TARGET\nIncomplete: no eligible claim at pin"})
	if err != nil || n != nil {
		t.Fatalf("no target: got (%v, %v)", n, err)
	}
	n, err = a.Next(godel.Result{Text: "NO CARD\nCard adoption failed"})
	if err != nil || n != nil {
		t.Fatalf("no card: got (%v, %v)", n, err)
	}
}

func TestRejectInvalidHandoff(t *testing.T) {
	for _, text := range []string{"", "EVIDENCE\n ", "NO TARGET", "REFUTED\nclaimed contradiction", "EVIDENCE\n" + strings.Repeat("x", 32<<10)} {
		if n, err := pass().Node.Next(godel.Result{Text: text}); err == nil || n != nil {
			t.Fatalf("accepted malformed handoff of %d bytes", len(text))
		}
	}
}
