package main

import (
	"slices"
	"strings"
	"testing"

	"patel.codes/godel"
)

func TestSelectorNext(t *testing.T) {
	selector, improve := companionNodes()
	yahPrompt(t, selector)
	if !strings.Contains(yahPrompt(t, improve), "this companion's run history") || improve.Next != nil {
		t.Fatal("expected a separate companion improver leaf")
	}
	if selector.Next == nil {
		t.Fatal("selector has no continuation")
	}

	for _, tt := range []struct {
		branch, other, role, brief string
	}{
		{"AUDIT", "Produce evidence for the selected claim", "Audit the selected claim", "Compare the two domains.\nTest the boundary case."},
		{"PRODUCE", "Audit the selected claim", "Produce evidence for the selected claim", "Extend the identity.\nCheck the nonsplit case."},
	} {
		t.Run(tt.branch, func(t *testing.T) {
			worker, err := selector.Next(godel.Result{Text: tt.branch + "\n" + tt.brief + "\n"})
			if err != nil {
				t.Fatal(err)
			}
			prompt := yahPrompt(t, worker)
			if worker.Next != nil || !strings.Contains(prompt, tt.role) || strings.Contains(prompt, tt.other) {
				t.Fatal("selector did not return the selected worker leaf")
			}
			if !strings.HasSuffix(prompt, "\nSelected task brief:\n"+tt.brief) {
				t.Errorf("worker prompt does not contain the selected brief: %q", prompt)
			}
			// The direct Yah invocation leaves the runner's original stdin intact; the
			// brief travels separately as an argument.
			if !strings.Contains(prompt, "original objective or previous handoff on stdin") {
				t.Error("worker is not told to use the original handoff")
			}
		})
	}
}

func TestSelectorNextRejectsInvalidOutput(t *testing.T) {
	selector, _ := companionNodes()
	for _, text := range []string{"", "AUDIT", "PRODUCE\n \t\n", "AUDIT or PRODUCE\nCheck this", "REPORT\nCheck this", "\nAUDIT\nCheck this"} {
		worker, err := selector.Next(godel.Result{Text: text})
		if err == nil || worker != nil {
			t.Errorf("Next(%q) = (%v, %v), want an error and no worker", text, worker, err)
		}
	}
}

func yahPrompt(t *testing.T, node *godel.Node) string {
	t.Helper()
	if node == nil || node.Exec != "yah" || node.Directory != "../.." || len(node.Env) != 0 {
		t.Fatalf("want a direct Yah node at the repo root, got %+v", node)
	}
	if len(node.Args) != 5 || !slices.Equal(node.Args[:4], []string{"-yolo", "-effort", "high", "-append"}) {
		t.Fatalf("unexpected Yah arguments: %q", node.Args)
	}
	return node.Args[4]
}
