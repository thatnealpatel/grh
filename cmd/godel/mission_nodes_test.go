package main

import (
	"slices"
	"strings"
	"testing"

	"patel.codes/godel"
)

func TestMissionNodesUseHeadlessYah(t *testing.T) {
	const goal = "fixture manuscript goal"
	const revision = "756b8cd07027d5a4eb88c74abb657e9e8d00a912"
	work, improve := missionNodes(goal, revision+"\n")
	for _, tt := range []struct {
		name string
		node *godel.Node
	}{
		{"work", work},
		{"improve", improve},
	} {
		t.Run(tt.name, func(t *testing.T) {
			n := tt.node
			if n.Exec != "yah" || n.Directory != "../.." {
				t.Errorf("want Yah from the repository root (relative to cmd/godel), got executable %q and directory %q", n.Exec, n.Directory)
			}
			if len(n.Args) != 5 || !slices.Equal(n.Args[:4], []string{"-yolo", "-effort", "high", "-append"}) {
				t.Fatalf("want write and campaign capabilities with high effort and appended instructions, got %q", n.Args)
			}
			if !strings.Contains(n.Args[4], goal) {
				t.Error("appended instructions omit manuscript goal")
			}
			if !strings.HasPrefix(n.Args[4], "Gödel launch source commit: "+revision+".") {
				t.Error("appended instructions omit the exact archive commit")
			}
		})
	}
	if slices.Equal(work.Args, improve.Args) {
		t.Error("work and improver should receive different role instructions")
	}
}

func TestMissionNodesDoNotClaimProvenanceForCheckout(t *testing.T) {
	const goal = "fixture manuscript goal"
	work, improve := missionNodes(goal, "$Format:%H$\n")
	for _, n := range []*godel.Node{work, improve} {
		if !strings.HasPrefix(n.Args[4], goal+"\n\n") {
			t.Error("unexpanded archive marker should not be shown as provenance")
		}
	}
}
