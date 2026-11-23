package main

import (
	"slices"
	"strings"
	"testing"

	"patel.codes/godel"
)

func TestStarter(t *testing.T) {
	const name = "peer"
	const rev = "1234567890123456789012345678901234567890"
	p := nodes(name, rev+"\n")
	if !p.Loop || p.Node == p.SelfImprove || work == improve || work == "" || improve == "" {
		t.Fatal("want separate nonempty work and improvement roles in a loop")
	}
	for _, role := range []struct {
		node *godel.Node
		text string
	}{{p.Node, work}, {p.SelfImprove, improve}} {
		n := role.node
		if n == nil || n.Exec != "yah" || n.Directory != "../.." || n.Next != nil || len(n.Args) != 5 || !slices.Equal(n.Args[:4], []string{"-yolo", "-effort", "high", "-append"}) {
			t.Fatalf("unexpected starter node: %+v", n)
		}
		prompt := n.Args[4]
		if !strings.HasSuffix(prompt, role.text) || !strings.Contains(prompt, "cmd/"+name) || !strings.Contains(prompt, rev) {
			t.Errorf("node missing its role, identity, or launch revision")
		}
	}
	if strings.Contains(nodes(name, "$Format:%H$").Node.Args[4], "Gödel launch source commit:") {
		t.Error("checkout placeholder presented as launch revision")
	}
}
