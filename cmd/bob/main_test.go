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
	root := t.TempDir()
	p := nodes(root, name, rev+"\n")
	if !p.Loop || p.Node == p.SelfImprove || work == improve || work == "" || improve == "" {
		t.Fatal("want separate nonempty work and improvement roles in a loop")
	}
	for _, role := range []struct {
		node *godel.Node
		text string
	}{{p.Node, work}, {p.SelfImprove, improve}} {
		n := role.node
		if n == nil || n.Exec != "yah" || n.Directory != root || n.Next != nil || len(n.Args) != 5 || !slices.Equal(n.Args[:4], []string{"-yolo", "-effort", "high", "-append"}) {
			t.Fatalf("unexpected starter node: %+v", n)
		}
		if !slices.Equal(n.Env, []string{"YAH_DEFAULT_MODEL=gpt-6.2-sol"}) {
			t.Errorf("unexpected node environment: %q", n.Env)
		}
		prompt := n.Args[4]
		if !strings.HasSuffix(prompt, role.text) || !strings.Contains(prompt, "cmd/"+name) || !strings.Contains(prompt, rev) {
			t.Errorf("node missing its role, identity, or launch revision")
		}
	}
	if strings.Contains(nodes(root, name, "$Format:%H$").Node.Args[4], "Gödel launch source commit:") {
		t.Error("checkout placeholder presented as launch revision")
	}
}
