package main

import (
	"slices"
	"testing"
)

func TestPass(t *testing.T) {
	p := pass()
	n := p.Node
	if p.Loop || p.SelfImprove != nil || n == nil || n.Next != nil {
		t.Fatal("want one coordinator invocation per launch")
	}
	if n.Exec != "yah" || n.Directory != "../.." || !slices.Equal(n.Env, []string{"YAH_DEFAULT_MODEL=gpt-6.2-astra"}) {
		t.Fatalf("wrong coordinator: %+v", n)
	}
	if protocol == "" || !slices.Equal(n.Args, []string{"-yolo", "-effort", "high", "-append", protocol}) {
		t.Fatal("append the protocol to the harness; leave stdin for the user message")
	}
}
