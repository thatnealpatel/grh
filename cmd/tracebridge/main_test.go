package main

import (
	"testing"

	"patel.codes/godel"
)

func TestNext(t *testing.T) {
	for _, tc := range []struct {
		name string
		text string
		stop bool
		fail bool
	}{
		{"successor", "Try the common-space control.\nBRIDGE_CONTINUE\n", false, false},
		{"blocked", "The proposed domains differ.\nBRIDGE_STOP\n", true, false},
		{"blank", "", false, true},
		{"no handoff", "BRIDGE_CONTINUE", false, true},
		{"not final", "BRIDGE_CONTINUE\nno decision", false, true},
	} {
		t.Run(tc.name, func(t *testing.T) {
			n, err := next(godel.Result{Text: tc.text})
			if (err != nil) != tc.fail || (n != nil) != tc.stop {
				t.Fatalf("next returned node %v, error %v", n, err)
			}
		})
	}
}
