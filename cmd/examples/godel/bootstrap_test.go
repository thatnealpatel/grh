package main

import (
	"context"
	"errors"
	"os"
	"os/exec"
	"strconv"
	"testing"
	"time"
)

func TestBuiltMarkerConsumed(t *testing.T) {
	const builtEntry = "GRH_GODEL_BUILT_ENTRY"
	// A canceled built entry reaches Run but cannot
	// invoke any mission node. Run is once per
	// process, so exercise it in a test subprocess.
	if os.Getenv("GRH_TEST_CONSUME_MARKER") == "1" {
		os.Args = os.Args[:1]
		source := t.TempDir()
		t.Setenv(builtEntry, strconv.Itoa(os.Getpid())+":"+source)
		ctx, cancel := context.WithCancel(t.Context())
		cancel()
		if err := run(ctx); !errors.Is(err, context.Canceled) {
			t.Fatal(err)
		}
		if got, err := os.Getwd(); err != nil || got != source {
			t.Fatalf("registration directory = %q, %v; want %q", got, err, source)
		}
		if _, set := os.LookupEnv(builtEntry); set {
			t.Fatal("marker would reach a loop launch")
		}
		return
	}
	ctx, cancel := context.WithTimeout(t.Context(), 10*time.Second)
	defer cancel()
	exe, err := os.Executable()
	if err != nil {
		t.Fatal(err)
	}
	cmd := exec.CommandContext(ctx, exe, "-test.run=^TestBuiltMarkerConsumed$")
	cmd.Env = append(os.Environ(), "GRH_TEST_CONSUME_MARKER=1")
	if out, err := cmd.CombinedOutput(); err != nil {
		t.Fatalf("marker: %s: %v", out, err)
	}
}
