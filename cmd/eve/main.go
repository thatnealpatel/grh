// Command eve runs one formalization pass over Alice and Bob's accepted work.
package main

import (
	"context"
	_ "embed"
	"errors"
	"fmt"
	"os"
	"os/signal"
	"syscall"

	"patel.codes/godel"
	"patel.codes/grh/internal/accepted"
)

//go:embed formalize.md
var protocol string

func main() {
	ctx, stop := signal.NotifyContext(context.Background(), os.Interrupt, syscall.SIGTERM)
	defer stop()
	if err := run(ctx); err != nil {
		fmt.Fprintln(os.Stderr, err)
		os.Exit(1)
	}
}

func run(ctx context.Context) error {
	if len(os.Args) != 1 {
		return errors.New("eve takes the run prompt on stdin, not in arguments")
	}
	if err := accepted.Enter(ctx, "eve"); err != nil {
		return err
	}
	// Stay in cmd/eve for Gödel's per-source lock and history. Only Yah needs the
	// repository root as its working directory.
	result, err := godel.New("Formalize arguments from Alice and Bob in Lean.").Run(ctx, pass())
	if err != nil {
		return err
	}
	_, err = fmt.Print(result.Text)
	return err
}

func pass() *godel.Params {
	return &godel.Params{Node: &godel.Node{
		Directory: "../..",
		Exec:      "yah",
		Env:       []string{"YAH_DEFAULT_MODEL=gpt-6.2-astra"},
		Args:      []string{"-yolo", "-effort", "high", "-append", protocol},
	}}
}
