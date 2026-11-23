// Command godel pursues the manuscript mission from its accepted source.
package main

import (
	"context"
	_ "embed"
	"errors"
	"fmt"
	"io"
	"os"
	"os/signal"
	"strings"
	"syscall"

	"patel.codes/godel"
	"patel.codes/grh/internal/accepted"
	"patel.codes/grh/internal/worker"
)

//go:embed mission.md
var mission string

//go:embed source-revision.txt
var archiveRevision string

func main() {
	ctx, stop := signal.NotifyContext(context.Background(), os.Interrupt, syscall.SIGTERM)
	defer stop()
	if err := run(ctx); err != nil {
		fmt.Fprintln(os.Stderr, err)
		os.Exit(1)
	}
}
func run(ctx context.Context) error {
	if len(os.Args) > 1 {
		if os.Args[1] == "check" {
			return checkProof(ctx, os.Stdout, os.Args[2:])
		}
		return fmt.Errorf("unknown argument %q: usage: godel [check]", os.Args[1])
	}
	if err := accepted.Enter(ctx, "godel"); err != nil {
		return err
	}
	goal := strings.TrimSpace(mission)
	work, improve := missionNodes(goal, archiveRevision)
	result, err := godel.New(goal).Run(ctx, &godel.Params{Node: work, Loop: true, SelfImprove: improve})
	if err != nil {
		return err
	}
	fmt.Print(result.Text)
	return nil
}

func checkProof(ctx context.Context, out io.Writer, args []string) error {
	if len(args) < 2 {
		return errors.New("from the repository root: go run ./cmd/godel check <full-commit-id> <declaration> [<declaration> ...]")
	}
	root, err := os.Getwd()
	if err != nil {
		return err
	}
	if err := worker.Check(ctx, root, args[0], args[1:]); err != nil {
		return err
	}
	_, err = fmt.Fprintf(out, "Designated worker built and audited %s for: %s\n", args[0], strings.Join(args[1:], ", "))
	return err
}
