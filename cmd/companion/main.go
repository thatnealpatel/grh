// Command companion investigates gaps in the coverage of Masullo's manuscript.
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
	if len(os.Args) != 1 {
		return errors.New("companion takes no arguments; supply the task on stdin")
	}
	if err := accepted.Enter(ctx, "companion"); err != nil {
		return err
	}
	// Enter leaves us in the durable cmd/companion
	// directory, which Gödel uses for both its history
	// identity and the next go run . launch.
	selector, improve := companionNodes(archiveRevision)
	result, err := godel.New(goal).Run(ctx, &godel.Params{Node: selector, Loop: true, SelfImprove: improve})
	if err != nil {
		return err
	}
	_, err = fmt.Print(result.Text)
	return err
}
