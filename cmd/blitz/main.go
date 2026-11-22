// Command blitz separately assesses whether the accepted formalization supports
// bounded proof attempts at classical RH and full Masullo GRH.
package main

import (
	"context"
	_ "embed"
	"errors"
	"fmt"
	"os"
	"os/signal"
	"syscall"
	"time"

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
		return errors.New("blitz takes no arguments; supply a nonblank seed on stdin for the first launch")
	}
	if err := accepted.Enter(ctx, "blitz"); err != nil {
		return err
	}
	// Enter leaves us in the durable cmd/blitz directory, which Gödel uses for its
	// history identity and the next go run .
	node, err := blitzNodes(archiveRevision, func() error { return pauseBetweenCycles(ctx) })
	if err != nil {
		return err
	}
	runner := godel.New("Assess separately whether the accepted formalization supports a bounded attempt at classical RH or full Masullo GRH. " +
		"Trace how the accepted results fit together and identify the assumptions each route would still require. " +
		"Do not assume either proof is within reach or treat ordinary lemma work as a blitz.")
	result, err := runner.Run(ctx, &godel.Params{Node: node, Loop: true})
	if err != nil {
		return err
	}
	_, err = fmt.Print(result.Text)
	return err
}

// pauseBetweenCycles is only called from the terminal
// logging node's Next.
func pauseBetweenCycles(ctx context.Context) error {
	timer := time.NewTimer(30 * time.Minute)
	defer timer.Stop()
	select {
	case <-ctx.Done():
	case <-timer.C:
	}
	return ctx.Err()
}
