// Command conjecture investigates one mathematical claim against the accepted
// GRH evidence and may publish one conjecture card.
package main

import (
	"context"
	"errors"
	"fmt"
	"os"
	"os/signal"
	"path/filepath"
	"syscall"
	"time"

	"patel.codes/godel"
	"patel.codes/grh/internal/accepted"
)

func main() {
	ctx, stop := signal.NotifyContext(context.Background(), os.Interrupt, syscall.SIGTERM)
	defer stop()
	ctx, cancel := context.WithTimeout(ctx, 60*time.Minute)
	defer cancel()
	if err := run(ctx, os.Args[1:]); err != nil {
		fmt.Fprintln(os.Stderr, "conjecture:", err)
		os.Exit(1)
	}
}

func run(ctx context.Context, args []string) (err error) {
	if len(args) != 0 {
		return errors.New("takes no arguments; run go run ./cmd/conjecture from the GRH workspace root")
	}
	cwd, err := os.Getwd()
	if err != nil {
		return err
	}
	pin, err := accepted.Resolve(ctx, cwd, os.Getenv("YAH_CAMPAIGN_TARGET"))
	if err != nil {
		return err
	}
	if cwd != pin.Root {
		return errors.New("launch from the GRH workspace root")
	}
	scratch, err := os.MkdirTemp("/tmp", "grh-conjecture-*")
	if err != nil {
		return err
	}
	defer func() { err = errors.Join(err, os.RemoveAll(scratch)) }()
	evidence := filepath.Join(scratch, "evidence")
	cards, err := exportEvidence(ctx, pin, evidence)
	if err != nil {
		return err
	}
	investigation := investigation{ctx: ctx, scratch: scratch, root: pin.Root, target: pin.Target, cards: cards}
	node, err := investigation.start(pin.Revision, evidence)
	if err != nil {
		return err
	}
	// Gödel requires nonblank stdin for a
	// first run and otherwise can feed back
	// its history. Always provide a fixed
	// seed, never user input or a previous
	// result; each research node reads its
	// own packet instead.
	name := filepath.Join(scratch, "launch.txt")
	if err := os.WriteFile(name, []byte("Investigate once at accepted commit "+pin.Revision+".\n"), 0600); err != nil {
		return err
	}
	seed, err := os.Open(name)
	if err != nil {
		return err
	}
	stdin := os.Stdin
	os.Stdin = seed
	defer func() {
		os.Stdin = stdin
		seed.Close()
	}()
	// Register the command source with Gödel; nodes use explicit directories.
	if err := os.Chdir(filepath.Join(pin.Root, "cmd", "conjecture")); err != nil {
		return err
	}
	defer func() { err = errors.Join(err, os.Chdir(cwd)) }()
	result, err := godel.New("Investigate one worthwhile, precisely stated claim for the GRH mission.").Run(ctx, &godel.Params{Node: node})
	if err != nil {
		return err
	}
	_, err = fmt.Print(result.Text)
	return err
}
