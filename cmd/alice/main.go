// This command runs a self-improving research loop for RH and GRH.
package main

import (
	"context"
	_ "embed"
	"fmt"
	"os"
	"os/signal"
	"path"
	"path/filepath"
	"runtime/debug"
	"strings"
	"syscall"

	"patel.codes/godel"
	"patel.codes/grh/internal/accepted"
	grhgodel "patel.codes/grh/internal/godel"
)

const goal = "Advance the Riemann hypothesis or generalized Riemann hypothesis by original mathematical research."

//go:embed WORK.md
var work string

//go:embed IMPROVE.md
var improve string

//go:embed source-revision.txt
var revision string

func main() {
	ctx, stop := signal.NotifyContext(context.Background(), os.Interrupt, syscall.SIGTERM)
	defer stop()
	if err := run(ctx); err != nil {
		fmt.Fprintln(os.Stderr, err)
		os.Exit(1)
	}
}

func run(ctx context.Context) error {
	// The package path identifies the peer
	// even on the first launch from the repo
	// root. Neither the working directory
	// nor argv[0] does.
	info, ok := debug.ReadBuildInfo()
	if !ok || info.Path == "" || info.Path == "command-line-arguments" {
		return fmt.Errorf("launch the command by package, not by source file")
	}
	name := path.Base(info.Path)
	if len(os.Args) != 1 {
		return fmt.Errorf("%s takes its task on stdin, not in arguments", name)
	}
	if err := accepted.Enter(ctx, name); err != nil {
		return err
	}
	root, err := filepath.Abs("../..") // Enter leaves us in the durable cmd/<name> directory.
	if err != nil {
		return err
	}
	result, err := godel.New(goal).Run(ctx, nodes(root, name, revision))
	if err != nil {
		return err
	}
	_, err = fmt.Print(result.Text)
	return err
}

func nodes(root, name, rev string) *godel.Params {
	intro := fmt.Sprintf("You are cmd/%s. %s\n", name, goal)
	if hash := strings.TrimSpace(rev); (len(hash) == 40 || len(hash) == 64) && strings.Trim(hash, "0123456789abcdef") == "" {
		intro += "Gödel launch source commit: " + hash + ". Read program sources at this revision; get the current accepted mathematics from campaign status.\n"
	}
	intro += grhgodel.ScratchPolicy + "\n\n"
	yah := func(role string) *godel.Node {
		return &godel.Node{
			Directory: root,
			Exec:      "yah",
			Env:       []string{"YAH_DEFAULT_MODEL=gpt-6.2-astra"},
			Args:      []string{"-yolo", "-effort", "high", "-append", intro + role},
		}
	}
	return &godel.Params{Node: yah(work), SelfImprove: yah(improve), Loop: true}
}
