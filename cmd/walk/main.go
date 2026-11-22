// Command walk drafts a finite review of Masullo's manuscript.
package main

import (
	"context"
	"fmt"
	"os"
	"os/signal"
	"path/filepath"
	"syscall"

	"patel.codes/godel"
)

func main() {
	if len(os.Args) != 1 {
		fmt.Fprintln(os.Stderr, "walk takes no arguments; supply the task on stdin")
		os.Exit(1)
	}
	if err := run(); err != nil {
		fmt.Fprintln(os.Stderr, err)
		os.Exit(1)
	}
}

func run() error {
	root, err := filepath.Abs("../..")
	if err != nil {
		return err
	}
	if _, err := os.Stat(filepath.Join(root, ".godel/sources/masullo/README.md")); err != nil {
		return fmt.Errorf("start from cmd/walk: %w", err)
	}
	t, err := openTraversal(filepath.Join(root, ".godel/walk"))
	if err != nil {
		return err
	}
	launchRoot := os.Getenv("GRH_LAUNCH_ROOT")
	if !filepath.IsAbs(launchRoot) {
		return fmt.Errorf("set GRH_LAUNCH_ROOT to the absolute path of the durable GRH workspace")
	}
	launchRoot, err = filepath.EvalSymlinks(launchRoot)
	if err != nil {
		return fmt.Errorf("resolve GRH_LAUNCH_ROOT: %w", err)
	}
	node, err := t.nextNode(launchRoot)
	if err != nil || node == nil {
		return err
	}
	ctx, stop := signal.NotifyContext(context.Background(), os.Interrupt, syscall.SIGTERM)
	defer stop()
	result, err := godel.New("Draft traversal of Masullo's The Music of the Primes, SHA-256 "+edition).
		Run(ctx, &godel.Params{Node: node})
	if err != nil {
		return err
	}
	_, err = fmt.Print(result.Text)
	return err
}
