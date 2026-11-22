// Command walk drafts a finite review of Masullo's manuscript.
package main

import (
	"context"
	"flag"
	"fmt"
	"os"
	"os/signal"
	"path/filepath"
	"syscall"

	"patel.codes/godel"
)

func main() {
	reviewer := flag.String("reviewer", "", "executable accepting a walk request as its only argument")
	flag.Parse()
	if err := run(*reviewer); err != nil {
		fmt.Fprintln(os.Stderr, err)
		os.Exit(1)
	}
}

func run(reviewer string) error {
	if reviewer == "" {
		return fmt.Errorf("no reviewer configured (draft requires -reviewer)")
	}
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
	node, err := t.nextNode(godel.Node{Exec: reviewer, Directory: root})
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
