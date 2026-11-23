// Command walk drafts a finite review of Masullo's manuscript.
package main

import (
	"context"
	"crypto/sha256"
	"fmt"
	"os"
	"os/signal"
	"path/filepath"
	"syscall"

	"patel.codes/godel"
	"patel.codes/grh/internal/accepted"
)

func main() {
	if len(os.Args) != 1 {
		fmt.Fprintln(os.Stderr, "walk takes no arguments; supply the task on stdin")
		os.Exit(1)
	}
	ctx, stop := signal.NotifyContext(context.Background(), os.Interrupt, syscall.SIGTERM)
	defer stop()
	if err := run(ctx); err != nil {
		fmt.Fprintln(os.Stderr, err)
		os.Exit(1)
	}
}

func run(ctx context.Context) error {
	if err := accepted.Enter(ctx, "walk"); err != nil {
		return err
	}
	source, err := os.Getwd()
	if err != nil {
		return err
	}
	home, err := os.UserHomeDir()
	if err != nil {
		return err
	}
	root, ledgerDir, err := walkPaths(source, home)
	if err != nil {
		return err
	}
	result, err := godel.New("Draft traversal of Masullo's The Music of the Primes, SHA-256 "+edition).
		Run(ctx, &godel.Params{Node: startNode(root, ledgerDir)})
	if err != nil {
		return err
	}
	_, err = fmt.Print(result.Text)
	return err
}

func walkPaths(source, home string) (root, ledgerDir string, err error) {
	if !filepath.IsAbs(home) {
		return "", "", fmt.Errorf("walk requires an absolute home directory")
	}
	// Match Gödel's program identity, not the
	// temporary accepted build tree.
	source, err = filepath.EvalSymlinks(source)
	if err != nil {
		return "", "", err
	}
	return filepath.Join(source, "../.."), filepath.Join(home, fmt.Sprintf(".grh-walk-%x", sha256.Sum256([]byte(source)))), nil
}

func startNode(root, ledgerDir string) *godel.Node {
	// Next runs under Gödel's program lock. Read the ledger only then, after any
	// preceding writer has finished. Stdin is not traversal state.
	return &godel.Node{Exec: "cat", Args: []string{"/dev/null"}, Next: func(godel.Result) (*godel.Node, error) {
		t, err := openTraversal(ledgerDir)
		if err != nil {
			return nil, err
		}
		return t.nextNode(root)
	}}
}
