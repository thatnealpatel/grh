// Command tracebridge investigates the rational global-to-local trace comparison.
package main

import (
	"context"
	_ "embed"
	"fmt"
	"log"
	"os"
	"os/signal"
	"path/filepath"
	"strings"
	"syscall"

	"patel.codes/godel"
)

//go:embed mission.md
var mission string

func main() {
	ctx, cancel := signal.NotifyContext(context.Background(), os.Interrupt, syscall.SIGTERM)
	defer cancel()
	if err := run(ctx); err != nil {
		log.Fatal(err)
	}
}

func run(ctx context.Context) error {
	cwd, err := os.Getwd()
	if err != nil {
		return err
	}
	// Gödel keys history and relaunches go run . at the runner's cwd.
	if filepath.Base(cwd) != "tracebridge" || filepath.Base(filepath.Dir(cwd)) != "cmd" {
		return fmt.Errorf("launch from the durable workspace's cmd/tracebridge directory")
	}
	result, err := godel.New(mission).Run(ctx, &godel.Params{
		Node: &godel.Node{
			Directory: "../..",
			Exec:      "yah",
			Args:      []string{"-effort", "high", "-append", mission},
			Next:      next,
		},
		Loop: true,
	})
	if err != nil {
		return err
	}
	_, err = fmt.Print(result.Text)
	return err
}

func next(r godel.Result) (*godel.Node, error) {
	text := strings.TrimSpace(r.Text)
	i := strings.LastIndexByte(text, '\n') + 1
	if strings.TrimSpace(text[:i]) == "" {
		return nil, fmt.Errorf("missing trace comparison handoff")
	}
	switch strings.TrimSpace(text[i:]) {
	case "BRIDGE_CONTINUE":
		return nil, nil
	case "BRIDGE_STOP":
		return godel.Stop(), nil
	default:
		return nil, fmt.Errorf("missing trace comparison decision on final line")
	}
}
