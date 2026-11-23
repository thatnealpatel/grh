package main

import (
	"context"
	"fmt"
	"io"
	"os"
	"os/signal"
	"strings"
	"syscall"

	"patel.codes/godel"
)

func main() {
	ctx, stop := signal.NotifyContext(context.Background(), os.Interrupt, syscall.SIGTERM)
	defer stop()
	if err := run(ctx, os.Args[1:]); err != nil {
		fmt.Fprintln(os.Stderr, err)
		os.Exit(1)
	}
}

func run(ctx context.Context, args []string) error {
	exe, err := os.Executable()
	if err != nil {
		return err
	}
	var text string
	switch {
	case len(args) == 0:
		result, err := godel.New("Test signed floor-grid trace increments by deriving, challenging, and repairing four claims.").Run(ctx, &godel.Params{Node: &godel.Node{Exec: exe, Args: []string{"graph"}}})
		if err != nil {
			return err
		}
		text = result.Text
	case len(args) == 1 && args[0] == "graph":
		input, err := io.ReadAll(os.Stdin)
		if err != nil {
			return err
		}
		if strings.TrimSpace(string(input)) == "" {
			return fmt.Errorf("empty task")
		}
		text, err = graph(ctx, string(input), func(ctx context.Context, instructions, payload string) (string, error) {
			return infer(ctx, "http://100.75.6.66:9001/v1/responses", instructions, payload)
		})
		if err != nil {
			return err
		}
	default:
		return fmt.Errorf("usage: ffring [graph]")
	}
	_, err = fmt.Print(text)
	return err
}
