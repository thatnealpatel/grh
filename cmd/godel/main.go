// Command godel pursues the manuscript mission from its accepted source.
package main

import (
	"context"
	_ "embed"
	"errors"
	"flag"
	"fmt"
	"io"
	"os"
	"os/signal"
	"path/filepath"
	"strconv"
	"strings"
	"syscall"
	"time"

	"patel.codes/godel"
	"patel.codes/grh/internal/worker"
)

//go:embed mission.md
var mission string

//go:embed selection.txt
var selection string

func main() {
	ctx, stop := signal.NotifyContext(context.Background(), os.Interrupt, syscall.SIGTERM)
	defer stop()
	if err := run(ctx); err != nil {
		fmt.Fprintln(os.Stderr, err)
		os.Exit(1)
	}
}
func run(ctx context.Context) error {
	selection = strings.TrimSpace(selection)
	mission = strings.TrimSpace(mission)
	if len(os.Args) == 1 {
		source, built := strings.CutPrefix(os.Getenv(builtEntry), strconv.Itoa(os.Getpid())+":")
		if !built {
			return launchAccepted(ctx)
		}
		if err := os.Unsetenv(builtEntry); err != nil {
			return err
		}
		// Gödel registers cwd and relaunches
		// go run . there. The root is the
		// operator's entry directory, not the
		// command's package.
		if err := os.Chdir(source); err != nil {
			return err
		}
		work, improve := missionNodes(mission)
		result, err := runTree(ctx, work, improve)
		if err != nil {
			return err
		}
		fmt.Print(result.Text)
		return nil
	}
	if len(os.Args) > 1 && os.Args[1] == "check" {
		return checkProof(ctx, os.Stdout, os.Args[2:])
	}
	if len(os.Args) > 1 && os.Args[1] == "_assess" {
		return assess(os.Stdin, os.Stdout, os.Args[2:])
	}
	child := len(os.Args) > 1 && os.Args[1] == "_step"
	args := os.Args[1:]
	if child {
		args = args[1:]
	}
	fs := flag.NewFlagSet("godel", flag.ContinueOnError)
	planPath := fs.String("plan", ".godel/pilot.json", "goal and passage obligations (relative to repository)")
	budget := fs.String("budget", "pilot-1", "persistent allowance identifier")
	n := fs.Int("attempts", 12, "maximum stage attempts across launches")
	duration := fs.Duration("time", 25*time.Minute, "wall time from first launch with this allowance")
	if err := fs.Parse(args); err != nil {
		return err
	}
	if fs.NArg() != 0 || !identifier.MatchString(*budget) || *n < 1 || *duration <= 0 {
		return errors.New("invalid arguments or allowance")
	}
	cwd, err := os.Getwd()
	if err != nil {
		return err
	}
	root := filepath.Clean(filepath.Join(cwd, "../.."))
	if filepath.Clean(filepath.Join(root, "cmd/godel")) != cwd {
		return errors.New("launch from cmd/godel (Gödel loops run go run . in this directory)")
	}
	pp := *planPath
	if !filepath.IsAbs(pp) {
		pp = filepath.Join(root, pp)
	}
	bp := filepath.Join(root, ".godel", "budgets", *budget+".json")
	w, err := load(root, pp, bp)
	if err != nil {
		return err
	}
	if child {
		if err = w.initBudget(*n, *duration); err != nil {
			return err
		}
		if err = w.step(ctx, live); err != nil {
			return err
		}
		reason := w.terminal()
		if reason == "" {
			reason = "continue"
		}
		fmt.Println(w.report(reason))
		return nil
	}
	exe, err := os.Executable()
	if err != nil {
		return err
	}
	task := w.plan.Goal + "\n"
	for _, p := range w.plan.Passages {
		task += p.ID + ": " + p.Question + "\n"
	}
	if w.budget.Limit > 0 {
		task += w.report("resume")
	}
	// Reconstruct input from durable work, not
	// history fallback, untrusted prior stdout, or
	// terminal state. godel v0.0.5 reads os.Stdin
	// and has no Input parameter.
	input, err := os.CreateTemp("", "grh-context-*")
	if err != nil {
		return err
	}
	defer input.Close()
	if err = os.Remove(input.Name()); err != nil {
		return err
	}
	if _, err = io.WriteString(input, task); err != nil {
		return err
	}
	if _, err = input.Seek(0, 0); err != nil {
		return err
	}
	os.Stdin = input
	node := &godel.Node{Exec: exe, Args: append([]string{"_step"}, args...), Next: func(godel.Result) (*godel.Node, error) {
		w, err := load(root, pp, bp)
		if err != nil {
			return nil, err
		}
		if w.terminal() != "" {
			return godel.Stop(), nil
		}
		return nil, nil
	}}
	result, err := runTree(ctx, node, &godel.Node{Exec: exe, Args: []string{"_assess", root, pp, bp}})
	if err != nil {
		if ctx.Err() != nil {
			return fmt.Errorf("canceled; no relaunch: %w", ctx.Err())
		}
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

func runTree(ctx context.Context, n, improve *godel.Node) (*godel.Result, error) {
	return godel.New(strings.TrimSpace(mission)).Run(ctx, &godel.Params{Node: n, Loop: true, SelfImprove: improve})
}
