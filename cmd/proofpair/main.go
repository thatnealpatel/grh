// Command proofpair admits one bounded scheduling arm on an isolated base export.
package main

import (
	"context"
	"errors"
	"flag"
	"fmt"
	"io"
	"os"
	"os/exec"
	"path/filepath"
	"strings"
	"time"
)

const (
	baseTree  = "09b74ef69354212b6741c669578efa55388e957a"
	model     = "gpt-6.2-sol"
	review    = "gpt-5.6-luna"
	effort    = "high"
	unit      = "proofpair.service"
	cgroup    = "/system.slice/" + unit
	baseDir   = "/srv/proofpair/base"
	trialHome = "/var/lib/proofpair"
	binDir    = "/opt/proofpair/bin"
	yahBin    = binDir + "/yah"
)

func main() {
	if err := run(os.Args[1:], os.Stdout, os.Stderr); err != nil {
		fmt.Fprintln(os.Stderr, "proofpair:", err)
		os.Exit(1)
	}
}

type arm string

const (
	sequential arm = "sequential"
	concurrent arm = "concurrent"
)

func parseArm(args []string, diagnostics io.Writer) (arm, error) {
	flags := flag.NewFlagSet("proofpair", flag.ContinueOnError)
	flags.SetOutput(diagnostics)
	selected := flags.String("arm", "", "required: sequential or concurrent")
	if err := flags.Parse(args); err != nil {
		return "", err
	}
	a := arm(*selected)
	if flags.NArg() != 0 || (a != sequential && a != concurrent) {
		return "", errors.New("use -arm sequential or -arm concurrent, with no operands")
	}
	return a, nil
}

func run(args []string, out, diagnostics io.Writer) error {
	a, err := parseArm(args, diagnostics)
	if errors.Is(err, flag.ErrHelp) {
		return nil
	}
	if err != nil {
		return err
	}
	return runArm(a, out, diagnostics, launch)
}

func runArm(a arm, out, diagnostics io.Writer, start func(checkout, string, io.Writer, io.Writer) error) error {
	ctx, cancel := context.WithTimeout(context.Background(), time.Minute)
	defer cancel()
	if err := checkEnvironment(os.Environ()); err != nil {
		return fmt.Errorf("preflight: %w", err)
	}
	wd, err := os.Getwd()
	if err != nil {
		return err
	}
	root, err := filepath.EvalSymlinks(wd)
	if err != nil {
		return err
	}
	if root != baseDir || os.Getenv("HOME") != trialHome {
		return fmt.Errorf("preflight: require WorkingDirectory=%s and HOME=%s", baseDir, trialHome)
	}
	if err := checkService(ctx); err != nil {
		return fmt.Errorf("preflight: %w", err)
	}
	c := checkout{root: root, env: trialEnv(root)}
	if err := c.checkSnapshot(ctx, baseTree); err != nil {
		return fmt.Errorf("preflight: %w", err)
	}
	if err := c.checkInputs(); err != nil {
		return fmt.Errorf("preflight: %w", err)
	}
	marker, err := os.OpenFile(filepath.Join(trialHome, ".proofpair-admitted"), os.O_CREATE|os.O_EXCL|os.O_WRONLY, 0600)
	if err != nil {
		return fmt.Errorf("reserve one-shot admission: %w", err)
	}
	if err := marker.Close(); err != nil {
		return fmt.Errorf("close admission marker: %w", err)
	}
	fmt.Fprintf(diagnostics, "proofpair: admitted arm=%s tree=%s seed=%s\n", a, baseTree, c.seed)
	return start(c, prompt(a, c.seed), out, diagnostics)
}

func launch(c checkout, prompt string, out, diagnostics io.Writer) error {
	// The service manager owns the hard deadline and kills
	// the whole cgroup. CommandContext alone would only kill
	// the immediate process.
	cmd := exec.Command(yahBin, "-yolo", "-effort", effort)
	cmd.Dir, cmd.Env = c.root, c.env
	cmd.Stdin, cmd.Stdout, cmd.Stderr = strings.NewReader(prompt), out, diagnostics
	started := time.Now()
	if err := cmd.Start(); err != nil {
		return fmt.Errorf("coordinator launch failed: %w", err)
	}
	o := observer{root: filepath.Join(trialHome, ".yah", "sessions"), start: started, byFile: make(map[string]*dispatchObservation)}
	done, observed := make(chan struct{}), make(chan error, 1)
	go func() { observed <- o.watch(done) }()
	type exit struct {
		err     error
		elapsed time.Duration
	}
	waited := make(chan exit, 1)
	go func() {
		err := cmd.Wait()
		waited <- exit{err, time.Since(started)}
	}()
	var end exit
	var watchErr error
	select {
	case end = <-waited:
		close(done)
		watchErr = <-observed
	case watchErr = <-observed:
		// A corrupt observation ends the arm. Kill and join the coordinator; systemd
		// still owns descendant teardown.
		if err := cmd.Process.Kill(); err != nil && !errors.Is(err, os.ErrProcessDone) {
			return errors.Join(watchErr, fmt.Errorf("stop coordinator: %w", err))
		}
		end = <-waited
	}
	err, elapsed := end.err, end.elapsed
	status := "exited_zero_unverified"
	if err != nil {
		status = "process_error"
	}
	fmt.Fprintf(diagnostics, "\nproofpair: coordinator_wall_ns=%d status=%s\n", elapsed.Nanoseconds(), status)
	if err != nil {
		err = fmt.Errorf("coordinator: %w", err)
	}
	return errors.Join(err, o.report(diagnostics, elapsed, watchErr))
}
