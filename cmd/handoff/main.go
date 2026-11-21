// Command handoff compares readings of preselected historical evidence.
package main

import (
	"context"
	"debug/buildinfo"
	"encoding/json/v2"
	"errors"
	"flag"
	"fmt"
	"io"
	"os"
	"os/exec"
	"os/signal"
	"path/filepath"
	"syscall"

	"patel.codes/godel"
)

func main() {
	flag.Usage = func() { fmt.Fprintln(os.Stderr, "usage (from cmd/handoff): go run . PLAN.json") }
	flag.Parse()
	if flag.NArg() != 1 {
		flag.Usage()
		os.Exit(2)
	}
	ctx, cancel := signal.NotifyContext(context.Background(), os.Interrupt, syscall.SIGTERM)
	defer cancel()
	if err := run(ctx, flag.Arg(0)); err != nil {
		fmt.Fprintln(os.Stderr, "handoff:", err)
		os.Exit(1)
	}
}

func run(ctx context.Context, planPath string) error {
	root, err := launchRoot(ctx)
	if err != nil {
		return err
	}
	plan, err := readPlan(planPath)
	if err != nil {
		return err
	}
	yah, err := checkedYah()
	if err != nil {
		return err
	}
	train, err := loadPacket(ctx, root, plan.Train)
	if err != nil {
		return fmt.Errorf("training packet: %w", err)
	}
	heldOut, err := loadPacket(ctx, root, plan.HeldOut)
	if err != nil {
		return fmt.Errorf("held-out packet: %w", err)
	}
	empty, err := os.MkdirTemp("/tmp", "handoff-empty-*")
	if err != nil {
		return err
	}
	defer os.RemoveAll(empty)
	rootNode, err := (experiment{yah: yah, empty: empty, train: train, heldOut: heldOut}).tree()
	if err != nil {
		return err
	}
	input, err := neutralInput()
	if err != nil {
		return err
	}
	defer input.Close()
	original := os.Stdin
	os.Stdin = input
	defer func() { os.Stdin = original }()
	result, err := godel.New("Test one historical handoff reading instruction without applying it.").Run(ctx, &godel.Params{
		Node: rootNode,
		Loop: false,
	})
	if err != nil {
		return err
	}
	_, err = io.WriteString(os.Stdout, result.Text)
	return err
}

func readPlan(path string) (plan, error) {
	f, err := os.Open(path)
	if err != nil {
		return plan{}, err
	}
	defer f.Close()
	const maxPlanBytes = 16 << 10
	data, err := io.ReadAll(io.LimitReader(f, maxPlanBytes+1))
	if err != nil {
		return plan{}, err
	}
	if len(data) > maxPlanBytes {
		return plan{}, errors.New("plan exceeds 16 KiB")
	}
	var p plan
	if err := json.Unmarshal(data, &p, json.RejectUnknownMembers(true)); err != nil {
		return p, fmt.Errorf("read plan: %w", err)
	}
	return p, p.validate()
}

func checkedYah() (string, error) {
	path, err := exec.LookPath("yah")
	if err != nil {
		return "", err
	}
	path, err = filepath.Abs(path)
	if err != nil {
		return "", err
	}
	// The empty tool allowlist is an
	// implementation contract, not a CLI
	// flag.
	info, err := buildinfo.ReadFile(path)
	if err != nil {
		return "", fmt.Errorf("inspect Yah executable: %w", err)
	}
	if info.Path != "patel.codes/yah/cmd/yah" || info.Main.Path != "patel.codes/yah" || info.Main.Version != "v0.0.59" || info.Main.Replace != nil {
		return "", errors.New("need patel.codes/yah/cmd/yah v0.0.59 on PATH (verified no-tools configuration)")
	}
	return path, nil
}

// neutralInput prevents both arbitrary
// operator input and Gödel history
// fallback. Gödel v0.0.5 passes these
// exact bytes to every continuation.
func neutralInput() (*os.File, error) {
	r, w, err := os.Pipe()
	if err != nil {
		return nil, err
	}
	_, err = w.WriteString("HANDOFF_START\n")
	if err = errors.Join(err, w.Close()); err != nil {
		r.Close()
		return nil, err
	}
	return r, nil
}
