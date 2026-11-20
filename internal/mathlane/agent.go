package mathlane

import (
	"bytes"
	"context"
	"encoding/json"
	"errors"
	"fmt"
	"os"
	"os/exec"
	"path/filepath"
	"syscall"
	"time"
)

const agentTimeout = 3 * time.Minute

func runYah(ctx context.Context, root, instructions string, input []byte) (_ []byte, err error) {
	ctx, cancel := context.WithTimeout(ctx, agentTimeout)
	defer cancel()
	modules, err := pinnedSources(ctx, root, os.Getenv("GRH_MATHLIB"))
	if err != nil {
		return nil, fmt.Errorf("retrieve mathlane Mathlib sources: %w", err)
	}
	data, err := json.Marshal(struct {
		MathlibRev     string
		MathlibSources []moduleSource
		Request        json.RawMessage
	}{mathlibRev, modules, input})
	if err != nil {
		return nil, fmt.Errorf("encode agent input: %w", err)
	}
	if cause := context.Cause(ctx); cause != nil {
		return nil, cause
	}

	tmp, err := filepath.Abs(os.TempDir())
	if err != nil {
		return nil, fmt.Errorf("resolve mathlane temporary directory: %w", err)
	}
	scratch, err := os.MkdirTemp(tmp, "grh-mathlane-")
	if err != nil {
		return nil, fmt.Errorf("create mathlane scratch: %w", err)
	}
	defer func() {
		if cleanErr := os.RemoveAll(scratch); cleanErr != nil {
			err = errors.Join(err, fmt.Errorf("remove mathlane scratch: %w", cleanErr))
		}
	}()
	cmd := exec.CommandContext(ctx, "yah", "-tmp", "-effort", "high", "-append", instructions)
	cmd.Dir = scratch
	// Keep Yah's temporary repository under the directory we reclaim even
	// when the subprocess is killed. This does not sandbox Yah's tools. Let
	// -tmp select its own adoption target rather than inheriting a target
	// from the caller's campaign.
	cmd.Env = append(cmd.Environ(), "TMPDIR="+scratch, "YAH_CAMPAIGN_TARGET=")
	cmd.Stdin = bytes.NewReader(data)
	// The caller's Gödel scope owns descendants. Cancel
	// this process group on a per-request deadline,
	// including ordinary launcher children.
	cmd.SysProcAttr = &syscall.SysProcAttr{Setpgid: true}
	cmd.Cancel = func() error {
		err := syscall.Kill(-cmd.Process.Pid, syscall.SIGKILL)
		if errors.Is(err, syscall.ESRCH) {
			return os.ErrProcessDone
		}
		return err
	}
	cmd.WaitDelay = 2 * time.Second
	var stdout agentOutput
	cmd.Stdout = &stdout
	runErr := cmd.Run()
	if cause := context.Cause(ctx); cause != nil {
		return nil, cause
	}
	if runErr != nil {
		// Child diagnostics may contain credentials or
		// supplied source data.
		return nil, fmt.Errorf("run headless Yah: %w", runErr)
	}
	if stdout.truncated {
		return nil, errors.New("mathlane agent response too large")
	}
	return stdout.buf.Bytes(), nil
}

type agentOutput struct {
	buf       bytes.Buffer
	truncated bool
}

func (b *agentOutput) Write(p []byte) (int, error) {
	n := len(p)
	if remain := maxReplyBytes - b.buf.Len(); remain < n {
		p = p[:remain]
		b.truncated = true
	}
	b.buf.Write(p)
	return n, nil
}
