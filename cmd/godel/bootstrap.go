package main

import (
	"context"
	"errors"
	"fmt"
	"os"
	"os/exec"
	"path/filepath"
	"strconv"
	"strings"
	"syscall"
)

// Scope the skip to the exec'd process.
// Even if a replacement program knows
// nothing about the marker, its next go
// run . starts a different PID.
const builtEntry = "GRH_GODEL_BUILT_ENTRY"

func launchAccepted(ctx context.Context) (err error) {
	cwd, err := os.Getwd()
	if err != nil {
		return err
	}
	jj := func(args ...string) (string, error) {
		// Don't even merge divergent jj operations during this read.
		return stageOutput(ctx, cwd, "jj", append([]string{"--ignore-working-copy", "--at-op=@"}, args...)...)
	}
	root, err := jj("workspace", "root")
	if err != nil {
		return err
	}
	source := filepath.Join(root, "cmd/godel")
	if cwd != root && cwd != source {
		return errors.New("launch from the durable GRH workspace root or its cmd/godel directory")
	}
	target := os.Getenv("YAH_CAMPAIGN_TARGET")
	if target == "" {
		target = "main"
	}
	// Only a single, unconflicted local target is eligible. In particular neither
	// a revset nor a matching remote bookmark is a local bookmark.
	rev, err := jj("bookmark", "list", "-T", `if(!remote && normal_target && !normal_target.conflict(), normal_target.commit_id() ++ "\n")`, "--", "exact:"+strconv.Quote(target))
	if err != nil {
		return err
	}
	if (len(rev) != 40 && len(rev) != 64) || strings.Trim(rev, "0123456789abcdef") != "" {
		return fmt.Errorf("no unambiguous local accepted commit for bookmark %q", target)
	}
	gitDir, err := jj("git", "root")
	if err != nil {
		return err
	}
	branch, err := stageOutput(ctx, root, "git", "--git-dir", gitDir, "rev-parse", "--verify", "refs/heads/"+target)
	if err != nil {
		return err
	}
	if branch != rev {
		return fmt.Errorf("accepted target %q disagrees: jj %s, Git %s", target, rev, branch)
	}

	dir, err := os.MkdirTemp("", "grh-accepted-*")
	if err != nil {
		return err
	}
	defer func() { err = errors.Join(err, os.RemoveAll(dir)) }()
	tree := filepath.Join(dir, "src")
	if err := os.Mkdir(tree, 0700); err != nil {
		return err
	}
	archive := filepath.Join(dir, "src.tar")
	if err := stageCommand(ctx, root, "git", "--no-replace-objects", "--git-dir", gitDir, "archive", "--format=tar", "-o", archive, rev).Run(); err != nil {
		return fmt.Errorf("archive accepted %s: %w", rev, err)
	}
	if err := stageCommand(ctx, tree, "tar", "-xf", archive).Run(); err != nil {
		return fmt.Errorf("extract accepted %s: %w", rev, err)
	}
	binary := filepath.Join(dir, "godel")
	build := stageCommand(ctx, tree, "go", "build", "-o", binary, "./cmd/godel")
	build.Env = append(build.Environ(), "GOWORK=off", "GOTMPDIR="+dir)
	if err := build.Run(); err != nil {
		return fmt.Errorf("build accepted %s: %w", rev, err)
	}

	// Exec doesn't run defers, and the
	// accepted program may itself exec.
	// Unlink everything now; Linux can exec
	// the inode via its open fd, which is
	// close-on-exec. There is no waiting
	// bootstrap in the loop.
	entry, err := os.Open(binary)
	if err != nil {
		return err
	}
	defer entry.Close()
	if err := os.RemoveAll(dir); err != nil {
		return err
	}
	if err := os.Setenv("YAH_CAMPAIGN_TARGET", target); err != nil {
		return err
	}
	if err := os.Setenv(builtEntry, strconv.Itoa(os.Getpid())+":"+source); err != nil {
		return err
	}
	if err := ctx.Err(); err != nil {
		return err
	}
	return fmt.Errorf("exec accepted %s: %w", rev, syscall.Exec(fmt.Sprintf("/proc/self/fd/%d", entry.Fd()), os.Args, os.Environ()))
}

func stageOutput(ctx context.Context, dir, name string, args ...string) (string, error) {
	out, err := stageCommand(ctx, dir, name, args...).Output()
	if err != nil {
		return "", fmt.Errorf("%s %s: %w", name, args[0], err)
	}
	return strings.TrimSuffix(string(out), "\n"), nil
}

func stageCommand(ctx context.Context, dir, name string, args ...string) *exec.Cmd {
	cmd := exec.CommandContext(ctx, name, args...)
	cmd.Dir = dir
	cmd.Stderr = os.Stderr
	// In particular go build starts compiler and linker
	// children. Cancel their process group before Run
	// returns and we remove the build tree.
	cmd.SysProcAttr = &syscall.SysProcAttr{Setpgid: true}
	cmd.Cancel = func() error {
		err := syscall.Kill(-cmd.Process.Pid, syscall.SIGKILL)
		if errors.Is(err, syscall.ESRCH) {
			return os.ErrProcessDone
		}
		return err
	}
	return cmd
}
