package main

import (
	"bufio"
	"bytes"
	"context"
	"errors"
	"fmt"
	"io"
	"os"
	"os/exec"
	"path/filepath"
	"strconv"
	"strings"
	"syscall"
	"testing"
	"time"
)

// A replacement entry with no staging
// logic. The deleted init would still
// run if the accepted sources were just
// copied over the launch checkout.
const acceptedProgram = `package main
import ("fmt"; "io"; "os")
func main() {
	wd, err := os.Getwd(); if err != nil { panic(err) }
	in, err := io.ReadAll(os.Stdin); if err != nil { panic(err) }
	files, err := os.ReadDir(os.TempDir()); if err != nil || len(files) != 0 { panic("scratch still in use") }
	fmt.Printf("accepted pid=%d argv0=%q cwd=%q target=%q input=%q\n", os.Getpid(), os.Args[0], wd, os.Getenv("YAH_CAMPAIGN_TARGET"), in)
	fmt.Fprintln(os.Stderr, "accepted diagnostic")
	os.Exit(17)
}`

func TestAcceptedEntry(t *testing.T) {
	ctx, cancel := context.WithTimeout(t.Context(), time.Minute)
	defer cancel()
	base := t.TempDir()
	control := filepath.Join(base, "control")
	launch := filepath.Join(base, "launch")
	config := filepath.Join(base, "jj.toml")
	write := func(path, s string) {
		t.Helper()
		if err := os.WriteFile(path, []byte(s), 0700); err != nil {
			t.Fatal(err)
		}
	}
	write(config, "[user]\nname = 'Fixture'\nemail = 'fixture@example.invalid'\n")
	t.Setenv("JJ_CONFIG", config)
	t.Setenv("GIT_CONFIG_GLOBAL", "/dev/null")
	t.Setenv("GIT_CONFIG_NOSYSTEM", "1")
	jj := func(dir string, args ...string) string {
		t.Helper()
		cmd := exec.CommandContext(ctx, "jj", args...)
		cmd.Dir = dir
		out, err := cmd.CombinedOutput()
		if err != nil {
			t.Fatalf("fixture jj %v: %s: %v", args, out, err)
		}
		return string(out)
	}
	jj(base, "git", "init", "--colocate", control)
	src := filepath.Join(control, "cmd/godel")
	if err := os.MkdirAll(src, 0700); err != nil {
		t.Fatal(err)
	}
	write(filepath.Join(control, "go.mod"), "module fixture\n\ngo 1.27.4\n")
	write(filepath.Join(src, "main.go"), "package main\nfunc main() { panic(\"old entry\") }\n")
	deleted := filepath.Join(src, "deleted.go")
	write(deleted, "package main\nfunc init() { panic(\"deleted init\") }\n")
	jj(control, "workspace", "add", "--revision", "@", launch)
	if err := os.Remove(deleted); err != nil {
		t.Fatal(err)
	}
	write(filepath.Join(src, "main.go"), acceptedProgram)
	jj(control, "bookmark", "create", "-r", "@", "main")
	topic := filepath.Join(base, "topic")
	jj(control, "workspace", "add", "--revision", "@", topic)
	write(filepath.Join(topic, "cmd/godel/main.go"), strings.Replace(acceptedProgram, "accepted diagnostic", "topic/test diagnostic", 1))
	jj(topic, "bookmark", "create", "-r", "@", "topic/test")
	jj(topic, "git", "export")
	cwd := filepath.Join(launch, "cmd/godel")
	// A dirty launch must not even get snapshotted by
	// source resolution.
	write(filepath.Join(cwd, "dirty.go"), "not Go source")
	checkpoint := func() string {
		return jj(launch, "--ignore-working-copy", "log", "--no-graph", "-r", "@", "-T", "commit_id")
	}
	before := checkpoint()
	scratch := t.TempDir()
	exe, err := os.Executable()
	if err != nil {
		t.Fatal(err)
	}
	command := func(target string) *exec.Cmd {
		// The existing controlled TestMain
		// invokes the real no-arg main.
		cmd := exec.CommandContext(ctx, exe)
		cmd.Dir = cwd
		cmd.Env = append(cmd.Environ(), "GRH_CONTROLLED=1", "YAH_CAMPAIGN_TARGET="+target, "TMPDIR="+scratch, builtEntry+"="+strconv.Itoa(os.Getpid())+":"+cwd, "GOPROXY=off")
		return cmd
	}
	for _, target := range []string{"", "topic/test"} {
		const input = " first line\nsecond line\n"
		cmd := command(target)
		if target == "" {
			cmd.Dir = launch // Operator entry; later loops start in cmd/godel.
		}
		cmd.Stdin = strings.NewReader(input)
		var stdout, stderr bytes.Buffer
		cmd.Stdout, cmd.Stderr = &stdout, &stderr
		if err := cmd.Start(); err != nil {
			t.Fatal(err)
		}
		err := cmd.Wait()
		if err == nil || cmd.ProcessState.ExitCode() != 17 {
			t.Fatalf("entry: %v, stderr: %s", err, &stderr)
		}
		diagnostic := target + " diagnostic\n"
		if target == "" {
			target = "main"
			diagnostic = "accepted diagnostic\n"
		}
		want := fmt.Sprintf("accepted pid=%d argv0=%q cwd=%q target=%q input=%q\n", cmd.Process.Pid, exe, cmd.Dir, target, input)
		if stdout.String() != want || stderr.String() != diagnostic {
			t.Fatalf("stdout %q, want %q; stderr %q", &stdout, want, &stderr)
		}
	}
	if out, err := command("@").CombinedOutput(); err == nil || !strings.Contains(string(out), "no unambiguous local accepted commit") {
		t.Fatalf("non-bookmark @: %s: %v", out, err)
	}
	if checkpoint() != before {
		t.Fatal("launcher snapshotted the dirty workspace")
	}

	t.Run("cancel during build", func(t *testing.T) {
		bin := t.TempDir()
		// This launcher waits for a child, like the Go tool. The child's inherited
		// diagnostic fd stays open until it too is stopped.
		write(filepath.Join(bin, "go"), "#!/bin/sh\nsh -c 'echo ready $PPID >&2; exec sleep 50'\nexit 0\n")
		t.Setenv("PATH", bin+":"+os.Getenv("PATH"))
		cmd := command("main")
		r, w, err := os.Pipe()
		if err != nil {
			t.Fatal(err)
		}
		defer r.Close()
		defer w.Close()
		cmd.Stderr = w
		if err := cmd.Start(); err != nil {
			t.Fatal(err)
		}
		defer func() {
			if cmd.ProcessState == nil {
				cmd.Process.Signal(syscall.SIGTERM)
				cmd.Wait()
			}
		}()
		w.Close()
		if err := r.SetReadDeadline(time.Now().Add(10 * time.Second)); err != nil {
			t.Fatal(err)
		}
		reader := bufio.NewReader(r)
		ready, err := reader.ReadString('\n')
		var pgid int
		if _, scanErr := fmt.Sscanf(ready, "ready %d", &pgid); err != nil || scanErr != nil || pgid <= 1 {
			t.Fatalf("build not ready: %q: %v", ready, err)
		}
		if err := cmd.Process.Signal(syscall.SIGTERM); err != nil {
			t.Fatal(err)
		}
		if _, err := io.ReadAll(reader); err != nil {
			syscall.Kill(-pgid, syscall.SIGKILL)
			t.Fatalf("build descendant retained stderr: %v", err)
		}
		if err := cmd.Wait(); err == nil {
			t.Fatal("interrupted bootstrap succeeded")
		}
		if files, err := os.ReadDir(scratch); err != nil || len(files) != 0 {
			t.Fatalf("scratch after cancellation: %v, %v", files, err)
		}
	})
}

func TestBuiltMarkerConsumed(t *testing.T) {
	// A canceled built entry reaches Run but cannot
	// invoke any mission node. Run is once per
	// process, so exercise it in a test subprocess.
	if os.Getenv("GRH_TEST_CONSUME_MARKER") == "1" {
		os.Args = os.Args[:1]
		source := t.TempDir()
		t.Setenv(builtEntry, strconv.Itoa(os.Getpid())+":"+source)
		ctx, cancel := context.WithCancel(t.Context())
		cancel()
		if err := run(ctx); !errors.Is(err, context.Canceled) {
			t.Fatal(err)
		}
		if got, err := os.Getwd(); err != nil || got != source {
			t.Fatalf("registration directory = %q, %v; want %q", got, err, source)
		}
		if _, set := os.LookupEnv(builtEntry); set {
			t.Fatal("marker would reach a loop launch")
		}
		return
	}
	ctx, cancel := context.WithTimeout(t.Context(), 10*time.Second)
	defer cancel()
	exe, err := os.Executable()
	if err != nil {
		t.Fatal(err)
	}
	cmd := exec.CommandContext(ctx, exe, "-test.run=^TestBuiltMarkerConsumed$")
	cmd.Env = append(os.Environ(), "GRH_TEST_CONSUME_MARKER=1")
	if out, err := cmd.CombinedOutput(); err != nil {
		t.Fatalf("marker: %s: %v", out, err)
	}
}
