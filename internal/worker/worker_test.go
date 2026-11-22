package worker

import (
	"archive/tar"
	"bufio"
	"bytes"
	"context"
	"crypto/sha256"
	"encoding/json"
	"errors"
	"fmt"
	"io"
	"maps"
	"os"
	"os/exec"
	"path/filepath"
	"slices"
	"strings"
	"syscall"
	"testing"
	"time"
)

func write(t *testing.T, name, content string, mode os.FileMode) {
	t.Helper()
	if err := os.WriteFile(name, []byte(content), mode); err != nil {
		t.Fatal(err)
	}
}

// Snapshot only a disposable repository. Changing a source file afterwards
// distinguishes a revision export from an accidental working-directory copy.
func repository(t *testing.T, additionalModules ...string) (root, revision string) {
	t.Helper()
	root = t.TempDir()
	jj := func(args ...string) string {
		t.Helper()
		cmd := exec.CommandContext(t.Context(), "jj", args...)
		cmd.Dir = root
		out, err := cmd.Output()
		if err != nil {
			t.Fatalf("jj %s: %v", args, err)
		}
		return strings.TrimSpace(string(out))
	}
	jj("git", "init")
	for _, name := range []string{"lakefile.toml", "lake-manifest.json", "lean-toolchain"} {
		b, err := os.ReadFile(filepath.Join("..", "..", name))
		if err != nil {
			t.Fatal(err)
		}
		write(t, filepath.Join(root, name), string(b), 0644)
	}
	if err := os.MkdirAll(filepath.Join(root, "Proofs", "Props"), 0755); err != nil {
		t.Fatal(err)
	}
	source := filepath.Join(root, "Proofs", "Props", "Example.lean")
	write(t, source, "theorem Example.ok : True := True.intro\n", 0644)
	for _, m := range additionalModules {
		write(t, filepath.Join(root, "Proofs", "Props", m+".lean"), "def exampleTwo : Nat := 2\n", 0644)
	}
	revision = jj("log", "-r", "@", "-T", "commit_id", "--no-graph")
	write(t, source, "not the selected commit\n", 0644)
	write(t, filepath.Join(root, "dirty"), "untracked", 0644)
	return root, revision
}

func transport(t *testing.T, body string) {
	t.Helper()
	name := filepath.Join(t.TempDir(), "transport")
	write(t, name, "#!/bin/sh\nset -eu\n"+body, 0700)
	t.Setenv("GRH_PROOF_WORKER", name)
}

// This transport never runs its argv.
// Its receipts are protocol fixtures,
// not build results. Compare the
// transferred archive and the requested
// commands independently of the
// fixture's response.
func TestCheckTransfer(t *testing.T) {
	root, rev := repository(t)
	capture := t.TempDir()
	t.Setenv("CAPTURE", capture)
	transport(t, `cat > "$CAPTURE/tar"
printf '%s' "$3" > "$CAPTURE/script"
printf '%s' "$7" > "$CAPTURE/stamp"
[ "$8" = Props.Example ]
printf '%s\n' "$7" '{"severity":"information","data":"checked project declarations"}' "{\"severity\":\"information\",\"data\":\"'Example.ok' does not depend on any axioms\"}"
`)
	if err := Check(t.Context(), root, rev, []string{"Example.ok"}); err != nil {
		t.Fatal(err)
	}
	read := func(name string) []byte {
		b, err := os.ReadFile(filepath.Join(capture, name))
		if err != nil {
			t.Fatal(err)
		}
		return b
	}
	raw := read("tar")
	if stamp := string(read("stamp")); stamp != fmt.Sprintf("%s %x", rev, sha256.Sum256(raw)) {
		t.Fatalf("bad stamp: %s", stamp)
	}
	script := string(read("script"))
	for _, want := range []string{
		"lake --no-cache --wfail build Proofs", `lake env leanchecker "$@"`,
		"import Props.Example\n", "#print axioms Example.ok\n", "collectAxioms c.name",
	} {
		if !strings.Contains(script, want) {
			t.Errorf("command missing %q", want)
		}
	}
	tr := tar.NewReader(bytes.NewReader(raw))
	files := map[string]string{}
	for {
		h, err := tr.Next()
		if err == io.EOF {
			break
		}
		if err != nil {
			t.Fatal(err)
		}
		b, err := io.ReadAll(tr)
		if err != nil {
			t.Fatal(err)
		}
		files[h.Name] = string(b)
	}
	if len(files) != 4 || files["Proofs/Props/Example.lean"] != "theorem Example.ok : True := True.intro\n" {
		t.Errorf("unexpected transferred files: %v", slices.Sorted(maps.Keys(files)))
	}
}

func TestCheckFailure(t *testing.T) {
	root, rev := repository(t)
	decls := []string{"Example.ok"}
	t.Setenv("GRH_PROOF_WORKER", "")
	if err := Check(t.Context(), root, rev, decls); err == nil || !strings.Contains(err.Error(), "GRH_PROOF_WORKER") {
		t.Fatalf("no designation: %v", err)
	}
	t.Setenv("GRH_PROOF_WORKER", filepath.Join(t.TempDir(), "missing"))
	if err := Check(t.Context(), root, rev, decls); !errors.Is(err, os.ErrNotExist) {
		t.Fatalf("missing transport: %v", err)
	}
	transport(t, "echo 'failed build' >&2\nexit 23\n")
	var exit *exec.ExitError
	if err := Check(t.Context(), root, rev, decls); !errors.As(err, &exit) || exit.ExitCode() != 23 || !strings.Contains(err.Error(), "failed build") {
		t.Fatalf("build failure: %v", err)
	}
	transport(t, "echo wrong-stamp\n")
	if err := Check(t.Context(), root, rev, decls); err == nil || !strings.Contains(err.Error(), "receipt") {
		t.Fatalf("wrong receipt: %v", err)
	}
}

func TestRejectUntrustedBuildInputs(t *testing.T) {
	for name, want := range map[string]string{
		"lean-toolchain":           "project pin changed",
		"Proofs/Props/Stale.olean": "precompiled input",
		"lakefile.lean":            "unexpected build input",
	} {
		t.Run(name, func(t *testing.T) {
			root, _ := repository(t)
			write(t, filepath.Join(root, name), "not a trusted build input", 0644)
			cmd := exec.CommandContext(t.Context(), "jj", "log", "-r", "@", "-T", "commit_id", "--no-graph")
			cmd.Dir = root
			out, err := cmd.Output()
			if err != nil {
				t.Fatal(err)
			}
			if _, err := archive(t.Context(), root, strings.TrimSpace(string(out)), io.Discard); err == nil || !strings.Contains(err.Error(), want) {
				t.Fatalf("wanted %q, got %v", want, err)
			}
		})
	}
}

func TestCheckCancelDuringTransport(t *testing.T) {
	root, rev := repository(t)
	fifo := filepath.Join(t.TempDir(), "started")
	if err := syscall.Mkfifo(fifo, 0600); err != nil {
		t.Fatal(err)
	}
	started, err := os.OpenFile(fifo, os.O_RDWR|syscall.O_NONBLOCK, 0)
	if err != nil {
		t.Fatal(err)
	}
	defer started.Close()
	if err := started.SetReadDeadline(time.Now().Add(15 * time.Second)); err != nil {
		t.Fatal(err)
	}
	t.Setenv("STARTED", fifo)
	transport(t, "echo admitted > \"$STARTED\"\nexec tail -f /dev/null\n")
	ctx, cancel := context.WithCancel(t.Context())
	done := make(chan error, 1)
	go func() { done <- Check(ctx, root, rev, []string{"Example.ok"}) }()
	msg, readErr := bufio.NewReader(started).ReadString('\n')
	cancel()
	err = <-done
	if readErr != nil || msg != "admitted\n" {
		t.Fatalf("transport never admitted: %q %v, Check: %v", msg, readErr, err)
	}
	if !errors.Is(err, context.Canceled) {
		t.Fatalf("lost cancellation: %v", err)
	}
}

func TestAudit(t *testing.T) {
	info := func(msg string) string {
		b, _ := json.Marshal(map[string]string{"severity": "information", "data": msg})
		return string(b) + "\n"
	}
	m := info("checked project declarations")
	a := info("'A' does not depend on any axioms")
	b := info("'T.b'' depends on axioms: [Quot.sound, propext, Classical.choice]")
	decls := []string{"T.b'", "A"}
	if err := audit([]byte(m+a+b), decls); err != nil {
		t.Fatal(err)
	}
	for name, msgs := range map[string]string{
		"extra signature":       m + a + b + info("endpoint signature 'A':\nA : True"),
		"skipped project check": a + b,
		"absent":                m + b,
		"duplicate":             m + a + b + b,
		"admission":             m + a + strings.Replace(b, "propext", "sorryAx", 1),
		"global axiom":          m + strings.Replace(b, "Quot.sound", "Project.leaf", 1) + a,
		"warning":               m + b + strings.Replace(a, "information", "warning", 1),
		"corrupt":               m + a + b + "{",
		"unrequested":           m + a + strings.Replace(b, "T.b'", "Other", 1),
	} {
		t.Run(name, func(t *testing.T) {
			if err := audit([]byte(msgs), decls); err == nil {
				t.Fatal("accepted incomplete or forbidden audit")
			}
		})
	}

}
