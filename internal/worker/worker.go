// Package worker checks a mathematical candidate on an explicitly designated remote worker.
package worker

import (
	"bytes"
	"context"
	"crypto/sha256"
	"encoding/json"
	"errors"
	"fmt"
	"io"
	"os"
	"os/exec"
	"path/filepath"
	"regexp"
	"strings"
	"time"
)

var (
	commitID = regexp.MustCompile(`^[0-9a-f]{40}$`)
	leanName = regexp.MustCompile(`^[\pL_][\pL\pN_']*(\.[\pL_][\pL\pN_']*)*$`)
)

// Check builds the full jj commit (not a bookmark, prefix or working
// directory) and audits each named project constant. The caller selects the
// complete list from independent review; a successful check is specific to
// that pair of inputs.
//
// GRH_PROOF_WORKER must be the absolute path to an operator-provisioned
// transport to the designated remote Linux worker. It receives command argv
// (sh -c SCRIPT grh-check ...), tar on stdin, and must forward stdout,
// stderr and exit status faithfully. It must run that argv directly on
// the worker in fresh, private scratch, with no other writable mounts, a
// trusted v4.36.0 toolchain on PATH and the locked dependencies available to
// Lake. Optionally it can supply a private, verified copy of the manifest's
// packages in ./packages. The transport owns remote job lifetime, time
// limits and scratch reclamation (including after disconnect). No local
// toolchain or host-discovery fallback.
func Check(ctx context.Context, root, revision string, decls []string) error {
	if err := ctx.Err(); err != nil {
		return err
	}
	transport := os.Getenv("GRH_PROOF_WORKER")
	if !filepath.IsAbs(transport) {
		return errors.New("designated remote proof worker unavailable: GRH_PROOF_WORKER must name an absolute transport executable")
	}
	if root == "" || !commitID.MatchString(revision) {
		return errors.New("expected repository root and full jj commit ID")
	}
	if len(decls) == 0 {
		return errors.New("no declarations to audit")
	}
	seen := map[string]bool{}
	for _, d := range decls {
		if !leanName.MatchString(d) || seen[d] {
			return fmt.Errorf("invalid or repeated Lean constant %q", d)
		}
		seen[d] = true
	}
	boot, err := os.ReadFile("/proc/sys/kernel/random/boot_id")
	if err != nil {
		return fmt.Errorf("identify local kernel: %w", err)
	}
	f, err := os.CreateTemp("", "grh-check-*.tar")
	if err != nil {
		return err
	}
	defer os.Remove(f.Name())
	defer f.Close()
	digest := sha256.New()
	modules, err := archive(ctx, root, revision, io.MultiWriter(f, digest))
	if err != nil {
		return fmt.Errorf("export %s: %w", revision, err)
	}
	if _, err := f.Seek(0, io.SeekStart); err != nil {
		return err
	}
	stamp := fmt.Sprintf("%s %x", revision, digest.Sum(nil))
	args := []string{"sh", "-c", remote + auditSource(modules, decls) + "EOF_GRH_AUDIT\n", "grh-check", strings.TrimSpace(string(boot)), fmt.Sprintf("%x", digest.Sum(nil)), stamp}
	cmd := exec.CommandContext(ctx, transport, append(args, modules...)...)
	cmd.Stdin = f
	cmd.WaitDelay = 2 * time.Second
	out, err := cmd.Output()
	if err != nil {
		var exit *exec.ExitError
		if errors.As(err, &exit) {
			return fmt.Errorf("proof worker %s: %w (stderr %q; audit output %q)", revision, errors.Join(ctx.Err(), err), tail(exit.Stderr), tail(out))
		}
		return fmt.Errorf("proof worker %s: %w", revision, errors.Join(ctx.Err(), err))
	}
	if err := ctx.Err(); err != nil {
		return err
	}
	receipt, msgs, ok := bytes.Cut(out, []byte("\n"))
	if !ok || string(receipt) != stamp {
		return errors.New("missing exact candidate build receipt")
	}
	if err := audit(msgs, decls); err != nil {
		return fmt.Errorf("audit %s: %w", revision, err)
	}
	return ctx.Err()
}

// The boot comparison catches accidental
// loopback routing. It is not a way to
// discover a worker or authenticate one;
// designation and isolation are the
// transport's responsibility. Keep build
// logs separate from audit messages.
const remote = `set -eu
boot=$(cat /proc/sys/kernel/random/boot_id)
[ -n "$boot" ] && [ "$boot" != "$1" ] || exit 20
umask 077
mkdir project tmp home
export HOME="$PWD/home" TMPDIR="$PWD/tmp" XDG_CACHE_HOME="$PWD/home/.cache" MATHLIB_NO_CACHE_ON_UPDATE=1
cat > snapshot.tar
printf '%s  snapshot.tar\n' "$2" | sha256sum --check --status || exit 21
tar -xf snapshot.tar -C project
cd project
if test -d ../packages; then mkdir .lake; mv ../packages .lake/packages; fi
[ "$(lean --short-version)" = 4.36.0 ] || exit 22
lake --no-cache --wfail build Proofs >&2 || exit 23
stamp=$3
shift 3
lake env leanchecker "$@" >&2 || exit 24
printf '%s\n' "$stamp"
exec lake env lean --json --stdin <<'EOF_GRH_AUDIT'
`

// Limit diagnostics returned to the workflow after a build or audit failure.
func tail(b []byte) string { return strings.TrimSpace(string(b[max(0, len(b)-2048):])) }

const moduleReceipt = "checked project declarations"

func auditSource(modules, decls []string) string {
	var b strings.Builder
	b.WriteString("import Lean\n")
	for _, m := range modules {
		fmt.Fprintf(&b, "import %s\n", m)
	}
	// A name from an imported dependency is
	// not a project declaration. Likewise an
	// unsafe implementation must not count as
	// a mathematical result.
	fmt.Fprintf(&b, `set_option pp.fullNames true
open Lean in
run_cmd do
  let env ← getEnv
  let modules : List Name := [%s]
  let allowed : List Name := [%s]
  let mut audited : List Name := []
  for m in env.header.moduleNames, data in env.header.moduleData do
    if modules.contains m then
      audited := m :: audited
      for c in data.constants do
        if c matches .axiomInfo _ then throwError m!"project axiom {c.name}"
        for ax in ← collectAxioms c.name do
          unless allowed.contains ax do throwError m!"{c.name} uses unapproved axiom {ax}"
  for m in modules do
    unless audited.contains m do throwError m!"no module data for {m}"
  for d in ([%s] : List Name) do
    let some i := env.getModuleIdxFor? d | throwError "unknown endpoint"
    unless modules.contains env.header.moduleNames[i]! do throwError "not a project endpoint"
    let some c := env.find? d | throwError "unknown endpoint"
    if c.isUnsafe || c.isPartial then throwError "not a safe endpoint"
  logInfo "%s"
`, "`"+strings.Join(modules, ", `"), "`propext, `Classical.choice, `Quot.sound", "`"+strings.Join(decls, ", `"), moduleReceipt)
	for _, d := range decls {
		fmt.Fprintf(&b, "#print axioms %s\n", d)
	}
	return b.String()
}

func audit(output []byte, decls []string) error {
	pending := map[string]bool{}
	for _, d := range decls {
		pending[d] = true
	}
	checked := false
	dec := json.NewDecoder(bytes.NewReader(output))
	for {
		var m struct{ Severity, Data string }
		if err := dec.Decode(&m); err == io.EOF {
			break
		} else if err != nil {
			return fmt.Errorf("invalid Lean JSON: %w", err)
		}
		if m.Severity == "information" && m.Data == moduleReceipt && !checked {
			checked = true
			continue
		}
		data, ok := strings.CutPrefix(m.Data, "'")
		name, rest, found := strings.Cut(data, "' ")
		// Lean names may end in a prime; the delimiter includes the
		// following space.
		if !ok || !found || !pending[name] || m.Severity != "information" {
			return errors.New("unexpected or duplicate Lean diagnostic")
		}
		delete(pending, name)
		if rest == "does not depend on any axioms" {
			continue
		}
		list, ok := strings.CutPrefix(rest, "depends on axioms: [")
		list, closed := strings.CutSuffix(list, "]")
		if !ok || !closed {
			return fmt.Errorf("incomplete axiom report for %s", name)
		}
		for a := range strings.SplitSeq(list, ",") {
			switch strings.TrimSpace(a) {
			case "propext", "Classical.choice", "Quot.sound":
			default:
				return fmt.Errorf("unapproved axiom %q for %s", strings.TrimSpace(a), name)
			}
		}
	}
	if !checked {
		return errors.New("missing project declaration audit")
	}
	for _, d := range decls {
		if pending[d] {
			return fmt.Errorf("no axiom report for %s", d)
		}
	}
	return nil
}
