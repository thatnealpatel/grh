package landing

import (
	"context"
	"encoding/json"
	"errors"
	"fmt"
	"os"
	"os/exec"
	"path/filepath"
	"reflect"
	"slices"
	"strings"
	"testing"
)

const (
	proofPath = `Proofs/Pilot/Exact"Name.lean`
	proofText = "theorem exact_check : True := trivial\n"
	priorText = "theorem exact_check : True := by trivial\n"
	message   = "Pilot: check exact landing"
)

// This subprocess stands in for the
// trusted bridge, not for jj inspection
// or grh staging. The fixture never
// mutates a real campaign's accepted
// target.
func TestAdapterProcess(t *testing.T) {
	planPath := os.Getenv("GRH_LANDING_TEST_PLAN")
	if planPath == "" {
		return
	}
	var in map[string]any
	if err := json.NewDecoder(os.Stdin).Decode(&in); err != nil {
		t.Fatal(err)
	}
	op, _ := in["op"].(string)
	if err := runAdapter(t, planPath, op, in); err != nil {
		fmt.Fprintln(os.Stderr, err)
		os.Exit(1)
	}
	os.Exit(0)
}

type fixtureStep struct {
	Op         string
	Request    map[string]any
	Reply      any
	ReadStaged string
	Fail       string
}

func runAdapter(t *testing.T, planPath, op string, in map[string]any) error {
	var plan []fixtureStep
	if err := json.Unmarshal([]byte(readFixture(t, planPath)), &plan); err != nil {
		return err
	}
	log := planPath + ".log"
	position := len(strings.Fields(readFixture(t, log)))
	appendEvent(t, log, op)
	if position >= len(plan) || plan[position].Op != op {
		return fmt.Errorf("unexpected %s at step %d", op, position)
	}
	step := plan[position]
	if !reflect.DeepEqual(in, step.Request) {
		return fmt.Errorf("%s request: got %v, want %v", op, in, step.Request)
	}
	if step.ReadStaged != "" && readFixture(t, step.ReadStaged) != proofText {
		return errors.New("gate did not stage exact proof bytes")
	}
	if step.Fail != "" {
		return errors.New(step.Fail)
	}
	return json.NewEncoder(os.Stdout).Encode(step.Reply)
}

type fixture struct {
	root, dir, base, prepared, checkpoint, output, candidate string
	drifts                                                   map[string]string
}

func newFixture(t *testing.T, replace bool) fixture {
	t.Helper()
	if _, err := exec.LookPath("jj"); err != nil {
		t.Skipf("requires jj for exact-revision inspection: %v", err)
	}
	// Ignore developer repository config, working copies and
	// credentials.
	t.Setenv("JJ_CONFIG", filepath.Join(t.TempDir(), "config.toml"))
	writeFixture(t, os.Getenv("JJ_CONFIG"), "[user]\nname = 'Landing Test'\nemail = 'landing@example.invalid'\n", 0o600)
	f := fixture{dir: t.TempDir(), drifts: make(map[string]string)}
	f.root = filepath.Join(f.dir, "control")
	fixtureJJ(t, f.dir, "git", "init", "--no-colocate", f.root)
	writeFixture(t, filepath.Join(f.root, "lean-toolchain"), "leanprover/lean4:v4.36.0\n", 0o644)
	writeFixture(t, filepath.Join(f.root, "lakefile.toml"), "name = 'test'\n", 0o644)
	writeFixture(t, filepath.Join(f.root, "lake-manifest.json"), `{"packages":[]}`, 0o644)
	writeFixture(t, filepath.Join(f.root, "Proofs", "Keep.lean"), "-- untouched\n", 0o644)
	if replace {
		writeFixture(t, filepath.Join(f.root, proofPath), priorText, 0o644)
	}
	f.base = snapshot(t, f.root)
	f.prepared = f.workspace(t, "prepared", f.base)
	f.checkpoint = snapshot(t, f.prepared)
	f.output = f.revision(t, "output", f.base, proofPath, proofText, 0o644)
	f.candidate = f.revision(t, "candidate", f.base, proofPath, proofText, 0o644)
	return f
}

func (f fixture) workspace(t *testing.T, label, base string) string {
	t.Helper()
	p := filepath.Join(f.dir, label)
	fixtureJJ(t, f.root, "workspace", "add", "--revision", base, "--message", label, p)
	return p
}

func (f fixture) revision(t *testing.T, label, base, name, value string, mode os.FileMode) string {
	t.Helper()
	p := f.workspace(t, label, base)
	writeFixture(t, filepath.Join(p, name), value, mode)
	return snapshot(t, p)
}

func snapshot(t *testing.T, workspace string) string {
	t.Helper()
	// Deliberately capture fixture content only, not the harness checkout.
	return strings.TrimSpace(fixtureJJ(t, workspace, "log", "--no-graph", "-r", "@", "-T", `commit_id ++ "\n"`))
}

func fixtureJJ(t *testing.T, dir string, args ...string) string {
	t.Helper()
	cmd := exec.CommandContext(t.Context(), "jj", args...)
	cmd.Dir = dir
	out, err := cmd.CombinedOutput()
	if err != nil {
		t.Fatalf("jj %v: %v\n%s", args, err, out)
	}
	return string(out)
}

func (f fixture) plan(accepted string) []fixtureStep {
	w := map[string]any{"path": f.prepared, "base": f.base, "checkpoint": f.checkpoint}
	req := func(op string, fields map[string]any) map[string]any {
		if fields == nil {
			fields = make(map[string]any)
		}
		fields["op"], fields["root"] = op, f.root
		return fields
	}
	status := func(revision string) fixtureStep {
		return fixtureStep{Op: "status", Request: req("status", nil), Reply: map[string]any{"available": true, "accepted": revision}}
	}
	return []fixtureStep{
		status(f.base),
		{Op: "prepare", Request: req("prepare", map[string]any{"on": f.base}), Reply: w},
		{Op: "finalize", Request: req("finalize", map[string]any{"workspace": w}), ReadStaged: filepath.Join(f.prepared, proofPath), Reply: map[string]any{
			"commit": f.output, "workspace": f.prepared, "base": f.base, "conflicted": false,
		}},
		{Op: "check-output"},
		{Op: "integrate", Request: req("integrate", map[string]any{"on": f.base, "outputs": []string{f.output}, "description": message}), Reply: map[string]any{
			"status": "pending", "base": f.base, "candidate": f.candidate, "inputs": []string{f.output}, "conflicted": false,
		}},
		{Op: "check-candidate"},
		status(f.base),
		{Op: "intent"},
		{Op: "adopt", Request: req("adopt", map[string]any{"candidate": f.candidate}), Reply: map[string]any{"accepted": accepted, "stale": false}},
		status(accepted),
	}
}

func usePlan(t *testing.T, steps []fixtureStep) string {
	t.Helper()
	dir := t.TempDir()
	executable, err := os.Executable()
	if err != nil {
		t.Fatal(err)
	}
	path := filepath.Join(dir, "bridge")
	writeFixture(t, path, "#!/bin/sh\nexec \"$GRH_LANDING_TEST_EXE\" -test.run='^TestAdapterProcess$'\n", 0o700)
	plan := filepath.Join(dir, "steps.json")
	data, err := json.Marshal(steps)
	if err != nil {
		t.Fatal(err)
	}
	writeFixture(t, plan, string(data), 0o600)
	writeFixture(t, plan+".log", "", 0o600)
	t.Setenv(adapterEnv, path)
	t.Setenv("GRH_LANDING_TEST_EXE", executable)
	t.Setenv("GRH_LANDING_TEST_PLAN", plan)
	return plan + ".log"
}

func writeFixture(t *testing.T, path, data string, mode os.FileMode) {
	t.Helper()
	if err := os.MkdirAll(filepath.Dir(path), 0o700); err != nil {
		t.Fatal(err)
	}
	if err := os.WriteFile(path, []byte(data), mode); err != nil {
		t.Fatal(err)
	}
}

func readFixture(t *testing.T, path string) string {
	t.Helper()
	data, err := os.ReadFile(path)
	if err != nil {
		t.Fatal(err)
	}
	return string(data)
}

func appendEvent(t *testing.T, log, event string) {
	t.Helper()
	file, err := os.OpenFile(log, os.O_APPEND|os.O_WRONLY, 0)
	if err != nil {
		t.Fatal(err)
	}
	_, err = fmt.Fprintln(file, event)
	if err := errors.Join(err, file.Close()); err != nil {
		t.Fatal(err)
	}
}

func checkEvents(t *testing.T, log string, plan []fixtureStep) {
	t.Helper()
	want := make([]string, len(plan))
	for i := range plan {
		want[i] = plan[i].Op
	}
	if got := strings.Fields(readFixture(t, log)); !slices.Equal(got, want) {
		t.Fatalf("operations = %v, want %v", got, want)
	}
}

func (f fixture) land(t *testing.T, log string, previous map[string]string, checkErr error, rejectCheck int, intentErr error) (string, error) {
	t.Helper()
	checked := 0
	return LandReplacing(t.Context(), f.root, map[string]string{proofPath: proofText}, []string{"exact_check"}, message,
		func(_ context.Context, root, revision string, declarations []string) error {
			t.Helper()
			checked++
			if root != f.root || !slices.Equal(declarations, []string{"exact_check"}) {
				t.Fatalf("worker invocation got %q, %q", root, declarations)
			}
			if checked == 1 && revision == f.output {
				appendEvent(t, log, "check-output")
			} else if checked == 2 && revision == f.candidate {
				appendEvent(t, log, "check-candidate")
			} else {
				t.Fatalf("unexpected revision %s at check %d", revision, checked)
			}
			if checked == rejectCheck {
				return checkErr
			}
			declarations[0] = "not_the_checked_declaration"
			return nil
		}, func(_ context.Context, revision string) error {
			if revision != f.candidate {
				t.Fatalf("adoption intent got %s, want %s", revision, f.candidate)
			}
			appendEvent(t, log, "intent")
			return intentErr
		}, previous)
}

func TestLandOrderAndExactRevision(t *testing.T) {
	for _, replace := range []bool{false, true} {
		t.Run(fmt.Sprintf("replace=%t", replace), func(t *testing.T) {
			f := newFixture(t, replace)
			accepted := f.revision(t, "accepted", f.candidate, "README", "unrelated later acceptance", 0o644)
			plan := f.plan(accepted)
			log := usePlan(t, plan)
			var previous map[string]string
			if replace {
				previous = map[string]string{proofPath: priorText}
			}
			revision, err := f.land(t, log, previous, nil, 0, nil)
			if err != nil || revision != f.candidate {
				t.Fatalf("LandReplacing = %q, %v; want %s", revision, err, f.candidate)
			}
			checkEvents(t, log, plan)
			p := filepath.Join(f.root, proofPath)
			if replace {
				if readFixture(t, p) != priorText {
					t.Fatal("landing changed control checkout")
				}
			} else if _, err := os.Stat(p); !errors.Is(err, os.ErrNotExist) {
				t.Fatalf("landing changed control checkout: %v", err)
			}
		})
	}
}

func TestLandStopsBeforeAdoption(t *testing.T) {
	workerErr := errors.New("worker rejected exact revision")
	intentErr := errors.New("intent not persisted")
	for _, tt := range []struct {
		name, problem string
		stop          int
		alter         func(*testing.T, fixture, []fixtureStep)
		reject        int
		intentErr     error
	}{
		{"prepare-base", "different base", 2, func(t *testing.T, f fixture, p []fixtureStep) {
			p[1].Reply = map[string]any{"path": f.prepared, "base": f.output, "checkpoint": f.checkpoint}
		}, 0, nil},
		{"output-scope", "diff includes unauthorized path", 3, func(t *testing.T, f fixture, p []fixtureStep) {
			p[2].Reply.(map[string]any)["commit"] = f.drifts["setup"]
		}, 0, nil},
		{"output-worker", workerErr.Error(), 4, nil, 1, nil},
		{"integrate-input", "exact output and base", 5, func(t *testing.T, f fixture, p []fixtureStep) {
			p[4].Reply.(map[string]any)["inputs"] = []string{f.candidate}
		}, 0, nil},
		{"candidate-parent", "sole parent", 5, func(t *testing.T, f fixture, p []fixtureStep) {
			p[4].Reply.(map[string]any)["candidate"] = f.drifts["parent"]
		}, 0, nil},
		{"candidate-bytes", "unexpected contents", 5, func(t *testing.T, f fixture, p []fixtureStep) {
			p[4].Reply.(map[string]any)["candidate"] = f.drifts["bytes"]
		}, 0, nil},
		{"candidate-mode", "non-executable", 5, func(t *testing.T, f fixture, p []fixtureStep) {
			p[4].Reply.(map[string]any)["candidate"] = f.drifts["mode"]
		}, 0, nil},
		{"candidate-worker", workerErr.Error(), 6, nil, 2, nil},
		{"accepted-advanced", "stale integration base", 7, func(t *testing.T, f fixture, p []fixtureStep) { p[6].Reply.(map[string]any)["accepted"] = f.output }, 0, nil},
		{"persist-intent", intentErr.Error(), 8, nil, 0, intentErr},
	} {
		t.Run(tt.name, func(t *testing.T) {
			f := newFixture(t, false)
			switch tt.name {
			case "output-scope":
				w := f.workspace(t, "setup-drift", f.base)
				writeFixture(t, filepath.Join(w, proofPath), proofText, 0o644)
				writeFixture(t, filepath.Join(w, "lean-toolchain"), "leanprover/lean4:nightly\n", 0o644)
				f.drifts["setup"] = snapshot(t, w)
			case "candidate-parent":
				f.drifts["parent"] = f.revision(t, "wrong-parent", f.output, proofPath, proofText, 0o644)
			case "candidate-bytes":
				f.drifts["bytes"] = f.revision(t, "wrong-bytes", f.base, proofPath, proofText+"\n", 0o644)
			case "candidate-mode":
				f.drifts["mode"] = f.revision(t, "wrong-mode", f.base, proofPath, proofText, 0o755)
			}
			plan := f.plan(f.candidate)[:tt.stop]
			if tt.alter != nil {
				tt.alter(t, f, plan)
			}
			log := usePlan(t, plan)
			revision, err := f.land(t, log, nil, workerErr, tt.reject, tt.intentErr)
			if revision != "" || err == nil || !strings.Contains(err.Error(), tt.problem) {
				t.Fatalf("LandReplacing = %q, %v, want error containing %q", revision, err, tt.problem)
			}
			if tt.reject != 0 && !errors.Is(err, workerErr) || tt.intentErr != nil && !errors.Is(err, tt.intentErr) {
				t.Fatalf("wrapped underlying error lost: %v", err)
			}
			checkEvents(t, log, plan)
		})
	}
}

func TestAdoptionRequiresAuthoritativeAcceptance(t *testing.T) {
	for _, name := range []string{"stale", "acknowledgment-unrelated", "acknowledgment-incomplete", "subprocess-failure", "status-unrelated", "status-contents-changed"} {
		t.Run(name, func(t *testing.T) {
			f := newFixture(t, false)
			plan := f.plan(f.candidate)
			ack := plan[8].Reply.(map[string]any)
			status := plan[9].Reply.(map[string]any)
			want := "unconfirmed"
			switch name {
			case "stale":
				ack["stale"] = true
				plan, want = plan[:9], "is stale"
			case "acknowledgment-unrelated":
				ack["accepted"] = f.output // Same proof bytes, but a sibling.
				plan = plan[:9]
			case "acknowledgment-incomplete":
				delete(ack, "stale")
				plan = plan[:9]
			case "subprocess-failure":
				plan[8].Fail = "could not persist adoption after refreshing target"
				plan = plan[:9]
			case "status-unrelated":
				status["accepted"] = f.output
			case "status-contents-changed":
				status["accepted"] = f.revision(t, "rewritten", f.candidate, proofPath, priorText, 0o644)
			}
			log := usePlan(t, plan)
			revision, err := f.land(t, log, nil, nil, 0, nil)
			if revision != "" || err == nil || !strings.Contains(err.Error(), want) {
				t.Fatalf("LandReplacing = %q, %v; want error containing %q", revision, err, want)
			}
			checkEvents(t, log, plan)
			if name == "subprocess-failure" {
				if _, ok := errors.AsType[*exec.ExitError](err); !ok || !strings.Contains(err.Error(), plan[8].Fail) {
					t.Fatalf("subprocess error lost: %v", err)
				}
				// A later authoritative read can
				// verify the recorded intent without
				// retrying an adoption whose
				// acknowledgment was lost.
				readPlan := f.plan(f.candidate)[9:]
				readLog := usePlan(t, readPlan)
				if err := ReadLanded(t.Context(), f.root, f.candidate, map[string]string{proofPath: proofText}); err != nil {
					t.Fatal(err)
				}
				checkEvents(t, readLog, readPlan)
			}
		})
	}
}

func TestReadLandedVerifiesAnchorAndRetention(t *testing.T) {
	f := newFixture(t, false)
	rewritten := f.revision(t, "rewrite", f.candidate, proofPath, priorText, 0o644)
	for _, tt := range []struct {
		name, anchor, accepted, contents, problem string
	}{
		{"anchor", f.candidate, f.candidate, proofText, ""},
		{"sibling", f.output, f.candidate, proofText, "not in accepted ancestry"},
		{"wrong-anchor-bytes", f.candidate, rewritten, priorText, "verify anchored revision"},
		{"wrong-retained-bytes", f.candidate, rewritten, proofText, "verify retained files"},
	} {
		t.Run(tt.name, func(t *testing.T) {
			plan := f.plan(tt.accepted)[9:]
			log := usePlan(t, plan)
			err := ReadLanded(t.Context(), f.root, tt.anchor, map[string]string{proofPath: tt.contents})
			if tt.problem == "" && err != nil || tt.problem != "" && (err == nil || !strings.Contains(err.Error(), tt.problem)) {
				t.Fatalf("ReadLanded = %v; want %q", err, tt.problem)
			}
			checkEvents(t, log, plan)
		})
	}
}

func TestLandRejectsUnauthorizedPreimage(t *testing.T) {
	f := newFixture(t, true)
	for _, tt := range []struct {
		name, problem string
		preimage      map[string]string
		calls         int
	}{
		{"add-existing", "without authorized preimage", nil, 1},
		{"incorrect-preimage", "unexpected contents", map[string]string{proofPath: priorText + "\n"}, 1},
		{"extra-preimage", "preimage for unauthorized path", map[string]string{"Proofs/Keep.lean": "-- untouched\n"}, 0},
	} {
		t.Run(tt.name, func(t *testing.T) {
			plan := f.plan(f.candidate)[:tt.calls]
			log := usePlan(t, plan)
			revision, err := f.land(t, log, tt.preimage, nil, 0, nil)
			if revision != "" || err == nil || !strings.Contains(err.Error(), tt.problem) {
				t.Fatalf("LandReplacing = %q, %v, want error containing %q", revision, err, tt.problem)
			}
			checkEvents(t, log, plan)
		})
	}
}

func TestLandRejectsSymlinkInPreparedWorkspace(t *testing.T) {
	f := newFixture(t, false)
	outside := t.TempDir()
	if err := os.Symlink(outside, filepath.Join(f.prepared, "Proofs", "Pilot")); err != nil {
		t.Fatal(err)
	}
	plan := f.plan(f.candidate)[:2]
	log := usePlan(t, plan)
	revision, err := f.land(t, log, nil, nil, 0, nil)
	if revision != "" || err == nil || !strings.Contains(err.Error(), "not a real directory") {
		t.Fatalf("LandReplacing = %q, %v; want symlink rejection", revision, err)
	}
	checkEvents(t, log, plan)
	files, err := os.ReadDir(outside)
	if err != nil || len(files) != 0 {
		t.Fatalf("landing changed outside directory: %v, %v", files, err)
	}
}

func TestLandRequiresWorkerAndTrustedBridge(t *testing.T) {
	t.Setenv(adapterEnv, "")
	files := map[string]string{proofPath: proofText}
	if got, err := Land(t.Context(), t.TempDir(), files, nil, message, nil); got != "" || err == nil || !strings.Contains(err.Error(), "missing exact-revision worker") {
		t.Fatalf("Land without worker = %q, %v", got, err)
	}
	check := func(context.Context, string, string, []string) error {
		t.Fatal("worker invoked without campaign")
		return nil
	}
	if got, err := Land(t.Context(), t.TempDir(), files, nil, message, check); got != "" || err == nil || !strings.Contains(err.Error(), adapterEnv) {
		t.Fatalf("Land without campaign = %q, %v", got, err)
	}
}

func TestReadLandedDoesNotResolveAcceptedIDAsBookmark(t *testing.T) {
	f := newFixture(t, false)
	missing := strings.Repeat("a", len(f.candidate))
	fixtureJJ(t, f.root, "bookmark", "create", "-r", f.candidate, missing)
	plan := f.plan(missing)[9:]
	log := usePlan(t, plan)
	err := ReadLanded(t.Context(), f.root, f.candidate, map[string]string{proofPath: proofText})
	if err == nil {
		t.Fatal("verified acceptance using a bookmark instead of the accepted commit ID")
	}
	checkEvents(t, log, plan)
}
