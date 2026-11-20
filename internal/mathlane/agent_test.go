package mathlane

import (
	"context"
	"encoding/json"
	"errors"
	"fmt"
	"io"
	"net"
	"os"
	"os/exec"
	"path/filepath"
	"reflect"
	"slices"
	"strings"
	"testing"
	"time"
)

const fixtureDiagnostic = "private fixture diagnostic"

type yahInvocation struct {
	Args      []string
	Dir, Temp string
	Target    string
	EmptyDir  bool
	Input     string
}

func TestMain(m *testing.M) {
	if filepath.Base(os.Args[0]) != "yah" {
		os.Exit(m.Run())
	}
	if err := yahFixture(); err != nil {
		fmt.Fprintln(os.Stderr, err)
		os.Exit(99)
	}
	if os.Getenv("GRH_FIXTURE_FAIL") == "1" {
		os.Exit(42)
	}
	os.Exit(0)
}

func yahFixture() error {
	input, err := io.ReadAll(os.Stdin)
	if err != nil {
		return err
	}
	dir, err := os.Getwd()
	if err != nil {
		return err
	}
	entries, err := os.ReadDir(dir)
	if err != nil {
		return err
	}
	// Simulate -tmp allocating a repository under the child's
	// temp root.
	if _, err := os.MkdirTemp("", "fixture-repo-"); err != nil {
		return err
	}
	call, err := json.Marshal(yahInvocation{
		Args: os.Args[1:], Dir: dir, Temp: os.TempDir(), Target: os.Getenv("YAH_CAMPAIGN_TARGET"),
		EmptyDir: len(entries) == 0, Input: string(input),
	})
	if err != nil {
		return err
	}
	if err := os.WriteFile(os.Getenv("GRH_FIXTURE_CALL"), call, 0o600); err != nil {
		return err
	}
	if addr := os.Getenv("GRH_FIXTURE_READY"); addr != "" {
		conn, err := net.DialTimeout("tcp", addr, 5*time.Second)
		if err != nil {
			return err
		}
		defer conn.Close()
		// Announce readiness by connecting,
		// then block until killed or the test
		// closes the peer during cleanup.
		_, err = io.Copy(io.Discard, conn)
		return err
	}
	fmt.Fprintln(os.Stderr, fixtureDiagnostic)
	_, err = io.WriteString(os.Stdout, os.Getenv("GRH_FIXTURE_ANSWER"))
	return err
}

func installYahFixture(t *testing.T) {
	t.Helper()
	bin := t.TempDir()
	exe, err := os.Executable()
	if err != nil {
		t.Fatal(err)
	}
	if err := os.Symlink(exe, filepath.Join(bin, "yah")); err != nil {
		t.Fatal(err)
	}
	// Do not inherit any PATH entries: a
	// missing fixture must fail lookup.
	t.Setenv("PATH", bin)
	t.Setenv("GRH_FIXTURE_READY", "")
	t.Setenv("GRH_FIXTURE_FAIL", "")
	t.Setenv("YAH_CAMPAIGN_TARGET", "caller-project-target")
	// Keep even unexpected fixture temporary
	// files under test cleanup.
	t.Setenv("TMPDIR", t.TempDir())
}

func checkYahInvocation(t *testing.T, path string) yahInvocation {
	t.Helper()
	data, err := os.ReadFile(path)
	if err != nil {
		t.Fatal(err)
	}
	var got yahInvocation
	if err := json.Unmarshal(data, &got); err != nil {
		t.Fatal(err)
	}
	if !got.EmptyDir || got.Temp != got.Dir {
		t.Fatalf("expected an empty launcher directory owning the child's temp root: %q, %q, empty=%v", got.Dir, got.Temp, got.EmptyDir)
	}
	if got.Target != "" {
		t.Fatalf("scratch session inherited adoption target %q", got.Target)
	}
	if _, err := os.Stat(got.Dir); !errors.Is(err, os.ErrNotExist) {
		t.Fatalf("launcher directory %q was not removed: %v", got.Dir, err)
	}
	return got
}

func TestYahTransport(t *testing.T) {
	root := filepath.Join("..", "..")
	cache := os.Getenv("GRH_MATHLIB")
	if cache == "" {
		cache = filepath.Join(root, ".lake", "packages", "mathlib")
	}
	wantSources := map[string]string{}
	for _, name := range []string{"Mathlib.Basic.Complex.Basic", "Mathlib.Tactic.LinearCombination"} {
		path := filepath.Join(cache, strings.ReplaceAll(name, ".", "/")+".lean")
		data, err := os.ReadFile(path)
		if errors.Is(err, os.ErrNotExist) && os.Getenv("GRH_MATHLIB") == "" {
			t.Skipf("production launch test needs the pinned Mathlib checkout: %v", err)
		}
		if err != nil {
			t.Fatal(err)
		}
		wantSources[name] = string(data)
	}
	seenDirs := make(map[string]bool)
	checkRequest := func(t *testing.T, got yahInvocation, want request, role string) {
		t.Helper()
		if seenDirs[got.Dir] {
			t.Fatalf("reused launcher directory %q", got.Dir)
		}
		seenDirs[got.Dir] = true
		if len(got.Args) != 5 || !slices.Equal(got.Args[:4], []string{"-tmp", "-effort", "high", "-append"}) ||
			!strings.Contains(got.Args[4], role) || !strings.Contains(got.Args[4], "Reason only from the supplied evidence") ||
			!strings.Contains(got.Args[4], "Return one JSON object only") {
			t.Fatalf("unexpected Yah arguments: %q", got.Args)
		}
		var in struct {
			MathlibRev     string
			MathlibSources []struct{ Module, Source string }
			Request        request
		}
		if err := json.Unmarshal([]byte(got.Input), &in); err != nil {
			t.Fatalf("invalid stdin JSON: %v", err)
		}
		if in.MathlibRev != mathlibRev || !reflect.DeepEqual(in.Request, want) || len(in.MathlibSources) != len(wantSources) {
			t.Fatalf("stdin did not contain the expected request and pins: rev=%q request=%+v modules=%d", in.MathlibRev, in.Request, len(in.MathlibSources))
		}
		seenModules := make(map[string]bool)
		for _, mod := range in.MathlibSources {
			if want, ok := wantSources[mod.Module]; !ok || mod.Source != want || seenModules[mod.Module] {
				t.Fatalf("unexpected pinned source for %q", mod.Module)
			}
			seenModules[mod.Module] = true
		}
	}
	installYahFixture(t)
	r := testRequest()
	r.Critique = "fixture critique with ℂ\nand a newline"
	translate := func(ctx context.Context) (Draft, error) {
		return Translate(ctx, root, r.Mission, r.Obligation, r.Packet, r.Critique)
	}
	for _, tt := range []struct {
		name, answer, errorText string
		fail, rejected          bool
	}{
		{name: "valid", answer: testEquations},
		{name: "invalid JSON", answer: testEquations + "\n{}", errorText: "invalid mathlane agent reply"},
		{name: "invalid equation", answer: strings.Replace(testEquations, "diagonal = zeros", "diagonal = diagonal", 1), rejected: true},
		{name: "oversize", answer: testEquations + strings.Repeat(" ", maxReplyBytes-len(testEquations)+1), errorText: "response too large"},
		{name: "nonzero exit", answer: testEquations, fail: true},
	} {
		t.Run(tt.name, func(t *testing.T) {
			path := filepath.Join(t.TempDir(), "call.json")
			t.Setenv("GRH_FIXTURE_CALL", path)
			t.Setenv("GRH_FIXTURE_ANSWER", tt.answer)
			if tt.fail {
				t.Setenv("GRH_FIXTURE_FAIL", "1")
			}
			ctx, cancel := context.WithTimeout(t.Context(), 10*time.Second)
			defer cancel()
			d, err := translate(ctx)
			got := checkYahInvocation(t, path)
			if tt.fail || tt.rejected || tt.errorText != "" {
				var exit *exec.ExitError
				if err == nil || len(d.Files) != 0 || errors.Is(err, ErrRejected) != tt.rejected ||
					tt.fail && (!errors.As(err, &exit) || exit.ExitCode() != 42) ||
					!strings.Contains(err.Error(), tt.errorText) || strings.Contains(err.Error(), fixtureDiagnostic) {
					t.Fatalf("got draft %+v, error %v", d, err)
				}
				return
			}
			if err != nil || !reflect.DeepEqual(d, translateFixture(t)) {
				t.Fatalf("got draft %+v, error %v", d, err)
			}
			checkRequest(t, got, r, "TRANSLATE")
		})
	}
	t.Run("reviews and proof", func(t *testing.T) {
		snapshot := t.TempDir()
		d := translateFixture(t)
		for name, data := range d.Files {
			putFile(t, snapshot, name, data)
		}
		for _, name := range []string{"lean-toolchain", "lake-manifest.json"} {
			data, err := os.ReadFile(filepath.Join(root, name))
			if err != nil {
				t.Fatal(err)
			}
			putFile(t, snapshot, name, string(data))
		}
		absCache, err := filepath.Abs(cache)
		if err != nil {
			t.Fatal(err)
		}
		t.Setenv("GRH_MATHLIB", absCache)
		want := testRequest()
		want.Draft = &d
		for _, review := range []struct {
			role string
			call func(context.Context, string, string, string, string, Draft) (Verdict, error)
		}{{"FIDELITY:", Fidelity}, {"CHALLENGE:", Challenge}} {
			t.Run(review.role, func(t *testing.T) {
				path := filepath.Join(t.TempDir(), "call.json")
				t.Setenv("GRH_FIXTURE_CALL", path)
				t.Setenv("GRH_FIXTURE_ANSWER", `{"Accept":true,"Reason":"fixture review"}`)
				ctx, cancel := context.WithTimeout(t.Context(), 10*time.Second)
				defer cancel()
				v, err := review.call(ctx, snapshot, want.Mission, want.Obligation, want.Packet, d)
				if err != nil || v != (Verdict{Accept: true, Reason: "fixture review"}) {
					t.Fatalf("got verdict %+v, error %v", v, err)
				}
				checkRequest(t, checkYahInvocation(t, path), want, review.role)
			})
		}
		path := filepath.Join(t.TempDir(), "call.json")
		t.Setenv("GRH_FIXTURE_CALL", path)
		t.Setenv("GRH_FIXTURE_ANSWER", `{"Status":"candidate","Combination":"hGeom - hSpec"}`)
		ctx, cancel := context.WithTimeout(t.Context(), 10*time.Second)
		defer cancel()
		out, err := Prove(ctx, snapshot, want.Mission, want.Obligation, want.Packet, d)
		if err != nil || out.Files[propsPath] != d.Files[propsPath] || !strings.Contains(out.Files[theoremPath], d.Leaf+" := by\n") {
			t.Fatalf("got proof draft %+v, error %v", out, err)
		}
		checkRequest(t, checkYahInvocation(t, path), want, "PROVE exactly")
	})
	t.Run("cancel", func(t *testing.T) {
		path := filepath.Join(t.TempDir(), "call.json")
		t.Setenv("GRH_FIXTURE_CALL", path)
		cause := errors.New("cancel mathlane request")
		ctx, cancel := context.WithCancelCause(t.Context())
		cancel(cause)
		if _, err := translate(ctx); !errors.Is(err, cause) {
			t.Fatalf("pre-canceled request: %v", err)
		}
		if _, err := os.Stat(path); !errors.Is(err, os.ErrNotExist) {
			t.Fatalf("pre-canceled request reached fixture: %v", err)
		}

		listener, err := net.ListenTCP("tcp4", &net.TCPAddr{IP: net.IPv4(127, 0, 0, 1)})
		if err != nil {
			t.Fatal(err)
		}
		defer listener.Close()
		t.Setenv("GRH_FIXTURE_READY", listener.Addr().String())
		bounded, stop := context.WithTimeout(t.Context(), 10*time.Second)
		defer stop()
		ctx, cancel = context.WithCancelCause(bounded)
		defer cancel(nil)
		deadline, _ := bounded.Deadline()
		if err := listener.SetDeadline(deadline); err != nil {
			t.Fatal(err)
		}
		done := make(chan error, 1)
		go func() {
			conn, err := listener.AcceptTCP()
			if err != nil {
				done <- err
				return
			}
			cancel(cause)
			// EOF while our end stays open
			// confirms the fixture stopped.
			err = conn.SetReadDeadline(deadline)
			if err == nil {
				_, err = io.Copy(io.Discard, conn)
			}
			done <- errors.Join(err, conn.Close())
		}()
		d, err := translate(ctx)
		listener.Close()
		if fixtureErr := <-done; fixtureErr != nil {
			t.Fatalf("fixture did not signal readiness and then stop: %v", fixtureErr)
		}
		if !errors.Is(err, cause) || len(d.Files) != 0 {
			t.Fatalf("canceled request got draft %+v, error %v", d, err)
		}
		checkYahInvocation(t, path)
	})
}

func TestMathlibPinAndSourceMismatch(t *testing.T) {
	root := t.TempDir()
	putFile(t, root, "lean-toolchain", leanToolchain+"\n")
	writeManifest := func(rev string) {
		putFile(t, root, "lake-manifest.json", fmt.Sprintf(`{"packages":[{"name":"mathlib","url":%q,"rev":%q}]}`, mathlibURL, rev))
	}
	writeManifest("not-the-pin")
	if _, err := pinnedSources(t.Context(), root, ""); err == nil || !strings.Contains(err.Error(), "unsupported Mathlib pin") {
		t.Fatalf("wrong manifest revision: %v", err)
	}
	writeManifest(mathlibRev)
	putFile(t, root, ".lake/packages/mathlib/Mathlib/Basic/Complex/Basic.lean", "edited source")
	if _, err := pinnedSources(t.Context(), root, ""); err == nil || !strings.Contains(err.Error(), "does not match Mathlib") {
		t.Fatalf("source with correct manifest but wrong content: %v", err)
	}
	if _, err := pinnedSources(t.Context(), root, filepath.Join("relative", "mathlib")); err == nil || !strings.Contains(err.Error(), "absolute path") {
		t.Fatalf("relative checkout override: %v", err)
	}
}
