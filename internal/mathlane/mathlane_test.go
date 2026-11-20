package mathlane

import (
	"context"
	"encoding/json"
	"errors"
	"io/fs"
	"maps"
	"os"
	"path/filepath"
	"reflect"
	"strings"
	"testing"
)

const testPacket = `{"disposition":"verified","anchor":"fixture passage","reading":"Fixture only: two diagonal evaluations under condition C.\nend TraceAssembly","attribution":"fixture attribution","boundary":"fixture boundary"}`

func testRequest() request {
	return request{Mission: "paper mission", Obligation: "assemble fixture step", Packet: testPacket}
}

// Deliberately not the manuscript signs. The renderer checks syntax, not
// fidelity: a syntactically valid wrong equation must reach the reviewers.
const testEquations = `{"Status":"candidate","Geometric":"diagonal = mellinPlus - (orbital + mellinMinus)","Spectral":"diagonal = zeros","Conclusion":"orbital = -(mellinMinus + zeros) + mellinPlus"}`

func staticAgent(reply string, err error) agent {
	return func(context.Context, string, string, []byte) ([]byte, error) { return []byte(reply), err }
}

func translateFixture(t *testing.T) Draft {
	t.Helper()
	d, err := staticAgent(testEquations, nil).translate(t.Context(), "unused", testRequest())
	if err != nil {
		t.Fatal(err)
	}
	return d
}

func putFile(t *testing.T, root, path, contents string) {
	t.Helper()
	file := filepath.Join(root, path)
	if err := os.MkdirAll(filepath.Dir(file), 0o755); err != nil {
		t.Fatal(err)
	}
	if err := os.WriteFile(file, []byte(contents), 0o644); err != nil {
		t.Fatal(err)
	}
}

func TestTranslateThenReviewExactDraft(t *testing.T) {
	d := translateFixture(t)
	if !strings.Contains(d.Files[propsPath], `-- Reading: "Fixture only: two diagonal evaluations under condition C.\nend TraceAssembly"`) ||
		strings.Count(d.Files[propsPath], "\nend TraceAssembly") != 1 ||
		!strings.HasSuffix(d.Leaf, "orbital = -(mellinMinus + zeros) + mellinPlus") {
		t.Fatalf("translation omitted or reinterpreted source and equation data: %+v", d)
	}
	r := testRequest()
	r.Draft = &d
	root := t.TempDir()
	putFile(t, root, propsPath, d.Files[propsPath])
	var seen []string
	review := agent(func(_ context.Context, gotRoot, instruction string, data []byte) ([]byte, error) {
		var got request
		if err := json.Unmarshal(data, &got); err != nil {
			t.Fatal(err)
		}
		if gotRoot != root || !reflect.DeepEqual(got, r) {
			t.Fatalf("review received different root or request: %q %+v", gotRoot, got)
		}
		seen = append(seen, instruction)
		return []byte(`{"Accept":false,"Reason":"spectral sign differs from the cited evaluation"}`), nil
	})
	for _, landed := range []bool{false, true} {
		v, err := review.review(t.Context(), root, r, landed)
		if err != nil || v.Accept || v.Reason != "spectral sign differs from the cited evaluation" {
			t.Fatalf("review(%v) = %+v, %v", landed, v, err)
		}
	}
	if !reflect.DeepEqual(seen, []string{fidelityPrompt, challengePrompt}) || fidelityPrompt == challengePrompt {
		t.Fatalf("did not make separate fidelity and challenge requests")
	}
}

func TestTranslateFailClosed(t *testing.T) {
	for _, test := range []struct{ name, output string }{
		{"same term", strings.Replace(testEquations, "diagonal = zeros", "diagonal = diagonal", 1)},
		{"unused analytic operand", strings.Replace(testEquations, "(orbital + mellinMinus)", "orbital", 1)},
		{"trailing prose", testEquations + " -- anything"},
		{"equation injection", strings.Replace(testEquations, "diagonal = zeros", `diagonal = zeros\naxiom bad : False`, 1)},
		{"zero coefficient", strings.Replace(testEquations, "diagonal = zeros", "diagonal = 0 * zeros", 1)},
		{"reasoned reject", `{"Status":"reject","Reason":"the passage supplies only the spectral evaluation"}`},
	} {
		t.Run(test.name, func(t *testing.T) {
			d, err := staticAgent(test.output, nil).translate(t.Context(), "unused", testRequest())
			if err == nil || len(d.Files) != 0 {
				t.Fatalf("invalid output yielded files or success: %+v, %v", d, err)
			}
		})
	}
	r := testRequest()
	r.Packet = strings.Replace(r.Packet, `"verified"`, `"ambiguous"`, 1)
	mustNotCall := agent(func(context.Context, string, string, []byte) ([]byte, error) {
		t.Fatal("called agent for ambiguous source")
		return nil, nil
	})
	if _, err := mustNotCall.translate(t.Context(), "unused", r); !errors.Is(err, ErrRejected) {
		t.Fatalf("ambiguous source: %v", err)
	}
}

func TestReviewRejectsOutOfScopeAndWrongLandedFiles(t *testing.T) {
	d := translateFixture(t)
	r := testRequest()
	r.Draft = &d
	root := t.TempDir()
	mustNotCall := agent(func(context.Context, string, string, []byte) ([]byte, error) {
		t.Fatal("called reviewer after an invalid scope or snapshot check")
		return nil, nil
	})
	for _, mutate := range []func(*Draft){
		func(d *Draft) { d.Files["../escape.lean"] = "" },
		func(d *Draft) { d.Decls = append(d.Decls, "Unexpected") },
		func(d *Draft) { d.Premises = nil },
		func(d *Draft) { d.Leaf = strings.Replace(d.Leaf, "(hSpec :", "(hSpec : True) (hTarget :", 1) },
		func(d *Draft) { d.Files[propsPath] += "\naxiom unexpected : False\n" },
	} {
		invalid := d
		invalid.Files = maps.Clone(d.Files)
		mutate(&invalid)
		r.Draft = &invalid
		if v, err := mustNotCall.review(t.Context(), root, r, false); err != nil || v.Accept || v.Reason == "" {
			t.Fatalf("invalid candidate not rejected: %+v %v", v, err)
		}
	}
	r.Draft = &d
	for _, different := range []string{"missing", "modified", "symlink"} {
		file := filepath.Join(root, propsPath)
		switch different {
		case "modified":
			putFile(t, root, propsPath, d.Files[propsPath]+"\n")
		case "symlink":
			if err := os.Remove(file); err != nil {
				t.Fatal(err)
			}
			putFile(t, root, "copy.lean", d.Files[propsPath])
			if err := os.Symlink(filepath.Join(root, "copy.lean"), file); err != nil {
				t.Fatal(err)
			}
		}
		if v, err := mustNotCall.review(t.Context(), root, r, true); err != nil || v.Accept || v.Reason == "" {
			t.Fatalf("landed %s candidate not rejected: %+v %v", different, v, err)
		}
	}
}

func TestProvePreservesFrozenInterface(t *testing.T) {
	d := translateFixture(t)
	r := testRequest()
	r.Draft = &d
	const combination = `-(hSpec - hGeom)`
	prover := agent(func(_ context.Context, _, prompt string, data []byte) ([]byte, error) {
		var got request
		if err := json.Unmarshal(data, &got); err != nil {
			t.Fatal(err)
		}
		if prompt != proofPrompt || !reflect.DeepEqual(got, r) {
			t.Fatal("proof request was not the frozen interface")
		}
		return []byte(`{"Status":"candidate","Combination":"` + combination + `"}`), nil
	})
	out, err := prover.prove(t.Context(), "unused", r)
	if err != nil {
		t.Fatal(err)
	}
	packet, err := r.source(t.Context())
	if err != nil {
		t.Fatal(err)
	}
	if err := validateDraft(packet, out); err != nil {
		t.Fatal(err)
	}
	if out.Leaf != "" || !reflect.DeepEqual(out.Premises, d.Premises) || !strings.Contains(out.Files[theoremPath], d.Leaf+" := by\n") ||
		!strings.Contains(out.Files[theoremPath], "linear_combination "+combination+"\n") || out.Files[propsPath] != d.Files[propsPath] || len(d.Files) != 1 {
		t.Fatalf("assembly candidate changed former files or premises, moved the goal, or failed to include proof: %+v", out)
	}
	// An assembled candidate still has two
	// outstanding analytic inputs. Do not
	// call the prover again or interpret
	// an empty Leaf as full closure.
	r.Draft = &out
	if _, err := prover.prove(t.Context(), "unused", r); !errors.Is(err, ErrProofNotReady) || !strings.Contains(err.Error(), "hGeom") || !strings.Contains(err.Error(), "hSpec") {
		t.Fatalf("assembled candidate result: %v", err)
	}
}

func TestDistinguishNotReadyUnsupportedAndTransport(t *testing.T) {
	d := translateFixture(t)
	r := testRequest()
	r.Draft = &d
	for _, test := range []struct {
		name, output string
		transport    error
		want         error
	}{
		{"blocked", `{"Status":"blocked","Reason":"the sourced signs do not eliminate the diagonal"}`, nil, ErrProofNotReady},
		{"injection", `{"Status":"candidate","Combination":"hSpec - hGeom\n  exact evil"}`, nil, ErrRejected},
		{"comment", `{"Status":"candidate","Combination":"hSpec--hGeom"}`, nil, ErrRejected},
		{"malformed", `{"Status":"candidate","Combination":"hSpec - hGeom"} {}`, nil, nil},
		{"duplicate", `{"Status":"blocked","status":"candidate","Combination":"hSpec - hGeom"}`, nil, nil},
		{"new header", `{"Status":"candidate","Combination":"hSpec - hGeom","Leaf":"True"}`, nil, nil},
		{"transport", "", fs.ErrPermission, fs.ErrPermission},
	} {
		t.Run(test.name, func(t *testing.T) {
			out, err := staticAgent(test.output, test.transport).prove(t.Context(), "unused", r)
			if err == nil || len(out.Files) != 0 || test.want != nil && !errors.Is(err, test.want) ||
				test.want == nil && (errors.Is(err, ErrRejected) || errors.Is(err, ErrProofNotReady)) {
				t.Fatalf("got candidate files %v and error %v, want error class %v", len(out.Files), err, test.want)
			}
		})
	}
	cause := errors.New("stop run")
	ctx, cancel := context.WithCancelCause(t.Context())
	cancelAgent := agent(func(context.Context, string, string, []byte) ([]byte, error) {
		cancel(cause)
		return []byte(`{"Status":"candidate","Combination":"hSpec - hGeom"}`), nil
	})
	if _, err := cancelAgent.prove(ctx, "unused", r); !errors.Is(err, cause) {
		t.Fatalf("in-flight cancellation: %v", err)
	}
}
