package main

import (
	"context"
	"encoding/json/v2"
	"errors"
	"os"
	"path/filepath"
	"slices"
	"strings"
	"testing"

	"patel.codes/godel"
)

const revision = "0123456789abcdef0123456789abcdef01234567"

var (
	choice    = selection{Action: "investigate", Reason: "test a useful bound", Brief: "a uniform bound under hypothesis H"}
	joined    = scouting{OpenAlex: "Nearby theorem with stronger assumptions", Search: "Claim does not imply the unconditional case", Think: "Test equality at the boundary", Joined: "Boundary test distinguishes the implication"}
	candidate = draft{Action: "draft", Slug: "uniform-bound", Title: "A uniform bound", Claim: "For all $x > 0$, suppose $H(x)$. Then $F(x) \u2264 1$.", Ingredient: "A new estimate at the endpoint.", Payoff: "Would handle the boundary under $H$.", Test: "Evaluate $F(x)$ for one allowed family."}
	openCard  = verdict{Action: "open", Critique: "Endpoint estimate is unproved but testable", Body: "# A uniform bound\n\n" + candidate.Claim + "\n\nThe paper estimate gives a weaker bound. No Lean or numeric verification of the claim."}
)

func step(t *testing.T, n *godel.Node, stage role, response any) *godel.Node {
	t.Helper()
	handoff(t, n, stage)
	data, err := json.Marshal(response)
	if err != nil {
		t.Fatal(err)
	}
	next, err := n.Next(godel.Result{Text: string(data)})
	if err != nil {
		t.Fatalf("%s: %v", stage.name, err)
	}
	return next
}

func handoff(t *testing.T, n *godel.Node, stage role) packet {
	t.Helper()
	if n == nil || n.Next == nil || n.Exec != "sh" || len(n.Args) < 7 || !strings.HasPrefix(filepath.Base(n.Args[2]), stage.name+"-") {
		t.Fatalf("expected %s research node, got %+v", stage.name, n)
	}
	if n.Args[5] != "-append" || !strings.Contains(n.Args[6], exclusion) {
		t.Fatalf("%s missing appended source exclusion", stage.name)
	}
	if (stage != publisher && n.Directory != filepath.Dir(n.Args[2])) || !slices.Contains(n.Env, "YAH_DEFAULT_TOOLS="+stage.tools) {
		t.Fatalf("%s not confined to the expected scratch directory/tool list: %+v", stage.name, n)
	}
	data, err := os.ReadFile(n.Args[2])
	if err != nil {
		t.Fatal(err)
	}
	var p packet
	if err := json.Unmarshal(data, &p); err != nil {
		t.Fatal(err)
	}
	if p.Revision != revision || (stage != publisher && p.Index != filepath.Join(p.Snapshot, "index.txt")) {
		t.Fatalf("incorrect evidence pin or index: %+v", p)
	}
	return p
}

func terminal(t *testing.T, n *godel.Node, action string) {
	t.Helper()
	if n == nil || n.Next != nil || n.Exec != "printf" || len(n.Args) != 2 {
		t.Fatalf("expected terminal node, got %+v", n)
	}
	var result struct{ Action, Path, Reason string }
	if err := json.Unmarshal([]byte(n.Args[1]), &result, json.MatchCaseInsensitiveNames(true)); err != nil || result.Action != action || blank(result.Reason) {
		t.Fatalf("terminal %s: %s (%v)", action, n.Args[1], err)
	}
	if (result.Path != "") != (action == "open" || action == "closed") {
		t.Fatalf("unexpected terminal path: %s", n.Args[1])
	}
}

func start(t *testing.T, r investigation) *godel.Node {
	t.Helper()
	n, err := r.start(revision, filepath.Join(r.scratch, "snapshot"))
	if err != nil {
		t.Fatal(err)
	}
	return n
}

func TestNoChange(t *testing.T) {
	t.Parallel()
	r := investigation{ctx: t.Context(), scratch: t.TempDir()}
	n := step(t, start(t, r), selector, selection{Action: "stop", Reason: "no worthwhile claim"})
	terminal(t, n, "no_change")
	n = step(t, start(t, r), selector, choice)
	n = step(t, n, scouts, scouting{Failure: "search child timed out"})
	terminal(t, n, "no_change")
	n = step(t, start(t, r), selector, choice)
	n = step(t, n, scouts, joined)
	n = step(t, n, constructor, draft{Action: "stop", Reason: "derivative of an accepted claim"})
	terminal(t, n, "no_change")
	n = step(t, start(t, r), selector, choice)
	n = step(t, n, scouts, joined)
	n = step(t, n, constructor, candidate)
	n = step(t, n, challenger, verdict{Action: "no_change", Critique: "Equivalent to an already tested claim"})
	terminal(t, n, "no_change")
}

func TestScoutHandoff(t *testing.T) {
	t.Parallel()
	r := investigation{ctx: t.Context(), scratch: t.TempDir()}
	n := step(t, start(t, r), selector, choice)
	p := handoff(t, n, scouts)
	if p.Choice == nil || *p.Choice != choice || p.Scouts != nil {
		t.Fatalf("initial scout handoff: %+v", p)
	}
	if _, err := n.Next(godel.Result{Text: `{"openalex":"one", "search":"two", "joined":"premature"}`}); err == nil {
		t.Fatal("advanced without the think scout")
	}
	n = step(t, n, scouts, joined)
	p = handoff(t, n, constructor)
	if p.Scouts == nil || p.Scouts.OpenAlex != joined.OpenAlex || p.Scouts.Search != joined.Search || p.Scouts.Think != joined.Think || p.Scouts.Joined != joined.Joined {
		t.Fatalf("missing joined evidence: %+v", p)
	}
}

func TestCancelAtScoutHandoff(t *testing.T) {
	t.Parallel()
	ctx, cancel := context.WithCancel(t.Context())
	defer cancel()
	r := investigation{ctx: ctx, scratch: t.TempDir()}
	n := step(t, start(t, r), selector, choice)
	data, err := json.Marshal(joined)
	if err != nil {
		t.Fatal(err)
	}
	cancel()
	if next, err := n.Next(godel.Result{Text: string(data)}); next != nil || !errors.Is(err, context.Canceled) {
		t.Fatalf("canceled join advanced: %+v, %v", next, err)
	}
}

func TestReviseAndRechallenge(t *testing.T) {
	t.Parallel()
	r := investigation{ctx: t.Context(), scratch: t.TempDir()}
	n := step(t, start(t, r), selector, choice)
	n = step(t, n, scouts, joined)
	n = step(t, n, constructor, candidate)
	critique := verdict{Action: "revise", Critique: "Test the endpoint as a limit, not at the excluded point"}
	n = step(t, n, challenger, critique)
	p := handoff(t, n, reviser)
	if p.Previous == nil || *p.Previous != candidate || p.Draft == nil || p.Draft.Claim != candidate.Claim || p.Review == nil || p.Review.Critique != critique.Critique {
		t.Fatalf("revision lost original claim or challenge: %+v", p)
	}
	bad := candidate
	bad.Slug = "another-claim"
	data, err := json.Marshal(bad)
	if err != nil {
		t.Fatal(err)
	}
	if _, err := n.Next(godel.Result{Text: string(data)}); err == nil {
		t.Fatal("accepted revision that changed the slug")
	}
	fixed := candidate
	fixed.Claim = "If $x > 0$ and $H(x)$, then $F(x) \u2264 1$."
	fixed.Test = "Let $x$ approach zero through allowed inputs."
	n = step(t, n, reviser, fixed)
	p = handoff(t, n, challenger)
	if p.Previous == nil || *p.Previous != candidate || p.Draft == nil || *p.Draft != fixed {
		t.Fatalf("unchallenged revised draft: %+v", p)
	}
	n = step(t, n, challenger, critique)
	terminal(t, n, "no_change")
}

func TestPrimaryGateAndPublication(t *testing.T) {
	t.Parallel()
	r := investigation{ctx: t.Context(), scratch: t.TempDir(), root: t.TempDir(), target: "main"}
	lead := "arXiv:1234.56789v2, Theorem 2"
	s := joined
	s.Leads = []string{lead}
	v := openCard
	v.Decisive = []string{lead}
	for _, status := range []string{"unavailable", "not_applicable", "verified"} {
		n := step(t, start(t, r), selector, choice)
		n = step(t, n, scouts, s)
		p := handoff(t, n, verifier)
		if p.Scouts == nil || len(p.Scouts.Leads) != 1 || p.Scouts.Leads[0] != lead {
			t.Fatalf("missing leads: %+v", p)
		}
		check := primaryCheck{Lead: lead, Status: status, Locator: lead, Statement: "Bound under H", Comparison: "Comparison of assumptions"}
		n = step(t, n, verifier, []primaryCheck{check})
		p = handoff(t, n, constructor)
		if len(p.Primary) != 1 || p.Primary[0] != check {
			t.Fatalf("lost source assessment: %+v", p.Primary)
		}
		n = step(t, n, constructor, candidate)
		if status != "verified" {
			data, err := json.Marshal(v)
			if err != nil {
				t.Fatal(err)
			}
			if _, err := n.Next(godel.Result{Text: string(data)}); err == nil {
				t.Fatalf("accepted decisive %s citation", status)
			}
			continue
		}
		n = step(t, n, challenger, v)
		p = handoff(t, n, publisher)
		if n.Directory != r.root || !slices.Contains(n.Env, "YAH_CAMPAIGN_TARGET="+r.target) || p.Choice != nil || p.Card == nil || p.Card.Path != ".godel/conjectures/open/uniform-bound.md" || !strings.HasPrefix(p.Card.Markdown, "---\nevidence_revision: "+revision+"\n---\n\n") {
			t.Fatalf("wrong publication handoff: %+v", p)
		}
		terminal(t, step(t, n, publisher, map[string]string{"status": "not_adopted", "reason": "another writer updated this slug"}), "not_adopted")
		const adopted = "9876543210abcdef0123456789abcdef01234567"
		done := step(t, n, publisher, map[string]string{"status": "adopted", "adopted_revision": adopted, "reason": "campaign accepted candidate"})
		terminal(t, done, "open")
		if !strings.Contains(done.Args[1], adopted) {
			t.Fatal("terminal output lost adoption receipt")
		}
	}
}

func TestNoArguments(t *testing.T) {
	t.Parallel()
	if err := run(t.Context(), []string{"--help"}); err == nil || !strings.Contains(err.Error(), "takes no arguments") {
		t.Fatalf("unexpected argument handling: %v", err)
	}
}
