package main

import (
	"context"
	"encoding/json/v2"
	"errors"
	"fmt"
	"os"
	"path/filepath"
	"strings"

	"patel.codes/godel"
)

type selection struct {
	Action   string `json:"action"`
	Reason   string `json:"reason"`
	Brief    string `json:"brief,omitempty"`
	Existing string `json:"existing_slug,omitempty"`
	Related  string `json:"related_slug,omitempty"`
}

type scouting struct {
	OpenAlex string   `json:"openalex"`
	Search   string   `json:"search"`
	Think    string   `json:"think"`
	Joined   string   `json:"joined"`
	Failure  string   `json:"failure,omitempty"`
	Leads    []string `json:"leads,omitempty"`
}

type primaryCheck struct {
	Lead       string `json:"lead"`
	Status     string `json:"status"`
	Locator    string `json:"locator"`
	Statement  string `json:"statement"`
	Comparison string `json:"comparison"`
}

type draft struct {
	Action     string `json:"action"`
	Reason     string `json:"reason,omitempty"`
	Slug       string `json:"slug,omitempty"`
	Title      string `json:"title,omitempty"`
	Claim      string `json:"claim,omitempty"`
	Ingredient string `json:"ingredient,omitempty"`
	Payoff     string `json:"payoff,omitempty"`
	Test       string `json:"test,omitempty"`
}

type verdict struct {
	Action   string   `json:"action"`
	Critique string   `json:"critique"`
	Body     string   `json:"body,omitempty"`
	Decisive []string `json:"decisive,omitempty"`
	Outcome  string   `json:"outcome,omitempty"`
}

// All handoffs are in memory and fresh
// private files for this run. Gödel
// otherwise sends the original launch
// stdin (possibly history) to every node.
type packet struct {
	Revision string         `json:"evidence_revision"`
	Index    string         `json:"evidence_index,omitempty"`
	Snapshot string         `json:"evidence_directory,omitempty"`
	Choice   *selection     `json:"selection,omitempty"`
	Scouts   *scouting      `json:"scouting,omitempty"`
	Primary  []primaryCheck `json:"primary_checks,omitempty"`
	Draft    *draft         `json:"draft,omitempty"`
	Previous *draft         `json:"original_draft,omitempty"`
	Review   *verdict       `json:"review_to_address,omitempty"`
	Card     *publication   `json:"publication,omitempty"`
}

type investigation struct {
	ctx                   context.Context
	scratch, root, target string
	cards                 map[string]string
}

const (
	luna    = "gpt-5.6-luna"
	maxCard = 64 << 10
)

type role struct {
	name, tools, prompt string
	privileged          bool
}

var (
	selector    = role{"select", "read", selectPrompt, false}
	scouts      = role{"scouts", "read:subagent:openalex:search:think", scoutPrompt, true}
	verifier    = role{"primary-sources", "read:arxiv:fetch", primaryPrompt, true}
	constructor = role{"construct", "read:think", constructPrompt, false}
	reviser     = role{"revise", "read:think", revisePrompt + "\n\n" + constructPrompt, false}
	challenger  = role{"challenge", "read:think", challengePrompt, false}
	publisher   = role{"publish", "read:write:bash:campaign", publishPrompt, true}
)

func (r investigation) node(stage role, p packet, next func(godel.Result) (*godel.Node, error)) (*godel.Node, error) {
	if err := r.ctx.Err(); err != nil {
		return nil, err
	}
	data, err := json.Marshal(p)
	if err != nil {
		return nil, err
	}
	f, err := os.CreateTemp(r.scratch, stage.name+"-*.json")
	if err != nil {
		return nil, err
	}
	_, err = f.Write(data)
	if err := errors.Join(err, f.Close()); err != nil {
		return nil, err
	}
	// Shell code is fixed. Both the prompt and the input
	// filename are argv, not shell syntax; Yah sees only
	// this stage's fresh packet on stdin.
	dir, prompt := r.scratch, commonPrompt+"\n\n"+stage.prompt
	env := []string{"YAH_DEFAULT_MODEL=" + luna, "YAH_DEFAULT_TOOLS=" + stage.tools, "YAH_INBOX=off"}
	promptFlag := "-replace"
	if stage == publisher {
		dir, prompt, promptFlag = r.root, stage.prompt, "-append"
		env = append(env, "YAH_CAMPAIGN_TARGET="+r.target)
	}
	args := []string{"-c", `exec timeout --kill-after=5s 12m yah "$@" < "$0"`, f.Name(), "-effort", "medium", promptFlag, prompt}
	if stage.privileged {
		// Yah classifies network retrieval as
		// rwx. The explicit tool filter still
		// excludes shell and file writes unless
		// this is publication.
		args = append(args, "-yolo")
	}
	return &godel.Node{
		Exec: "sh", Args: args, Directory: dir, Env: env,
		Next: func(result godel.Result) (*godel.Node, error) {
			if err := r.ctx.Err(); err != nil {
				return nil, err
			}
			if len(result.Text) > 64<<10 {
				return nil, fmt.Errorf("%s: response exceeds 64 KiB", stage.name)
			}
			n, err := next(result)
			if err != nil {
				return nil, fmt.Errorf("%s: %w", stage.name, err)
			}
			return n, nil
		},
	}, nil
}

func parse[T any](result godel.Result) (T, error) {
	var v T
	err := json.Unmarshal([]byte(result.Text), &v, json.RejectUnknownMembers(true))
	return v, err
}

func (r investigation) start(revision, evidence string) (*godel.Node, error) {
	p := packet{Revision: revision, Index: filepath.Join(evidence, "index.txt"), Snapshot: evidence}
	return r.node(selector, p, func(result godel.Result) (*godel.Node, error) {
		s, err := parse[selection](result)
		if err != nil {
			return nil, err
		}
		if blank(s.Reason) || (s.Existing != "" && s.Related != "") {
			return nil, errors.New("selection needs a reason and at most one existing or related slug")
		}
		switch s.Action {
		case "stop":
			if s.Brief != "" || s.Existing != "" || s.Related != "" {
				return nil, errors.New("stop cannot select a claim")
			}
			return finish(p, "no_change", "", "", s.Reason), nil
		case "investigate":
			if blank(s.Brief) {
				return nil, errors.New("missing investigation brief")
			}
			for _, slug := range []string{s.Existing, s.Related} {
				if slug != "" && r.cards[slug] == "" {
					return nil, fmt.Errorf("unknown accepted slug %q", slug)
				}
			}
			p.Choice = &s
			return r.scout(p)
		default:
			return nil, fmt.Errorf("invalid selection action %q", s.Action)
		}
	})
}

func (r investigation) scout(p packet) (*godel.Node, error) {
	return r.node(scouts, p, func(result godel.Result) (*godel.Node, error) {
		s, err := parse[scouting](result)
		if err != nil {
			return nil, err
		}
		if !blank(s.Failure) {
			return finish(p, "no_change", "", "", "scout failure: "+s.Failure), nil
		}
		if blank(s.OpenAlex) || blank(s.Search) || blank(s.Think) || blank(s.Joined) {
			return nil, errors.New("need all three attributed scout results and their synthesis")
		}
		if len(s.Leads) > 4 {
			return nil, errors.New("too many decisive source leads for one run")
		}
		seen := map[string]bool{}
		for _, lead := range s.Leads {
			if seen[lead] || blank(lead) {
				return nil, errors.New("duplicate or missing source lead")
			}
			seen[lead] = true
		}
		p.Scouts = &s
		if len(s.Leads) == 0 {
			return r.construct(p)
		}
		return r.verify(p)
	})
}

func (r investigation) verify(p packet) (*godel.Node, error) {
	return r.node(verifier, p, func(result godel.Result) (*godel.Node, error) {
		checks, err := parse[[]primaryCheck](result)
		if err != nil {
			return nil, err
		}
		if len(checks) != len(p.Scouts.Leads) {
			return nil, errors.New("need one primary-source assessment for each lead")
		}
		for i, c := range checks {
			if c.Lead != p.Scouts.Leads[i] || blank(c.Comparison) {
				return nil, errors.New("missing source assessment or comparison")
			}
			switch c.Status {
			case "verified", "not_applicable":
				if blank(c.Locator) || blank(c.Statement) {
					return nil, errors.New("need actual primary version, locator and statement")
				}
			case "unavailable":
			default:
				return nil, fmt.Errorf("invalid primary-source status %q", c.Status)
			}
		}
		p.Primary = checks
		return r.construct(p)
	})
}

func (r investigation) construct(p packet) (*godel.Node, error) {
	stage := constructor
	if p.Previous != nil {
		stage = reviser
	}
	return r.node(stage, p, func(result godel.Result) (*godel.Node, error) {
		d, err := parse[draft](result)
		if err != nil {
			return nil, err
		}
		if d.Action == "stop" && !blank(d.Reason) {
			return finish(p, "no_change", "", "", d.Reason), nil
		}
		if d.Action != "draft" || !validSlug(d.Slug) || blank(d.Title) || blank(d.Claim) ||
			blank(d.Ingredient) || blank(d.Payoff) || blank(d.Test) {
			return nil, errors.New("expected a well-formed draft with a stable slug, exact claim, new ingredient, payoff and test")
		}
		if p.Previous != nil && p.Previous.Slug != d.Slug {
			return nil, errors.New("revision changed the challenged slug")
		}
		if old := r.cards[d.Slug]; p.Choice.Existing != "" {
			if p.Choice.Existing != d.Slug || old == "" {
				return nil, errors.New("an existing card requires its same slug")
			}
		} else if old != "" {
			return nil, errors.New("new claim would reuse an accepted slug")
		}
		p.Draft = &d
		return r.challenge(p)
	})
}

func (r investigation) challenge(p packet) (*godel.Node, error) {
	return r.node(challenger, p, func(result godel.Result) (*godel.Node, error) {
		v, err := parse[verdict](result)
		if err != nil {
			return nil, err
		}
		if blank(v.Critique) {
			return nil, errors.New("missing challenge to the exact claim")
		}
		switch v.Action {
		case "no_change":
			return finish(p, v.Action, "", "", v.Critique), nil
		case "revise":
			if p.Previous != nil {
				return finish(p, "no_change", "", "", "revision budget exhausted: "+v.Critique), nil
			}
			p.Previous, p.Review = p.Draft, &v
			return r.construct(p)
		case "open", "closed":
			out, err := prepareCard(p, v, r.cards)
			if err != nil {
				return nil, err
			}
			return r.publish(p.Revision, v.Action, out)
		default:
			return nil, fmt.Errorf("invalid challenge action %q", v.Action)
		}
	})
}

func (r investigation) publish(revision, action string, card publication) (*godel.Node, error) {
	p := packet{Revision: revision, Card: &card}
	return r.node(publisher, p, func(result godel.Result) (*godel.Node, error) {
		receipt, err := parse[struct {
			Status   string `json:"status"`
			Revision string `json:"adopted_revision,omitempty"`
			Reason   string `json:"reason"`
		}](result)
		if err != nil {
			return nil, err
		}
		switch {
		case receipt.Status == "adopted" && commitID(receipt.Revision) && !blank(receipt.Reason):
			return finish(p, action, card.Path, receipt.Revision, receipt.Reason), nil
		case receipt.Status == "not_adopted" && receipt.Revision == "" && !blank(receipt.Reason):
			return finish(p, "not_adopted", "", "", receipt.Reason), nil
		default:
			return nil, errors.New("invalid campaign publication report")
		}
	})
}

func finish(p packet, action, path, accepted, reason string) *godel.Node {
	result := struct {
		Revision string `json:"evidence_revision"`
		Action   string `json:"action"`
		Path     string `json:"path,omitempty"`
		Accepted string `json:"adopted_revision,omitempty"`
		Reason   string `json:"reason"`
	}{p.Revision, action, path, accepted, reason}
	data, err := json.Marshal(result)
	if err != nil {
		panic(err) // Strings came from valid stage JSON or trusted inputs.
	}
	return &godel.Node{Exec: "printf", Args: []string{"%s\n", string(data)}}
}

func blank(s string) bool { return strings.TrimSpace(s) == "" }
