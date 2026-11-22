package main

import (
	"fmt"
	"regexp"
	"strings"
)

var slugPattern = regexp.MustCompile(`^[a-z0-9]+(-[a-z0-9]+)*$`)

func validSlug(s string) bool { return len(s) <= 100 && slugPattern.MatchString(s) }

func disposition(s string) bool { return s == "open" || s == "closed" }

type publication struct {
	Path     string `json:"path"`
	Previous string `json:"previous_path,omitempty"`
	Markdown string `json:"markdown"`
}

func prepareCard(p packet, v verdict, cards map[string]string) (publication, error) {
	if !commitID(p.Revision) || p.Draft == nil || !validSlug(p.Draft.Slug) || p.Choice == nil {
		return publication{}, fmt.Errorf("invalid card revision or slug")
	}
	slug := p.Draft.Slug
	old := cards[slug]
	if p.Choice.Existing != "" {
		if p.Choice.Existing != slug || old == "" {
			return publication{}, fmt.Errorf("expected existing slug %q", p.Choice.Existing)
		}
	} else if old != "" {
		return publication{}, fmt.Errorf("new claim reuses accepted slug %s", slug)
	}
	for _, lead := range v.Decisive {
		found := false
		for _, c := range p.Primary {
			found = found || (c.Status == "verified" && c.Lead == lead && !blank(lead))
		}
		if !found {
			return publication{}, fmt.Errorf("decisive source %q has not been verified", lead)
		}
	}
	body := strings.TrimSpace(v.Body)
	title, rest, _ := strings.Cut(body, "\n")
	if !strings.HasPrefix(title, "# ") || blank(strings.TrimPrefix(title, "# ")) || blank(rest) || strings.ContainsRune(body, 0) {
		return publication{}, fmt.Errorf("expected Markdown starting with an H1 and followed by the claim and prose")
	}
	var card strings.Builder
	fmt.Fprintf(&card, "---\nevidence_revision: %s\n", p.Revision)
	switch v.Action {
	case "open":
		if v.Outcome != "" {
			return publication{}, fmt.Errorf("open card cannot include an outcome")
		}
	case "closed":
		switch v.Outcome {
		case "established", "refuted", "parked", "superseded":
		default:
			return publication{}, fmt.Errorf("invalid closed outcome %q", v.Outcome)
		}
		fmt.Fprintf(&card, "outcome: %s\n", v.Outcome)
	default:
		return publication{}, fmt.Errorf("invalid card disposition %q", v.Action)
	}
	fmt.Fprintf(&card, "---\n\n%s\n", body)
	if card.Len() > maxCard {
		return publication{}, fmt.Errorf("rendered card exceeds %d bytes", maxCard)
	}
	out := publication{Path: cardPath(v.Action, slug), Markdown: card.String()}
	if old != "" && old != v.Action {
		out.Previous = cardPath(old, slug)
	}
	return out, nil
}
