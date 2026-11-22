package main

import (
	"strings"
	"testing"
)

func TestCardDisposition(t *testing.T) {
	t.Parallel()
	p := packet{Revision: revision, Choice: &choice, Draft: &candidate}
	cards := map[string]string{}
	open, err := prepareCard(p, openCard, cards)
	if err != nil {
		t.Fatal(err)
	}
	if open.Path != ".godel/conjectures/open/uniform-bound.md" || open.Previous != "" || open.Markdown != "---\nevidence_revision: "+revision+"\n---\n\n"+openCard.Body+"\n" {
		t.Fatalf("unexpected open card: %+v", open)
	}
	existing := choice
	existing.Existing = candidate.Slug
	p.Choice = &existing
	cards[candidate.Slug] = "open"
	closedCard := openCard
	closedCard.Action, closedCard.Outcome = "closed", "parked"
	closedCard.Body = "# A uniform bound\n\n" + candidate.Claim + "\n\nParked: no endpoint lemma. Reopen upon a uniform endpoint estimate."
	closed, err := prepareCard(p, closedCard, cards)
	if err != nil {
		t.Fatal(err)
	}
	if closed.Path != ".godel/conjectures/closed/uniform-bound.md" || closed.Previous != open.Path || closed.Markdown != "---\nevidence_revision: "+revision+"\noutcome: parked\n---\n\n"+closedCard.Body+"\n" {
		t.Fatalf("unexpected closed card: %+v", closed)
	}
	cards[candidate.Slug] = "closed"
	reopened, err := prepareCard(p, openCard, cards)
	if err != nil || reopened.Path != open.Path || reopened.Previous != closed.Path {
		t.Fatalf("unexpected reopened card: %+v (%v)", reopened, err)
	}
}

func TestInvalidCard(t *testing.T) {
	t.Parallel()
	d := candidate
	p := packet{Revision: revision, Choice: &choice, Draft: &d}
	for _, slug := range []string{"../../oops", "a/b", ".", "Uppercase"} {
		d.Slug = slug
		if _, err := prepareCard(p, openCard, nil); err == nil {
			t.Errorf("accepted slug %q", slug)
		}
	}
	d.Slug = candidate.Slug
	if _, err := prepareCard(p, openCard, map[string]string{d.Slug: "closed"}); err == nil {
		t.Fatal("new card reuses an accepted slug")
	}
	for _, v := range []verdict{
		{Action: "../other", Body: openCard.Body},
		{Action: "open", Outcome: "parked", Body: openCard.Body},
		{Action: "closed", Outcome: "unknown", Body: openCard.Body},
		{Action: "open", Body: "---\nforged_frontmatter: yes\n---\n\n" + openCard.Body},
	} {
		if _, err := prepareCard(p, v, nil); err == nil {
			t.Errorf("accepted invalid card %+v", v)
		}
	}
	p.Revision = revision[:12]
	if _, err := prepareCard(p, openCard, nil); err == nil || !strings.Contains(err.Error(), "revision") {
		t.Fatalf("wrong result for abbreviated revision: %v", err)
	}
}
