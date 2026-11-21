package main

import (
	"encoding/json/v2"
	"errors"
	"fmt"
	"strings"
	"unicode"
)

type decision[T any] struct {
	Decision string `json:"decision"`
	Reason   string `json:"reason"`
	Finding  *T     `json:"finding"`
}

type citation struct {
	Path  string `json:"path"`
	Quote string `json:"quote"`
}

type trainingFinding struct {
	ReaderQuote string   `json:"reader_quote"`
	Evidence    citation `json:"evidence"`
	RuleScope   string   `json:"rule_scope"`
	Rule        string   `json:"rule"`
}

type comparisonFinding struct {
	BaselineQuote  string   `json:"baseline_quote"`
	AugmentedQuote string   `json:"augmented_quote"`
	Evidence       citation `json:"evidence"`
	Retention      string   `json:"retention"`
	RuleScope      string   `json:"rule_scope"`
}

func decodeDecision[T any](text, positive, negative string) (decision[T], error) {
	var d decision[T]
	if !answerOK(text) {
		return d, errors.New("empty, invalid UTF-8, or oversized decision")
	}
	// json/v2 rejects duplicate members and matches names case-sensitively.
	if err := json.Unmarshal([]byte(text), &d, json.RejectUnknownMembers(true)); err != nil {
		return d, fmt.Errorf("invalid decision object: %w", err)
	}
	if len(strings.TrimSpace(d.Reason)) < 12 {
		return d, errors.New("decision must include a reason")
	}
	switch d.Decision {
	case positive:
		if d.Finding == nil {
			return d, errors.New("positive decision without a finding")
		}
	case negative:
		if d.Finding != nil {
			return d, errors.New("negative decision with a contradictory finding")
		}
	default:
		return d, errors.New("missing or unrecognized decision")
	}
	return d, nil
}

func parseTraining(text, answer string, p packet) (decision[trainingFinding], error) {
	d, err := decodeDecision[trainingFinding](text, "transfer", "stop")
	if err != nil || d.Finding == nil {
		return d, err
	}
	f := d.Finding
	if !verbatim(answer, f.ReaderQuote) || !verbatim(p.Files[f.Evidence.Path], f.Evidence.Quote) {
		return d, errors.New("training finding lacks verbatim evidence from the reader and selected revision")
	}
	if f.RuleScope != "general" || !ruleOK(f.Rule, p) || strings.Contains(f.Rule, f.ReaderQuote) || strings.Contains(f.Rule, f.Evidence.Quote) {
		return d, errors.New("training finding lacks a short generic rule or repeats a training locator or quotation")
	}
	return d, nil
}

func parseComparison(text, baseline, augmented string, p packet) (decision[comparisonFinding], error) {
	d, err := decodeDecision[comparisonFinding](text, "correction", "no_fold")
	if err != nil || d.Finding == nil {
		return d, err
	}
	f := d.Finding
	if f.Retention != "preserved" || f.RuleScope != "general" || strings.TrimSpace(baseline) == strings.TrimSpace(augmented) || f.BaselineQuote == f.AugmentedQuote {
		return d, errors.New("comparison finding lacks correction, preservation, or rule-scope attestation")
	}
	if !verbatim(baseline, f.BaselineQuote) || !verbatim(augmented, f.AugmentedQuote) || !verbatim(p.Files[f.Evidence.Path], f.Evidence.Quote) {
		return d, errors.New("comparison finding lacks verbatim evidence from both readers and selected revision")
	}
	return d, nil
}

func verbatim(source, quote string) bool {
	return len(strings.TrimSpace(quote)) >= 8 && strings.Contains(source, quote)
}

func ruleOK(rule string, p packet) bool {
	if len(rule) < 12 || len(rule) > ruleBytes || strings.TrimSpace(rule) != rule || strings.ContainsFunc(rule, func(r rune) bool {
		return !unicode.IsPrint(r)
	}) {
		return false
	}
	for _, locator := range append(p.paths(), p.Commit) {
		if strings.Contains(rule, locator) {
			return false
		}
	}
	return true
}
