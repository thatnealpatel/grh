// Package mathlane generates and reviews Lean candidates for the bounded
// two-identity algebra assembly in Masullo's trace formula. It does not run
// Lean, certify source evidence, or publish files. Each agent stage runs a
// fresh headless Yah session in scratch, not in the proofs worktree.
// GRH_MATHLIB may point to an absolute checkout of the pinned Mathlib sources.
package mathlane

import (
	"context"
	"encoding/json"
	"errors"
	"fmt"
	"slices"
	"strings"
)

// Draft is a cumulative candidate. Decls
// lists the qualified names present in
// Files, and Premises lists the named
// analytic inputs still to be supplied
// for a manuscript application. Leaf is
// the frozen, not-yet-implemented theorem
// header, or empty when a proof candidate
// for it is present (not Lean-checked).
type Draft struct {
	Files    map[string]string
	Decls    []string
	Premises []string
	Leaf     string
	Summary  string
}

// Verdict is a semantic review result, not a proof check.
type Verdict struct {
	Accept bool
	Reason string
}

var (
	// ErrRejected indicates that an input or candidate
	// failed this lane's contract.
	ErrRejected = errors.New("mathlane candidate rejected")
	// ErrProofNotReady indicates that there is no supported
	// proof candidate for the fixed leaf. It is distinct from
	// launch, transport, and cancellation errors.
	ErrProofNotReady = errors.New("mathlane proof not ready")
)

// Translate proposes the bounded interface and freezes its assembly goal.
// packet is the caller's independently verified source packet, serialized as
// JSON.
func Translate(ctx context.Context, root, mission, obligation, packet, critique string) (Draft, error) {
	return agent(runYah).translate(ctx, root, request{Mission: mission, Obligation: obligation, Packet: packet, Critique: critique})
}

// Fidelity independently reviews the supplied candidate and frozen header.
func Fidelity(ctx context.Context, root, mission, obligation, packet string, d Draft) (Verdict, error) {
	return agent(runYah).review(ctx, root, request{Mission: mission, Obligation: obligation, Packet: packet, Draft: &d}, false)
}

// Challenge independently reviews the exact landed files. The caller must
// supply root as a stable snapshot of the intended landed revision, not a
// mutable checkout. This function matches bytes, not revision identities.
func Challenge(ctx context.Context, root, mission, obligation, packet string, d Draft) (Verdict, error) {
	return agent(runYah).review(ctx, root, request{Mission: mission, Obligation: obligation, Packet: packet, Draft: &d}, true)
}

// Prove asks for a proof of the fixed leaf, not for a replacement statement.
// A successful candidate adds the assembly theorem and preserves the analytic
// premises and every former file. No file is written by this function.
func Prove(ctx context.Context, root, mission, obligation, packet string, d Draft) (Draft, error) {
	return agent(runYah).prove(ctx, root, request{Mission: mission, Obligation: obligation, Packet: packet, Draft: &d})
}

type request struct {
	Mission    string
	Obligation string
	Packet     string
	Critique   string `json:",omitempty"`
	Draft      *Draft `json:",omitempty"`
}

type agent func(ctx context.Context, root, instructions string, in []byte) ([]byte, error)

const maxPromptBytes = 128 << 10

func (r request) source(ctx context.Context) (sourceReading, error) {
	var packet sourceReading
	if err := context.Cause(ctx); err != nil {
		return packet, err
	}
	if strings.TrimSpace(r.Mission) == "" || strings.TrimSpace(r.Obligation) == "" {
		return packet, fmt.Errorf("%w: supply mission and current obligation", ErrRejected)
	}
	if len(r.Packet) > maxPromptBytes || json.Unmarshal([]byte(r.Packet), &packet) != nil {
		return packet, fmt.Errorf("%w: malformed source packet", ErrRejected)
	}
	if packet.Disposition != "verified" || !meaningful(packet.Anchor) || !meaningful(packet.Reading) ||
		!meaningful(packet.Attribution) || !meaningful(packet.Boundary) {
		return packet, fmt.Errorf("%w: verified reading, edition anchor, attribution, and boundary are required", ErrRejected)
	}
	return packet, nil
}

func (a agent) ask(ctx context.Context, root, instructions string, r request, reply any) error {
	data, err := json.Marshal(r)
	if err != nil {
		return fmt.Errorf("encode mathlane request: %w", err)
	}
	if len(data) > maxPromptBytes {
		return fmt.Errorf("%w: source and candidate exceed prompt limit", ErrRejected)
	}
	out, err := a(ctx, root, instructions, data)
	if cause := context.Cause(ctx); cause != nil {
		return cause
	}
	if err != nil {
		return err
	}
	if err := decodeReply(out, reply); err != nil {
		return fmt.Errorf("invalid mathlane agent reply: %w", err)
	}
	return nil
}

func (a agent) translate(ctx context.Context, root string, r request) (Draft, error) {
	packet, err := r.source(ctx)
	if err != nil {
		return Draft{}, err
	}
	var reply struct {
		Status, Geometric, Spectral, Conclusion, Reason string
	}
	if err := a.ask(ctx, root, translatePrompt, r, &reply); err != nil {
		return Draft{}, fmt.Errorf("translate: %w", err)
	}
	if reply.Status == "reject" && meaningful(reply.Reason) && reply.Geometric == "" && reply.Spectral == "" && reply.Conclusion == "" {
		return Draft{}, fmt.Errorf("translate: %w: %s", ErrRejected, reply.Reason)
	}
	if reply.Status != "candidate" || reply.Reason != "" {
		return Draft{}, fmt.Errorf("translate: %w: expected three equations or a reason for rejection", ErrRejected)
	}
	return interfaceDraft(packet, reply.Geometric, reply.Spectral, reply.Conclusion)
}

func (a agent) review(ctx context.Context, root string, r request, landed bool) (Verdict, error) {
	packet, err := r.source(ctx)
	if err != nil {
		return Verdict{}, err
	}
	if err := validateDraft(packet, *r.Draft); err != nil {
		return Verdict{Reason: err.Error()}, nil
	}
	instruction := fidelityPrompt
	if landed {
		verdict, err := matchLanded(ctx, root, *r.Draft)
		if err != nil || !verdict.Accept {
			return verdict, err
		}
		instruction = challengePrompt
	}
	var reply struct {
		Accept *bool
		Reason string
	}
	if err := a.ask(ctx, root, instruction, r, &reply); err != nil {
		return Verdict{}, fmt.Errorf("review: %w", err)
	}
	if reply.Accept == nil || !meaningful(reply.Reason) {
		return Verdict{}, errors.New("review: missing explicit decision or reason")
	}
	return Verdict{*reply.Accept, reply.Reason}, nil
}

func (a agent) prove(ctx context.Context, root string, r request) (Draft, error) {
	packet, err := r.source(ctx)
	if err != nil {
		return Draft{}, err
	}
	d := *r.Draft
	if err := validateDraft(packet, d); err != nil {
		return Draft{}, err
	}
	if d.Leaf == "" {
		return Draft{}, fmt.Errorf("%w: assembly candidate already supplied; remaining inputs are analytic and outside the proof surface (%s)", ErrProofNotReady, strings.Join(d.Premises, "; "))
	}
	var reply struct {
		Status, Combination, Reason string
	}
	if err := a.ask(ctx, root, proofPrompt, r, &reply); err != nil {
		return Draft{}, fmt.Errorf("prove: %w", err)
	}
	if reply.Status == "blocked" && meaningful(reply.Reason) && reply.Combination == "" {
		return Draft{}, fmt.Errorf("%w: %s", ErrProofNotReady, reply.Reason)
	}
	if reply.Status != "candidate" || reply.Reason != "" || !validCombination(reply.Combination) {
		return Draft{}, fmt.Errorf("prove: %w: expected a signed combination of the two fixed hypotheses, or an explicit blocker", ErrRejected)
	}

	out := Draft{
		Files:    map[string]string{propsPath: d.Files[propsPath], theoremPath: theoremFile(d.Leaf, reply.Combination)},
		Decls:    append(slices.Clone(d.Decls), assemblyDecl),
		Premises: slices.Clone(d.Premises),
		Summary:  assemblySummary,
	}
	return out, nil
}
