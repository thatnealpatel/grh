package main

import (
	"context"
	"encoding/json"
	"fmt"
	"strings"
	"sync"
)

const width = 8
const frame = `Frame the task. Output only a JSON object with nonblank string "criteria" and "assignments", an array of exactly eight distinct, complementary short instructions. Route the lanes to lines of inquiry appropriate to this specific task.`

var roles = []string{
	"Propose a solution or partial result for your assignment. Give decisive reasoning and the weakest assumption.",
	"Challenge the two proposals. Test a consequential disagreement, or a shared assumption, against a concrete case. Identify each proposal by ID.",
	"Repair, narrow, or withdraw the proposal in response to both challenges. State the resulting claim, evidence, and remaining gap.",
	"Audit the two repairs against their challenge records. Identify surviving claims by ID, decisive evidence, and unresolved conditions. Do not vote.",
}

const synth = `Answer the original task using the criteria, audits, and repaired claims. Evaluate evidence rather than counting votes. State conditions for consequential unresolved disagreements.`

type artifact struct {
	ID   string `json:"id"`
	Text string `json:"text"`
}
type packet struct {
	Task       string     `json:"task"`
	Criteria   string     `json:"criteria,omitempty"`
	Assignment string     `json:"assignment,omitempty"`
	ID         string     `json:"id"`
	Sources    []artifact `json:"sources,omitempty"`
}
type caller func(context.Context, string, string) (string, error)

func graph(ctx context.Context, task string, call caller) (string, error) {
	send := func(ctx context.Context, role string, p packet) (artifact, error) {
		b, err := json.Marshal(p)
		if err != nil {
			return artifact{}, err
		}
		s, err := call(ctx, role, string(b))
		if err == nil && strings.TrimSpace(s) == "" {
			err = fmt.Errorf("empty response")
		}
		if err != nil {
			return artifact{}, fmt.Errorf("%s: %w", p.ID, err)
		}
		return artifact{p.ID, s}, nil
	}
	f, err := send(ctx, frame, packet{Task: task, ID: "frame"})
	if err != nil {
		return "", err
	}
	var plan struct {
		Criteria    string
		Assignments []string
	}
	if err := json.Unmarshal([]byte(f.Text), &plan); err != nil {
		return "", fmt.Errorf("frame: %w", err)
	}
	if strings.TrimSpace(plan.Criteria) == "" || len(plan.Assignments) != width {
		return "", fmt.Errorf("frame needs criteria and %d assignments", width)
	}
	seen := map[string]bool{}
	for _, a := range plan.Assignments {
		k := strings.TrimSpace(a)
		if k == "" || seen[k] {
			return "", fmt.Errorf("blank or duplicate assignment")
		}
		seen[k] = true
	}
	var layers [4][width]artifact
	names := []string{"propose", "challenge", "repair", "audit"}
	for stage, role := range roles {
		layer, cancel := context.WithCancelCause(ctx)
		var wg sync.WaitGroup
		for i := range width {
			wg.Go(func() {
				p := packet{Task: task, Criteria: plan.Criteria, ID: fmt.Sprintf("%s/%d", names[stage], i)}
				prev := (i + width - 1) % width
				switch stage {
				case 0:
					p.Assignment = plan.Assignments[i]
				case 1:
					p.Sources = []artifact{layers[0][i], layers[0][(i+1)%width]}
				case 2:
					p.Assignment = plan.Assignments[i]
					p.Sources = []artifact{layers[0][i], layers[1][prev], layers[1][i]}
				case 3:
					j := (i + 3) % width
					p.Sources = []artifact{layers[2][i], layers[2][j], layers[1][prev], layers[1][i], layers[1][(j+width-1)%width], layers[1][j]}
				}
				a, err := send(layer, role, p)
				if err != nil {
					cancel(err)
					return
				}
				layers[stage][i] = a
			})
		}
		wg.Wait()
		err := context.Cause(layer)
		cancel(nil)
		if err != nil {
			return "", err
		}
	}
	last, err := send(ctx, synth, packet{Task: task, Criteria: plan.Criteria, ID: "synthesize", Sources: append(layers[3][:width:width], layers[2][:]...)})
	return last.Text, err
}
