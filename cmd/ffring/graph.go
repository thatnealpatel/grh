package main

import (
	"context"
	"encoding/json"
	"fmt"
	"strings"
	"sync"
)

const problem = `Study signed trace increments on the nested rational theta floor grids, not changes of basis within a span. At width 0 <= a < 1/2 use H_a = L²(exp(2a|x|)(1+x²)² dx). At level j >= 1 take B=2^j, h=2^(-j), m=B/h, and columns 2 exp(-x/2) floor(k {h exp(x)}) for 2 <= k <= m (braces denote fractional part). Q_j is their full-metric orthogonal projector. The increment is Tr(M_{rho_R} A_f (Q_{j+1}-Q_j)), with ordinary convolution A_f for smooth f supported in (0, log 2), and smooth position cutoffs rho_R exhausting the line. Exhaust band at fixed R and width before exhausting position. The question is whether one can separate the phase mean introduced by projection and bound the remaining signed trace across levels. Do not assume a width-continuity estimate or claim a zero-location result.`

var derive = [4]string{
	"Compute the phase mean introduced by projecting a raw refinement detail off the old phase span. Calibrate on u uniform in [0,1): detail 2 floor(3u)-floor(2u)-floor(4u), old column floor(2{2u}). Then identify what generalizes. Distinguish flat phase from H_a.",
	"Derive the signed increment in H_a by projecting genuinely new columns off the old grid. Use the residual Gram inverse on independent directions. Identify how a phase mean enters after this projection and which constants depend on level.",
	"Bound the centered contribution after ordinary convolution. State the required mean, norm, grid dependence, and cutoff dependence precisely enough to test summability after residual Gram normalization.",
	"Seek a concrete obstruction to the proposed separation or summation. Test genuine floor increments in the stated order of limits; label any obstruction that only applies to a surrogate space or a stronger bound.",
}

var challenge = [4]string{
	"Test whether A1's flat-phase mean calculation transfers to the weighted residual in A2. Exhibit the transfer estimate or a specific discrepancy.",
	"Test whether A3's centered convolution bound applies to A2's projected, normalized columns, not just the raw details. Track the inverse Gram cost.",
	"Test A3's bound against A4's obstruction. Match quantifiers, level, width, cutoff, and order of limits before declaring a contradiction.",
	"Test whether A1's phase-mean leakage accounts for A4's obstruction. Check on a common example and distinguish a finite discrepancy from a nonsummable tail.",
}

const repair = `Repair your original derivation using both supplied challenges. Address each by ID. Return a quantified claim with its hypotheses, decisive calculation, and first uncontrolled term, or explicitly withdraw the claim. Your original assignment: `

const decide = `Decide from the four repairs, not by voting. Report a signed estimate that survives summing refinement levels, a counterexample to a precisely stated bound, or the first uncontrolled term and why the estimates stop there. Show the decisive calculation and its order of limits. A finite Gram identity alone is not a bound on the sum.`

type artifact struct {
	ID   string `json:"id"`
	Text string `json:"text"`
}

type packet struct {
	Task    string     `json:"task"`
	ID      string     `json:"id"`
	Sources []artifact `json:"sources,omitempty"`
}

func graph(ctx context.Context, task string, call func(context.Context, string, string) (string, error)) (string, error) {
	send := func(ctx context.Context, id, role string, sources ...artifact) (artifact, error) {
		input, err := json.Marshal(packet{task, id, sources})
		if err != nil {
			return artifact{}, err
		}
		text, err := call(ctx, problem+"\n\n"+role, string(input))
		if err == nil && strings.TrimSpace(text) == "" {
			err = fmt.Errorf("empty response")
		}
		if err != nil {
			return artifact{}, fmt.Errorf("%s: %w", id, err)
		}
		return artifact{id, text}, nil
	}

	var layers [3][4]artifact
	a, b, c := &layers[0], &layers[1], &layers[2]
	for stage := range layers {
		layer, cancel := context.WithCancelCause(ctx)
		var wg sync.WaitGroup
		for i := range 4 {
			wg.Go(func() {
				role := derive[i]
				var sources []artifact
				switch stage {
				case 1:
					role, sources = challenge[i], []artifact{a[i], a[(i+1)%4]}
				case 2:
					role, sources = repair+derive[i], []artifact{a[i], b[(i+3)%4], b[i]}
				}
				id := fmt.Sprintf("%c%d", 'A'+stage, i+1)
				out, err := send(layer, id, role, sources...)
				if err != nil {
					cancel(err)
					return
				}
				layers[stage][i] = out
			})
		}
		wg.Wait()
		err := context.Cause(layer)
		cancel(nil)
		if err != nil {
			return "", err
		}
	}
	out, err := send(ctx, "D1", decide, c[:]...)
	return out.Text, err
}
