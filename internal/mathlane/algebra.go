package mathlane

import (
	"fmt"
	"strings"
)

// The lane supports additive expressions over a
// small set of named roles, each occurring exactly
// once. Checking this grammar never executes Lean or
// interprets arbitrary Lean syntax. In particular,
// signed expressions are only candidates: reviewers
// assess their source meaning and the worker checks
// whether a proof's coefficients actually close the
// frozen goal.
func additive(input string, roles ...string) bool {
	if len(input) > 256 || strings.Contains(input, "--") {
		return false
	}
	p := additiveParser{rest: input, roles: roles}
	return p.sum() && strings.Trim(p.rest, " ") == "" && p.seen == (1<<len(roles))-1
}

type additiveParser struct {
	rest  string
	roles []string
	seen  uint
}

func (p *additiveParser) take(c byte) bool {
	p.rest = strings.TrimLeft(p.rest, " ")
	if len(p.rest) == 0 || p.rest[0] != c {
		return false
	}
	p.rest = p.rest[1:]
	return true
}

func (p *additiveParser) sum() bool {
	if !p.term() {
		return false
	}
	for p.take('+') || p.take('-') {
		if !p.term() {
			return false
		}
	}
	return true
}

func (p *additiveParser) term() bool {
	p.take('-')
	if p.take('(') {
		return p.sum() && p.take(')')
	}
	for i, role := range p.roles {
		if rest, ok := strings.CutPrefix(p.rest, role); ok && p.seen&(1<<i) == 0 {
			p.rest = rest
			p.seen |= 1 << i
			return true
		}
	}
	return false
}

func equation(input, left string, roles ...string) (string, error) {
	lhs, rhs, ok := strings.Cut(input, "=")
	if !ok || strings.Trim(lhs, " ") != left || !additive(rhs, roles...) {
		return "", fmt.Errorf("%w: expected %s = a signed additive expression using %s exactly once", ErrRejected, left, strings.Join(roles, ", "))
	}
	return left + " = " + strings.Trim(rhs, " "), nil
}

func validCombination(s string) bool {
	return s == strings.Trim(s, " ") && additive(s, "hGeom", "hSpec")
}
