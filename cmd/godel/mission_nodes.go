package main

import (
	"strings"

	"patel.codes/godel"
)

// missionNodes is a bootstrap, not a protocol later versions
// must implement.
func missionNodes(goal string) (work, improve *godel.Node) {
	codingNode := func(role string) *godel.Node {
		return &godel.Node{Exec: "pi", Args: []string{
			"--print", "--mode", "text", "--no-session", "--no-context-files",
			"--provider", "exe-dev-openai", "--model", "gpt-6.2-sol@llm",
			"--append-system-prompt", goal + "\n\n" + practice + "\n\n" + role,
		}}
	}
	work = codingNode(`Act on the operator's objective or the preceding handoff on stdin. Choose useful work yourself and carry it out with your tools. Take one meaningful step, then yield to improvement. Keep the operator objective in your handoff. Report what observably changed relative to the starting point, what check supports that, and any wall you encountered. A failed experiment is useful data. If progress stalled, say what you tried and what observation would distinguish causes. A wall in the current method is not a reason to end the loop. End with a line MISSION_STOP only on achieving the objective or a genuine external stop condition; explain which it was.`)
	work.Next = func(r godel.Result) (*godel.Node, error) {
		lines := strings.Split(strings.TrimSpace(r.Text), "\n")
		if strings.TrimSpace(lines[len(lines)-1]) == "MISSION_STOP" {
			return godel.Stop(), nil
		}
		return nil, nil
	}
	improve = codingNode(`You own the entire live program, including this improver. Compare the run against the mission and earlier observations. Identify what actually advanced or stalled. When the method is the obstacle, use your coding tools to change the method, not just recommend a patch. You may replace the program, create or remove nodes and tools, split obligations, parallelize independent work, or write different improvers. Choose your own experiments and measures; check a change against the failure that motivated it and preserve what worked. Test the edited Go program before handing it to the next fresh launch. Leave it alone if no change is useful.`)
	return work, improve
}

const practice = `This is a live, disposable campaign workspace. Work from this checkout; the repository root is ../.. from cmd/godel. The earlier pilot, code, and handoffs under .godel at the root are resources and suggestions, not a required route or a limit on the mission. Keep findings and open obligations understandable on disk; the loop carries work stdout, not improver stdout. Keep the mission and standards of evidence distinct from mutable procedure. Use the pinned manuscript and Mathlib. Distinguish navigation from checked readings, conditional claims from proofs, and infrastructure gaps from mathematical gaps. Use the designated worker for Lean builds and audits, never elaborate RH/GRH locally. Do not fabricate evidence, substitute a weaker target, or declare an unchecked revision accepted. Leave main and publication to the operator. Edit this working copy directly; do not manage version control, invoke yah, or modify runtime bookkeeping. Keep mathematical results separate from workflow experiments. Do not add top-level directories under Proofs. Format changed Go with gocmt and gofmt.`
