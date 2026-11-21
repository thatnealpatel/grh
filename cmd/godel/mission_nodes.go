package main

import (
	"strings"

	"patel.codes/godel"
)

// missionNodes is a bootstrap, not a protocol later versions
// must implement.
func missionNodes(goal string) (work, improve *godel.Node) {
	codingNode := func(role string) *godel.Node {
		// Yah attaches to the campaign at its cwd, not an ancestor.
		return &godel.Node{Exec: "yah", Directory: "../..", Args: []string{
			"-yolo", "-effort", "high", "-append", goal + "\n\n" + practice + "\n\n" + role,
		}}
	}
	work = codingNode(`Act on the operator's objective or the preceding handoff on stdin. Choose useful work yourself and carry it out with your tools. Take one meaningful step, then yield to improvement.

Keep the operator objective in your handoff. Report what observably changed and what check supports it. If progress stalled, say what you tried and what observation would distinguish causes. Name the next useful action that can run with the capabilities available now, if one remains. List blocked actions separately with their reopening conditions, not as the next action.

A wall in the current method is not a reason to end the loop. End with a line MISSION_STOP only on achieving the objective or a genuine external stop condition; explain which it was.`)
	work.Next = func(r godel.Result) (*godel.Node, error) {
		lines := strings.Split(strings.TrimSpace(r.Text), "\n")
		if strings.TrimSpace(lines[len(lines)-1]) == "MISSION_STOP" {
			return godel.Stop(), nil
		}
		return nil, nil
	}
	improve = codingNode(`You own the entire accepted program, including this improver. Compare the run against the mission and earlier observations. Identify what actually advanced or stalled. When the method is the obstacle, use your coding tools to change the method, not just recommend a patch. You may replace the program, create or remove nodes and tools, split obligations, parallelize independent work, or write different improvers. Choose your own experiments and measures; check a change against the failure that motivated it and preserve what worked. Test the edited Go program before handing it to the next fresh launch. Leave it alone if no change is useful.`)
	return work, improve
}

const practice = `The repository root is the stable launch workspace. Gödel's registered Source is a launch path, not a snapshot of the program now running. First get the current accepted commit from tool_campaign status. Inspect cmd/godel and other inputs at that exact revision (jj --ignore-working-copy file list/show -r 'commit_id("HASH")' from the root), not by reading possibly stale launch files. The earlier pilot, code, and handoffs under .godel are resources, not a required route or a limit on the mission. Keep findings and open obligations understandable on disk; the loop carries work stdout, not improver stdout.

For both work and improvement, read .godel/frontier.md at the accepted revision alongside the latest handoff. The handoff points to one branch; it is not the queue for the whole paper. Use the frontier to choose a concrete obligation whose result would change the next proof step, including independent branches when a favored route is blocked or a downstream interface needs challenging. Preserve the current branch's unresolved premises. When you materially change an obligation's dependencies, status, or runnable next step, update the frontier and put evidence in the linked handoff. The frontier is navigation, not proof or source evidence.

When the latest handoff extends a conditional branch and its decisive premise is still open, look one citation upstream before extending the same chain again. Audit a specific manuscript dependency: Match the operator, domain, topology, and limit order required by the consuming step against what the cited passage actually provides. A documented mismatch with a concrete repair or falsification test is an independent frontier task; do not treat it as a reason to discard the conditional branch, or require a branch change when no useful upstream check is available.

Both nodes can organize work across fresh Yah contexts. When an obligation needs its own investigation and several distinct subtasks, use tool_subagent and request a recursion-capable Yah coordinator in the intent. Give it the accepted revision, the obligation, and the evidence you need back; let it manage its own subagents and reconcile their results. For example, a formalization coordinator can split lemma drafting, independent statement review, and preparing the exact candidate for the designated worker. A missing worker blocks the build and audit, not the other branches. Use a single context for small tasks; reshape the tree or the program when the work calls for it.

Use leandoc for Lean and Mathlib declaration lookup, and sagedoc for Sage APIs. Inspect source when the lookup does not answer the question. A documentation result is not an elaboration check.

For changes, use tool_campaign new on the accepted commit or dispatch a campaign writer based on it. Edit and check the isolated output, not the launch checkout. Integrate the output, check the exact candidate, and use tool_campaign adopt. Confirm acceptance through the campaign; no parent manual bridge or separate operator approval is needed. If the campaign is unavailable, report the blocker rather than editing the launch workspace. Do not manage the jj/git graph directly, publish, or modify runtime bookkeeping.

Use Yah for manuscript work, including independent text review. Do not request a native Claude reviewer. Read the pinned PDF's text with page and equation locators; use it to map claims, compare hypotheses, and formulate obligations. Label extraction-based findings as provisional, especially when glyphs or layout matter. Reserve verified visual readings for independent inspection of the rendered pages. If Yah has no image input, leave that specific check open and continue the text-based work; do not send a PNG path to a text-only reader or wait for visual review to proceed elsewhere.

Treat failed routes as scoped blockers, not manuscript findings. Before retrying a provider, authentication, or missing-transport failure, identify a concrete change to the failed prerequisite or a materially different supported route. Start a changed route with one small control, not a passage batch. If the control fails, record what failed and what would justify reopening it, then work on an independent obligation using already verified source evidence or a clearly labeled mathematical repair. Do not replay the blocked route merely because the previous stdout suggested it or the next launch is fresh. When Lean checking is blocked, an independently reviewed proof candidate can be kept in a handoff outside Proofs and explicitly labeled unelaborated; do not adopt it as a Lean module.

Keep the mission and standards of evidence distinct from mutable procedure. Use the pinned manuscript and Mathlib. Distinguish navigation from checked readings, conditional claims from proofs, and infrastructure gaps from mathematical gaps. Use the designated worker for Lean builds and audits, never elaborate RH/GRH locally. From a workspace at a program revision that supports it, run go run ./cmd/godel check <full-candidate-commit-id> <qualified-declaration> ... from the repository root with the designated GRH_PROOF_WORKER transport. This checks but does not adopt. Use ordinary relevant tests for program-only changes; they do not require a Lean proof-worker pass. Do not fabricate evidence, substitute a weaker target, or declare an unchecked revision accepted. Keep mathematical results separate from workflow experiments. Do not add top-level directories under Proofs. Format changed Go with gocmt and gofmt.`
