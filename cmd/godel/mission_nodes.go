package main

import (
	"strings"

	"patel.codes/godel"
)

// missionNodes is a bootstrap, not a protocol later versions must implement.
func missionNodes(goal, archiveRevision string) (work, improve *godel.Node) {
	// git archive expands this marker in the
	// accepted build, even when an older bootstrap
	// launched it. A checkout build has no such
	// provenance.
	revision := strings.TrimSpace(archiveRevision)
	source := ""
	if (len(revision) == 40 || len(revision) == 64) && strings.Trim(revision, "0123456789abcdef") == "" {
		source = "Gödel launch source commit: " + revision + ". This identifies the archive used to build the executable, not the current campaign tip.\n\n"
	}
	codingNode := func(role string) *godel.Node {
		// Yah attaches to the campaign at its cwd, not an ancestor.
		return &godel.Node{Exec: "yah", Directory: "../..", Args: []string{
			"-yolo", "-effort", "high", "-append", source + goal + "\n\n" + practice + "\n\n" + role,
		}}
	}
	work = codingNode(`Act on the operator's objective or the preceding handoff on stdin. Choose useful work yourself and carry it out with your tools. Take one meaningful step, then yield to improvement.

Keep the operator objective in your handoff. Report what observably changed and what check supports it. Include the accepted revision and the relevant handoff link for completed work. If progress stalled, say what you tried and what observation would distinguish causes. Name the next useful action that can run with the capabilities available now, if one remains. List blocked actions separately with their reopening conditions, not as the next action.

A wall in the current method is not a reason to end the loop. End with a line MISSION_STOP only on achieving the objective or a genuine external stop condition; explain which it was.`)
	work.Next = func(r godel.Result) (*godel.Node, error) {
		lines := strings.Split(strings.TrimSpace(r.Text), "\n")
		if strings.TrimSpace(lines[len(lines)-1]) == "MISSION_STOP" {
			return godel.Stop(), nil
		}
		return nil, nil
	}
	improve = codingNode(`Analyze the full mission iteration. Use the Gödel run record and the corresponding Yah work and subagent sessions to reconstruct what was tried, including failed and unadopted attempts. Compare with earlier work and improvement sessions when deciding whether a pattern recurs. Use the accepted revision to verify what landed, revision history to recover the exact cmd/godel tree and prompts at a given revision, and session evidence to understand how the program behaved. If you cannot link a run to a revision or session, say so.

You own the shape of cmd/godel. A node can do work directly, run a deterministic check, or make a one-shot Yah inference with a precise system prompt and one task message. Its Next function can choose a different successor on each traversal. For example, a stalled argument might need a source audit, a missing lemma might need a prover, and an existing candidate might need only a checker. Sequence steps when one answer determines the next question. Delegate independent questions in parallel when one coordinator can explain how the answers fit together. Give a branch its own child Gödel program when it benefits from separate handoffs, run history, and improvement cycles. Add, merge, or remove nodes as the proof effort warrants.

Improvement need not be a single node. SelfImprove names the root of an improvement tree. For example, one Yah node could analyze the run and its sessions, then use Next to finish if the method worked, route an uncertain diagnosis to a bounded experiment, or send a well-supported program change to an implementer. Every successor receives the same original run context, so pass the selected finding explicitly if the next node needs it. Keep analysis and action in one node when that is simpler; split them when the distinction improves a real decision.

Own .godel/experiments/ as your continuous, terse ledger. Keep its README.md useful to a future improver: For each consequential change or trial, say what prompted it, what happened, and what you decided. Link to the named experiment directory, exact revisions, and relevant run or session IDs for the richer history. Do not duplicate old programs or transcripts in the index. Preserve negative results, and distinguish “we tried it and it did not help” from “we never ran it.”

Use .godel/experiments/<slug>/ to try a change without installing it in the main tree. Start with an observed proof decision and the smallest trial that could change your judgment. For example, try a proposed router on a recorded handoff using only the evidence available at that decision; keep the prompt, the route it chose, and your assessment in the experiment directory. That tests the routing decision without changing where the next live proof worker goes. Add a standalone harness only if the trial needs one. A replay can show that the router chose differently; it cannot by itself show that the new route advanced the proof. Promote a pattern into cmd/godel when the evidence warrants its lasting effect on future runs. Otherwise revise or retire it, leaving a short finding and pointers so a later improver need not repeat the trial.

Judge changes by the proof decisions they improve and the gaps they close on the way to the manuscript’s full GRH claim. A rational RH result can be valuable without discharging the general case. Test the edited Go program before handing it to the next fresh launch. If you land proof or source work during improvement, record the checked outcome, remaining scope, and runnable successor in the accepted frontier and its linked handoff, not just in your response.`)
	return work, improve
}

const practice = `The repository root is the stable launch workspace. Gödel's registered Source is a launch path, not a snapshot of the program now running. First get the current accepted commit from tool_campaign status. Inspect cmd/godel and other inputs at that exact revision (jj --ignore-working-copy file list/show -r 'commit_id("HASH")' from the root), not by reading possibly stale launch files. The earlier pilot, code, and handoffs under .godel are resources, not a required route or a limit on the mission. Keep findings and open obligations understandable on disk; the loop carries work stdout, not improver stdout.

For both work and improvement, read .godel/frontier.md at the accepted revision alongside the latest handoff. The handoff points to one branch, and the frontier maps known obligations, not the whole paper. Before acting on a prior run's suggested next step, reconcile it with the accepted Lean declarations and linked proof and review evidence. Improvement may have finished that step after work stdout was fixed. If the evidence already closes the exact obligation, advance to its unmet successor or another useful open task rather than repeating the proof or review. If only part is closed, use the remaining scope. This does not override a fresh operator request to revisit a result.

Choose a concrete step whose result would change the next proof step. When the map is concentrated on one endpoint, look beyond it for a complete substantive statement or a foundation used by several branches. For one promising passage, read the statement and its dependencies in the pinned text, check the pinned Mathlib interface, and record a runnable obligation with its exact scope. Do not add a contents inventory or rotate by quota; preserve productive chains and their unresolved premises. When you materially change an obligation's dependencies, status, or runnable next step, update the frontier and put evidence in the linked handoff. The frontier is navigation, not proof or source evidence.

When the latest handoff extends a conditional branch and its decisive premise is still open, look one citation upstream before extending the same chain again. Audit a specific manuscript dependency: Match the operator, domain, topology, and limit order required by the consuming step against what the cited passage actually provides. A documented mismatch with a concrete repair or falsification test is an independent frontier task; do not treat it as a reason to discard the conditional branch, or require a branch change when no useful upstream check is available.

Both nodes can organize work across fresh Yah contexts. When an obligation needs its own investigation and several distinct subtasks, use tool_subagent and request a recursion-capable Yah coordinator in the intent. Give it the accepted revision, the obligation, and the evidence you need back; let it manage its own subagents and reconcile their results. For example, a formalization coordinator can split lemma drafting, independent statement review, and checking the integrated candidate locally. Use a single context for small tasks; reshape the tree or the program when the work calls for it.

Use leandoc for Lean and Mathlib declaration lookup, and sagedoc for Sage APIs. Inspect source when the lookup does not answer the question. A documentation result is not an elaboration check.

For changes, use tool_campaign new on the accepted commit or dispatch a campaign writer based on it. Edit and check the isolated output, not the launch checkout. Integrate the output, check the exact candidate, and use tool_campaign adopt. Write the integration description in the style of ~/p/proofs: Start the subject with the relevant project area and a colon, then a short imperative naming the concrete result (for example, “Proofs/Theorems: Extend rational adelic Fourier to L²”). Use the body for scope or reasoning that the subject does not convey, not routine handoff notes. Confirm acceptance through the campaign; no parent manual bridge or separate operator approval is needed. If the campaign is unavailable, report the blocker rather than editing the launch workspace. Do not manage the jj/git graph directly, publish, or modify runtime bookkeeping.

Use Yah for manuscript work, including independent text review. Do not request a native Claude reviewer. For manuscript work, start in ~/d/masullo/. Read the relevant chapter or appendix Markdown first: Its LaTeX often renders fractions, subscripts, and superscripts more clearly than pdftotext -layout. Use the layout extraction to locate the passage and its surrounding text on the numbered PDF page. Inspect the rendered page directly if the readings disagree or if the conclusion depends on exact notation, wording, or layout. Cite only Masullo’s manuscript, by PDF page and theorem, equation, or section number; pass those locators to delegated readers. If the rendered page was not inspected, label the reading provisional. Reserve verified visual readings for independent inspection of the rendered pages. If Yah has no image input, leave that specific check open and continue the text-based work; do not send a PNG path to a text-only reader or wait for visual review to proceed elsewhere.

Treat failed routes as scoped blockers, not manuscript findings. Before retrying a provider, authentication, or missing-transport failure, identify a concrete change to the failed prerequisite or a materially different supported route. Start a changed route with one small control, not a passage batch. If the control fails, record what failed and what would justify reopening it, then work on an independent obligation using already verified source evidence or a clearly labeled mathematical repair. Do not replay the blocked route merely because the previous stdout suggested it or the next launch is fresh. When Lean checking is blocked, an independently reviewed proof candidate can be kept in a handoff outside Proofs and explicitly labeled unelaborated; do not adopt it as a Lean module.

When returning to a branch with Lean drafts written during a checking outage, use the current checking route, not the draft's historical blocker. Before adding another downstream Lean draft on that branch, locally elaborate the first independently reviewed, unelaborated dependency you need. Repair implementation failures without weakening its statement. If it cannot be checked in this run, record the specific obstacle and keep the downstream interface provisional. This does not block independent manuscript audits or work on other branches.

Keep the mission and standards of evidence distinct from mutable procedure. Use the pinned manuscript and Mathlib. Distinguish navigation from checked readings, conditional claims from proofs, and infrastructure gaps from mathematical gaps. This is the proof machine. Follow the local campaign workflow in cmd/godel/README.md: Choose and repair proofs yourself, obtain independent statement review, then run the full local audit and compare its built endpoint signatures with the reviewed statements before adopting that exact candidate. This supersedes older handoffs waiting for a remote worker. If a proof is checked but unadopted, reconcile its patch with the latest base before extending it. Use the README's recovery procedure for stale bases and unregistered prior-session outputs. When the restacked Lean inputs match an audited candidate exactly, seed from its trusted build cache and repeat the full audit on the new candidate. Use ordinary relevant tests for program-only changes; they do not require a Lean proof-worker pass. Do not fabricate evidence, substitute a weaker target, or declare an unchecked revision accepted. Keep mathematical results separate from workflow experiments. Do not add top-level directories under Proofs. Format changed Go with gocmt and gofmt.`
