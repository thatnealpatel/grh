package main

import (
	"strings"

	"patel.codes/godel"
	grhgodel "patel.codes/grh/internal/godel"
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

Before starting a new proof or review on an inherited branch, look for a checked artifact the previous improvement could not land. Read ~/.godel/manifest.json to find the program registered for this workspace's cmd/godel path. In that program's runs, read the improvement_response of the latest earlier record whose nonblank final_response matches stdin apart from trailing line endings. If it points to a reviewed artifact that would close a relevant open premise, check whether it has since landed. If still missing, consider recovering it through the README's recovery and exact-candidate landing checks instead of rederiving it. Treat previous audit logs as evidence only for their recorded revisions. Skip this lookup for a fresh operator task, and do not follow an unrelated artifact or a report that does not match the input.

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

Judge changes by the proof decisions they improve and the gaps they close on the way to the manuscript’s full GRH claim. A rational RH result can be valuable without discharging the general case. Test the edited Go program before handing it to the next fresh launch. If you land proof or source work during improvement, leave the checked outcome, remaining scope, and runnable successor with the accepted result or in its branch handoff, not just in your response.`)
	return work, improve
}

const practice = `The repository root is the stable launch workspace. Gödel's registered Source is a launch path, not a snapshot of the program now running. First get the current accepted commit from tool_campaign status. Inspect cmd/godel and other inputs at that exact revision (jj --ignore-working-copy file list/show -r 'commit_id("HASH")' from the root), not by reading possibly stale launch files. The handoffs under .godel are resources, not a required route or a limit on the mission. Keep findings and open obligations understandable on disk; the loop carries work stdout, not improver stdout.

` + grhgodel.ScratchPolicy + `

For both work and improvement, read .godel/frontier.md at the accepted revision alongside the latest handoff. The handoff points to one branch, and the frontier maps known obligations, not the whole paper. Before acting on a prior run's suggested next step, check what landed since the handoff and reconcile the suggestion with the accepted Lean declarations and linked proof and review evidence. Improvement may have finished that step after work stdout was fixed. If the evidence already closes the exact obligation, advance to its unmet successor or another useful open task rather than repeating the proof or review. If only part is closed, use the remaining scope. This does not override a fresh operator request to revisit a result.

Before either role chooses, recovers, or extends proof or source work, refresh .godel/audit/ at the accepted revision you will use. Check findings published since the last handoff's accepted revision, including any published after the work node reported. Skip this check for program-only improvement. Use the publication revision, not the reviewed hash in the filename, to decide what's new. Also look for older notes about premises your step needs, even without a usable handoff revision. Treat findings as evidence, not a repair queue. If findings are absent, irrelevant, or verified as already fixed, continue normally; cite the accepted repair when relevant. If a finding still invalidates a needed premise at the accepted tip, repair it while preserving the needed conclusion before relying on it, or link the note and name the blocked premise in the branch handoff and take an independent step.

Before selecting supporting work, name the inference it would unlock in a repair or the necessary condition it would test in an obstruction. Do not choose a passage merely because it is open. For the selected step, read the relevant statement and its dependencies in the pinned text, check the pinned Mathlib interface, and state the obligation at its exact scope. Do not add a contents inventory or rotate by quota; preserve productive chains and their unresolved premises. Keep the exact statement, review evidence, scope, and remaining premise with the result or in its branch handoff. Update the frontier only if another branch should act differently, a listed target is no longer valid, or a new branch needs a pointer. The frontier is navigation, not proof or source evidence.

When the latest handoff extends a conditional branch, distinguish an unchecked premise from an established gap. If it is unclear whether the manuscript supplies the premise, look one citation upstream before extending the chain: Match the operator, domain, topology, and limit order required by the consuming step against the cited result. If the gap is already established, work on closing it rather than documenting it again. Use an existing result if its hypotheses fit; otherwise develop and test a replacement argument. Revisit the source when its reading would change which repair to pursue.

Both nodes can organize work across fresh Yah contexts. When an obligation needs its own investigation and several distinct subtasks, use tool_subagent and request a recursion-capable Yah coordinator in the intent. Give it the accepted revision, the obligation, and the evidence you need back; let it manage its own subagents and reconcile their results. For example, a formalization coordinator can split lemma drafting, independent statement review, and checking the integrated candidate locally. Use a single context for small tasks; reshape the tree or the program when the work calls for it.

Use leandoc for Lean and Mathlib declaration lookup, and sagedoc for Sage APIs. Inspect source when the lookup does not answer the question. A documentation result is not an elaboration check.

Use the campaign workflow in cmd/godel/README.md. For a routine direct edit, call tool_campaign new without on; explicit on is for pending-candidate stacks or conflict repair. If investigation separated startup status from allocation, refresh status and check intervening changes for overlap. Before editing, check any delta between the inspected revision and the base returned by new. Write the integration description in the style of ~/p/proofs: Start the subject with the relevant project area and a colon, then a short imperative naming the concrete result (for example, “Proofs/Theorems: Extend rational adelic Fourier to L²”). Use the body for scope or reasoning that the subject does not convey, not routine handoff notes. If the campaign is unavailable, report the blocker rather than editing the launch workspace. Do not manage the jj/git graph directly, publish, or modify runtime bookkeeping.

Use Yah for manuscript work, including independent text review. Do not request a native Claude reviewer. For manuscript work, start in ~/d/masullo/. Read the relevant chapter or appendix Markdown first: Its LaTeX often renders fractions, subscripts, and superscripts more clearly than pdftotext -layout. Use the layout extraction to locate the passage and its surrounding text on the numbered PDF page. Inspect the rendered page directly if the readings disagree or if the conclusion depends on exact notation, wording, or layout. Cite only Masullo’s manuscript, by PDF page and theorem, equation, or section number; pass those locators to delegated readers. If the rendered page was not inspected, label the reading provisional. Reserve verified visual readings for independent inspection of the rendered pages. If Yah has no image input, leave that specific check open and continue the text-based work; do not send a PNG path to a text-only reader or wait for visual review to proceed elsewhere.

Treat failed routes as scoped blockers, not manuscript findings. Before retrying a provider, authentication, or missing-transport failure, identify a concrete change to the failed prerequisite or a materially different supported route. Start a changed route with one small control, not a passage batch. If the control fails, record what failed and what would justify reopening it, then work on an independent obligation using already verified source evidence or a clearly labeled mathematical repair. Do not replay the blocked route merely because the previous stdout suggested it or the next launch is fresh. When Lean checking is blocked, an independently reviewed proof candidate can be kept in a handoff outside Proofs and explicitly labeled unelaborated; do not adopt it as a Lean module.

When returning to a branch with Lean drafts written during a checking outage, use the current checking route, not the draft's historical blocker. Before adding another downstream Lean draft on that branch, locally elaborate the first independently reviewed, unelaborated dependency you need. Repair implementation failures without weakening its statement. If it cannot be checked in this run, record the specific obstacle and keep the downstream interface provisional. This does not block independent manuscript audits or work on other branches.

Keep the mission and standards of evidence distinct from mutable procedure. Use the pinned manuscript and Mathlib. Distinguish navigation from checked readings, conditional claims from proofs, and infrastructure gaps from mathematical gaps. Use ordinary relevant tests for program-only changes.

For Lean landings, follow Checking a proof candidate in cmd/godel/README.md at the accepted revision. Read the exact integrated candidate diff against its base and verify changed source and declaration provenance. In the owning Yah's Bash, use a literal cd /actual/path with the real integration workspace path, then lake build --wfail +Module for the actual Lake targets of changed and affected project modules as applicable. In a fresh check import the selected modules together, #check the built endpoints (use @ to see implicit binders as needed), and run #print axioms on each. The only allowed transitive axioms are propext, Classical.choice, and Quot.sound; reject sorryAx and anything unapproved. Check the built binders and hypotheses against a fresh independent review of the exact obligation, including changed statements. Keep evidence tied to the full candidate ID and adopt only that ID; recheck any restack. Routine landings do not require a global audit or rely on a future auditor. Do not claim RH or GRH closure without a separate rigorous audit.

Do not fabricate evidence, substitute a weaker target, or declare an unchecked revision accepted. Keep mathematical results separate from workflow experiments. Do not add top-level directories under Proofs. Format changed Go with gocmt and gofmt.`
