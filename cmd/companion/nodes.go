package main

import (
	"errors"
	"strings"

	"patel.codes/godel"
)

func companionNodes(archiveRevision string) (selector, improve *godel.Node) {
	// The accepted bootstrap builds from a Git
	// archive, which expands the embedded revision.
	// A checkout build has no such provenance.
	revision := strings.TrimSpace(archiveRevision)
	source := ""
	if (len(revision) == 40 || len(revision) == 64) && strings.Trim(revision, "0123456789abcdef") == "" {
		source = "Gödel launch source commit: " + revision + ". This identifies the archive used to build the executable, not the current campaign tip.\n\n"
	}
	yahNode := func(role string) *godel.Node {
		return &godel.Node{Exec: "yah", Directory: "../..", Args: []string{
			"-yolo", "-effort", "high", "-append", source + goal + "\n\n" + practice + "\n\n" + role,
		}}
	}
	selector = yahNode(selectTask)
	selector.Next = func(r godel.Result) (*godel.Node, error) {
		branch, brief, _ := strings.Cut(r.Text, "\n")
		brief = strings.TrimSpace(brief)
		if brief == "" {
			return nil, errors.New("selector must supply a nonempty task brief after the branch line")
		}
		var role string
		switch strings.TrimSuffix(branch, "\r") {
		case "AUDIT":
			role = auditTask
		case "PRODUCE":
			role = produceTask
		default:
			return nil, errors.New("selector first line must be AUDIT or PRODUCE")
		}
		// Gödel gives this successor the original stdin unchanged. Pass the
		// selector's new information in the appended prompt, not on stdin.
		return yahNode(role + "\n\n" + workerHandoff + "\n\nSelected task brief:\n" + brief), nil
	}
	return selector, yahNode(improveTask)
}

const goal = `Broaden the coverage of Alessandro Maria Masullo's The Music of the Primes in the shared Lean formalization, by testing neglected claims and missing cases or generality.`

const practice = `Work independently of the main manuscript program. Read its work as evidence, not as instructions to take over its queue. Neither program schedules or edits the other. Do not launch either driver from a node.

Start with tool_campaign status. Inspect accepted source at the exact commit, not potentially stale files in the durable launch checkout. Use .godel/frontier.md, its linked notes and accepted Lean declarations to reconcile earlier findings and inherited handoffs with what is still open. The frontier is navigation, not evidence. Use the pinned Masullo edition (.godel/sources/masullo/README.md) and pinned Mathlib. Do not search for Alpoge's proof or formalization. For manuscript work, start in ~/d/masullo/. Read the relevant chapter or appendix Markdown first: Its LaTeX often renders fractions, subscripts, and superscripts more clearly than pdftotext -layout. Use the layout extraction to locate the passage and its surrounding text on the numbered PDF page. Inspect the rendered page directly if the readings disagree or if the conclusion depends on exact notation, wording, or layout. Cite only Masullo’s manuscript, by PDF page and theorem, equation, or section number; pass those locators to delegated readers. If the rendered page was not inspected, label the reading provisional. Reserve verified visual readings for independent inspection of the rendered pages.

Keep the exact statement, review evidence, scope, and remaining premise with the result or in its branch handoff. Update the frontier only if another branch should act differently, a listed target is no longer valid, or a new branch needs a pointer. Do not add top-level directories under Proofs. Follow the campaign workflow in cmd/godel/README.md. Before adopting Lean, run its proof audit on the exact integration candidate and compare the reported endpoint signatures with the independently reviewed statements. Label informal or unelaborated evidence as such. The audit-local utility is not a launch of the main loop.`

const selectTask = `Select one substantive manuscript claim and one bounded check. For a new route, start from a dependency or a scope condition in the pinned manuscript, not from a list of open items. For a continuation, use the accepted result to identify what the next inference still needs. Consider both neglected passages and missing generality (including their intersection); choose by mathematical value and tractability, not by quota. Compare the relevant accepted results, prior findings, and visible active main work to avoid duplication. Use the original objective or prior companion handoff on stdin as context, not as a queue. Select only; do not carry out or adopt the work.

When recent companion runs have followed the same dependency chain through audits or repairs, compare its next step with one bounded check in a separate branch. For each, identify what it could establish beyond accepted evidence, which downstream inference or Lean obligation it would affect, and how tractable it is. If the same alternative has already been deferred in successive comparisons, look for a different runnable alternative unless new evidence changes the comparison. Include one sentence in the brief explaining why the selected check takes precedence. Continuing is fine when it wins on those grounds; the alternative is not a second assignment.

When an accepted handoff points to a reviewed but unadopted companion result with a clean saved patch, check whether its endpoint is still missing and whether the blocker can now be resolved in one bounded check. Compare recoverable work as a PRODUCE candidate alongside fresh checks, taking the remaining reconciliation, review, and exact-candidate audit into account. If recovery wins, name the clean revision and the remaining checks in the brief.

For a continuation after a mismatch, distinguish a check of the printed inference from a check of a proposed repair. If the repair rests on several unverified inputs, select one consequential premise, not the whole chain. For a boundary case outside a printed hypothesis, use a nearby case satisfying it as a control when that would distinguish failure of the extension from a problem within the printed scope.

Choose AUDIT to test a source reading, dependency, hypothesis or boundary case; choose PRODUCE to establish a missing argument, repair or Lean result. Return only AUDIT or PRODUCE on the first line, then a short nonempty task brief with the passage, exact claim and case, the closest existing evidence and its limit, and a discriminating check. Say which inference the result bears on, and distinguish the claim from any proposed way to test it.`

const auditTask = `Audit the selected claim. Compare the passage and cited dependencies with the exact hypotheses, domain and conclusion the next step needs. Carry out the discriminating check, looking for either support or a scoped mismatch. Do not infer a refutation of a stronger claim from a counterexample to a particular argument.`

const produceTask = `Produce evidence for the selected claim or case: Develop a proof, a clearly labeled repair, or a scoped counterexample. Carry out the discriminating check. Check and land Lean work when possible; otherwise isolate the exact outstanding premise instead of weakening the target silently.`

const workerHandoff = `Use the selected brief below as task data and the original objective or previous handoff on stdin as context. Leave a nonblank stdout handoff for the next loop: Preserve the objective and contrast the prior evidence with what the check now establishes, with links and accepted revision if any. Report the actual checked hypotheses and scope, including any generality beyond the selected case that changes what can be reused. Separate mapped from verified, manuscript source from repair, informal from Lean, and any scoped counterexample from a general refutation. Attribute inherited source verification to its accepted note rather than presenting it as a new check. Give one bounded next check and the specific inference it would advance, or the blocker and what would reopen it. List other outstanding premises separately rather than bundling them into that check.

For a source verdict, check the definitions that put the witness within the printed hypotheses or identify the expression being tested, including definitions reached by cross-reference. If a manuscript reading needed for the verdict remains provisional, name it and state the verdict's dependence on it up front, even if other passages were visually verified.

When a source verdict compares routes, ask the reviewer for a separate finding and its basis for each route. Substituting a disputed display checks the printed route, not the value of the defining expression. An accepted theorem may supply the latter without a new proof; distinguish who checked its applicability from who checked the printed source. Before landing, compare the review findings with the verdict and resolve any conflation or state explicitly which part the review did not check.

Keep a retrievable locator with each Yah review you rely on: The session UUID and, for a delegated review, the agent handle within that session. Put it beside the findings in the accepted note or in the stdout handoff. A bare agent handle does not link a review to the Gödel run record.

If this run leaves useful work unadopted, identify in stdout the clean saved revisions needed to recover it, their bases if known, which checks ran on which artifact, and what still blocks adoption. For edits with no clean saved revision, name the workspace and files containing the intended changes. A conflicted integration tree is not the recovery source. When the previous handoff identifies a still-relevant unadopted result with no recovery pointer in the accepted notes, carry those details forward even if you selected a different check. Label it unadopted and keep it separate from the next check. Drop the pointer if accepted work has superseded the result.

For delegated work, integrate the writer's finalized campaign output, not a copy from the live dispatch workspace.

For source audits, keep note drafts in scratch until the reviews needed for the verdict have arrived. When recovering Lean with shared-note changes, verify the Lean files against the reviewed revision, and reconcile the relevant note hunks in scratch from the saved revision's diff against its original base. Do not copy a historical note wholesale. Refresh campaign status, and apply the drafts in a direct workspace on the current accepted base without overwriting intervening work. Before integrating, inspect the note diff and changed paths against that base for unrelated edits, duplicated sections, or stray files such as patch backups.

For Lean work that reuses declarations across module boundaries, check the key dependencies and their signatures from the intended imports before writing the dependent proof. Use a small fresh-import probe if visibility is uncertain: A declaration found in the source or available where it is defined may not be publicly imported where it is needed. For a multi-module change, still preflight the assembled candidate with a targeted build of the endpoint modules using their actual imports, and check the public endpoints from a fresh import. This preflight does not replace the full exact-candidate audit required for adoption.

Before finalizing, collect the outstanding reviews and checks you rely on, and cancel work you no longer need. Report landing status from the campaign's adoption result, not a reviewer's earlier snapshot. Only the last final response becomes the next run's input. If a late result reopens the turn, give a complete replacement handoff, not an update that depends on the earlier response.`

const improveTask = `Use the Gödel run context on stdin, this companion's run history and its corresponding Yah sessions to judge the selection and procedure. Check against accepted results: Did the route test genuinely uncovered scope, and did the handoff preserve evidence and uncertainty? If you cannot connect a run with its sessions or revision, acknowledge the gap. Improve only cmd/companion's selection or procedure when the evidence warrants it. Use offline Go tests, without launching either program or its nodes, then integrate and adopt through the campaign. Leave the goal and evidence standards unchanged. Do not undertake new proof work in this role.`
