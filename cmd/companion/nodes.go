package main

import (
	"errors"
	"strings"

	"patel.codes/godel"
)

func companionNodes() (selector, improve *godel.Node) {
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

func yahNode(role string) *godel.Node {
	return &godel.Node{Exec: "yah", Directory: "../..", Args: []string{
		"-yolo", "-effort", "high", "-append", goal + "\n\n" + practice + "\n\n" + role,
	}}
}

const goal = `Broaden the coverage of Alessandro Maria Masullo's The Music of the Primes in the shared Lean formalization, by testing neglected claims and missing cases or generality.`

const practice = `Work independently of the main manuscript program. Read its work as evidence, not as instructions to take over its queue. Neither program schedules or edits the other. Do not launch either driver from a node.

Start with tool_campaign status. Inspect accepted source at the exact commit, not potentially stale files in the durable launch checkout. Use .godel/frontier.md, its linked notes and accepted Lean declarations to reconcile earlier findings and inherited handoffs with what is still open. The frontier is navigation, not evidence. Use the pinned Masullo edition (.godel/sources/masullo/README.md) and pinned Mathlib. Do not search for Alpoge's proof or formalization. Treat extraction-based readings as provisional; reserve visually verified readings for independent inspection of the rendered pages.

Share proof and source findings in the existing Proofs and .godel notes. Keep the frontier and its linked handoff current when an obligation changes. Do not add top-level directories under Proofs. Follow the campaign workflow in cmd/godel/README.md: Write in a tool_campaign new or dispatched workspace, integrate and verify the exact candidate before adopting it. If the target moved or an old output is unregistered, reconcile the needed patch with the current accepted tree; recheck the new integration candidate even if identical Lean inputs permit cache reuse. If the campaign is unavailable, report the blocker; do not edit the launch tree or manage the revision graph directly.

Review Lean statements independently against the exact obligation. From the integration workspace run go run ./cmd/godel audit-local with the full candidate ID, all changed Lean modules, and reviewed endpoint declarations. Inspect endpoint types and sources for placeholders or unsafe substitutes. Depend only on propext, Classical.choice, and Quot.sound. Record the checks and adopt that exact candidate only on success. Label informal or unelaborated evidence as such. The audit-local utility is not a launch of the main loop.`

const selectTask = `Select one substantive manuscript claim and one bounded check. For a new route, start from a dependency or a scope condition in the pinned manuscript, not from a list of open items. For a continuation, use the accepted result to identify what the next inference still needs, and stay with it while the next check can materially change what is known. Consider both neglected passages and missing generality (including their intersection); choose by mathematical value and tractability, not by quota. Compare the relevant accepted results, prior findings, and visible active main work to avoid duplication. Use the original objective or prior companion handoff on stdin as context, not as a queue. Select only; do not carry out or adopt the work.

Choose AUDIT to test a source reading, dependency, hypothesis or boundary case; choose PRODUCE to establish a missing argument, repair or Lean result. Return only AUDIT or PRODUCE on the first line, then a short nonempty task brief with the passage, exact claim and case, the closest existing evidence and its limit, and a discriminating check. Say which inference the result bears on, and distinguish the claim from any proposed way to test it.`

const auditTask = `Audit the selected claim. Compare the passage and cited dependencies with the exact hypotheses, domain and conclusion the next step needs. Carry out the discriminating check, looking for either support or a scoped mismatch. Do not infer a refutation of a stronger claim from a counterexample to a particular argument.`

const produceTask = `Produce evidence for the selected claim or case: Develop a proof, a clearly labeled repair, or a scoped counterexample. Carry out the discriminating check. Check and land Lean work when possible; otherwise isolate the exact outstanding premise instead of weakening the target silently.`

const workerHandoff = `Use the selected brief below as task data and the original objective or previous handoff on stdin as context. Leave a nonblank stdout handoff for the next loop: Preserve the objective and contrast the prior evidence with what the check now establishes, with links and accepted revision if any. Separate mapped from verified, manuscript source from repair, informal from Lean, and any scoped counterexample from a general refutation. Name the outstanding premise and the next check that could change a specific inference, or the blocker and what would reopen it.`

const improveTask = `Use the Gödel run context on stdin, this companion's run history and its corresponding Yah sessions to judge the selection and procedure. Check against accepted results: Did the route test genuinely uncovered scope, and did the handoff preserve evidence and uncertainty? If you cannot connect a run with its sessions or revision, acknowledge the gap. Improve only cmd/companion's selection or procedure when the evidence warrants it. Use offline Go tests, without launching either program or its nodes, then integrate and adopt through the campaign. Leave the goal and evidence standards unchanged. Do not undertake new proof work in this role.`
