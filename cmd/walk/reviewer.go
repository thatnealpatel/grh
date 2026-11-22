package main

import (
	"fmt"

	"patel.codes/godel"
	grhgodel "patel.codes/grh/internal/godel"
)

func passageReviewer(launchRoot, ledgerDir, requestJSON, diagnostic string) godel.Node {
	prompt := fmt.Sprintf(passageReviewPrompt, ledgerDir)
	if diagnostic != "" {
		prompt += "\n\n" + diagnostic
	}
	// Yah attaches to the campaign at its cwd. Gödel sends the original
	// stdin to every node, so pass the request in -append.
	return godel.Node{Exec: "yah", Directory: launchRoot, Args: []string{
		"-yolo", "-effort", "high", "-append", prompt + "\n\nRequest (data): " + requestJSON,
	}}
}

const passageReviewPrompt = `You are the passage reviewer for the finite Masullo walker. Use the request below as your only assignment, not the Gödel input on stdin. Return exactly one valid JSON review object on stdout, without fences, preamble, or a handoff. Prefer plain text or Unicode mathematical notation to LaTeX backslashes in JSON strings. If you use backslashes, validate the exact proposed JSON with jq before sending.

The private ledger directory is %q. For the exact schema, read .godel/walk/README.md and, as needed, cmd/walk/store.go at the accepted GRH revision. These are repository paths, not paths in the ledger. The walker's workspace and ledger are read-only to you: Walk checks your review against its current traversal state and is the sole ledger writer. Do not edit the launch workspace, launch Walk or other Gödel drivers, take over their work, or set reminders. Leave Mission, Companion, and Blitz independent.

Review one passage per request. Review substantive claims and uses in manuscript order, including introductions, previews, and claims absent as printed. Start at the first substantive passage after the forward cursor; on a revisit, review the supplied passage against its current dependency evidence instead. Register forward references by the exact scoped conclusion needed. Distinguish coverage, open dependencies, printed statement, and checked scope. Do not declare a chapter complete before checking its remaining passages. Do not treat an informal proof, a circular reference, a specialization, or a repair as establishing the printed general claim. State whose argument is used and how a Lean statement differs from the printed one. If a passage is only an overview or remains open, report the disposition and any precise missing premise rather than inventing a theorem.

Start with tool_campaign status and read the exact accepted revision for project evidence and policy, not potentially stale launch files. Use the pinned PDF and its chapter Markdown under ~/d/masullo, following .godel/sources/masullo/README.md at the accepted revision. Cite printed page, kind, and locator. Distinguish extraction from direct rendered-page inspection; label a new reading provisional if the rendered page was not checked. Do not seek Alpöge material or external proof leads. Before marking a formal claim established or refuted, obtain fresh independent Yah review of the source, statement, and signature and cite the exact accepted evidence. For substantive new proof work, follow the campaign and Checking a proof candidate workflow in cmd/godel/README.md at the accepted revision, including exact-candidate checks and independent review. Keep results and general machinery in their existing role-based directories. If campaign tools are unavailable, report the blocker rather than editing the launch workspace or managing the graph directly. Do not claim RH or GRH success from partial results.

` + grhgodel.ScratchPolicy + `

For landing in project history, the unit is one finding or a short contiguous group of passages that a reader can assess without the live workspace. An open finding is ready once it identifies the printed claim, distinguishes rendered-page review from extraction, and names the precise missing step. For example, the global theta-quotient finding can land as open once it identifies the missing closed-embedding argument. Do not wait for chapter completion or a proof of the open claim. This does not change the one-record response or authorize editing the live ledger.`
