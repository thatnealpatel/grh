# Conjecture

From the durable GRH workspace root, run:

```sh
go run ./cmd/conjecture
```

There are no arguments or alternate modes. This runs one bounded investigation,
not a proof search. It needs the usual GRH JJ/Git setup, Yah and its retrieval
services, and Gödel's user systemd manager. The accepted bookmark defaults to
`main` (`YAH_CAMPAIGN_TARGET` can identify another accepted bookmark). Git and JJ
must agree on its exact commit.

The command reads the accepted mission, frontier, obligations, conjectures,
source notes, and Lean sources from Git objects at that commit, not from the
working copy. The selector chooses one line of inquiry or stops. A coordinator
requests and joins three scouts in parallel: OpenAlex for scholarly discovery,
web search for other records and entry points, and `think` for implications and
counterexamples. Up to four distinct leads can get an explicit primary-source
check. The constructor states one claim, and a fresh challenger can stop,
request one targeted repair and rechallenge, or recommend one open or closed
card. A citation snippet or an inaccessible primary text is not verification.

Only a validated card disposition starts the separate Yah publication stage.
It gets a prepared path and complete card with the exact `evidence_revision`.
It uses the ordinary campaign workflow to create a direct workspace, integrate
only the card (and remove its old name for a move), inspect the candidate, and
adopt it. It is instructed to stop if the accepted base has moved. No-change
paths do not start the publisher. There is no remote upload.

## Enforcement and limits

The Go transitions bound the run, check the report envelope, pin the evidence,
and derive card paths from the disposition and slug. Research stages have a
filtered Yah tool set without workspace writes or shell tools. They receive
request-local packets rather than prior conversational history. This setup is
not a filesystem sandbox; the read tool is not confined to the exported files.

The coordinator requests Luna/medium for all three children and is instructed
to dispatch all before waiting. Yah's dispatcher can change child model, effort,
or instructions; a report does not attest the runtime choices or concurrency.
The children share the filtered retrieval tool set, not individually locked
retrieval capabilities. The transition requires three distinct attributed reports
or an explicit scout failure. It does not certify what a report says.

Mathematical identity, quality, and Markdown substance are reviewed by the
challenger, not mechanically proved by the program. Publication uses a trusted
campaign agent; the path/byte scope and candidate inspection are instructions,
not an independent filesystem or diff-enforcement layer. Tests exercise pinned
blob export and scripted Gödel transitions. They do not run the retrieval
services or adopt a live campaign candidate.
