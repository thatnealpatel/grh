# Independent accepted-history auditor

`cmd/audit` runs a Gödel loop backed by Yah, without self-improvement. It
examines each successive accepted commit, including claims and handoffs later
reverted. Each pass pins the next accepted parent and child; newer accepted
work waits for a later pass. On launch, the first check is immediate. After a
completed review (including accepted publication, if needed), it checks for
the next commit without a scheduled delay. Only when caught up does it wait
ten minutes before polling again. The idle wait is interruptible and starts
no Yah reviewer.
The auditor does not repair proofs, gate producer landings, or certify RH/GRH.

## Launch and restart

After `cmd/audit` is accepted and present in the **durable** GRH workspace,
launch there (not in a campaign session workspace). Choose a **full commit ID**
that is an ancestor of the intended accepted target. For example, use
`daeaa4e3432b2be499c10fb1ee6495911dc765cc` to start *after* the scoped checks
migration, if that is the desired starting boundary:

```sh
printf 'Audit accepted progress.\n' | YAH_CAMPAIGN_TARGET=main go run ./cmd/audit \
    -baseline daeaa4e3432b2be499c10fb1ee6495911dc765cc
```

The baseline explicitly **excludes** earlier history; it is not an audit of
that commit or its ancestors. `accepted.Enter` runs the command from the
accepted source archive. Use the same durable workspace, target and home on
restart. Supply the same seed again, since Gödel needs nonblank input when no
prior final response is available. Omit `-baseline` on restart, or repeat the
original value. Use a normal interrupt to stop; an invalid report, lost tool,
inconsistent accepted pointer, or divergent history stops without granting
coverage for the failed work. Inspect diagnostics and fix the cause before
restarting; do not change the baseline to skip a failure.

## Evidence and findings

The command prints the path to its private `$HOME/.grh-audit-*.json` journal.
Gödel locks the program by durable source directory; the journal is the sole
checkpoint, not Gödel's last response. Go syncs and atomically replaces the
journal. Keep it across restarts: moving/deleting it loses coverage and finding
state. The checkpoint means *examined*, not *proved*. It retains the latest
substantive review and all accepted finding pointers; it does not automatically
mark a finding resolved. Earlier reports may be available through existing
Gödel run records, not a second audit archive. Changes to a finding file at
the current tip do not change the original accepted note at its pinned revision.

A validated finding is recorded as pending **before** publication. Only after
verifying the exact standalone note addition in accepted history does Go
advance to the reviewed target. The handoff is available at
`.godel/audit/<reviewed-commit>.md` and gives the precise issue, evidence and
proposed follow-up. A restart recovers an already accepted note or resumes
publication without rerunning the review. A submitted candidate is not
accepted evidence.
The auditor skips only its own verified note commit, never a later revision
editing it or a producer commit that landed during the pass.

The reviewer requires campaign attachment, access to the pinned Masullo PDF,
and (for Lean-affecting work) exact-revision Yah child workspaces with managed
Lean provisioning. Each Lean review distinguishes the full build, joint import,
scoped kernel replay, and endpoint signatures/provenance/axioms. Go validates
scope and the reported dispositions, not the mathematics or tool transcripts.
The campaign target must expose one linear accepted history and agree in jj
and its backing Git ref. A failed review does not invalidate earlier coverage
or allow later accepted work to pass the failed commit.

Focused offline verification: `go test ./cmd/audit`. The tests use fake
accepted history; they do not run Yah, build Lean, or land a handoff.
