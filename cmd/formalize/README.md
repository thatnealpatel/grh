# Formalize

This program consumes the [Walk private ledger](../../.godel/walk/README.md) in small batches, with one Yah coordinator per batch. It does not improve itself or advance Walk. The [coordinator protocol](coordinator.md) defines the writing, independent review, and adoption workflow. The [receipt directory](../../.godel/formalize/README.md) explains disposition evidence.

## Launch after adoption

From the root of the durable GRH checkout used by Walk, with the program present both there and at the accepted target:

```sh
cd -P "${GRH_LAUNCH_ROOT:?set the durable workspace used by Walk}"
printf '%s\n' 'Formalize substantive passages from the pinned Walk ledger.' |
    YAH_CAMPAIGN_TARGET=main go run ./cmd/formalize
```

Use the prerequisites in [the manuscript program](../godel/README.md). Keep the same canonical checkout path and home as Walk. `accepted.Enter` builds from the exact accepted target, not stale working files. `main` is the default target; use the target whose accepted evidence this Walk's records describe. The launch seed satisfies Gödel but is not authority for work. Stop with INT/TERM sent to the job, not just the outer `go run` wrapper. Keep one instance per canonical command source. Within each run Gödel holds its per-source lock from before selection through the cancellable idle wait, coordinator, and acknowledgment. It does not lock Walk, the accepted target, or other launch checkouts.

## Selection and restart

The gate reads the canonical private Walk directory by path hash. It observes per-file atomic snapshots, not a transaction across chapters. `open`, `established`, and `refuted` substantive records are eligible; `not_applicable` is not. Order is chapter, then appendix, then Walk's order within each file. Identity includes the edition, chapter, kind, locator, and printed page. The revision is a hash of the canonical whole record, including reviewed dependency evidence, not of the cursor, completion flag, JSON object layout, or accepted tip. Array order and changes to record prose count; the gate cannot infer semantic equivalence.

Go makes the oldest pending **proof** primary, or the oldest eligible
**statement** if no proof is pending. It offers up to three other passages,
reserving up to two offers for pending proofs before filling the remaining
places with eligible statements in Walk order. No passage appears twice.
Thus older partial-proof statement work cannot crowd out fresh proofs, and
statement work is available even with a proof backlog. Full proof coverage
or a valid statement disposition suppresses the statement option. A
statement disposition does not retire a proof or its recorded remainder.

The coordinator reads the dependency evidence and likely declarations/files
before selecting at most one near-ready, independent offer. It declines on
overlap, dependence, or uncertainty. The primary and selected offer may be
written and independently reviewed in parallel. One coordinator serializes
final integration, exact checks, and adoption, checking the accepted target
before expensive checks and again before adoption. A replacement candidate
always needs exact checks; earlier source/patch review carries forward only
when the patch and relevant dependencies and source are unchanged.

If no work is pending, Go waits ten minutes and rescans (no Yah). Go creates
a private dispatch directory in the system temp directory (`TMPDIR` if set,
which must be outside the checkout). The coordinator gets fixed stdin, the
fresh mode-0600 request, and a path at which to bind the primary and any
selected offer **before** dispatching writers. This disposable selection is
separate from stdout and is never inferred from which receipts landed. On
successful coordinator exit, Go validates it and checks just the bound
lanes' receipts at a fresh accepted tip. Missing or invalid selection or
unresolved selected work stops continuation. After acknowledgment Gödel
relaunches the program to plan the next batch. Bound the seven-day worker's
lifetime at launch; do not wrap it in an automatic error-retry loop.

Go removes the dispatch files on completion or failure. A hard kill can
leave them or a running coordinator scope behind; check that the previous
coordinator stopped before restarting. Restart ignores the old dispatch
files and model replies. There is no mutable journal or second queue.

The **accepted target tree** is the durable disposition store. Each proof or statement disposition has its own receipt; a new Lean artifact and its receipt land together. Restart does not require a model response or local acknowledgment. Invalid or missing receipts do not count. A nonzero exit, cancellation, or a successful process with invalid selection or unresolved selected assignments stops the run; reconcile the operational blocker and restart with the launch command. Already accepted siblings are retained. A substantive proof failure, partial landing with intact evidence, or statement blocker is not attempted again in its lane for the same record merely because of a restart, idle scan, or unrelated accepted movement. A partial proof keeps its finding and retry condition even after statement work. A changed Walk record (including refreshed relevant evidence) gets a new revision and new receipt paths under the same selection rules; if the recorded retry condition is independently met but Walk has not changed, an operator can arrange explicit retirement of the obsolete receipt through the campaign. Do not edit the live Walk ledger to force a retry.

This deduplicates accepted dispositions, not executions. A race between selection and adoption, an interrupted unlanded attempt, or an external producer that did not use receipts can require reconciliation. The coordinator checks current accepted work before dispatch and at the landing gate; it must not treat a pending candidate as accepted. For Lean outcomes the gate requires accepted evidence revisions and unchanged bytes in the cited Lean files. A change to a cited file triggers reconciliation, not necessarily new Lean work. A checked statement is a named `def … : Prop := …` over the real definitions, with exact-candidate Lean checks and independent rendered-source review. The gate does not itself run Lean, check declarations or imported dependencies, or certify source fidelity or mathematical validity; explicitly retire receipts invalidated in ways these checks cannot see. No exactly-once or cross-checkout lock guarantee is made.

Evaluate throughput as faithful checked statements per wall hour and
printed proofs per wall hour, separately. Count only work that actually
establishes the respective result, not blocked or duplicate receipts or
partial proofs as full printed proofs. Include coordination and stale
recheck time in elapsed time and account for repeated exact checks after
stale candidates when comparing runs. Receipt count is not throughput; no
telemetry is added.

Offline checks: `go test -count=1 ./cmd/formalize`. These exercise planning,
selection, and receipt/restart decisions without launching Yah, starting
Gödel, using the live ledger, or observing real landing throughput.
