# Formalize (draft)

This program consumes the [Walk private ledger](../../.godel/walk/README.md) and sends one fresh batch to one Yah coordinator. It does not improve itself or advance Walk. The [coordinator protocol](coordinator.md) defines the future writing, independent review, and adoption workflow. The [receipt directory](../../.godel/formalize/README.md) explains disposition evidence.

## Launch after adoption

From the root of the durable GRH checkout used by Walk, with the program present both there and at the accepted target:

```sh
cd -P "${GRH_LAUNCH_ROOT:?set the durable workspace used by Walk}"
printf '%s\n' 'Formalize substantive passages from the pinned Walk ledger.' |
    YAH_CAMPAIGN_TARGET=main go run ./cmd/formalize
```

Use the prerequisites in [the manuscript program](../godel/README.md). Keep the same canonical checkout path and home as Walk. `accepted.Enter` builds from the exact accepted target, not stale working files. `main` is the default target; use the target whose accepted evidence this Walk's records describe. The launch seed satisfies Gödel but is not authority for work. Stop with INT/TERM sent to the job, not just the outer `go run` wrapper. Keep one instance per canonical command source. Within each run Gödel holds its per-source lock from before selection through the cancellable idle wait, coordinator, and acknowledgment. It releases the lock at the loop's re-exec; it does not lock Walk, the accepted target, or other launch checkouts.

## Selection and restart

The gate reads the canonical private Walk directory by path hash. It observes per-file atomic snapshots, not a transaction across chapters. `open`, `established`, and `refuted` substantive records are eligible; `not_applicable` is not. Order is chapter, then appendix, then Walk's order within each file. Identity includes the edition, chapter, kind, locator, and printed page. The revision is a hash of the canonical whole record, including reviewed dependency evidence, not of the cursor, completion flag, JSON object layout, or accepted tip. Array order and changes to record prose count; the gate cannot infer semantic equivalence. The limit is one (`batchCap`); the request and receipt protocol is keyed for multiple independent assignments.

If no assignment is pending, Go waits ten minutes and rescans (no Yah). On dispatch it writes a fresh mode-0600 request in the system temp directory (`TMPDIR` if set, which must be outside the checkout); the coordinator gets fixed stdin and the new request path. The request is removed by the running process on normal completion or failure. A hard kill can leave a temp file or a running coordinator scope behind; check that the previous coordinator stopped before restarting. The request is never used to recover work. There is no mutable journal or second queue. After a successful run the Go continuation verifies the batch at a fresh accepted tip before letting Gödel loop.

The **accepted target tree** is the durable disposition store. A proof and its receipt land together; restart does not require a model response or local acknowledgment. Invalid or missing receipts do not count. A nonzero exit, cancellation, or a successful process with unresolved assignments stops the run; reconcile the operational blocker and restart with the launch command. Already accepted siblings are retained. A substantive failure or partial landing with intact evidence is not attempted again for the same record merely because of a restart, idle scan, or unrelated accepted movement. A changed Walk record (including refreshed relevant evidence) is automatically eligible; if the recorded retry condition is independently met but Walk has not changed, an operator can arrange explicit retirement of the obsolete receipt through the campaign. Do not edit the live Walk ledger to force a retry.

This deduplicates accepted dispositions, not executions. A race between selection and adoption, an interrupted unlanded attempt, or an external producer that did not use receipts can require reconciliation. The coordinator checks current accepted work before dispatch and again on conflicts; it must not treat a pending candidate as accepted. For Lean outcomes the gate requires accepted evidence revisions and unchanged bytes in the cited Lean files. A change to a cited file triggers reconciliation, not necessarily new proof work. The gate does not check declarations, imported dependencies, or mathematical validity; explicitly retire receipts invalidated in ways these checks cannot see. No exactly-once or cross-checkout lock guarantee is made.

Offline checks: `go test ./cmd/formalize`. These exercise the gate and receipt decisions without launching Yah, starting Gödel, or using the live ledger.
