# Proof-breadth companion

**Not run; not automatically scheduled.** This independent Gödel loop complements the [main manuscript program](../../../cmd/godel/README.md) without scheduling or editing it. Each iteration chooses one substantive Masullo claim to test, looking for neglected passages and missing cases or generality. The selector returns `AUDIT` or `PRODUCE` and a brief; the selected Yah worker receives that brief in its prompt and the unchanged input on stdin. Invalid selection runs no worker and ends the loop with an error. The worker's handoff, not the improver's report, feeds the next iteration.

Both programs share the proof library and notes through the owning campaign. The companion uses the [same local proof checks and stale-candidate recovery](../../../cmd/godel/README.md#checking-a-proof-candidate). Its separate improver reviews its own runs and may change only the companion's selection or procedure.

## Later manual launch

Use the root of a **durable GRH jj workspace** in the owning campaign, with `cmd/companion` and its accepted-source bootstrap present in the checkout and accepted target. Use the same tooling, Yah authentication, and user systemd prerequisites as the main program.

```sh
cd -P "${GRH_LAUNCH_ROOT:?set the durable launch workspace}"
export YAH_CAMPAIGN_TARGET=main  # or the intended local target bookmark
printf '%s\n' 'Test an uncovered claim or case in Masullo’s manuscript.' | go run ./cmd/companion
```

Gödel registers the durable `cmd/companion` path, so history under `$HOME/.godel` is separate from `cmd/godel` although all Yah nodes run at the repository root. Each loop re-enters the accepted-source bootstrap. Use a time bound and send INT or TERM to the job's process group to stop. Offline routing tests (`go test ./cmd/companion`) inspect actual `Next` decisions without launching Yah or the loop.
