# Running the manuscript program

Start at **the root of a durable GRH jj workspace**. The workspace must contain this bootstrap and share the owning campaign’s backing repository. A retained, harness-provisioned workspace is suitable; a temporary writer checkout or a separate clone is not. Do not start from old pilot source in the canonical working tree merely because the campaign has advanced `main`: adoption moves the target, not the working files.

```sh
# GRH_LAUNCH_ROOT is the absolute path of that durable workspace.
cd -P "${GRH_LAUNCH_ROOT:?set the durable launch workspace}"
export YAH_CAMPAIGN_TARGET=main   # or the intended local target bookmark
printf '%s\n' 'Pursue the manuscript mission from the evidence already here.' | go run ./cmd/godel
```

Use Linux with `/proc`, writable executable temporary storage, `jj`, `git`, `tar`, the Go toolchain and module dependencies, an authenticated `yah` on `PATH`, and a working user systemd manager. Both nodes start headless Yah at the **workspace root** with `-yolo`, `-effort high`, and `-append` (mission and role instructions in addition to Yah’s standard instructions).

On each no-flag entry, the bootstrap reads the exact local target (`main` by default) without snapshotting the launch checkout. It checks agreement with the backing Git branch, exports that commit with `git archive`, and builds `./cmd/godel` in a clean temporary tree. Build inputs must be present in the archive or available as Go dependencies; untracked files, submodule contents and neighboring modules aren’t copied. An absent or ambiguous target, jj/Git disagreement, or failed build stops the launch rather than falling back to stale code. Scratch is removed before the accepted executable takes over the process. Its cwd and streams stay unchanged; it must not rely on the temporary source tree or binary pathname persisting.

The Gödel runner changes to the launch workspace's stable `cmd/godel` directory for registration, not the temporary build directory. Work receives the objective on stdin; improvement receives run context, including the registered source path and run record. When `Params.Loop` continues, the driver replaces itself with `go run .` **there**, passing work stdout as stdin. This starts the next iteration after work and improvement finish; neither node calls the driver. That launch resolves the target again, so a checked and adopted edit runs without refreshing the checkout. `go run ./cmd/godel </dev/null` from the same workspace root uses the latest nonblank Gödel handoff. Keep the launch path intact between runs. Use a time limit for unattended work and send INT/TERM to the job (process group), not just its outer `go run` wrapper. The old pilot attempt allowance does not meter this loop.

Work reports an observable result or stall; improvement can test and change any part of the program, including itself. Inspect the campaign’s **accepted revision** and Gödel run history, not the files at the registered source path, to see what changed. Since only work stdout becomes the next input, an improver that lands proof or source work records its result and next step in the accepted frontier and linked handoff. Reconcile an inherited suggestion with that evidence before acting on it: Skip an exact obligation already closed, but preserve any remaining scope. A narrow frontier is not the manuscript's scope: When warranted, use it alongside a targeted reading in another chapter to identify a tractable source claim or a premise shared by several branches. Keep the existing runnable work visible. Start edits in `tool_campaign new` or a campaign writer workspace based on accepted source. Integrate, check, and adopt through the owning campaign; there is no routine parent/operator handoff. If campaign tools are unavailable, report the blocker. Do not manage the graph directly or publish changes. Gödel v0.0.5 records work failures and can run improvement, but does not automatically relaunch after process failure. Neither adoption nor model output certifies a mathematical result: Check proof candidates locally as described below. Program-only changes need relevant ordinary tests.

## Checking a proof candidate

Use this machine. Have a second agent review the proposed statement against the mathematical obligation. Elaborate drafts in the writer workspace, then use `tool_campaign integrate`. From the **workspace returned by integration**, pass the full candidate ID, every changed Lean module, and the independently reviewed endpoints to:

```sh
go run ./cmd/godel audit-local <full-candidate-id> Lemmas.Example -- Masullo.exampleLemma
```

The command compares `Proofs/` and the pinned Lake inputs on disk with the candidate, runs `lake --wfail build Proofs`, replays each listed module in a separate `leanchecker` process, and checks their axioms and endpoint provenance in Lean. It repeats the input comparison before reporting success. It uses the workspace's trusted local Lake dependencies, and neither contacts a proof worker nor adopts the candidate. Run it with a time bound and keep its output. The check covers the modules named on the command line; it does not select them or certify that a declaration has the intended statement.

Inspect the reviewed statement in the built environment (`import Lemmas.Example` and `#check Masullo.exampleLemma` via `lake env lean --stdin`), and inspect changed Lean sources for new axioms, proof placeholders, or unsafe substitutes. The theorem must be proved in the project and depend only on `propext`, `Classical.choice`, and `Quot.sound`. Record the candidate ID, declarations, and results. Adopt that exact ID only on success. If a proof needs repair, edit in a writer workspace, integrate, and repeat the checks on the new candidate. The older `cmd/godel check` uses a designated remote worker and is not part of this workflow.

### Recovering a checked but unadopted proof

A stale adoption means the target moved, not that the proof failed. Read `tool_campaign status` again and reconcile the checked patch with the new accepted tree. If it is still needed, integrate the registered output against the fresh base. If the base moves again before integration resolves it, refresh status before choosing the base. A commit readable in jj is not necessarily a registered output in this campaign. If the prior output is not in `status` with `verbose=true`, inspect the old candidate's patch against its parent and restore only the needed changes in a new direct workspace on the current base. Compare the resulting patch with the reviewed one; do not overwrite later work or change the graph manually.

For a restack with identical Lean build inputs, reuse the trusted project build cache from the finished audit rather than starting cold. From the repository root, use the full old and new candidate IDs and the workspace paths returned by integration:

```sh
changed=$(jj --ignore-working-copy diff --summary \
  --from "commit_id(\"$OLD\")" --to "commit_id(\"$NEW\")" -- \
  Proofs lakefile.toml lake-manifest.json lean-toolchain) &&
test -z "$changed" &&
test ! -e "$NEW_WS/.lake/build" &&
cp -a --reflink=auto "$OLD_WS/.lake/build" "$NEW_WS/.lake/build"
```

Only seed from a finished local audit under the same trusted toolchain and Lake dependencies. If the comparison is nonempty or the trusted cache is unavailable, use the ordinary audit. In either case, run `audit-local` and inspect the endpoint types in the new integration workspace before adoption. Reusing build artifacts saves elaboration time; it does not transfer an audit verdict to a new candidate.

## Bounded pilot

From `cmd/godel`, explicit pilot flags bypass the accepted-source bootstrap and select the earlier passage workflow documented in [the pilot handoff](../../.godel/README.md). Its scheduler is an available tool, not the outer control loop. Its `GRH_CAMPAIGN_ADAPTER` is a transport for authorized operations, not a separate grant of authority.
