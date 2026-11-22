# Running the manuscript program

Start at **the root of a durable GRH jj workspace**. The workspace must contain this bootstrap and share the owning campaign’s backing repository. A retained, harness-provisioned workspace is suitable; a temporary writer checkout or a separate clone is not. Adoption advances the target, not the working files.

```sh
# GRH_LAUNCH_ROOT is the absolute path of that durable workspace.
cd -P "${GRH_LAUNCH_ROOT:?set the durable launch workspace}"
export YAH_CAMPAIGN_TARGET=main   # or the intended local target bookmark
printf '%s\n' 'Pursue the manuscript mission from the evidence already here.' | go run ./cmd/godel
```

Use Linux with `/proc`, writable executable temporary storage, `jj`, `git`, `tar`, the Go toolchain and module dependencies, an authenticated `yah` on `PATH`, and a working user systemd manager. Both nodes start headless Yah at the **workspace root** with `-yolo`, `-effort high`, and `-append` (mission and role instructions in addition to Yah’s standard instructions).

On each no-flag entry, the bootstrap reads the exact local target (`main` by default) without snapshotting the launch checkout. It checks agreement with the backing Git branch, exports that commit with `git archive`, and builds `./cmd/godel` in a clean temporary tree. Build inputs must be present in the archive or available as Go dependencies; untracked files, submodule contents and neighboring modules aren’t copied. An absent or ambiguous target, jj/Git disagreement, or failed build stops the launch rather than falling back to stale code. Scratch is removed before the accepted executable takes over the process. Its cwd and streams stay unchanged; it must not rely on the temporary source tree or binary pathname persisting.

Both Yah nodes record `Gödel launch source commit:` in the session's
`runtime_baseline.inference.system_prompt`. The value is expanded by
`git archive` and embedded in the accepted executable, so it also works
when the stable workspace still runs an older bootstrap. Use it to recover
the `cmd/godel` tree that actually made a decision; use campaign status
separately to find the proof tree available to that node. Older sessions
lack the marker, but the same baseline contains their actual prompt.

The Gödel runner changes to the launch workspace's stable `cmd/godel` directory for registration, not the temporary build directory. Work receives the objective on stdin; improvement receives run context, including the registered source path and run record. When `Params.Loop` continues, the driver replaces itself with `go run .` **there**, passing work stdout as stdin. This starts the next iteration after work and improvement finish; neither node calls the driver. That launch resolves the target again, so a checked and adopted edit runs without refreshing the checkout. `go run ./cmd/godel </dev/null` from the same workspace root uses the latest nonblank Gödel handoff. Keep the launch path intact between runs. Use a time limit for unattended work and send INT/TERM to the job (process group), not just its outer `go run` wrapper.

Work reports an observable result or stall; improvement can test and change any part of the program, including itself. Inspect the campaign’s **accepted revision** and Gödel run history, not the files at the registered source path, to see what changed. Since only work stdout becomes the next input, an improver that lands proof or source work leaves the checked outcome, remaining scope, and runnable successor with the accepted result or in its branch handoff. Check what landed since the handoff before acting on an inherited suggestion: Skip an exact obligation already closed, but preserve any remaining scope. Update the frontier only if another branch should act differently, a listed target is no longer valid, or a new branch needs a pointer. A narrow frontier is not the manuscript's scope: When warranted, use it alongside a targeted reading in another chapter to identify a tractable source claim or a premise shared by several branches. Keep the existing runnable work visible. Start edits in `tool_campaign new` or a campaign writer workspace based on accepted source. For delegated work, integrate the finalized writer output. Inspect the integrated change, check it, and adopt that exact candidate. A successful, non-stale adoption result confirms landing; no second status or contents check is needed. If campaign tools are unavailable, report the blocker. Do not manage the graph directly or publish changes. Gödel v0.0.5 records work failures and can run improvement, but does not automatically relaunch after process failure. Neither adoption nor model output certifies a mathematical result: Check proof candidates locally as described below. Program-only changes need relevant ordinary tests.

## Checking a proof candidate

Use this machine. Have a second agent review the proposed statement against the mathematical obligation. Elaborate drafts in the writer workspace, then use `tool_campaign integrate`. From the **workspace returned by integration**, pass the full candidate ID, every changed Lean module, and the independently reviewed endpoints to:

```sh
go run ./cmd/godel audit-local <full-candidate-id> Lemmas.Example -- Masullo.exampleLemma
```

The command compares `Proofs/` and the pinned Lake inputs on disk with the candidate, runs `lake --wfail build Proofs`, replays each listed module in a separate `leanchecker` process, and checks their axioms and endpoint provenance in Lean. It reports each requested declaration's built signature alongside its axiom report. It repeats the input comparison before reporting success. It uses the workspace's trusted local Lake dependencies, and neither contacts a proof worker nor adopts the candidate. Run it with a time bound and keep its output. The check covers the modules named on the command line; it does not select them or certify that a declaration has the intended statement.

Compare the built signatures in the audit output with the independently reviewed statements, and inspect changed Lean sources for new axioms, proof placeholders, or unsafe substitutes. The theorem must be proved in the project and depend only on `propext`, `Classical.choice`, and `Quot.sound`. Record the candidate ID, declarations, and results. Adopt that exact ID only on success. If a proof needs repair, edit in a writer workspace, integrate, and repeat the checks on the new candidate. The older `cmd/godel check` uses a designated remote worker and is not part of this workflow.

### Integrating a direct edit

If investigation separated the initial `tool_campaign status` from
workspace allocation, refresh status just before `tool_campaign new`.
If the accepted tip moved, review the intervening changes for overlap
before opening on the new tip. If allocation fails with `unknown
integration candidate`, stop repository edits and use a read-only
status check to distinguish an observed target move from a rejection
with no observed move. Do not keep retrying the same hash. This narrows
the setup race; it does not remove it.

Once the edit is ready, call `tool_campaign integrate` with `description`
but without `on` or `outputs`. The campaign finalizes the direct work and
integrates it on the current accepted target. Check the returned base
and patch before running the audit or tests, especially if another
campaign has advanced the target. Passing the old accepted hash as
`on` after the target moves can be rejected as an unknown integration
candidate. A superseded accepted commit is not a pending candidate.
Explicit pending-candidate stacks and conflict repair use the campaign
tool's separate `on` and Change-Id rules.

### Recovering a checked but unadopted proof

After a conflict, stale adoption, or ambiguous error, inspect `tool_campaign status` and the current accepted source. Recover only what is still needed.

- **Stale adoption:** The candidate did not land. If it is still pending on its intended parent, land the parent through its normal checks, then retry the same audited child without rebuilding it. If the base or parent was superseded, reconcile the needed changes with its successor. Integrate the registered outputs on the intended base; do not replay a child alone on accepted if it still needs an unlanded parent's changes. If an output is readable in jj but no longer registered in this campaign (`status` with `verbose=true`), restore the needed changes from its clean patch in a fresh workspace on the intended base.
- **Content conflict:** Replaying the same outputs on the same base will not resolve the conflict. Even if the outputs are registered, open a fresh direct workspace on the intended base: Use the pending parent if the change still depends on it, or the current accepted revision otherwise. Compare the clean saved outputs with their original bases and reconcile the intended changes with intervening work. Do not use the conflicted integration tree as the source of the patch.

For any new integration candidate, compare its patch with the reviewed work. Have any changed statement independently reviewed and audit that exact candidate before adoption.

For a restack with identical Lean build inputs, reuse the trusted project build cache from the finished audit rather than starting cold. From the repository root, use the full old and new candidate IDs and the workspace paths returned by integration:

```sh
changed=$(jj --ignore-working-copy diff --summary \
  --from "commit_id(\"$OLD\")" --to "commit_id(\"$NEW\")" -- \
  Proofs lakefile.toml lake-manifest.json lean-toolchain) &&
test -z "$changed" &&
test ! -e "$NEW_WS/.lake/build" &&
cp -a --reflink=auto "$OLD_WS/.lake/build" "$NEW_WS/.lake/build"
```

Only seed from a finished local audit under the same trusted toolchain and Lake dependencies. If the comparison is nonempty or the trusted cache is unavailable, use the ordinary audit. In either case, run `audit-local` in the new integration workspace and inspect the endpoint signatures it reports before adoption. Reusing build artifacts saves elaboration time; it does not transfer an audit verdict to a new candidate.
