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

Use these checks for routine proof landings. Elaborate the assembled
endpoint module with its intended imports and built supporting modules,
not just the helper proofs in scratch. In a split proof, do this as soon
as the supporting outputs are available together. If that first happens
at integration, the required candidate build below is the first check.
Neither a writer build nor a passing helper establishes the integrated
endpoint.

1. Read the exact integrated candidate diff against the base returned by `tool_campaign integrate`. Verify that the patch matches the intended work and that the workspace sources and pinned Lean/Lake inputs are those of the candidate. Inspect changed Lean source for proof placeholders, new axioms, or unsafe substitutes. Trace the intended declarations to their defining project modules and distinguish manuscript steps from repairs against the pinned source.
2. Use the owning Yah's Bash in the **integration workspace**, not the writer or durable launch checkout. Start the command with a literal `cd /actual/path`, replacing `/actual/path` with the real absolute path returned by integration, not a shell variable. Build the changed and affected project modules as applicable with `lake build --wfail +Module`. If the writer checked the assembled endpoint, start from its tested target list and reconcile it with the exact candidate. Verify targets against the defining source paths, not inferred names: For example, `Proofs/Lemmas/AddSubgroupCharIntegral.lean` is `+Lemmas.AddSubgroupCharIntegral`, not `+Proofs.Lemmas.AddSubgroupCharIntegral`. Include the modules defining the endpoints and affected importers when relevant; pass multiple targets to the build as needed.
3. From that same workspace in the owning Yah's Bash, run a fresh scratch check with `lake env lean` on the scratch file. Import the selected modules **together** in that file. Run `#check` on each intended built declaration and inspect its binders and hypotheses (use `@` to expose implicit arguments when needed). Run `#print axioms` on each declaration. Only `propext`, `Classical.choice`, and `Quot.sound` are allowed transitively. Reject `sorryAx` or any unknown or unapproved axiom. For example, a check importing one selected module would contain:

   ```lean
   import Lemmas.AddSubgroupCharIntegral

   #check @Masullo.addSubgroup_integral_star_char
   #print axioms Masullo.addSubgroup_integral_star_char
   ```

   Lean can wrap an axiom list across lines. Read the complete report
   for every expected declaration. If checking mechanically, prefer
   `lake env lean --json`: Each diagnostic's `data` contains the entire
   message, including any newlines. Leave `pp.universes` off for
   `#print axioms` if matching names exactly: Enabling it can print
   universe suffixes on allowed names. Match the expected declaration
   names, require one report per name, and check every axiom in each list.
   When matching the signature diagnostic from `#check @Name`, allow its
   leading `@`; the separate axiom report still names `Name` without it.
   A count of lines containing `depends on axioms:` is not a verdict.

4. Obtain a fresh independent Yah review of the intended statements against the exact mathematical obligation, including any added endpoint or changed statement. Give the reviewer fixed statement text or an exact revision and the manuscript locators. For a statement review in parallel with elaboration, assign the build to the owner; the reviewer should not build a moving writer workspace. Compare the built signatures, including assumptions and scope, with the independently reviewed statements. A familiar declaration name, clean axiom report, or successful build cannot establish that the built statement is the right one. If a statement changes after review, send that statement back for independent review.
5. Keep the full candidate ID and base, reviewed declarations, build and import results, built signatures, axiom reports, and source and independent review evidence (or their durable references). In the accepted branch handoff, point to the **owning** check session as well as any writer checks. Put that session ID in the handoff before integration if the checks are still pending, and record the full candidate ID, check results, and adoption in that session. This avoids changing the checked candidate merely to insert its own ID. Adopt only that exact checked ID, and report whether adoption succeeded. If a proof needs repair, edit in a writer workspace and integrate again. A restack is a new candidate: Repeat the landing checks and get independent review of any changed statement.

A full-project audit, all-project joint import, and separate kernel replay are not routine landing gates. Continuous rigorous `cmd/audit` is deferred; do not assume any future auditor has covered a result. Do not claim RH or GRH closure without a separate rigorous audit. Keep old per-revision audit logs as historical evidence for their stated revisions, not as instructions or checks for new candidates.

If a candidate was integrated directly on the accepted target and a
concurrent landing may have moved it, prepare the scoped checks first,
then compare its base with one fresh `tool_campaign status` immediately
before starting the build. If the base has already been superseded, use
the recovery steps below instead. This is an optional preflight, not
polling or a new landing check. It does not apply to an intentional
stack on a pending parent and cannot prevent a later stale adoption.

### Integrating a direct edit

For a routine edit on accepted source, call `tool_campaign new` without
`on`. The campaign selects the current accepted base at allocation. If
investigation separated the initial `status` from allocation, refresh
status and check intervening changes for overlap. Before editing, compare
the base returned by `new` with the revision you inspected. If it has
moved again, check that delta too. Reserve explicit `on` for deliberate
pending-candidate stacks and conflict repair.

If allocation fails with `unknown integration candidate`, stop repository
edits and use one read-only `status` check to distinguish an observed
move from a rejection with no observed move. Do not retry the same hash.
Leaving `on` unset avoids passing a superseded accepted hash; it does not
prevent unrelated setup failures or a later stale adoption.

Once the edit is ready, call `tool_campaign integrate` with `description`
but without `on` or `outputs`. The campaign finalizes the direct work and
integrates it on the current accepted target. Check the returned base
and patch before running the landing checks or tests, especially if another
campaign has advanced the target. Passing the old accepted hash as
`on` after the target moves can be rejected as an unknown integration
candidate. A superseded accepted commit is not a pending candidate.
Explicit pending-candidate stacks and conflict repair use the campaign
tool's separate `on` and Change-Id rules.

### Recovering a checked but unadopted proof

After a conflict, stale adoption, or ambiguous error, inspect `tool_campaign status` and the current accepted source. Recover only what is still needed.

- **Stale adoption:** The candidate did not land. If it is still pending on its intended parent, land the parent through its normal checks, then retry the same child without rebuilding it only if the candidate ID is unchanged and its evidence meets the landing checks above. If the base or parent was superseded, reconcile the needed changes with its successor. Integrate the registered outputs on the intended base; do not replay a child alone on accepted if it still needs an unlanded parent's changes. If an output is readable in jj but no longer registered in this campaign (`status` with `verbose=true`), restore the needed changes from its clean patch in a fresh workspace on the intended base.
- **Content conflict:** Replaying the same outputs on the same base will not resolve the conflict. Even if the outputs are registered, open a fresh direct workspace on the intended base: Use the pending parent if the change still depends on it, or the current accepted revision otherwise. Compare the clean saved outputs with their original bases and reconcile the intended changes with intervening work. Do not use the conflicted integration tree as the source of the patch.

For any replacement integration candidate, compare its exact diff against the new base with the reviewed work, then repeat the proof landing checks on that candidate. Have any added endpoints or changed statements independently reviewed. An old handoff's audit or build-cache directions do not override this recipe.

For a docs-only or other non-Lean restack, you can seed the replacement
workspace's Lake build cache from your previous checked candidate if
its artifacts are still present. Check both source directories before
copying; an earlier check session is not a guarantee that its cache
is available in a fresh invocation. If they are absent, proceed with
the normal Lake build. First verify that the Lean source tree, Lean/Lake
inputs, and build environment are unchanged between the two candidates.
If checking the tracked input delta mechanically, use
`jj --ignore-working-copy diff --from OLD --to NEW --name-only -- PATHS`
from the launch root, with the two exact candidate commits and the Lean
source and pinned input paths. Require command success and empty stdout.
`--stat` prints a summary even when nothing changed, and empty stdout
from a failed command is not an identity check. Still read the new
candidate's diff against its own base and verify its workspace inputs.
From the replacement workspace, copy the artifact directories **into**
its existing build directory:

```sh
# Set previous to the absolute path of the checked integration workspace.
mkdir -p .lake/build &&
  cp -a --reflink=auto "${previous:?set the old workspace}/.lake/build/"{lib,ir} .lake/build/
```

Copying the whole `build` directory onto an existing one nests it at
`.lake/build/build`, where Lake does not look. This only provides cached
inputs to the replacement's `lake build --wfail`. Run that build and the
fresh joint import from the replacement workspace; do not reuse a verdict
or skip the source and statement checks. If useful, compare the fresh
report with the prior report already in the transcript, identifying both
full candidate IDs and recording the comparison result.

### Compatibility for pinned callers

The designated remote worker check remains available for pinned callers, not as a routine landing gate. From the repository root, run `go run ./cmd/godel check <full-commit-id> <declaration> [<declaration> ...]`.
