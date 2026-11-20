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

Work reports an observable result or stall; improvement can test and change any part of the program, including itself. Inspect the campaign’s **accepted revision** and Gödel run history, not the files at the registered source path, to see what changed. Start edits in `tool_campaign new` or a campaign writer workspace based on accepted source. Integrate, check, and adopt through the owning campaign; there is no routine parent/operator handoff. If campaign tools are unavailable, report the blocker. Do not manage the graph directly or publish changes. Gödel v0.0.5 records work failures and can run improvement, but does not automatically relaunch after process failure. Neither adoption nor model output certifies a mathematical result: Lean builds and audits require the designated proof worker. Program-only changes need relevant ordinary tests.

From `cmd/godel`, explicit pilot flags bypass the accepted-source bootstrap and select the earlier passage workflow documented in [the pilot handoff](../../.godel/README.md). Its scheduler is an available tool, not the outer control loop. Its `GRH_CAMPAIGN_ADAPTER` is a transport for authorized operations, not a separate grant of authority.
