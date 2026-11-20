# Running the manuscript program

Start from `cmd/godel` in the owning campaign’s canonical writable checkout. Run from an environment that allows launching Yah subprocesses; a harness that blocks nested Yah launches cannot run this loop.

```sh
printf '%s\n' 'Pursue the manuscript mission from the evidence already here.' | go run .
```

The setup needs an authenticated `yah` on `PATH` and a user systemd manager. Both nodes run headless Yah at the checkout root, where Yah discovers the campaign. They use `-yolo` for editing and campaign tools, `-effort high`, and `-append` to add mission and role instructions without replacing Yah’s standard instructions. If Yah cannot infer the campaign target, set `YAH_CAMPAIGN_TARGET` to the intended target (normally `main`).

Gödel sends the operator objective (or preceding work handoff) to the work node on stdin, and sends the improver the actual run context on stdin, including the live source directory and run record. Gödel rebuilds and relaunches `go run .` from `cmd/godel` in the same checkout with the work node’s stdout as stdin. On a subsequent launch from the same directory, `go run . </dev/null` uses Gödel’s most recent nonblank handoff. Use an external time limit for an unattended experiment; the shell can send TERM to stop it. The mission loop is not metered by the old pilot's attempt allowance.

Both nodes can edit the program, including their own definitions. A work node reports an observable result or a stall, not just a next-step recommendation. The improver can use earlier run records to compare attempts, change the method, and test a repair. Work failures are recorded and can receive improvement, but Gödel v0.0.5 does not automatically relaunch after a process failure. Inspect the live checkout and run history to see what actually changed. Neither a self-edit nor a model's success report certifies a mathematical result.

The assistant and both manuscript nodes may adopt ready work through the owning project’s campaign without asking the operator to advance `main`. Use an authorized campaign capability when available. Otherwise, leave reviewable changes in the working copy with a handoff to the owning harness for adoption at its next checkpoint: what to adopt, why, the proposed commit subject, checks and results, and any open gates. A handoff is not adoption; report acceptance only when the campaign confirms it. Do not manage the `jj` or Git graph directly or publish changes.

Mathematical changes still require the designated proof worker for Lean builds and audits. Program-only changes need ordinary relevant tests, not a Lean proof-worker pass.

The explicit pilot flags still select the earlier reproducible passage workflow documented in [the pilot handoff](../../.godel/README.md). Its scheduler is an available tool, not the outer control loop. The pilot’s `GRH_CAMPAIGN_ADAPTER` is a transport for authorized campaign operations, not a separate grant of authority.
