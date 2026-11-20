# Running the manuscript program

Start from `cmd/godel` in a writable experiment checkout, not the checkout where you maintain `main`:

```sh
printf '%s\n' 'Pursue the manuscript mission from the evidence already here.' | go run .
```

With no flags, stdin is the operator objective. Gödel runs a tool-enabled Pi work node, gives a second coding node the actual run record and the live source directory, and starts `go run .` again with the work handoff as stdin. On a subsequent launch from the same directory, `go run . </dev/null` uses Gödel’s most recent nonblank handoff. The setup needs an authenticated Pi installation with the exe-dev OpenAI provider and a user systemd manager. Use an external time limit for an unattended experiment; the shell can send TERM to stop it. The mission loop is not metered by the old pilot's attempt allowance.

Both nodes can edit the program, including their own definitions. A work node reports an observable result or a stall, not just a next-step recommendation. The improver can use earlier run records to compare attempts, change the method, and test a repair. Work failures are recorded and can receive improvement, but Gödel v0.0.5 does not automatically relaunch after a process failure. Inspect the live checkout and run history to see what actually changed. Neither a self-edit nor a model's success report certifies a mathematical result.

The explicit pilot flags still select the earlier reproducible passage workflow documented in [the pilot handoff](../../.godel/README.md). Its scheduler is an available tool, not the outer control loop. For an experiment where the operator alone advances `main`, leave the pilot's `GRH_CAMPAIGN_ADAPTER` unset.
