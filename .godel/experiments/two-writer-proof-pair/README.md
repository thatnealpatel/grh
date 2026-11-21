# Two-writer proof pair

**Protocol only; no arm has been run.** Test whether two independent proof writers can produce one usable joint result sooner if dispatched concurrently. Compare exactly one sequential arm (A terminal, then B) with exactly one concurrent arm (dispatch A, immediately dispatch B, then join). This is not a new Gödel scheduler, a proof of either obligation, or evidence of a general speedup.

## Fixed inputs and conditions

- Upstream base `69355b3ae0441fa395a1110d88d0df06b01dcbc1`, tree `09b74ef69354212b6741c669578efa55388e957a`, synthetic parentless seed `4c0ccd361d70957dc93ec9be3cc109fb3362458a`. Never substitute a later revision, even one with equivalent theorems. Both A and B start at the seed in both arms. The harness's construction checkout is **not** an arm input.
- A: paired finite Haar shells in the actual rational completion, unit-subtracted radial integrand, paired integral and Mellin samples. B: translated rational unit test on Q_p, integrability and vanishing of its log-weighted Fourier pairing. The frozen obligation, pinned manuscript and exact task/review briefs and public endpoints in [`prompt.go`](../../../cmd/proofpair/prompt.go) are the handoff. Do not give either writer the other output or the arm identity.
- Coordinator and two fresh writers: `gpt-6.2-sol/high`. One fresh, nonrecursive statement reviewer: `gpt-5.6-luna/high`, both statements on one candidate. Writers and reviewer are nonrecursive; the reviewer must not change tracked files. Writer timeout request: 1,800 s each; review: 900 s. No retries, resumes, forks, repairs, or extra dispatches. The selector is remote: these are **requests**, not controls exposed by `tool_subagent`. Missing or different actual settings invalidate a comparison. Use one approved inference/selector configuration, account and policy window for both arms; record changes or throttling, including transport retries if known.
- Use two independent, disposable Linux VMs (systemd 255, unified cgroup v2), each 8 vCPUs, 64 GiB RAM, identical image, storage class, disk budget, clean process state, resource limits, toolchain and immutable cache input. Limits apply to the whole service, not per writer. Reserve identical host capacity; run the arms separately, not against each other. Fix the order by a coin flip before running either arm, and record it. Finish and seal the first arm before starting the second; no tuning based on the first. Record service/version/input hashes and readiness for both before admitting either. If these conditions cannot be met, stop rather than replace this with a different experiment.

## Prepare without running agents

**Operator owns provisioning and admission.** Stage outside either VM and outside the construction workspace. An operator with access to upstream exports only the pinned tree closure, not a bundle, commit, worktree, `.jj`, or Git history. Verify the commit-to-tree binding at the source; on the staging machine the following uses Git plumbing on the readable source object store and writes only the pack to an external export directory. Use Bash with `set -euo pipefail` here and for the import below, and stop on any error.

```bash
base=69355b3ae0441fa395a1110d88d0df06b01dcbc1
tree=09b74ef69354212b6741c669578efa55388e957a
# Set SOURCE_GIT_DIR to the absolute path to the trusted upstream Git store.
# Set EXPORT to an empty absolute staging directory, outside the source checkout.
source_git() {
  env -i PATH=/usr/bin:/bin GIT_CONFIG_NOSYSTEM=1 GIT_CONFIG_GLOBAL=/dev/null \
    GIT_NO_REPLACE_OBJECTS=1 /usr/bin/git --git-dir="$SOURCE_GIT_DIR" "$@"
}
test "$(source_git rev-parse "$base^{tree}")" = "$tree"
printf '%s\n' "$tree" | source_git pack-objects --stdout --revs --no-reuse-object > "$EXPORT/base.pack"
sha256sum "$EXPORT/base.pack"
```

In separate clean build staging, and independently in each arm, unpack the same pack into a fresh SHA-1 Git repository **at** `/srv/proofpair/base` (as the local unprivileged owner; no existing checkout or files). Use a fresh shell, no `GIT_*`, `JJ_*` or `YAH_*` overrides, and use this helper just for import (do not export its variables to the trial service):

```bash
cd /srv/proofpair/base
trial_git() {
  env -i PATH=/usr/bin:/bin GIT_CONFIG_NOSYSTEM=1 GIT_CONFIG_GLOBAL=/dev/null \
    GIT_NO_REPLACE_OBJECTS=1 /usr/bin/git "$@"
}
trial_git init --template= --initial-branch=main --object-format=sha1 .
trial_git unpack-objects < "$EXPORT/base.pack"
seed=$(
  printf 'tree %s\nauthor Proofpair <proofpair@invalid> 946684800 +0000\ncommitter Proofpair <proofpair@invalid> 946684800 +0000\n\nFreeze proofpair input\n' \
    09b74ef69354212b6741c669578efa55388e957a | trial_git hash-object -w -t commit --stdin
)
test "$seed" = 4c0ccd361d70957dc93ec9be3cc109fb3362458a
trial_git -c core.logAllRefUpdates=false update-ref refs/heads/main "$seed"
# Populate index/checkout without a reset backup ref or reflog.
trial_git read-tree --reset -u "$seed"
```

Keep three inputs separate:

1. **Baseline:** The import above is the only repository mounted in a VM. The launcher independently checks full tree and seed, sole ref `main`, object closure (including no unreachable objects), Git metadata/config, canonical cwd, index and exact on-disk bytes/modes. It rejects `.jj`, alternates, extra/ignored files outside `.lake`, inherited Git/JJ/Yah routing, and nonempty trial HOME. Yah is started at that checked absolute cwd, with an explicit `main` campaign target and a filtered environment; the pinned Yah initializes the colocated JJ repo itself. No original remotes, snapshots, histories, alternate objects, construction workspace, or other arm may be accessible.
2. **Operator binaries:** Build `proofpair` from the experiment implementation with `go build -trimpath -buildvcs=false -o /absolute/stage/bin/proofpair ./cmd/proofpair`. In the *fresh base build staging*, build `godel-base` with `go build -trimpath -buildvcs=false -o /absolute/stage/bin/godel-base ./cmd/godel`; do not execute it there. Transfer binaries, not the construction source, Go cache or working history. Use a trusted module-version build of `patel.codes/yah@v0.0.59-0.20261119201545-8f0869c38bc6` (the launcher checks Go build metadata without running it), pinned JJ 0.45.1, Poppler, and the full Lean `leanprover/lean4:v4.36.0` distribution including `leanchecker`. At `/opt/proofpair/bin`, install `proofpair`, `yah`, `godel-base`, `jj`, `pdftotext`, and `lake` as root-owned regular executables mode `0555`, with no other entries in that directory (in particular no shadow `git`); `lake` can be a regular wrapper executing the absolute pinned toolchain's Lake, not an elan downloader. Keep `/opt/proofpair` read-only to the trial account. Record binary, wrapper, toolchain, and VM image digests and the Go toolchain and source identities used to build them. Build provenance of `godel-base` and checksum verification at deployment are the operator's responsibility, not inferred from a file name.
3. **Lean and manuscript inputs:** In the clean base build staging only, with the frozen `lean-toolchain`, `lakefile.toml`, and `lake-manifest.json`, fetch the manifest-pinned dependencies from trusted sources and check package revisions (mathlib `fc4f59e577feb1a4956671bc04ac18aaaf8cd842`). Produce one warm cache with `lake --wfail build Proofs` on the frozen inputs and the same toolchain, paths and numeric trial UID as deployment. Do not use a project build from another checkout, shared writable cache, other arm, or later proof/build. Export only `.lake/build` and `.lake/packages` as one immutable, checksummed archive, with no escaping symlinks/alternates; preserve modes and mtimes. Record source seed, package/toolchain pins, command/result and archive SHA-256. Unpack verified identical copies in the two baselines. The unit mounts canonical `.lake` read-only to the service, and preflight checks real build/package directories on read-only mounts; it does **not** authenticate their contents or inspect package histories. Supply only necessary pinned dependency material and confirm it needs no fetch at runtime. Yah symlinks packages and copies the baseline build into each private writer/review workspace on the first literal `lake build`; the coordinator seeds the integration build from the same baseline, not from a writer. Put the pinned PDF at `/srv/proofpair/masullo.pdf` (6,756,996 bytes, SHA-256 `e039d3f6cf0a4b14f03c7edb85097752dd65c0a2fe543c76fe992be234f97bf5`). Do not transfer excerpts from later work.

Validate provisioning before admission without invoking Yah: same digests and fixed resources, canonical paths, no ambient Git/JJ/Yah routing, PDF and dependency receipts, no other host mounts/credentials, reachable *approved* runtime services, installed service rendered identically except `-arm`. If any prerequisite cannot be verified, do not start. A passing offline Go build/help/test is not acceptance of this isolated setup.

## Contain, start, and release

Use a dedicated `proofpair` user with an empty writable `/var/lib/proofpair`, ownership of the baseline, no login, no sudo, no manager delegation, no user D-Bus/systemd manager, and no privileges to start system services or move cgroups. Use a dedicated throwaway VM identity for the approved Yah services. Before startup, the operator must restrict egress to the necessary Tailscale infrastructure and authorized inference/proxy, selector and runtime telemetry paths: pinned Yah reads local Tailscale status, uses the proxy and supermarket service addresses, and calls the library's `/select`. Arrange read-only status access, not a privileged host control socket. Yah also configures remote logging; this is not an air-gapped run. Confirm permission for these flows and deny retrieval, repository access, uploads/publication, other VMs and arbitrary network destinations (including via the proxy). If endpoint-level/service authorization is unavailable, **do not run**. The tool allowlist and prompt do not constrain what Bash can do over an open network.

Render [`proofpair.service.in`](proofpair.service.in) by replacing `@ARM@` with the one assigned literal (`sequential` or `concurrent`). Install it as `/etc/systemd/system/proofpair.service`, and verify the rendered unit (`systemd-analyze verify /etc/systemd/system/proofpair.service`) and effective properties with no drop-ins that weaken it. Persistent journald storage must be sized for the arm. As VM admin run `systemctl daemon-reload` and `systemctl start proofpair.service` **once**. Do not enable restart, log in as the trial account, or run the command interactively. Confirm start and collect `InvocationID`, cgroup path, the invocation journal (`journalctl _SYSTEMD_INVOCATION_ID=...`), service `Result`, `ExecMainCode`, and `ExecMainStatus`. `systemctl start` returning is not admission, completion, or release.

The launcher is the sole preflight/one-shot owner (a marker reserves the empty HOME before launch). It requires the dedicated cgroup, itself as MainPID and effective kill/runtime settings, then starts one headless Yah process with the fixed prompt on stdin. No user bus is allowed: otherwise pinned Yah probes `systemd-run --user --scope` and can move Bash jobs outside this service. In this unit it must use the process-group fallback; process groups still remain in the service cgroup. The operator is responsible for the absence of other escape paths (e.g. privileged socket access, polkit grants, shared task launchers). Systemd owns the hard stop: at 2 h service runtime, including preflight, stop the whole group, allow up to 10 s then SIGKILL. Child timeouts and direct-child cancellation are not subtree containment. Also arm an independent VM power-off deadline (2 h 5 min from start request) before starting to cover a hung guest/manager; losing evidence makes the arm incomplete.

Inside the process, the coordinator alone dispatches and joins writers, integrates once in `[A,B]` order using `tool_campaign`, joins one statement review, invokes the frozen `audit-local` once, then adopts the exact passing candidate locally once. Do not help it interactively or rerun failed stages. Use durable tool calls and results, not just the final answer, to verify all of this. The audit must use the returned integration workspace and full candidate, build `Proofs`, replay each affected module and check both declaration names/axiom provenance. It checks exact proof/configuration inputs; it does not decide intended mathematical statements. The only acceptable diff is the byte-for-byte union of the two specified added files. No repository publication.

**Operator owns terminal collection and teardown.** On timeout, interruption, or unwanted behavior, stop the service; record why and reconcile any observed adoption from campaign state, never retry it. Verify the service stopped and the cgroup is gone or `cgroup.events` reports `populated 0`; record this separately from Yah process/child terminals. Seal available raw artifacts (unit journal, service and VM outcomes, session/campaign/dispatch journals, candidate diff and digests, review evidence, complete audit diagnostics, deployment receipts) in access-controlled storage outside both VMs and this repository. Then destroy the VM and its disk/worktree/campaign, revoke its identity, and record release. A forced power-off without usable evidence, or inability to establish cleanup, is an incomplete arm; never reuse the VM or enlist another agent to reconstruct missing evidence.

Use the [evaluation rules](evaluation.md) and [blank summary](summary-template.md) after both arms are sealed. Keep raw proof artifacts, logs, private prompts and credentials out of this directory. Store only the sanitized summary here if authorized.
