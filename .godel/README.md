# Manuscript formalization handoff

`pilot.json` names the mathematical goal and the first two passage questions. It does not specify their answers. `cmd/godel/mission.md` is the enduring goal. Run from the live program directory:

```sh
cd ~/p/grh/cmd/godel
go run . -budget pilot-1 -attempts 12 -time 25m
```

Resume with **the same command**. It reads `obligations/` and the allowance under `budgets/`; it does not need chat, a model response on stdin, or a stage selector. To authorize more time or attempts after exhaustion, choose a new budget ID; unchanged blocks and accepted records are shared. Do not reset the clock by deleting an allowance. Ctrl-C stops work and suppresses relaunch. Read-only work interrupted mid-stage can be rerun, but it still costs an attempt. An uncertain adoption is not retried as if it had failed.

The [Masullo edition record](../godel/sources/masullo/README.md) identifies the source bytes. The manuscript PDF and page renders are not tracked. SOURCE needs Poppler, image-capable Pi models, and credentials. `GRH_PDF` can point to a local copy of the pinned edition. TRANSLATE, fidelity review, CHALLENGE, and PROVE use fresh, tool-free Pi processes and the pinned Mathlib source cache. `GRH_MATHLIB` can point to the absolute path of that cache. The default generator and reviewers use different provider/model IDs. Proofs are checked only through `GRH_PROOF_WORKER`. `GRH_CAMPAIGN_ADAPTER` must designate a trusted bridge for the owning Yah campaign. See the transport contracts in `internal/worker/` and `internal/landing/`. Without both capabilities, proposals are not checked results. To check the mathematical library independently on the proof worker, use `lake build` from the checkout, without this program or any model credentials.

A source disposition is about the passage in this edition, not the truth of a theorem. An obligation record keeps the packet, current candidate, and stage; `Revision` is populated only after adoption. Read its review, premises, and blocker together. Rejected or superseded interfaces are not inputs to proof search. `checkpoint` concerns this obligation only. Nothing here equates a conditional comparison of trace evaluations to an unconditional trace formula or an all-zeros result.

Infrastructure failures can become eligible when their configured capability changes. If an external service is repaired without changing paths, set `GRH_CAPABILITY_EPOCH` to a new value before resuming. This does not clear a source disposition or semantic block; those require changed evidence. A changed passage must have a new obligation ID. The command currently accepts a plan (goal and passage questions); discovery outside those questions is not implemented.

Gödel's private launch history lives under `$HOME/.godel`, not here. Its self-improvement process can propose a different scheduler ordering under `proposals/` after replaying a failed handoff and a control. It has no model-operated editor or adoption capability. Review the proposal separately before changing the live policy; an ordinary run makes no change. This repository tracks human-reviewable run handoffs, not transient PNGs, PDF caches, agent scratch, or locks.
