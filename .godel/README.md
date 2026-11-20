# Manuscript formalization handoff

Start or resume the [manuscript program](../cmd/godel/README.md) for work across the paper. Its [mission](../cmd/godel/mission.md) is the goal of both the work node and the improver. The two passages in `pilot.json` are starting questions, not a limit on that mission. Both nodes use Yah and can change and adopt the program. A validated workflow change needs relevant program tests; it is not a checked mathematical result.

## What the first passage run established

The [edition record](sources/masullo/README.md) identifies the source bytes. The [divisor heading](obligations/divisor-heading.json) records what was missing at the visible passage boundary in this edition, not that a divisor theorem is false. The [trace comparison](obligations/trace-assembly.json) records a reading from the end of the trace formula proof. The common admissible test class is still a translation blocker. Neither record contains an adopted Lean theorem. Reader identities there are historical provenance, not the configuration for new runs.

The [geometric trace handoff](obligations/trace-geometric.md) locates the test class and separates three obligations in the passage from local kernels to the global diagonal. It also gives a conditional support argument for the omitted local terms and identifies relevant pinned Mathlib interfaces. Its passage leads remain navigation, not a visually verified supplement to the trace packet.

Keep new passage findings, attribution, remaining premises, and exact accepted declaration revisions here. A source packet alone does not close a proof obligation. Keep the PDF, extraction, renders, and agent scratch outside tracked history. Gödel's private launch history is under `$HOME/.godel`, not in this directory.

## Replaying the bounded pilot

The original two-passage scheduler is still available with explicit flags. Run it in a writable checkout of the intended program revision, from `cmd/godel`:

```sh
go run . -budget pilot-1 -attempts 12 -time 25m
```

Resume with the same command. It reads `obligations/` and `budgets/` rather than taking a stage selector. A new budget ID grants a new allowance; it does not remove a semantic block or invalidate an accepted interface. Do not delete the prior allowance. Ctrl-C suppresses relaunch. An interrupted read-only stage can be retried at the cost of an attempt; an uncertain adoption must be reconciled, not repeated. If an external capability is repaired without its configuration changing, set `GRH_CAPABILITY_EPOCH` to a new value. This does not change the evidence for a passage.

The pilot needs Poppler, the pinned edition (`GRH_PDF` may name a local copy), and a Yah reader that can inspect actual rendered pages. Without visual access, SOURCE cannot attest to a reading or absence. The mathematical roles use separate Yah sessions with the pinned Mathlib sources (`GRH_MATHLIB` may name an absolute cache path). Separate sessions do not certify separate models. The pilot's mathematical landing gate needs `GRH_PROOF_WORKER` for exact-revision builds and axiom audits, and `GRH_CAMPAIGN_ADAPTER` for authorized campaign operations. Neither a missing capability nor an agent's own report is a pass. The Lean project can be checked independently on the designated worker without Gödel or model credentials.

The pilot improver can replay a failed handoff and a control to propose a scheduling change under `proposals/`. This limited experiment is not the mission improver: In the default program, the improver can change the graph, roles, and its own implementation.
