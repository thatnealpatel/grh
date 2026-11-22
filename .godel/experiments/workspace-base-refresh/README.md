# Refresh the base before allocating a workspace

## Allocation evidence

The previous improvement of Gödel run
`01a20162-6011-751f-a0e3-1cc2cce305a2` (Yah
`01a20168-77eb-7fb7-9ea2-dc9f8cc0136f`) replayed three observed
allocation rejections. In each, another campaign had adopted a new tip
between the earlier `status` and explicit `new`. Using the last observed
adoption before `new` would select the new tip in all three cases. A
stable companion control kept the same hash. The trial tested base
selection, not whether the counterfactual allocations would succeed.
That improvement also hit a setup rejection and did not change the
program. See `assessment-01a20162-6011-751f-a0e3-1cc2cce305a2.md` in
Gödel's program directory for the replay and exact event locators. The
improvement's own rejection was not one of the three classified races.

The pattern recurred while the next run was landing its Lean proof. The
separate companion session `01a20177-6927-7d0b-ad78-865488044f5f` read
`160bcef06c89e3b21752193481ba0b034775d633` at 04:15:34 UTC. Main work
adopted `4e37ced863adec2785cb30724b80b45cdad023ee` at 04:17:19. The
companion passed the old hash to `new` at 04:18:19 and was rejected.
Its next status returned `b86509c4d177ccd392cd47add3ac23eed92cf2f8`.
There is no companion output to replay from that allocation. See
companion events 5 and 53–56, and main work events 159–160.

Live control in improvement session
`01a20179-d37b-7a6c-9df8-dd6bf603d44a`: After investigation, refresh
found `aede18fbd165c313ee931c446b0ada70e7fdf160` instead of the initial
`b86509c4d177ccd392cd47add3ac23eed92cf2f8`. A patch comparison found
only a separate conflict-recovery README edit. `new` on the refreshed
hash succeeded. The old hash was not retried.

## Separate adoption evidence

Gödel run `01a2016d-1e85-7f02-92bf-9bca3cc0b1dc` matches the input and
stdout of Yah work `01a2016d-1f48-75eb-968a-c198d9068666`. Its launch
marker and work prompt match the archive at
`0cce9c672bc164b62f42a47a6d011ebf1e6c2bc6`, also its initial accepted
revision. It allocated successfully and reused the previous scratch
source. Four targeted builds failed while implementing the Haar
transport and moving the Gaussian theorems into modules; the fifth
passed. `ZTZcZfz` independently reviewed the statements and the
provisional manuscript comparison. Its campaign output is empty, not
a proof patch. The main proof output was
`68a17e025824b2c0e241ae73f2718b0b0cb58bc1`.

| Integration candidate | Audit | Adoption |
| --- | --- | --- |
| `a49bd6bceca8b5894b1748508ea56dee17a866ad` | Passed, 130 s | Stale after the rational Mellin sign result added a Lean module. |
| `d7bdc3f4ceb783df328c28df368c0639976de3e7` | Passed, 141 s | Stale after documentation and prompt changes. |
| `4e37ced863adec2785cb30724b80b45cdad023ee` | Passed, 21 s including cache seeding | Adopted. |

Task times come from transcript events 92/120, 136/141, and 151/156.
The last two candidates have identical `Proofs/` and pinned Lake
inputs. Seeding from the completed audit of the second candidate saved
rebuilding the project; the third still ran the full audit and all
kernel replays. All seven built signatures and axiom reports were
identical across the three audits. The [proof handoff and reproduction
command](../../obligations/hecke-right-line-majorant.md#archimedean-gaussian-pairings-on-the-completion-unit-haar-measures)
remain the source of the mathematical result and remaining obligations.

## Decision

Document the just-in-time refresh in the shared [direct-edit
workflow](../../../cmd/godel/README.md#integrating-a-direct-edit). Do not
add a retry loop or change proof routing. A refresh does not prevent a
move during the audit; the existing candidate-exact restack and cache
rules worked for that distinct failure. Do not apply the identical-input
cache procedure when the Lean inputs changed.
