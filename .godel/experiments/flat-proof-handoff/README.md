# Integrate proof source with its landing note

## Decision replay: Below-one trace moments

Gödel run `01a20615-9bca-76f9-99c3-bf4ff4a96428` matches Yah work
`01a20615-9d61-7879-bfbb-bb714a7cbca9` by input and final response.
Its launch marker and first accepted pin were
`2ca821aea800534a391adc283dad17441e167d4a`; the `cmd/godel` tree did
not change through the proof landing. The preceding work
(`01a2060d-0e81-7500-b3fb-99f77cce99e8`) and improvement
(`01a20611-b76e-7946-91c9-23d09590b3b1`) instead launched
`820e31dc3ac7d12f8a2a55428be5301e79be5fc4`. They recovered the
lower-edge proof and clarified clean-patch recovery. The latest work
used that checked result and moved on rather than recovering it again.

Work separated a common global/local trace requirement from a
supporting local scalar claim. `nGRsVZp` reviewed the mathematical
constant-weight lift obstruction; `kAlBMLS` wrote and checked the
local separator, and `IolcisX` independently reviewed its exact
statement and the manuscript interface. The review was text/layout
only, not a rendered-page check. The paper result and local Lean
result both landed, but the omitted-sample filter and trace comparison
were not checked in Lean in this run. See the
[branch handoff](../../obligations/trace-below-shell-q.md).

1. The independently useful paper note first integrated as
   `63cd3b5f8c839348967fed68ad2c4b28f20dbbf5`, was superseded by a
   concurrent Walk landing, then was reconciled and adopted at
   `22bb3ec7a05a7b7ee6e649bb9140eef00ce7a9cf` (work seqs. 108, 119).
   Keeping this reviewed source result separate made sense.
2. A later follow-up merely linked the Lean result and its checks.
   Work stacked the proof on that pending note
   (`31eeb41ebb6c1489740ba4bf20d95b779a7530f3`), checked child
   `2ee0df7a322f05412fba742a9c41c99d6e4fe60a`, and tried to adopt
   the child first. The reply said stale even though the same accepted
   tip `22bb3ec7…` remained (seqs. 135–150). This was not a race:
   The child's immediate parent had not been adopted.
3. The owner then replayed both registered outputs on `22bb3ec7…`
   and checked `875ff38ff23ba5857f856b3edfcf7fce5f8da6ac`. A
   read-only `jj diff --name-only` between this flat candidate and the
   checked child reports no tree differences; their parents differ.
   Concurrent Yah `01a2061d-6bc7-725a-b079-14f4d6c12d36`, seq. 84,
   adopted `fe0c4ef71b0cc478d5b841127893d982675ccef1` at 02:02:05 UTC,
   after the replacement build started at 02:01:59 UTC. A preflight at
   that decision would not have caught that move. The subsequent
   restack, with fresh checks, landed at
   `0fa139d2d20de39dcc566b38d23103eb95ff957d` (work seqs. 163–170).

## Disposition

Replay the first build decision using the two registered outputs
already available then: Integrate the landing-only note and proof
on accepted, and build that exact candidate. The later flat replay
establishes that the same tree results without a pending parent.
This removes a parent-order rejection at that decision, not the
possibility of a concurrent adoption. The earlier
[cut-output replay](../prebuild-stale-check/#live-follow-up-cut-output-orbital-transfer)
and [lower-edge recovery](../matched-improvement-recovery/#live-recovery-the-rational-sharp-lower-edge)
were different failure modes: Superseded bases and a content conflict,
not a missing parent adoption. Do not add a polling or recovery node.

Document the combined candidate for a landing-only note, not for a
parent meant to land independently. No changed routing, relaxed
checks, or measured counterfactual timing. Assessment Yah:
`01a20624-d19d-7566-86d3-0dc22f4adc92`.
