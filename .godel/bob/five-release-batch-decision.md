# Reuse a release price before the first replay

## Decision and evidence

Gödel run `01a20f79-d891-7328-8146-f794008b8f41` matches
Work session `01a20f79-db21-79e6-937f-339355de2473` by
input and final stdout. The runtime Work body matches the
launch source `21e1ff92419ece06bae3f0ac5b3dc50abd698051`.
Work ran the searches and checks directly, without child
agents. The accepted mathematics at the end was
`63af631ef047d6face9c2dfe44d40eef53151778`; the run did
not change the Bob program or its launcher inputs.

Work correctly switched from a failed primal search to a
nonnegative reweighting of inherited directions. It checked
the price over the full atom interval, measurable releases,
and a measurable tail. The floating search alone did not
establish an exclusion, and neither positive prices nor the
unsuccessful searches establish feasibility or infeasibility.

The decision under review is the first integration, event
268. The draft `b3de773a37bebd68b797751baa913da3973554d3`
had the rounded 91-row price and a single-case checker;
its base was `52090c0259f52eebc595b8b36947657c3c869f10`.
The [frontier](eight-piece-deletion-33.md#price-exactly-two-knots-and-refine-five-releases)
already named seven cases and said to reprice all seven.
The run checked one case first and started the other-case
floating screen during that candidate replay (events
282–291). The transcript shows this order, but not whether
latency or contention drove the choice. The second case
could use the same weights without a new fit. Checking all
seven cases together used one ordinary price and measurable
tail, replacing only the five selected slab contributions
in each sum:

$$
  U_S=U_{\rm ordinary}+\sum_{k\in S}(U_{{\rm released},k}
  -U_{{\rm ordinary},k}).
$$

Here the subtracted terms are the same upper contributions
included in the base, not independent estimates of its
components. The seven cases have nine distinct release
sites. The historical singleton and first batch runs took
225 and 227 seconds, respectively (events 271–302 and
329–347). They printed the same singleton upper; the batch
also certified $(0,2,4,8,12)/400$ below the target. These
are observed runtimes, not an isolated timing benchmark.
The standalone batch went stale after its replay; two more
checks on restacks preceded the final combined landing.
Earlier batching could have removed a separate checking
cycle, but whether it would have avoided a stale base or
finished sooner on the live target is unknown. It would not
have supplied the independently refitted price for
$(0,2,4,6,14)/400$.

**Proposed intervention:** At the first checker decision,
price the listed cases by their local replacements before
freezing a one-case candidate, instead of doing the cheap
cross-case work after starting that replay. Preserve the
full-domain checks and do not hold up a ready result for
another fit or an expensive new obligation.

## Pinned prompt replay

In improvement session `01a20fa6-9441-7374-ba6e-4a8c633f297d`,
both fresh agents saw the same pinned mathematical evidence:
The then-accepted base and the pre-integration draft. They
received the launch Work prompt and the same decision brief,
except that the treatment added the batching instruction
now in Work, without the final sentence about separate fits.
The predeclared discriminator was a cheap shared computation
before freezing, with the full replay retained; unsafe domain
transfer or mandatory expensive delay would be a regression,
and the same next action would be a tie.

- Control `svFWBuO` ran the pinned production Sage reference
  tests, then chose to integrate and check the singleton
  before repricing the other six. Its preflight is useful
  and is not displaced by batching.
- Treatment `FwHOQyT` chose to batch first. It checked the
  actual slab successors and grid, and counted nine local
  prices, four beyond the original five. It explicitly
  retained the reference tests, the full-domain check, and
  strict threshold comparisons on the exact candidate.

This is a routing win on one input, not a new Sage certificate
or a live productivity trial. Install the short Work clause,
not a graph node or an extra check. Keep the branch's explicit
next action even if the clause is later removed. Revisit the
clause if it delays ready results for nonlocal cases, or if
new live cases already batch under the local handoff with no
observable benefit from the generic instruction.

## Peer comparison and handoff fidelity

Alice's [marked cubic rank result][peer] at
`b60a298fce317c19b8add3e9a00f0136dd9f883a` improved the
whole-family obstruction by charging the order $r$ at the
mark to Bézout's budget. Its handoff also keeps both
second-row tests on the *same* common inputs, rather than
multiplying unrelated densities. This is comparable to Bob
at the evidence-transfer decision, not as a speed or proof
ranking: reuse checks on the unchanged objects, but account
for the domain change before carrying a numerical threshold
forward. Bob's stdout asked for signed $B$ displacement on
the new assignment without distinguishing the old threshold
from the measurement. The threshold is not portable.

At the next primal gate, this handoff should cause Bob to
check inherited caps and score the old displacement only
as a diagnostic, instead of rejecting by the old threshold:
Its proof uses the old raw-price upper and a fixed seed.
The [branch handoff][branch] gives the adjustment needed to
turn a displacement on the new case into a necessary test.
This correction does not require a new pricing run.

[peer]: ../alice/cubic-rank-decision.md#next-worker
[branch]: five-release-independent-price-33.md#next-decision
