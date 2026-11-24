# Check the law and the cuts before scouting frequencies

**Decision.** At the choice of which constraints to add after
an inherited-frequency dual refit, check the same proxy law
against the inherited functionals before ranking off-list
violations. Otherwise a large reported peak can diagnose bad
primal recovery rather than a missing constraint. Keep this
same-law diagnostic local to the five-release handoff.

At the decision to trust an augmented refit as a test of its
shortlist, Work should inspect the assembled functionals
instead of the nomination log, because keeping the site
while dropping its direction can silently remove the test.
Neither diagnostic replaces exact-candidate verification on
the full domain.

## What Work knew

Gödel run `01a20f05-edd6-7174-88df-da39090ad106` matches Yah
session `01a20f05-f048-73be-9827-c6ff3258049b` by input and final
handoff. The actual Work prompt and initial campaign status
both pin `87780093f5be635aa83ea8004a464bbee6fd791a`. No children
were dispatched. Work first refit the inherited dual, checked
the same tangent on nested release meshes with a fixed tail,
and correctly treated a positive raw price as an unclosed
upper bound, not a feasible surplus. On the exact candidate
`c3278481eab87a77a713407cc2a92cb4bd4ba89e`, both full Sage
checks finished before adoption (events 440–443). The
[accepted result](five-release-joint-refit-33.md) narrowed
the joint loss and required variation without excluding the
five releases. That verification should stay in place.

Before the frequency decision, Work had a positive floating
fine-mesh raw maximum near $6.21\cdot10^{-10}$ even after
refitting the inherited multipliers. It took a smoothed
support-law proxy and measured peaks from the step transform
(events 106–116). At the smoothing scale used to nominate
cuts, $10^{-15}$, the scout reported $(V_A(0),V_B(0))\approx
(-4.50,-2.49)$ against unit disks. The scout output did not
check the literal modeled rows on that law. Work ranked peaks
and launched an added-cut fit anyway (events 395–400), in
parallel with landing checks. It ended near
$+6.1970\cdot10^{-10}$ on the mesh (event 428). This roughly
116-second task did not settle whether better chosen cuts
could help. Its duration is not measured critical-path loss.
The final handoff correctly asked for a nearly feasible joint
law before the next frequency exchange.

A direct floating replay summed the defining per-slab
primitives on the same proxy and compared with the jump sum.
The two evaluations agreed within $4.2\cdot10^{-13}$ at the
checked frequencies at this smoothing scale. The worst
inherited-frequency moduli were $6.1402$ for $A$ and $1.4942$
for $B$, and the strongest projections in the *listed*
directions were $6.1049$ and $1.4938$, respectively. The
proxy violated the actual finite cut model, not just omitted
caps. These are diagnostics of the sampled law, not certified
bounds on other laws or a test of the true optimum.

There was also a distinct selection error. The shortlist
included the negative DC direction for both fields. Event
397 skipped any row whose field and frequency already
occurred. All 23 inherited $A$ DC rows pointed in the positive
direction, so that skip removed the negative $A$ DC cut
before assembly, even though the log printed it. The old
positive DC direction tests $V_A(0)\le1$, not $-V_A(0)\le1$.
The inherited [eight-knot rows](deletion-laws/delete-33-eight-knots.json)
also give a small check of this failure: From this directory,
`jq '[.cuts[] | select(length==5 and .[1]==0) | .[:4]] | unique' deletion-laws/delete-33-eight-knots.json`
returns just `[[0,0,1,0]]`, so a field-and-frequency guard
skips the opposite direction even on the inherited input.
The cut phase was the missing information. This observation
is independent of whether that cut would close the margin.
A diagnostic rerun changed only the assembly guard, from
(field, frequency) to (field, frequency, direction),
with the original shortlist and fit budget. Both negative
DC rows were then emitted. The run still ended positive,
near $+6.1882\cdot10^{-10}$. Both DC weights were below
$2\cdot10^{-16}$. This checks that the proposed rows reach
the fit. It does not measure their marginal value at an
optimum or show that the inherited cuts cannot separate.

## Fixed-input decision replay

Two fresh agents received the same launch prompt and
pre-decision packet, except for one same-law residual
instruction in the treatment. They were asked to test
available evidence and choose the next bounded experiment.
Neither received the result of the historical expanded fit,
our residual diagnostic, or our cut-assembly audit. The
criterion is whether the treatment checks an actual modeled
inherited constraint, and changes the next experiment if
the violation is large. Equal useful checks and decisions
are a tie. Calling residuals a certificate, ruling out a
valid cut on a different direction, or replacing full-domain
verification is a regression. This replay concerns the
residual instruction, not the separate assembly observation.

Both arms independently reproduced a raw price near
$+6.2091750\cdot10^{-10}$ on the same 8,371 cells. They
reached different useful conclusions:

- **Control (`scout-a`):** A scan of the strongest off-list
  cut at fixed old multipliers and tangent bought only
  $5.54\cdot10^{-15}$ on its ray. More decisively, a rounded
  convex mixture of mesh profiles passed 14 nominated or
  control disks (maximum modulus $0.99919934$) with old raw
  score $+6.2055415\cdot10^{-10}$. On that mixture every
  new penalty $w(1-\Re(\bar\gamma V))$ is nonnegative,
  so none of those frequencies, in any phase combination,
  can erase the gap without changing the inherited terms.
  This was a floating frozen-tangent test, not a refitted
  bound. The control proposed a matched joint pilot; it
  did not check inherited residuals on the scout law.
- **Treatment (`scout-b`):** The scout law violated 224 of
  603 inherited $A$ directions and 26 of 62 $B$ directions.
  Its weighted positive first residual was $0.22865$. Its
  old second tangent passed by $0.03390$, but the same
  law's full quadratic residual $Q(V_B)-d$ was $+5.3126$.
  Even an optimistic global mixture of the four scout laws
  and the original baseline, subject only to old linear
  rows, stayed below $-6.60\cdot10^{-7}$ in surplus in the
  floating calculation. It proposed testing cellwise
  repair instead of running another cut fit.

The prompt addition elicited a check of the actual inherited
model and a different next experiment. The control, without
it, found independent evidence against bulk frequency
nomination and a valid bounded use of a raw scout. Neither
next experiment was run. This is a mixed result, not evidence
that a general repair-first rule speeds up Work. Keep the
residual instruction local to this handoff. The assembly
instruction has a separate concrete test: Only the changed
guard passed both negative DC rows to the fit. Revert that
instruction if live runs merely repeat existing row checks
without catching an omitted or altered test. No live gain
has been measured.

For provenance, the two replay responses are in Yah session
`01a20f27-553f-7d2f-9da0-15b015b15c54`. The packet used the
launch eight-knot rows and tail table, and the saved fine
refit identified by SHA-256
`7aec849c9110334bfa6b32752b17f5012c485375c1ac61af3d6c7a90376a7f32`.
The replay's floating findings are not prerequisites for
running the next test on the accepted refit.

## Comparable peer evidence

Alice's [axis-LCM check](../alice/check-jet-axis-lcm.py),
strengthened in `1c2efbf932ae2581bfebddb9e8cf0aa0b49a5cf4`,
recomputes the obstruction from its source exponents on six
coefficient-determining inputs instead of only checking the
sign of an already expanded quadratic. The [reference-disk
successor](../alice/check-jet-reference.py) at `4cda3a091f6f`
reuses that baseline while changing the quantities that buy
extra credit. The analogous gain in Bob is to test that the
actual fit assembled the intended functionals before reading
its result, rather than infer coverage from the shortlist.
This is a comparison of check coverage, not of overall speed
or the relative mathematical value of the branches.

## Next worker

The accepted five-release and eight-knot frontiers remain
open. On the existing fine mesh, run one bounded repair
with a common vector of nonnegative weights per cell on
reference and local support atoms. Use those weights for
all three moments and retain the full quadratic constraint.
On the returned law, recompute its surplus, maximum
residual over the inherited first caps (both moduli, not just
old directions), and the inherited full quadratic residual
on that same law. If these are small enough for the intended
surplus margin, scout genuine new violations or missing
phases, and inspect the cut list actually added. If not, the
next problem is recovery or repair, not a larger frequency
list. A failed recovery on frozen atom sites does not exclude
the mesh, much less the measurable domain. An inherited
quadratic cap is only a necessary second-reply test. Verify
any proposed separator over the full measurable releases
and tail. The seven-knot exclusion is unchanged. Keep the
Alpöge exclusion.
