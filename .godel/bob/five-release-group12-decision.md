# Gate the family the grouped solver actually searches

**Decision.** Leave `cmd/bob` unchanged. Both replay arms
skip the first group-12 solve as a target search and allow
less weight sharing on the existing mesh. The treated arm
provided stronger evidence, not different routing. The
accepted strategic preflight paragraph at `bb5adfaaeae1`
was a separate change to both programs, not this treatment.

## What the worker knew

Gödel run `01a20f5a-0299-7781-805f-641247f1b5d1` matches
Work session `01a20f5a-0523-7776-acfe-730040d2fb87` by input
and final stdout. The runtime prompt was the embedded
`cmd/bob/WORK.md` from launch
`4fc0c11e733130fcdf9bfcd06551f27df43e744d`.
There were no Work children. At event 25, Work launched
`fit.py --rounds 3 --group 12 --time 95` with a fresh
prefix. The [preceding replay][splice] had rejected the
two-law splice for the target by a floating raw-price bound
and cleared that gate for a larger independent atom family.
The rounded recovery seed passed the inherited finite
tests, but missed $T=-10^{-10}$ by over $6.5\cdot10^{-8}$.

The new code at event 23 did **not** give each cell
independent weights. Each group shares weights across four
cell profiles and the seed. The first profile is the
sampled local raw maximizer in every cell, so shared
weights still attain the sum of the sampled local maxima,
up to atom rounding. A positive raw maximum cannot tell
whether the grouped family is wide enough once it must
pass the inherited constraints. The first cone solve
returned `NumericalError`; that status cannot exclude a
family. The record does not show that Work considered it
an exclusion, or that the first pilot served only one of
target search and seed improvement.

Work obtained a useful $9.77\cdot10^{-9}$ improvement on
one rounded law, checked both disk lists and the full
quadratic, and correctly refused a target or continuous
feasibility claim. The law's raw price is below target and
its off-list first cap still fails. The [landing][recovery]
at `7532bb8d575dd4cc9d1d7cb04ca10087e8c7c61e` adds uniform
signed-movement necessities, not a grouped optimum. Its
checker passed at Work events 208–210. No `cmd/bob`
change landed in Work.

## Intervention and replay

At the first grouped refit, this change should cause the
program to price the actual shared-weight family under a
cheap necessary inherited constraint before tuning the
cone solver, instead of relying on the independent raw
gate, because group supports can bound every restricted
law even when the cone solver is ill-conditioned. This is
a filter for a target solve, not a ban on improving a seed
or a replacement for the exact rounded-law check.

Alice's [marked cubic rank result][alice], sharpened at
`b60a298fce31`, debits the marked intersection multiplicity
before asserting where a unit minor is guaranteed. It
rules out a common factor on the whole qualifying family,
not on each selected minor or for the remaining occupancy
problem. The comparable opportunity here is fidelity:
Test the actual restricted atom family before paying for
its solver, and do not promote the result to a bound on
independent weights or arbitrary measurable laws. This
comparison does not rank the programs' research speed.

In improvement session `01a20f6e-2588-7fe2-a84c-822712fd89d5`,
`qrHvLsg` and `KfkRRbu` got the launch prompt, pinned
inputs, the impending first solve, and a bounded diagnostic
budget with no cone solve. Neither got the later outcome.
Only the second arm received:

> When weakening or grouping an already priced refit, gate
> the actual restricted family at the target before tuning
> its solver. If its raw cap clears, price a cheap necessary
> constraint on that same family rather than reading an
> unconstrained maximizer or a solver status as a verdict.

The rubric counted a materially different, scope-correct
routing as improvement, the same justified routing as a
tie, and mistaken exclusion or loss of a necessary check
as regression. Both arms found that the raw cap cleared
($6.16\cdot10^{-10}$, floating), then used disk half-planes
and quadratic tangents to price the same target decision.
The control used one tangent and independently repriced
its LP multipliers on the original geometry, obtaining
about $-4.14765\cdot10^{-8}$ in extended precision. This
is a routing screen, not an error-bounded certificate. The
treated arm used two tangents and ball repricing. Its LP
used a rearranged floating kernel that changed atom
coordinates, so the nominal LP price does not apply to the
original table. Its nonnegative multipliers can still be
used on that table, and the checked repricing below does
so. A separate projection-only screen on the original
family left a positive raw cap, so did not decide the route.

This is a routing tie with stronger proof evidence in the
treated arm. Both agents were explicitly attending to the
grouping decision, so the replay does not test whether the
added sentence would pick it out during open work. There
was no controlled cost comparison or live trial. Revisit
if a later run spends target-search effort tuning the same
restricted family despite an available whole-family gate.

## Checked exclusion of the first group-12 family

Use the exact rational [recovery seed][seed] on 2,701 cells
at depth $39/20$, with the reference law fixed from $56$
onward. The [price table][table] encodes 238 contiguous
groups and four atom-coordinate profiles in units of
$10^{-14}$. On every cell in group $g$, the law is the seed
plus a convex displacement toward the four stored atoms
$(A,B,U)=(2u^2-1,4(2u^2-1)^3-3(2u^2-1),u)$. Precisely,
each weight $x_{gm}\ge0$ is common to all cells of that
group and $\sum_m x_{gm}\le1$; the remainder stays on the
seed. Within-group duplicate profiles give 927 distinct
columns. The profile table matched entry for entry between
two reconstructions using the original dense construction
through template generation, with no warm prefix. The
historical `fit.py` had SHA-256
`6275fdddc0693e7ce40670276c33953f0f0936d722dddb423cbd5ca46dff0281`.
The recorded table, not that scratch script or the LP,
defines the exact family certified here.

Let $V_i$ be the normalized first values, $Q$ the
[positive semidefinite inherited quadratic][curvature],
$Q(Z,V)$ its real polar form, and $d$ its inherited cap.
For every law obeying the 581 $A$ and 62 $B$ disks and
$Q(V_B)\le d$, the surplus $S=M-8/9$ is at most

$$
 P=S+\sum_i w_i(1-\Re(\bar\gamma_i V_i))
     +\sum_Z \mu_Z(d+Q(Z)-2Q(Z,V_B)).
$$

Here $w_i,\mu_Z\ge0$, the directions $\gamma_i$ are unit,
and $Z$ ranges over the moved center and the seed. Each
last slack is $d-Q(V_B)+Q(V_B-Z)\ge0$. Since $P$ is
affine, if $c_{gm}$ is its change from replacing an entire
group by mode $m$, then its maximum on the whole product
of simplices is $P(\mathrm{seed})+\sum_g\max(0,\max_m c_{gm})$.
The checker bounds each of these maxima from above, not
the price at a single primal corner. It reconstructs the
phases, both quadratic tangents, and every group gain in
128-bit Sage balls from the exact fixtures. It cross-checks
the quadratic anchors against the scalar implementation
and tests the signed-shift bilinear kernel against direct
sums on a small asymmetric table. No optimizer runs.

```sh
PYTHONDONTWRITEBYTECODE=1 /opt/sage-10.9/bin/python .godel/bob/check-five-release-group12-price-33.py
```

The computed upper price is about $-4.54164159192829\cdot
10^{-8}$, strictly below $-4.54\cdot10^{-8}$, so this family
cannot reach target under the inherited tests. Two priced
$A$ disks (near $18.45148$ and $20.86059$) were not in the
first cone trial subset. The bound excludes laws that pass
the full inherited lists, not a nominal target-valued
iterate of that smaller cone model. It does not exclude
later refits with different groups or profiles, prohibit
seed improvement, or prove anything about the continuous
five-release domain or the eight-knot frontier. The
seven-knot exclusion is unchanged.

**Next target test.** Reduce weight sharing on the same
mesh, ideally to independent common-law atom weights per cell.
Reprice that new product of simplices under inherited
constraints; do not reuse the old bound when the group
supports change. If an updated bound fails to exclude,
that is not feasibility. A proposed law still needs the
rounded-law checks, the local deficit budget in the
[handoff][recovery], and, if near target, the continuous
caps. Keep the Alpöge exclusion in force.

[splice]: five-release-splice-decision.md
[recovery]: five-release-joint-recovery-33.md
[seed]: deletion-laws/delete-33-five-release-recovery.json.gz
[table]: deletion-laws/delete-33-five-release-group12-price.json.gz
[curvature]: five-release-curvature-33.md#identity-and-uniform-localization
[alice]: ../alice/jet-reducible-cubics.md#why-the-same-determinant-gives-no-uniform-q-factor-on-the-complement
