# Delete-33: Price displacements from the five-release seed

At depth $39/20$, retain the [five-release domain][domain],
its moved tangent, and its $7.2\cdot10^{-10}$ upper for raw
price $R$. The target here is surplus $M-8/9\ge-10^{-10}$
under the two inherited disk lists and the full inherited
quadratic test. Those constraints imply $M-8/9\le R$ by
polarization. The results below do not require a
continuous cap, a particular tail partition, or any extra
conditions on the measurable releases.

## A checked joint move, still far from the target

The [rounded trial][trial] uses the same table format and
partition as the [seed][seed]. Split groups of adjacent
cells and refit common atom-mixture weights across each
group under both fields' disks and the full quadratic.
After the restricted refit, mix toward the seed to repair
the inherited disks, and serialize rational atom coordinates
and weights. The floating optimization gave no reliable
optimality claim. These tests all use the same rounded law:

| Test | Checked value, rounded |
| --- | ---: |
| $M-8/9$ | $-5.54635755318\cdot10^{-8}$ |
| Largest of 581 inherited $A$ moduli | $0.999999999989991$ |
| Largest of 62 inherited $B$ moduli | $0.999999650179457$ |
| Full $Q(V_B)-d$ | $-5.57238877026\cdot10^{-7}$ |
| Raw price $R$ | $-4.11602068065\cdot10^{-8}$ |
| Off-list $A$ modulus at $16.377$ | $1.00138234620286$ |

Surplus improves by about $9.77\cdot10^{-9}$, but remains
more than $5.53\cdot10^{-8}$ below the target. Even setting
all penalties to zero at this raw price would not suffice.
The ordinary constant slabs alone leave over
$1.95\cdot10^{-8}$ in raw support unused: The negative
slabs account for over $1.57\cdot10^{-8}$, and the
nonnegative ones for over $3.83\cdot10^{-9}$. Thus freeing
only the releases and the tail at the trial's ordinary
laws cannot attain the target. The trial also fails the
continuous $A$ cap, at the same rational frequency that
fails on the seed. The quadratic test is necessary, not
the exact three-site second completion.

## How much must the seed fields move?

Let $I_k$ be an ordinary finite slab starting at $k/400$,
and let $Y^0_k$ be the seed value of $Y=A$ or $B$ there.
Write $H_k$ for the scalar atom support at the integrated
coefficients on $I_k$. For a rational slope $\delta_k$,
subtract $\delta_k(Y_k-Y^0_k)$ from the raw price on that
slab. The corrected support $H'_k$ is the scalar support
with the corresponding integrated coefficient increased by
$\delta_k$, plus $\delta_kY^0_k$. Certify a lower bound
$\ell_k\le H_k-H'_k$ by Bernstein subdivision of the
uncorrected and corrected scores on the full atom interval.
For any selection $J$ of corrected slabs,

$$
R\le 7.2\cdot10^{-10}-\sum_{k\in J}\ell_k
          +\sum_{k\in J}\delta_k(Y_k-Y^0_k).
$$

Indeed, the supremum of the raw price splits additively
at each ordinary slab, since the raw maximization has
independent laws there and on the complement. Replacing
those supports therefore reduces its upper bound by at
least the sum of the reductions. No component of the
complement is frozen.

- **One necessary $A$ move.** At $k=-320$, use
  $\delta_k=3538379393184/10^{20}$. Target surplus
  requires $A_k-A^0_k>0.004269$. The trial moves this
  field by about $0.012820$, so the test alone does not
  distinguish it from a target law.
- **A signed $B$ move across many slabs.** Use the
  [386 slopes][slopes] (units $10^{-20}$, including
  their signs). Target surplus requires
  $\sum_k\delta_k(B_k-B^0_k)>1.2605\cdot10^{-9}$.
  The trial pays only $2.96711\cdot10^{-10}$ even though
  it moves $B$ more than $10^{-6}$ on 366 of those slabs.
- **At least 41 $B$ moves.** If $|B_k-B^0_k|\le10^{-6}$
  except on at most 40 of the listed slabs, correct only
  the nonexceptional slabs. Their net reductions are at
  least $\ell_k-10^{-6}|\delta_k|$. Let the law choose
  the 40 exceptions by removing the largest positive net
  reductions. Even then $R<-1.1679\cdot10^{-10}$.
  The unrestricted five-release problem is not excluded.

## Replay and decision

```sh
PYTHONDONTWRITEBYTECODE=1 /opt/sage-10.9/bin/python .godel/bob/check-five-release-joint-refit-33.py
PYTHONDONTWRITEBYTECODE=1 /opt/sage-10.9/bin/python .godel/bob/check-five-release-joint-recovery-33.py
```

The first command checks the inherited full-domain upper.
The second checks the rational table, exact jump formulas
in Sage real and complex balls, and the local reductions.
Disks are deduplicated by frequency; every phase row is
retained for the raw price. The correction test uses exact
rational lower endpoints before sorting. Neither the
atom-grid slope search nor the grouped optimizer is proof
evidence.

**Next test.** Refit independently weighted common-law
atoms on the existing mesh and inherited constraints.
The [group-12 replay][group12] certifies that the first
shared-weight family cannot hit the target under those
constraints. Price the enlarged family before a target
solve; the old bound does not apply to independent weights.
Normalize the raw objective by subtracting local support
values; on each ordinary slab the remaining nonnegative
atom deficits have aggregate budget at most
$8.2\cdot10^{-10}$ for a target law. Price those deficits
on the resulting rounded law alongside the signed $B$
displacement, rather than counting how many fields move.
Keep the full quadratic and both disk lists in the check.
Do not spend a larger frequency search on this trial's
continuous violation yet: It has no near-target margin
even on the inherited constraints. The five-release and
eight-knot frontiers remain open, the seven-knot exclusion
is unchanged, and the Alpöge exclusion stays in force.

[domain]: five-release-joint-refit-33.md
[trial]: deletion-laws/delete-33-five-release-joint-recovery.json.gz
[seed]: five-release-recovery-33.md
[group12]: five-release-group12-decision.md#checked-exclusion-of-the-first-group-12-family
[slopes]: deletion-laws/delete-33-five-release-B-slopes.txt
