# Delete-33: Reprice independent laws on the recovery mesh

At depth $39/20$, consider the five slabs with starts
$(0,2,4,6,16)/400$, each of length $2/400$. The target is
$M-8/9\ge-10^{-10}$ under the 581 inherited $A$ disks, the
62 inherited $B$ disks, and the inherited quadratic $Q\le d$.
The [group-12 exclusion][group] only priced shared weights
on four stored atom modes and a seed. The question here is
whether dropping all those restrictions can reach target.

**Result.** The target is impossible on these five slabs,
even when their laws and the tail from $29/5$ are arbitrary
measurable and all other finite slabs have independent
constant laws. The common surplus upper is $-6.0\cdot10^{-10}$.
The zero-field convention left of $-144/25$ is unchanged.
This excludes one of the [seven assignments][frontier]
left by the earlier five-release screen, not the entire
five-release frontier. No other eight-knot assignment is
priced here.

The tighter upper $-7.2\cdot10^{-10}$ holds on the recovery
mesh of 2,701 cells: The five releases have spacing $1/25600$,
and the tail cell spacings in units of $1/400$ are
$8,16,32,64,128$ starting at $2320,5200,8800,12800,16000$,
respectively. The law from $56$ onward is the reference law.
There is no weight sharing, atom-site restriction, or
cardinality hypothesis on a cell.

## What changed

Retain the [joint-refit tangent][old], its center $Z$ and
quadratic multiplier $\sigma$, and all inherited frequencies
and unit directions $\gamma_i$. Change only 91 weights on
existing $A$ rows. The [replacement table][weights] is
indexed by zero-based position among the five-entry rows,
not among the deduplicated disks. All weights are nonnegative.
There are 603 directional $A$ rows at the 581 $A$ frequencies.
Using the [polarization identity][identity], every law
satisfying the inherited tests has $M-8/9\le R$, with

$$
R=M-8/9+\sum_i w_i(1-\Re(\bar\gamma_i V_i))
  +\sigma(d-Q(V_B))+\sigma Q(V_B-Z).
$$

All additional terms are nonnegative. The last two terms
combine to an affine functional of $V_B$. In particular the
constant $\sigma(d+Q(Z))$ and the full weighted sum of the
first-row constants must be included when changing weights.
The integrated price on one constant-law cell is linear in
its moments $A=\mathbb EX$, $B=\mathbb E(4X^3-3X)$, and
$U=\mathbb E u$, with $X=2u^2-1$ and $0\le u\le1$. Its
maximum over common laws is the maximum of its scalar atom
polynomial over all $u\in[0,1]$. The checker bounds that
maximum by Bernstein subdivision and sums the independent
cell uppers, including the exact reference remainder at $56$
for the mesh bound.

For a measurable law, interpolate the score of a fixed atom
at each cell's endpoints and midpoint and bound each of the
three Bernstein controls by an independent atom support.
The Bernstein weights are nonnegative, so the pointwise
upper also bounds any time-dependent probability mixture.
Integrate the controls and charge the uniform [remainder][error],
including the mass term. Use spacing $1/12800$ on the five
released slabs and $1/800$ on the tail through $60$; all
kernel branches are cell boundaries. Pay the analytic
allowance after $60$, with no fixed remote law. The
measurable upper computed this way is about
$-6.04190761559\cdot10^{-10}$; the mesh upper is about
$-7.26520283401\cdot10^{-10}$. These are prices, not
estimates of the optimal surplus.

To find the replacement weights, let $h=8.2\cdot10^{-10}$
be the inherited raw-support deficit budget. Target attainment
would imply $0\le 1-\Re(\bar\gamma_i V_i)\le h/w_i$ for
all positive original weights. The raw-support loss and
these upper and lower projection bounds gave a small LP
screen on independent weights for the inherited atom table. With
multipliers $\lambda_i^+$ and $\lambda_i^-$ on the upper
and lower projection rows, normalized in weighted units,
and multiplier $\lambda_R$ on the raw-deficit row, the
proposed weight factor was $1+(\lambda_i^+-\lambda_i^-)/\lambda_R$.
Keeping only the 40 largest adjustments lost the mesh
separation in floating repricing; keep all 91. The search
is not proof evidence:
The replay reassembles a valid nonnegative price and bounds
it directly over the entire atom interval. It does not rely
on LP termination, the floating raw-max law, the signed
$B$ displacement constraint, or a rounded primal candidate.

## Replay

```sh
PYTHONDONTWRITEBYTECODE=1 /opt/sage-10.9/bin/python .godel/bob/check-five-release-independent-price-33.py
```

The checker uses 128-bit Sage balls for the constants,
primitives, and Bernstein coefficients. It requires neither
an optimizer nor an external scratch artifact. The seven-knot
exclusion is unchanged. No Alpöge input is used.

**Next decision.** Do not refit this assignment. Reprice
one of the other six assignments with its own localized
projection budgets, retaining the same frequencies first.
If a new price is negative on a fit mesh, check the
measurable release and tail costs before claiming exclusion.

[group]: five-release-group12-decision.md#checked-exclusion-of-the-first-group-12-family
[frontier]: eight-piece-deletion-33.md#price-exactly-two-knots-and-refine-five-releases
[error]: measurable-negative-deletion-33.md#continuum-to-cell-bound
[old]: five-release-joint-refit-33.md
[identity]: five-release-curvature-33.md#identity-and-uniform-localization
[weights]: deletion-laws/delete-33-five-release-independent-price.json
