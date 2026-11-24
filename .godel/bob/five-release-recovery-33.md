# Delete-33: A common-law recovery on the inherited disks

At depth $39/20$ use the [five-release domain](five-release-joint-refit-33.md):
The slabs starting at $(0,2,4,6,16)/400$, each of length
$2/400$, and the tail from $29/5$ are measurable. Other
finite slabs are constant, and the fields are zero to the
left of $-144/25$. This is a **negative-surplus** law for
the finite inherited necessary constraints. Its continuous
first cap fails, and it is not a solution or an exclusion
on either open frontier.

## One law for all of the tests

The [law table](deletion-laws/delete-33-five-release-recovery.json.gz)
uses rows `[k, w0, u1, w1, ...]`. The knot is $k/25600$;
atom coordinates and mixture weights are in units of
$10^{-14}$. The first component of weight `w0` uses the
inherited reference probability law on the cell. All other
components are single atoms. The checker verifies the
partition, nonnegative weights, and exact normalization.
There are 2,701 finite cells and the law is the reference
after $56$. Nothing requires the same law in different cells.

The table comes from blending a blockwise atom search with
the reference, first in groups of four adjacent cells, then
splitting groups with the largest floating dual gain from
independent coefficients. Damping the result toward the
reference and rounding to exact weights repairs the finite
constraints. It is the rounded table, not the solver or
its dual, that proves the following values.

| Test | Checked value (rounded) |
| --- | ---: |
| $M-8/9$ | $-6.52353674\cdot10^{-8}$ |
| Largest of 581 inherited $A$ moduli | $0.99999999958145$ |
| Largest of 62 inherited $B$ moduli | $0.99999991734163$ |
| Full inherited $Q(V_B)-d$ | $-2.10370820\cdot10^{-8}$ |
| Off-list $A$ modulus at $16.377$ | $1.00139289729$ |

Disks depend only on field and frequency, so one modulus
checks all inherited phases there. The signed price below
uses **every** inherited row, including repeated frequencies
with distinct phases. The second result uses the full
quadratic, not a tangent inequality. Prefix and suffix
sums evaluate the two jump kernels on the fine mesh
without a dense convolution. The checker compares this
implementation with ordered-pair summation on an asymmetric
signed example. One value of $Q$ under its cap is necessary,
not the exact three-site second completion.

## Invisible changes cannot close the deficit

Now let the common law vary with $z$ while keeping its
pointwise pair $(A,B)$ fixed. None of the disk or second
measurements change. On each cell the [fiber table](deletion-laws/delete-33-five-release-recovery.fiber.json.gz)
gives a candidate dual slope pair $(a,b)$ in units of
$10^{-12}$, and up to three atom sites in units of
$10^{-14}$. The lower check solves the three moment
equalities over the rationals on the listed triple when
possible, and keeps the original law if those weights are
invalid or yield no gain. For the upper price, the checker
proves the scalar bound

$$
U\le aA+bB+\max_{0\le u\le1}\{u-aX-b(4X^3-3X)\},
\qquad X=2u^2-1.
$$

Bernstein subdivision bounds the maximum on the entire
interval. Jensen's bound $U\le\sqrt{(1+A)/2}$ is available
without slopes. The remote upper uses $U\le1$ and the
negative side has zero $M$ weight. Thus the upper allows
arbitrary measurable laws at the fixed fields, not just
listed sites, or even the table's spatial partition.

- A polished law attains surplus greater than $-6.09\cdot10^{-8}$.
- Every law at these fields has surplus below $-5.76\cdot10^{-8}$.

The moved tangent's signed first loss is about
$9.56\cdot10^{-9}$, and the second slack plus distance
loss is about $6.44\cdot10^{-9}$. Adding these losses back
still leaves the best raw price **at the fixed fields**
below $-4.16\cdot10^{-8}$. The fixed-field deficit is not
mainly a question of eliminating disk and quadratic penalties.

## Replay and decision

```sh
PYTHONDONTWRITEBYTECODE=1 /opt/sage-10.9/bin/python .godel/bob/check-five-release-recovery-33.py
```

Use the serialized law as a finite-constraint starting
point, not a near-optimal witness. Do not repeat the
$U$-only polish to pursue the $-10^{-10}$ target: Even
its measurable fixed-field upper misses that target by
more than $5.75\cdot10^{-8}$. Expand the available
joint moment directions in the finite recovery, and check
on the same rounded law how much raw price is reclaimed
and what loss it pays. The adaptive two-endmember blend
alone does not establish any upper bound for the
unrestricted fit. Defer a larger frequency search until
there is a useful recovery margin; the off-list test here
already disproves interpreting the finite checks as a
continuous-cap proof. Do not treat the accepted positive
raw supremum as feasible surplus. Five-release and
eight-knot frontiers remain open, the seven-knot exclusion
is unchanged, and the Alpöge exclusion stays in force.
