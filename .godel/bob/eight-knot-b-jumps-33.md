# Delete-33: Price oriented third-moment jumps

The parent claim remains open: Exclude the 80 surviving
signed eight-knot masks at depth $39/20$ at target
$M-8/9\ge-10^{-10}$. Use the [local-quadratic frontier][front],
including its 581 $A$ disks, 62 $B$ disks, and $Q\le d$.
The common laws are independently constant on finite
pieces, field values vanish to the left of $-144/25$,
and the tail from $29/5$ is arbitrary measurable. An
earlier [necessary $A$ drop][drop] concerns a different,
negative slab. No Alpöge input is used.

Write $k$ for a slab's left endpoint in units of $1/400$.
Test the even $k$ in $[6,34]$ and $[38,52]$ that are split
in a mask. Define $J_k$ as the sum of positive upward
jumps of $B$ inside the slab for $k\le34$, and the sum of
positive downward jumps for $k\ge38$. These are one-sided
variations, not endpoint differences when there are two
knots. Every attaining law on an 80-mask survivor must:

* Have $J_k>0.0412$ on at least one tested slab.
* Have $J_k>0.0368$ on at least two distinct tested slabs.

The negative sites, $0,2,4,36,184$, and jumps between
original slabs are not subject to these conditions.
Neither condition excludes a mask unconditionally.

## Preserve the atom maximum, charge the residual

Use the [radial tangent][front] with score density
$m u-aX-bT_3(X)$, $X=2u^2-1$, $T_3(X)=4X^3-3X$, and
$m=t e^{-t}$ on the positive test slabs. For one such
slab $[l,r]$, let $v$ be a stationary atom for the score
with coefficients integrated over the original slab.
Bracket $v$ in $(0,1)$ by exact rational endpoints and
ball signs of the integrated derivative. Put
$$
D(v)=4v\{12(2v^2-1)^2-3\},\qquad
b_*(t)=\frac{m(t)-4v a(t)}{D(v)}.
$$
Here $D$ is the atom derivative of $T_3(X)$ at $v$.
The certified bracket keeps $D$ away from zero. Integrated
stationarity gives $\int_l^r b_* = \int_l^r b$. Also,
with $S_*(u)=m u-aX-b_*T_3(X)$ pointwise,
$$
S_*(u)-S_*(v)=(u-v)^2\left[-16b_*(u+v)^2(2u^2+4v^2-3)
-\frac{m}{2v}\right].
$$
The bracketed expression is strictly negative on the
whole product of the slab and $[0,1]$, as certified by
ball boxes of width $1/6400$ in time and $1/32$ in $u$.
For the time boxes, enclose $a$ and $m$ by their endpoint
unions plus the ordinary second-derivative secant debits.
In particular $v$ maximizes the new pointwise score, even
against mixtures. Its integral is the **original whole
slab support**: It is attained at $v$ with either integrated
price, and a constant competitor has the same integrated
price before and after the change. This construction does
not impose a relation on $A,B,U$ other than their common
law, nor does it change any disk or $Q$ constraint.

Set $P(t)=\int_l^t(b-b_*)$, so $P(l)=P(r)=0$. The original
minus new score on a split slab is exactly
$$
-\int_l^r (b-b_*)B = \sum_j P(x_j)(B_{j+1}-B_j),
$$
where $x_j$ are the interior knots. This determines the
sign of the charge. Bound $P$ on each $1/3200$ cell by
quadratic Bernstein controls interpolating the endpoints
and midpoint, with allowance
$$
\frac{e^{-l/2}}{3200^3\,72\sqrt3}
\left[(1+|4v/D(v)|)\,\mathrm{curv}+2/|D(v)|\right].
$$
The inherited `tail_data` curvature envelope bounds the
second derivatives of both price densities, with $2e^{-t/2}$
covering $|m''|$. The branch sites of the tangent kernels
lie on the $1/400$ lattice, so are never interior to an
interpolation cell. Store both extrema separately, with
outward rounding: $p_k$ is the larger one-sided price
(upper for $P$ before $36$, upper for $-P$ after $36$),
and $q_k$ is the opposite nonnegative price. At $k=6$
the two prices are $5.364077844\cdot10^{-7}$ and
$2.2114\cdot10^{-12}$, respectively.

## Mask budget

Work in integer units of $10^{-16}$. Start at the rounded
unsplit base $-2187294957$, including the measurable tail
and the remote debit. Let $R_k$ round up the direct
increment for the mask's count $n_k$ of interior knots.
The one-knot routine uses a $1/6400$ mesh and the two-knot
routine uses ordered cells. The five masks using $-2304$
pay that site's accepted local-quadratic increment once,
recomputed as $97311793$ instead of $274424971$. This
purchase already subtracts the quadratic remainder;
no other remainder payment is made in the mask budget.

With $p_k,q_k$ also expressed in integer units, a cap
$J_k\le c$ on a tested slab changes its increment to
$$
\min\{R_k,\lceil c p_k\rceil+2n_k q_k\},
$$
since each reverse jump has size at most $2$. Untested
slabs pay $R_k$. To leave one tested slab free, add back
the **largest** difference between raw and clipped cost
on the mask, not the difference at a predetermined site.
The checker takes the largest resulting budget in each
mask group. The largest passing caps on the $10^{-4}$
grid are:

| Negative sites | Masks | No free slab | One free slab |
| --- | ---: | ---: | ---: |
| $-216$ | 71 | 0.0412 | 0.0368 |
| $-2304,-216$ | 5 | 0.0462 | 0.0429 |
| $-2288,-216$ | 2 | 0.0480 | 0.0458 |
| $-322,-216$ | 2 | 0.0485 | 0.0465 |

Each entry gives a group maximum strictly below $-1000000$,
the target in integer units. One grid step above it
fails that strict test. This is saturation of the integer
budget, not sharpness of an extremum over laws.

## A B-only obstruction to enforcing the jump caps

On the mask $(-216,0,2,4,6,8,10,12)$, keep the baseline
$B_0$ except on the four original slabs at $6,8,10,12$.
On the left half of each use $B_0-1/40$, and on the right
half use $B_0+1/40$. This field has four favored jumps of
$1/20$ and no reverse jump on the tested slabs. It is in
$(-1,1)$ on the nonzero domain, with all inherited $B$
disk moduli below $0.999976$ and $d-Q(V_B)>4.8\cdot10^{-6}$.
The code evaluates full quadratic forms with cross terms,
both here and in the distance from the radial center $Z$.

More than just the $B$ feasibility tests pass. The field's
entire $B$-side slack in the radial identity,
$$
L_B=\sum_{i\in B}\omega_i(1-\ell_i)+
\sigma\bigl(d-Q(V_B)+Q(V_B-Z)\bigr),
$$
is less than $1.04\cdot10^{-8}$ and fits inside the
conditional raw-budget allowance above target computed at
its own four variations and zero reverse variation. The
allowance is $1.36067713\cdot10^{-8}$, leaving more than
$3.20\cdot10^{-9}$ after the $B$ loss. Thus adding this
scalar slack screen to the $B$ constraints still does not
enforce either cap. The screen does not fix $B$ inside
the raw support maximizations, and it does not test all
real frequency caps.

Restoring an $A$-sensitive input distinguishes this
field. For the earlier [signed baseline departure][band],
exempt the four negative slabs and the slab at $0$. The
only changes outside those slabs are on eight half-slabs,
so it suffices to recompute the accepted signed slopes
on those eight panels. The witness signal lies between
$9.13\cdot10^{-8}$ and $9.14\cdot10^{-8}$, strictly below
the certified necessary signal $1.50\cdot10^{-7}$. Thus
the witness cannot be completed to the target under the
$A$ disks, even if $B$ is released measurably on those
five exempt slabs. This uses a separate necessary test,
not addition of bounds from two tangent certificates.
It keeps $B$ fixed to the witness on the rest of the
domain through $60$, including the tail before $60$.

## A diluted dip passes the affine test, not the repriced test

The preceding affine rejection does not survive even a
simple change of the unsplit levels. Starting from the four-jump
field, subtract $3/1000$ on $[36/400,38/400)$, then multiply
the whole field, including its tail, by $1-1/200000$.
This uses the same eight-knot mask: The dip changes an
original slab level and consumes no knot. All four jumps
are now $0.04999975$. The resulting field passes **all
real-frequency $B$ caps** with modulus below $0.999999$,
and the 62 disk moduli are below $0.999980$. It has
$d-Q(V_B)>4.8\cdot10^{-6}$, and its full $B$ loss remains
below $1.04\cdot10^{-8}$ with over $3.20\cdot10^{-9}$
left in the raw-budget allowance at its own jump sizes.
The cap checker uses interval Taylor bounds on a bounded
frequency range and a total-variation estimate beyond it.

Release the same four negative slabs and the slab at $0$
in the $A$-only test. The exact gap for the baseline
support upper bound with those releases is approximately
$1.5104\cdot10^{-7}$. The dip and four jump slabs give
signed affine signal greater than $2.73\cdot10^{-7}$,
including dilution there. On the complement through $60$,
the slope sum from the baseline checker bounds the
absolute effect of dilution by $2.81\cdot10^{-8}$, since
$|B_0|\le1$. The full signed signal is thus greater than
$2.43\cdot10^{-7}$: The affine test no longer rejects,
even with continuous $B$ caps and the scalar $B$ loss
screen both included.

However, evaluating the $B$-fixed common-atom support
upper bound with fresh tilts on just the ten changed
half-panels, and keeping the baseline tilts and the
same dilution debit everywhere else, gives
$M-8/9<-6.7\cdot10^{-8}$. This retains the original
interpolation and remote debits, and uses no prescribed
values on the five released slabs or after $60$. Thus
this second witness also has no attaining completion
under the $A$ disks. The calculation does not combine
prices from separate tangent certificates or establish
an exclusion on all fields with the four jumps.

**Next test:** Use the repriced common-atom controls,
rather than a baseline affine threshold by itself, when
varying the $B$ levels and the measurable tail. To price
the whole frontier, the test must still handle changes
at $2,4$ and on the tail, not just dilution or the dip
on $[36/400,38/400)$.

## Replay

With SageMath 10.9 and assertions enabled, regenerate the
canonical `local-q.json` by the first three producers in
[the prior replay][replay] (155, 137, and 80 masks). Then
run, with `$work` pointing to that export directory:

```sh
export PYTHONDONTWRITEBYTECODE=1
sagepy=/opt/sage-10.9/bin/python
"$sagepy" .godel/bob/check-eight-knots-b-jumps-33.py --reference &&
"$sagepy" .godel/bob/check-eight-knots-b-jumps-33.py "$work/local-q.json"
```

The checker pins the export digest, and checks the mask
counts and split multiplicities. The reference checks the
exact atom factor, signed integration by parts, integer
rounding, the reverse charge, and free-slab selection.
The full checker also replays
the $A$-only band computation to obtain the panel
controls and the baseline release gap for repricing.

[front]: eight-knot-local-q-33.md
[drop]: eight-knot-a-drop-33.md
[replay]: eight-knot-a-drop-33.md#replay
[band]: third-moment-band-33.md
