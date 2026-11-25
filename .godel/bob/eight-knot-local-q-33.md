# Delete-33: Restore quadratic loss on the first negative slab

At depth $39/20$, **57 of the 137 radial upper-price masks**
cannot attain $M-8/9\ge-10^{-10}$. The deletion uses the same
radial cuts and center, not a refit. It acts only on masks with
one interior knot in $[l,r)=[-2304,-2288)/400$. The other 75
masks are untouched. The 80 remaining masks are not shown
feasible.

The domain is the [eight-knot frontier](eight-piece-deletion-33.md#eight-knots-exclude-the-all-nonnegative-class)
on the [1,257-knot partition](deletion-laws/delete-33-tail-baseline.txt).
The two first fields vanish to the left of $l$. On each finite
original or split piece the law is independently arbitrary and
constant, and from $29/5$ onward it is arbitrary measurable.
Each law has common atoms $0\le u\le1$ with moments
$(A,B,U)=\mathbb E(2u^2-1,T(2u^2-1),u)$, where $T(X)=4X^3-3X$,
and $M=\int_0^\infty te^{-t}U(t)\,dt$. Impose the inherited
581 $A$ disks, 62 $B$ disks, and $Q(V_B)\le d$. The masks
record original slab starts and counts (one or two). They
all spend eight units, so a two means exactly two interior
knots. Baseline boundaries and repeated knots are not new
interior knots. No restrictions on the jumps or variation of
the measurable tail are imposed.

## The loss that the tangent discards

Use the [joint-price conventions](joint-tail-deletion-33.md#joint-price):
$w=1/2+ix$, $E(t)=e^{-t/2}$, $\widehat f(x)=\int f(t)e^{ixt}\,dt$,
$d\mu=dx/(2\pi|w|^2)$, $C=\cosh(39/20)/3$, and
$V_B=(\bar w/w)\widehat{EB}/C$ (for $A$, use
$C/(2\cos(\pi/12))$ in place of $C$). Let $h_0=13/25$ and
$s\in\{-7,6,19\}/25$. Write $H=\sum_s\lambda_s e^{isx}$
and $q(h_0x)=\sum_m q_m e^{imh_0x}$ with $q_{-m}=q_m\in\mathbb R$.
The checker constructs the same certified Laurent majorant $q\ge |H|$,
sets $d=\int q\,d\mu$, and uses the real polarization
\[
Q(F)=\int(q|F|^2+\Re(HF^2))\,d\mu,\qquad
\mathcal B(F,G)=\Re\int(q F\overline G+HFG)\,d\mu.
\]
In particular $Q\ge0$ on ambient $L^2(\mu)$ and
$|\mathcal B(F,G)|\le\sqrt{Q(F)Q(G)}$ by positivity of
$Q(F+tG)$ for real $t$.

The accepted radial checker constructs the cut list and the
bounded step center $B_c$ on the original mesh, zero left of
$l$ and constant on the tail. Let $Z=(\bar w/w)\widehat{EB_c}/C$,
$V=V_B-Z$, $f=E(B-B_c)\in L^2(\mathbb R)$, and
$L=1+\max|B_c|$. The $L^2$ claim follows from the left cutoff
and $|B-B_c|\le L$. The center is not assumed to be a law.
$\ell_i\le1$ is the normalized disk cut on its first field,
with weight $\omega_i\ge0$. The raw linear score before
support bounds is
\[
\mathcal L=M-8/9+\sum_i\omega_i(1-\ell_i)
   +\sigma\bigl(d+Q(Z)-2\mathcal B(Z,V_B)\bigr).
\]
Its linear terms are evaluated by the inherited primitives.
The exact slack identity is
\[
\mathcal L-(M-8/9)=\sum_i\omega_i(1-\ell_i)
   +\sigma(d-Q(V_B))+\sigma Q(V),
\]
since $2\mathcal B(Z,V_B)=Q(Z)+Q(V_B)-Q(V)$. The checker
verifies $\sigma>0$. In particular $M-8/9\le\mathcal L-\sigma Q(V)$.
We use part of that loss to charge a positive drop $D=B_L-B_R$
at the unknown knot $k\in[l,r]$; the side subscripts are its
left and right laws, not center values.

## A test field for a whole knot cell

For a cell $[a_0,b_0]\subset[l,r]$, take its midpoint $c_0$ and
let $h_-=c_0-l$, $h_+=r-c_0$. Define $\phi=0$ off $[l,r]$ and
$\phi(y)=p(|y-c_0|/h_\pm)$ on its two halves, where
$p(v)=1-3v^2+2v^3$. It is nonnegative and decreases from 1 to 0
as $v$ runs from 0 to 1. It and its derivative match at $c_0$
and are clamped at $l,r$, so $\phi\in H^2(\mathbb R)$. Put
\[
g=-\phi'+\tfrac12\phi,\qquad
P=(\bar w/w)|w|^2\widehat g=\bar w^2 w\widehat\phi.
\]
Here $\widehat g=w\widehat\phi$ in the positive Fourier
convention, and $P\in L^2(\mu)$ by the $H^2$ bound. We use
$J=\int\phi=(r-l)/2$ and $\|\phi'\|_1=2$ for every cell.

**Hermitian pairing.** In $C\mathcal B(V,P)$ the $q$ multiplier
reduces to $q\widehat f\overline{\widehat g}$ with measure
$dx/(2\pi)$. Plancherel gives the real sum of
$q_m\int f(y-mh_0)g(y)\,dy$. For $m=0$ this integral without
$q_0$ is
\[
\int f g=\langle (B-B_c)',E\phi\rangle=-E(k)\phi(k)D.
\]
In this identity $(E\phi)'=-Eg$ and the boundary terms are
zero. The negative translations of the support (positive $m$)
are left of $l$ and give zero. By symmetry of the coefficients,
write the remaining translated intervals as $[l+mh_0,r+mh_0]$,
$m\ge1$. For $m=1,\ldots,7$ each is within a single original
unsplit slab for every tested mask, as checked from its endpoints
and the union of the split sites. There $B-B_c$ is constant and
$\int E g=0$, so these terms are also zero. For $m\ge8$ use
$|f(t)|\le L E(t)$ and $\|g\|_1\le2+J/2$, giving the bound
$L E(l+mh_0)(2+J/2)$ before multiplication by $|q_m|$.
This bound does not require constancy there.

**Reflected pairing.** For the $H$ term in $C\mathcal B(V,P)$,
the multiplier after the weight is $\bar w^2/w=w-2+1/w$
acting on $\widehat f$ in the product $e^{isx}\widehat f\widehat\phi$.
This pairs the transformed $f$ at $t=-y-s$ against $\phi(y)$.
In the time variable $w-2$ gives
\[
-f'(t)-\tfrac32 f(t)=-E(t)(B-B_c)'(t)-f(t).
\]
The first term vanishes for $s=6/25,19/25$, since the checker
locates $[-r-s,-l-s]$ within one unsplit original slab. For
$s=-7/25$ this interval lies in the measurable tail. Pair its
derivative distribution with $E(t)\phi(-t-s)$ and integrate
by parts against the bounded $B-B_c$. With no endpoint term,
the absolute value is at most $L E(-r-s)(2+J/2)$. This uses
only the $L^1$ norm of the derivative of the **test**. The
$-f$ term is bounded by $L E(-r-s)J$ for each $s$. Also $1/w$
is the Fourier transform of $\mathbf 1_{t\le0}e^{t/2}$, so its
convolution with $f$ is
\[
\int_t^\infty e^{-(z-t)/2} f(z)\,dz,
\qquad \left|\int_t^\infty e^{-(z-t)/2} f(z)\,dz\right|
   \le L E(t).
\]
It costs the same $L E(-r-s)J$. The Fourier identities hold
first for smooth compactly supported $f,\phi$ by inversion.
The derivative pairing extends in $L^2$ for $f$ and $H^1$
for the test, since $w\widehat\phi\in L^2$; the other terms
are bounded already on $L^2$. The test used here is in $H^2$.
No derivative of the tail is assumed to be a function or
finite measure.

Consequently $C\mathcal B(V,P)=-q_0 E(k)\phi(k)D+\epsilon$,
where $|\epsilon|\le\mathrm{err}$ uniformly on each cell, with
\[
\mathrm{err}=L\left[(2+J/2)\left(\sum_{m\ge8}|q_m|E(l+mh_0)
          +|\lambda_{-7/25}|E(-r+7/25)\right)
          +2J\sum_s |\lambda_s| E(-r-s)\right].
\]

**Probe norm.** In $Q(P)$ the Hermitian multiplier is
$q|w|^4$ against $|\widehat\phi|^2$ with measure $dx/(2\pi)$.
Expand $|w|^4=(x^2+1/4)^2$ and use Plancherel on each of
$\phi,\phi',\phi''$. Every nonzero $q$ shift gives zero for
each of these correlations since $r-l<h_0$. The reflected
multiplier is $e^{isx}\bar w^3 w$ against $\widehat\phi^2$.
It is polynomial apart from the shift, so before the shift it
is the transform of a linear combination of derivatives of
$\phi*\phi$, supported on $[2l,2r]$. Its pairing at $-s$
vanishes because $2r+s<0$. For example, mollify $\phi$ with
smooth compactly supported kernels of shrinking support; the
strict separation persists and convergence in $H^2$ gives
convergence of the pairing by Cauchy–Schwarz with the weight
$|w|^4$. Thus exactly
\[
\mathrm{den}=Q(P)=q_0\sum_{h=h_-,h_+}\sum_{j=0}^2
  {2\choose j}4^{-(2-j)} I_j h^{1-2j},\quad
(I_0,I_1,I_2)=(13/35,6/5,12),
\]
where the outer sum counts both half lengths even if equal,
and $I_j=\int_0^1(p^{(j)})^2$.

## Buying a tilt with the loss

Set $v=(b_0-a_0)/(2\min(h_-,h_+))$ and $a=q_0 E(b_0)p(v)$.
For $D\ge0$ the preceding pairing and positivity give
\[
aD\le\mathrm{err}+C\sqrt{Q(V)\mathrm{den}}.
\]
For $D<0$ this also holds since $a\ge0$. If $a>0$, then for
$\beta\ge0$ complete the square in $\sqrt{Q(V)}$ to obtain
\[
\beta D-\sigma Q(V)\le
  \beta\,\mathrm{err}/a+\frac{(\beta C/a)^2\mathrm{den}}{4\sigma}.
\]
Independently $D\le2$ and $Q(V)\ge0$, so the fee is bounded by
$2\beta$. Use the smaller certified upper, or just $2\beta$
if positivity of $a$ is not certified (in particular on the
edge cells with $v=1$). This gives a cell-wide bound on the
surplus by the raw score with $-\beta D$ added, plus the fee.
For the atom convention $m u-a_I X-b_I T(X)$, this means
adding $\beta$ to the **left** $B$ coefficient and subtracting
it from the **right** one.

## Computing and applying the cell bounds

Use the same radial cut list, changing only prices. The
inherited base routine prices the original finite mesh and the
arbitrary measurable tail with $1/400$ cells through $60$ and
an exponential remote allowance. For each nonlocal single
split used by the 62 tested masks, compute the direct shared-
coordinate price at $1/6400$; the sentinel 1 selects these
sites and is verified inactive as a cap. The inherited
ordered-control routine prices double splits at $1/3200$.
Each of these calculations bounds the increment over the
original finite mesh; none spends the quadratic loss.

On $[l,r]$ the mass primitive is constant, so both mass
coefficients are exactly zero. Partition the interval into 256
closed cells of width $1/6400$. Use endpoint and midpoint
primitives for the shared knot coordinate. The three quadratic
Bernstein controls are the endpoint values and twice the
midpoint minus half the sum of the endpoints. For each
$\beta=j/(2\cdot10^9)$, $0\le j\le44$, bound the sum of the
two tilted atom supports at each control. For fixed adjacent
laws the tilt is independent of the position, so the same
$\beta$ applies at all three controls and the maximum of the
three bounds prices the interpolant. Add the cell fee and take
the minimum over the candidate $\beta$'s. The uniform
interpolation remainder still uses the inherited primitive
third-derivative bound for a difference of two laws: if the
envelope is $\mathrm{curv}\,E(t)$ and the cell width is $h$,
the remainder is at most $\mathrm{curv}\,E(l)h^3/(72\sqrt3)$
by the endpoint–midpoint interpolation formula. No kernel
branch is interior to a cell: the center knots, $q$ shifts,
and $H$ sites all lie on the $1/400$ lattice. The bound is
uniform before maximizing over all laws and knot positions.

For the local increment, subtract the unsplit atom bound used
in the base, less the atom routine's $10^{-14}$ tolerance
(the tolerance is added back conservatively). Each base or
increment is rounded upward to integer units of $10^{-16}$
from ball uppers or exact rationals. Use the largest rounded
cell increment for a mask-level decision; for position counts,
use each cell's own increment. Delete only an integer total
**strictly** below $-1000000$. Equality is counted as unpaid.
There are finitely many masks because the radial export
already covers every assignment not previously priced out;
the 256 cells exhaust the **real** knot interval, including
cell boundaries. For edge counts, a run of excluded cells
starts from each end, so a fully excluded interval reports
256 in both columns, rather than counting 512 distinct cells.

| Negative starts (units of $1/400$) | Masks before | Worst plain upper | Worst paid upper | Masks left | Worst-mask cells left | Left/right edge cells excluded |
|:--|--:|--:|--:|--:|--:|:--|
| $(-2304)$ | 21 | 112823619 | -64289659 | 0 | 0 | 256 / 256 |
| $(-2304,-216)$ | 41 | 243037532 | 65924254 | 5 | 74 | 4 / 176 |

The worst mask in each row is determined by the largest
complement price (the local increment is common to the row).
The 75 untouched masks comprise 71 with negative starts
$(-216)$, two with $(-2288,-216)$, and two with $(-322,-216)$.
Of the 13 masks with a double slab, three are excluded and
10 are retained. The largest rounded upper among the 57
exclusions is $-11321191$ in units of $10^{-16}$, strictly
below the cutoff $-1000000$.

## Replay

Run with SageMath 10.9 and assertions enabled. From the
repository root, reproduce the radial export by the two
[accepted frontier replay steps](eight-piece-deletion-33.md#eight-knots-exclude-the-all-nonnegative-class),
then pass that `radial.json` to this checker. It pins the
export by SHA-256
`34df5c789255c8c519db79ca76f915eb2461b44e8b60c332f696e7bcb8ea1ef8`.
No search scratch is needed.

```sh
PYTHONDONTWRITEBYTECODE=1 /opt/sage-10.9/bin/python .godel/bob/check-eight-knots-local-q-33.py --reference
PYTHONDONTWRITEBYTECODE=1 /opt/sage-10.9/bin/python .godel/bob/check-eight-knots-local-q-33.py "$work/radial.json" --write-eight "$work/local-q.json"
```

The reference controls check the tilt orientation, the
positive-$a$ fee and fallback branches, the probe norm and
clamped cubic integrals, and strict exclusion at equality.
The full checker also verifies the input partition, mask and
cut counts, positive multiplier, sign and separation geometry,
and the resulting margins and residual counts. The canonical
80-mask export has SHA-256
`b15f16a1fc3662d4187dbbec71ec0cde6a77579b5fa015d34f5397b04ea4e31f`.
