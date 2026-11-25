# Delete-33: A signed third-moment departure is necessary

At depth $39/20$, the 581 inherited $A$ disks alone exclude
fixed baseline $B$, even when $A$ and the common-atom laws
are allowed to vary measurably **everywhere**. The certified
upper on $M-8/9$ is below $-2.30\cdot10^{-7}$, so the older
[fixed-$A,B$ fiber exclusion](tail-fiber-deletion-33.md) need
not freeze $A$ for this conclusion. The new bound also
prices uniform third-moment bands with selected whole slabs
exempted; neither the $B$ disks nor the quadratic cap are
used.

Use the [baseline partition and law](deletion-laws/delete-33-tail-baseline.txt).
The left cutoff is $l=-144/25$, and $A=0$ to its left. A
law is a measurable choice of probability measure on
$0\le u\le1$, with $X=2u^2-1$, $T(X)=4X^3-3X$, and
$(A,B,U)=\mathbb E(X,T(X),u)$. Write $B_0$ for the
baseline's third moment, including its constant tail, and
$M=\int_0^\infty te^{-t}U(t)\,dt$. An exemption allows
arbitrary common-atom laws, not just arbitrary $B$ with
$A$ held fixed. Let $N$ be the four original slabs with
left endpoints $(-2304,-2288,-322,-216)/400$. These cover
the negative split sites of the [80-mask frontier](eight-knot-local-q-33.md).
The following bounds require $|B-B_0|\le\eta$ almost
everywhere outside the exempted slabs, and in fact only
up to $t=60$. They do not limit the number of knots.

| Exempted original slabs (adjoin by left endpoint) | $\eta$ | Strict upper on $M-8/9$ |
| --- | ---: | ---: |
| $N$ | $1/30000$ | $-2\cdot10^{-8}$ |
| $N\cup\{0\}$ | $1/50000$ | $-2\cdot10^{-8}$ |
| $N\cup\{2/400\}$ | $1/10^6$ | $-10^{-8}$ |

In particular, a refinement confined to the negative split
slabs, even if it allows measurable changes there and arbitrary
changes in $A$ elsewhere, must change $B$ elsewhere to reach
the target if it would otherwise keep $B=B_0$ there. The
band itself does not follow from the inherited tests; no
additional mask is unconditionally eliminated.

## One price, three release tests

Use the $A$ rows of the [radial price](check-eight-knots-radial-33.py).
With $w_i=1/2+if_i$, normalized stored normal $v_i$, and
$C_A=\cosh(39/20)/(6\cos(\pi/12))$, put
$$
a(t)=-e^{-t/2}\Re\sum_i
 \frac{\omega_i}{C_A}\frac{\overline{w_i}}{w_i}
 \overline{v_i}e^{if_it},\qquad m(t)=t_+e^{-t_+}.
$$
The convention is that of the [joint price](joint-tail-deletion-33.md#joint-price).
Adding $\sum_i\omega_i(1-\ell_i)\ge0$ to $M-8/9$ gives
$-8/9+\sum_i\omega_i+\int_l^\infty(aA+mU)\,dt$. Thus only
the upper price of this last integral is needed. The
checker verifies that the radial rows have the inherited
$A$ frequencies, use nonnegative weights, and use the
phase shown above. The baseline is used to define $B_0$,
not to provide a feasible $A$ or a law.

On each panel $[L,H]$ in $[l,60]$ interpolate $(a,m)$ at
the two ends and midpoint. The three quadratic Bernstein
controls are $(a_j,m_j)$, with middle control twice the
midpoint value minus half the sum of the endpoint values.
Use exact left and right slab labels at panel boundaries;
$B_0=b$ is constant in the panel interior. If $m_j>0$,
choose a real $\beta_j$ and bound the control by
$$
a_j A+m_j U\le h_j+s_j(B-b),\quad
h_j=\sup_{0\le u\le1}(a_j X+\beta_jT(X)+m_ju)-\beta_j b,
\quad s_j=-\beta_j.
$$
A floating search only proposes $\beta_j$. The atom
maximum is bounded with ball Bernstein subdivision of the
whole degree-six polynomial, not at the search atoms.
The inequality therefore also holds for mixtures.

If $m_j=0$, the largest root of $T(x)=y$ on $[1/2,1]$
is $r(y)=\cos(\arccos(y)/3)$ and every $X\in[-1,1]$
satisfies $X\le r(T(X))$. The upper branch $r$ is
concave, since $T$ is increasing and convex there. Put
$e=\operatorname{sgn}(a_j)$ and use $h_j=|a_j|r(eb)$ and
$s_j=e|a_j|r'(eb)$, by applying the tangent to $eX$ and
using oddness of $T$. When the sign is not certified the
checker may instead take $(|a_j|,0)$. On an exempted
panel, use the unrestricted support for each control,
with $\beta_j=0$ (or $|a_j|$ at zero mass).

The Bernstein basis has nonnegative terms and integral
$(H-L)/3$ for each control. The integral of the absolute
nodal cubic product divided by $3!$ is $(H-L)^4/192$.
Since $|A|,|U|\le1$, multiply by the sum of the bounds on
$|a'''|$ and $|m'''|$ to debit the interpolation error.
For the first, use
$e^{-L/2}\sum_i\omega_i|w_i|^3/C_A$; for the second use
$(3+H)e^{-L}$ on the nonnegative side and zero on the
negative side. No panel straddles zero. The remote price
uses $|A|,U\le1$ directly on $[60,\infty)$, so it needs
no band restriction. Both debits are paid before any
exemptions. The band penalty is at most $\eta$ times the
sum of $(H-L)|s_j|/3$ on unexempted panels. The full sum
of these absolute slope prices is below $0.0057$.

## The signed observable is necessary but loses curvature

On each unexempted panel define $S(t)$ as the quadratic
Bernstein polynomial whose **signed controls** are $s_j$,
and set it to zero elsewhere. Without any band assumption,
the same certificate bounds the surplus by
the fixed-$B$ upper plus the release price plus
$\int S(t)(B(t)-B_0(t))\,dt$. For the three release sets in
table order, attaining $M-8/9\ge-10^{-10}$ therefore requires
this integral to be strictly above $2.20\cdot10^{-7}$,
$1.50\cdot10^{-7}$, or $1.90\cdot10^{-8}$, respectively.
These are three separate tests, not additive penalties.

The first $B$ cap and quadratic cap cannot force this
affine certificate below the target, even on the original
partition with **no extra knots**. Use
$$
B_*=(1-10^{-5})B_0-\frac1{200}\,\mathbf1_{[36/400,38/400)}.
$$
The real-frequency $B$ norm is below $0.99998$ (hence all
62 inherited $B$ disks hold), and $d-Q(V_{B_*})$ is above
$1.18\cdot10^{-5}$. The quadratic check evaluates the
whole form with the inherited majorant, not separate
prices for the dilution and the dip. For all three
exemption sets, the signed integral is above
$2.65\cdot10^{-7}$ and above even the **unrounded**
threshold given by the corresponding affine certificate.
The failure is not an artifact of rounding the thresholds
in the preceding paragraph.

The field $B_*$ can be lifted to deterministic common
atoms by setting $X=r(B_*)$ and $u=\sqrt{(1+X)/2}$ on each
original piece. That lift has $M-8/9>0.0225$ but violates
an inherited $A$ disk: Its normalized $A$ modulus at
frequency zero exceeds $49$. More strongly, recomputing
the atom prices at $B_*$, rather than using the tangent
at $B_0$, gives $M-8/9<-9\cdot10^{-8}$ in each of the
three cases for any law meeting the $A$ disks, with
$B=B_*$ required only outside that case's exemptions.
Thus the witness defeats pricing the **fixed linear
observable** using $B$ disks and $Q$ alone, not a
curvature-aware $B$ price. It is not a counterexample to
the eight-knot exclusion.

A next test is to retain the varying common-atom support
when charging for $B$ motion, or to keep an $A$-sensitive
constraint in the joint price. Merely maximizing this
fixed signed observable over the $B$ constraints cannot
close any of these three tests.

Replay with SageMath's Python and assertions enabled:
`.godel/bob/check-third-moment-band-33.py`. Its `--reference`
mode checks control conversion, both zero-mass branches,
positive-mass prices, and the signed disk phase.
