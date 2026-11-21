# Transport between the rational real and global levels

**Status:** Independently reviewed project calculations on the rational
real-band model. The theta edge and first-pair formula are checked in Lean;
the operator and trace calculations below are not. Source locators refer to
the digest-matched [pinned PDF](../sources/masullo/README.md) via
`pdftotext -layout`; claims about the text are provisional. This continues
the [positive-log control](trace-to-zeros.md#first-unmatched-geometric-evaluation-and-a-positive-log-control),
not the divisor uniqueness argument.

## Which transport is at issue?

Use $F=\mathbb Q$, $S=\{\infty\}$, and the trivial compact isotype. The two
level spaces in (11.2.1.6–7), pp. 488–489, are closures of *different* theta
images, local and global, and (11.2.1.8) projects orthogonally on the global
image closure. Those displays use $W^{s,2}$, not the positive-width norm.
For the positive-width model here, use the local and global twisted
Hardy–Sobolev norms (10.1.1.3–5), p. 434, with $a=1/2$, $I=[-\alpha,\alpha]$,
and $s=2r$, and the weight (9.2.2.41), p. 417. The centered real band on the
generator is the $S'=S$ case of (7.3.2.12–17), pp. 354–355. The real local
quotient by $\{\pm1\}$ and the rational class group modulo its compact
factor both have log measure $dx$ with the normalized Haar convention.
The unramified tensor transition (2.1.4.2–5), p. 71, and the global lift
(11.3.1.1), p. 492, use integer-ring tensors outside $S$. This calculation
does not identify all the global levels with this model. In particular,
no auxiliary finite factors from (7.3.2.13) enter this chosen core.
Thus the natural transport on these test generators pairs the same real
factor $b$ on both sides, but sums over
nonzero **integers**, rather than over the real $S$-units $\{\pm1\}$, on the
global side. The two sums are (2.2.3.1), p. 81, and (2.3.1.2), p. 99;
see also Remark 2.3.2.3, p. 106. The accepted theorem
`Masullo.rationalTheta_eq_unramified_sum` checks the global reduction on
the positive real section.

The proof on p. 515 appeals to Lemma C.3.2.2, pp. 695–696, for a trace
transfer on the *local* polar-free test image. The lemma needs a continuous
injection and a nuclear reverse factor with the given endomorphism as
their composition. It does not make the test-generator pairing a continuous
injection of the two **Hilbert** level closures. The density and semigroup
invariance in Proposition 7.3.2.4, pp. 355–357, and the fixed-position
level limit (11.2.1.9–10), p. 489, do not give such a Hilbert bound either.
The following control tests this particular way of trying to carry out the
missing comparison on p. 520. It does not challenge the local nuclear
factorization through a different, stronger topology.

## Uncut transport is unbounded even at a fixed band

Put $H=L^2(w\,dx)$, where $w(x)=e^{2\alpha|x|}(1+x^2)^r$,
$0<\alpha<1/2$, and $r\ge0$. For any $B>0$ let $\mathcal B_B$ consist of
even complex Schwartz $b$ with $b(0)=\int_{\mathbb R}b=0$ and additive
Fourier support strictly inside $[-B,B]$. Set

$$U_b(x)=e^{x/2}b(e^x),\qquad
  V_b(x)=e^{x/2}\sum_{n\ge1} b(ne^x).$$

Both are one half of the corresponding full half-twisted theta profile.
They lie in $H$: $b(t)=O(t^2)$ at zero by evenness and $b(0)=0$;
the global Poisson formula with both moments zero gives $V_b(x)=0$ for
$e^x<1/B$. Both profiles have rapid decay on the right by the Schwartz
bound (sum over $n$ for $V_b$).
Write $L_B=\overline{\{U_b:b\in\mathcal B_B\}}$ and
$G_B=\overline{\{V_b:b\in\mathcal B_B\}}$ in $H$. There is **no** finite
$C_B$ such that $\|V_b\|_H\le C_B\|U_b\|_H$ on $\mathcal B_B$.

To prove this, suppose there is such a bound. For any even two-moment
Schwartz $b$ of *any* finite band, take $b_L(t)=e^{-L/2}b(e^{-L}t)$ for
$L>0$. Its Fourier support contracts by $e^{-L}$, so $b_L\in\mathcal B_B$
for large $L$. The two profiles are translated by $L$. For $h=U_b,V_b$,

$$\frac{\|h(\cdot-L)\|_H^2}{e^{2\alpha L}(1+L^2)^r}
\longrightarrow \int e^{2\alpha x}|h(x)|^2\,dx.$$

The pointwise weight ratio tends to $e^{2\alpha x}$ and is bounded by
$2^r w(x)$, using $1+(L+x)^2\le2(1+L^2)(1+x^2)$ and the triangle
inequality. The assumed bound therefore holds on the right boundary in the
unweighted $L^2$ norm of the exponentially twisted profiles, for every
finite-band generator. With the positive-sign log Fourier transform
$\mathcal F_+ h(t)=\int e^{itx}h(x)\,dx$ and $\sigma=1/2+\alpha$, Mellin
continuation gives

$$\mathcal F_+(e^{\alpha\cdot}V_b)(t)
   =\zeta(\sigma+it)\mathcal F_+(e^{\alpha\cdot}U_b)(t).$$

This specializes the Weil identity (3.4.1.6), p. 143, with the finite Hecke
factor (3.2.1.7), p. 124, not the completed zeta factor. The continuation
on this line is already checked in
[`Masullo.rationalTheta_mellin_eq_zeta_mul_of_pos`](../../Proofs/Theorems/RationalThetaMellinContinuation.lean);
the full and one-ray factors of two cancel. The log Plancherel constants
on the two sides are the same. Pinned Mathlib exposes the integral agreement
and isometry as `SchwartzMap.toLp_fourier_eq` and
`MeasureTheory.Lp.norm_fourier_eq` in `Analysis/Fourier/LpSpace.lean` (for
its negative-sign, $2\pi$ convention; reflect and rescale the frequency).
This lookup is not a Lean check of the obstruction.

The input vectors $e^{\alpha x}U_b(x)$ used in this boundary bound are
dense in $L^2(dx)$. For $v\in C_c^\infty(\mathbb R)$ the local mean-zero
constraint is $\int e^{(1/2-\alpha)x}v(x)\,dx=0$. Correct this moment by a
translate to the right of a fixed compact smooth bump of positive
weighted moment. Its required coefficient tends to zero exponentially,
and the cost in unweighted $L^2$ also tends to zero. Every corrected
profile comes from a compactly supported smooth function on the positive
real ray, extended evenly across zero with a gap at zero. Approximate
that factor in Schwartz topology by multiplying its additive Fourier
transform by even smooth compact cutoffs
that equal one near zero and exhaust the line. The Fourier value at zero
stays zero. Restore the spatial value at zero by subtracting its error
times an even bandlimited mean-zero Schwartz function of value one at
zero (take the inverse transform of a suitably normalized smooth even
bump supported away from frequency zero). Convergence in the boundary
norm follows from $\|e^{\alpha\cdot}U_b\|_2^2=\int_0^\infty |b(t)|^2t^{2\alpha}\,dt$.

Plancherel now makes the multiplier estimate valid on a dense family in
frequency $L^2$. Pass to an almost-everywhere convergent subsequence and
use Fatou to extend the estimate to all $L^2$. Testing on finite intervals
and using continuity forces $|\zeta(\sigma+it)|\le C_B$ everywhere.

For completeness, on any fixed $0<\sigma<1$, a boundedness conclusion of
this kind contradicts an elementary mean calculation. For rational $q>0$,
shift the average of $q^s\zeta(s)$ on $[\sigma+i,\sigma+iT]$ to the parallel
segment with real part $2$; the pole is outside the rectangle. The top
edge is $o(T)$: For $\sigma\le \Re s\le2$ at height $T$, subtracting the
integral tail from the series at an integer $N\asymp T$ gives

$$\zeta(s)=\sum_{n\le N}n^{-s}+\frac{N^{1-s}}{s-1}
               +O_\sigma(|s|N^{-\Re s}).$$

The error bound comes from integrating the derivative of $t^{-s}$ over
the unit cells in the tail, first for $\Re s>1$, then by continuation for
$\Re s>0$. Each term of this estimate at height $T$ is $O_\sigma(T^{1-\sigma})$,
uniformly on the top edge. The bottom edge has bounded integral. The
absolutely convergent series on the right edge consequently gives

$$\lim_{T\to\infty}\frac1T\int_1^T \zeta(\sigma+it)q^{it}\,dt
 = \begin{cases}q^{-\sigma},&q\in\mathbb N,\\0,&q\notin\mathbb N.\end{cases}$$

Use the nonnegative trigonometric polynomial
$\prod_{p\le M}(1+\cos(t\log p))$, with primes $p$. Its mean is one by
unique prime factorization. The mean when multiplied by $\zeta(\sigma+it)$
is $\prod_{p\le M}(1+p^{-\sigma}/2)$: Only frequencies whose prime exponents
are all nonnegative survive. Boundedness of zeta would bound these means
independently of $M$, contrary to divergence of $\sum_p1/p$. This proves
the fixed-band obstruction without any assumption about zero locations.

## Compact convolution gives a bounded and nuclear leg in the forward direction

There is a smaller, smoothed transport that does not require the false
bound. On the generators, write $u=U_b$. Ordinary summation by parts on
the positive ray gives, with $t=e^x$ and fractional part $\{v\}$,

$$\sum_{n\ge1}b(nt)-\int_0^\infty b(vt)\,dv
  =\int_0^\infty \{v\}\,t b'(vt)\,dv.$$

Indeed the discrete counting function is $v-\{v\}$; integrating by parts
against both that counting function and $v$ leaves the term shown. The
integral on the left is zero by evenness and the mean-zero condition.
Multiplying by $t^{1/2}$ and using $v=e^y$ yields the exact formula

$$T U_b=V_b=\int_{\mathbb R} K(y)(u'-u/2)(\cdot+y)\,dy,
\qquad K(y)=\{e^y\}e^{-y/2}.$$

The kernel satisfies $|K(y)|\le e^{-|y|/2}$. If $f\in C_c^\infty((0,\infty))$
is a log test and $A_f u=f*u$, then $A_f U_b$ is still a fixed-band
generator: Each translate of $u$ by $z>0$ is induced by the dilated real
test $e^{-z/2}b(e^{-z}\cdot)$, preserving both moments and contracting its
band; integration over compact $z$ preserves the Schwartz conditions.
Consequently

$$T A_f U_b=\int K(y) A_{f'-f/2}U_b(\cdot+y)\,dy=A_f T U_b.$$

Translations on $H$ have norm bounded by
$2^{r/2} e^{\alpha|y|}(1+y^2)^{r/2}$. Integration against $K$ is bounded
since $\alpha<1/2$. Convolution against $f'-f/2$ or any of its derivatives
is bounded by the same weight estimate on its compact support. Thus the
smoothed transport has a bounded extension $L_B\to G_B$, with bounded
log derivatives of all orders in $H$. If $\rho$ is a fixed smooth compact
position cutoff, $M_\rho T A_f:L_B\to H$ is nuclear. It factors boundedly
through the ordinary periodic $H^2$ on any circle whose fundamental
interval contains the cutoff support in its interior. Multiplication by
$\rho$ and the derivative bounds give the $H^2$ norm estimate, since $H$
controls ordinary $L^2$ on the interval. The inclusion into periodic
$L^2$ is nuclear by the summable Fourier singular values
$O((1+|k|^2)^{-1})$, followed by bounded extension by zero from the
fundamental interval into $H$, where the weight is bounded. This is a
**map between different realizations**, not a trace of the global
compression. No rate uniform in a moving position cutoff is claimed.

## The Poisson edge separates the cutoff traces

Masullo's two-zero-mode inversion (2.2.3.2), p. 82, and the centered
band with both zero modes removed (7.3.2.12–15), pp. 354–355, give the
following rational consequence. With $t>0$, if $B<2/t$ then

$$\sum_{n\ne0}b(nt)=t^{-1}\bigl(\widehat b(1/t)+\widehat b(-1/t)\bigr).$$

If $B<1/t$ both samples vanish. The two public Lean endpoints are
`Masullo.rationalTheta_eq_first_pair_of_band` and
`Masullo.rationalTheta_eq_zero_of_inv_gt_band` in
[`Theorems.RationalThetaBand`](../../Proofs/Theorems/RationalThetaBand.lean).
They do not assume evenness: Inversion is followed by restricting the
nonzero lattice sum to $\{-1,1\}$. In the even model $V_b(x)$ is half
the full twisted sum, hence $G_B$ is supported a.e. in
$[-\log B,\infty)$; this passes to the closure because restriction to the
complement is a bounded multiplication operator on $H$. The edge is
sharp for the family: For any $s\in(B/2,B)$ choose an even smooth
Fourier bump nonzero at $\pm s$, supported strictly inside the band
away from zero, and subtract an even bump of the same integral away
from $0,\pm s$. Then both moments of the inverse transform vanish and
the first-pair formula gives $V_b(-\log s)=s^{1/2}\widehat b(s)\ne0$.

Let $P_B,Q_B$ be the orthogonal projections onto $L_B,G_B$ respectively.
For $f=\beta'$ with nonzero $\beta\in C_c^\infty((0,\log 2))$,
$\beta\ge0$, take $A_f u(x)=\int f(z)u(x-z)\,dz$. The global
compression $Q_B M_\rho A_f|_{G_B}$ is insensitive to a cutoff
perturbation supported below the Poisson edge because $Q_B$ kills
outputs supported there. In fact $A_f$ preserves that support lower
bound as well. For the local compression $P_B M_\rho A_f|_{L_B}$ the
trace instead changes by a strictly positive amount for any nonzero
smooth nonnegative perturbation supported sufficiently far below the
edge. Here is an estimate uniform at large $B$, including when that
region moves with $B$.

For $B\ge1$, let $u=x+\log B$. Dilation $b(t)\mapsto B^{1/2}b(Bt)$
sends the unit band to the $B$ band and translates both twisted profiles
by this substitution. After dividing the shifted squared norms by
$w(-\log B)$, work in $L^2(w_B\,du)$ with
$w_B(u)=w(u-\log B)/w(-\log B)$. This constant normalization does not
change trace, and convolution still acts by translation-invariant
integration against $f$. Given $2\alpha<\gamma<1$, both $w_B$ and
$1/w_B$ are bounded by $C_\gamma e^{\gamma |u|}$ uniformly in $B$: The
exponential ratio is bounded in both directions by $e^{2\alpha |u|}$,
and the log-polynomial ratio by $2^r(1+u^2)^r$ in both directions.
Also $w_B(u)\ge1$ for $u\le0$.

On the translated local space let $\ell_u$ be evaluation at $u$ and let
$\Lambda$ be the functional $U_b\mapsto b''(0)/2$ on the unit-band core.
For $0\le j\le4$ and $|t|\le1$, the norm of $b\mapsto b^{(j)}(t)$ is
uniformly bounded: Reproduce via convolution with a fixed Schwartz
$\psi$ whose Fourier transform equals one on the unit band, and apply
Cauchy–Schwarz in the even additive norm with weight
$w_B(\log|t|)$. The squared additive norm is twice the squared profile
norm. The reciprocal weight is bounded by
$C_\gamma\max(|t|,|t|^{-1})^\gamma$, integrable locally at zero because
$\gamma<1$ and harmless at infinity against the derivatives of $\psi$.
Thus evaluation and the derivative functionals extend to the closure,
and Taylor's theorem and evenness give, in dual norm,

$$\ell_u=e^{5u/2}\Lambda+O(e^{9u/2})\qquad (u\le0).$$

The norm of $\Lambda$ is bounded below uniformly in $B$: Use a fixed
unit-band generator with $b''(0)\ne0$, obtained by taking the Fourier
bumps in two disjoint symmetric subintervals away from zero with equal
integrals but different second moments. Its norm is uniformly bounded
by the upper bound for $w_B$.

Let $k_u$ be the Riesz vector with $\ell_u(h)=\langle h,k_u\rangle$
(inner product linear on the left). For a cutoff perturbation
$\eta_B(x)=\eta(x+\log B)$ with $\eta$ supported in $(-\infty,0)$, the
translated local compression is the trace-norm integral of
$h\mapsto\ell_{u-z}(h)k_u$ against
$\eta(u)w_B(u)f(z)\,du\,dz$. The pairing against a second vector proves
this identity first on generators and then by continuity. Indeed the
rank-one norm is $\|\ell_{u-z}\|\|\ell_u\|=O(e^{5u}e^{-5z/2})$ on
this region, making the integral finite even for bounded $\eta$ with
unbounded left support; the evaluation vectors are locally continuous
by the derivative estimates. Taking traces and expanding at the edge,

$$\operatorname{Tr}(P_B M_{\eta_B} A_f|_{L_B})=
\int \eta(u)w_B(u)e^{5u}
\left(\|\Lambda\|^2\int f(z)e^{-5z/2}\,dz+O(e^{2u})\right)du.$$

The trace is real, by complex conjugation invariance of the space and
operator. Integration by parts gives
$\int f(z)e^{-5z/2}dz=(5/2)\int \beta(z)e^{-5z/2}dz>0$. The constants
and the lower bound on $\|\Lambda\|$ are uniform, so for a nonzero
nonnegative fixed $\eta$ supported sufficiently far below $u=0$ this
trace is bounded below by a positive constant, independent of $B$.
In contrast, the global trace change is identically zero. Even two
smooth lower thresholds at distinct sufficiently small positive
multiples of $1/B$ with transition widths $o(1/B)$ can exhibit the
same difference: Give them a common upper cutoff and take their
nonnegative difference. It is one on a fixed interior interval in $u$
for all large $B$. Conversely, for any perturbation of size at most one
supported on norms at most $a_B$ with $a_B B\le1$, the same rank-one
norm bound gives a local trace-norm bound $O((a_B B)^{5-\gamma})$ by
integration up to $u=\log(a_B B)$. If $a_B B\to0$, these perturbations
cannot produce a surviving correction.

An independent Yah reader checked the endpoints, scaling, trace order,
and cutoff bounds against the stated model and pinned extraction. The
result concerns Hilbert compressions, not the additive Fourier
multiplier in (12.4.1.8–12), p. 517. A universal same-cutoff equality of
the two model traces fails for unrestricted compact position cutoffs.
The lower-edge variants are not pairs of cutoffs satisfying the
multiplicative symmetry in Definition 9.3.3.1, p. 427. Page 514 n. 2
suggests an independent lower endpoint, but does not prove a joint
limit for that change. The calculation does not refute a comparison
for prescribed cutoffs, identify the global $S$-piece of p. 520, or
attribute its missing Mellin term to the support edge.

## Next fixed-cutoff test: Lift the compressed global operator

A graph topology, rather than the uncut local Hilbert norm, is a
candidate for the continuous injection in C.3.2.2. In the rational model
write $T_B$ for the closure of $U_b\mapsto V_b$ from $L_B$ to $G_B$.
This operator is closable and injective: Convergence in $H$ implies
convergence in $L^2$ on the right log boundary. On bounded frequency
intervals the multiplier $\zeta(\sigma+it)$ is bounded, so the boundary
identity passes to graph limits there. A zero input entails a zero
output by Plancherel. A zero output entails a zero input since the zeros
on the boundary line have Lebesgue measure zero. Equip $X_B=\operatorname{Dom}T_B$
with the graph norm; $T_B:X_B\to G_B$ is then a bounded injection with
dense range.

Let $Q_B$ be the orthogonal projector of $H$ onto $G_B$, and at fixed
$\rho$ form $C_{\rho,B}=Q_B M_\rho A_f|_{G_B}$. Its trace, when obtained
from the ambient cutoff operator $M_\rho A_f Q_B$, is the corresponding
compressed trace (orthogonal block decomposition). The ambient operator
is trace class by the same compact $H^2$ factorization applied to $A_f$
alone. To test this graph route, take the derivative of the bump in the
[mass-zero control](trace-to-zeros.md#first-unmatched-geometric-evaluation-and-a-positive-log-control)
and determine whether $C_{\rho,B}$ takes values in $T_B(X_B)$ with a
nuclear lift $T_B^{-1}C_{\rho,B}:G_B\to X_B$. At fixed cutoffs a necessary
check on any candidate output $v=C_{\rho,B}h$ is that
$\mathcal F_+(e^{\alpha\cdot}v)/\zeta(\sigma+i\cdot)$ is the right boundary
of some $u\in L_B$ and that $(u,v)$ is a limit of paired fixed-band
profiles in $H\oplus H$. The quotient being in $L^2$ alone does not show
band membership or graph approximation. Failure of this check for one
output falsifies this factorization; a nuclear lift would identify a
trace on the graph space, not automatically the local-multiplier
finite part.

The Poisson edge settles the trivial case: If $\rho$ is supported below
$-\log B$, then $C_{\rho,B}=0$ and the lift is zero, even though the local
trace need not vanish. For the nontrivial test, use a smooth cutoff
whose support intersects $(-\log B+\sup\operatorname{supp} f,\infty)$
and an actual projected output $v=C_{\rho,B}V_b$ of a generator.
The band gives a necessary inverse test without dividing by the Mellin
multiplier on a boundary line. For $s>0$ put

$$g_v(s)=s^{-1/2}v(-\log s),\qquad D_v(s)=\sum_{n\le B/s}\mu(n)g_v(ns),$$

where $\mu$ is the Möbius function. Here $g_v$ is zero a.e. above $B$,
and change of variables gives $\|g_v\|_{L^2(ds)}=\|v\|_{L^2(dx)}\le\|v\|_H$.
On a paired generator, Poisson gives
$g_{V_b}(s)=\sum_{n\ge1}\widehat b(ns)$. This sum and its inverse are
finite at each $s>0$; regrouping at $k=nm$ uses
$\sum_{n\mid k}\mu(n)=\mathbf1_{k=1}$. Thus $D_{V_b}=\widehat b$ on the
positive ray. On $s\ge\delta>0$ the map $v\mapsto D_v$ is bounded from
edge-supported profiles in $H$ to $L^2([\delta,\infty),ds)$: There are
at most $\lfloor B/\delta\rfloor$ terms using the zero extension of
$g_v$, and the $n$-th dilation has $L^2(ds)$ norm $n^{-1/2}$.
For any graph pair $(u,v)$ take paired approximants $(U_{b_j},V_{b_j})$.
Since $w\ge1$, convergence of $U_{b_j}$ in $H$ implies convergence
of $b_j$ in even additive $L^2$ to $b(t)=|t|^{-1/2}u(\log|t|)$ off zero.
Plancherel and the bounds on each $[\delta,\infty)$ give $D_v=\widehat b$
a.e. on $(0,\infty)$.

**Runnable falsifier:** Test whether $\int_0^B |D_v(s)|^2\,ds$ diverges
for such an output. Only the small-$s$ tail can cause this; on $(B/2,B]$
one has $D_v=g_v$. Divergence for one output rules out the graph lift.
If finite, the inverse Fourier transform of the even extension of $D_v$
is the only possible local input. Still check the weighted norm,
membership in $L_B$, paired graph approximation, and nuclearity.
This necessary test was independently reviewed. The projector must be
applied before testing: Compact support of $M_\rho A_f V_b$ does not
imply compact support of $v$. The [unit-band, degree-zero successor](trace-reverse-lift-q.md)
implements this test using the Hardy representation of the projected
output. It gives an exact inverse criterion in that scope, with an open
reciprocal-zeta estimate at a general zero-free boundary width.

Neither leg has found the missing $+1/2$ Mellin subtraction. The actual
global $S$-piece comparison, the orbital identification, the full
rational explicit formula in Lean, and the number-field GRH proof remain
open.
