# Transport between the rational real and global levels

**Status:** Project calculation and a runnable fixed-cutoff test, not a Lean
proof. Source locators refer to the digest-matched [pinned PDF](../sources/masullo/README.md)
via `pdftotext -layout`; claims about the text are provisional. This continues
the [positive-log control](trace-to-zeros.md#first-unmatched-geometric-evaluation-and-a-positive-log-control),
not the divisor uniqueness argument. An independent Yah reader checked the
extracted source interface and the fixed-band and smoothed-leg calculations.

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

The forward map above does not supply this reverse leg. In particular
it has not found the missing $+1/2$ Mellin subtraction or shown any
compatibility of global and local projections. The actual global
$S$-piece comparison, the orbital identification, the full rational
explicit formula in Lean, and the number-field GRH proof remain open.
