# Rational explicit formula: Local terms and the contour

**Scope:** The trivial character over $\mathbb Q$, before the shift by $1/2$.
Source locators refer to the [digest-pinned manuscript](../sources/masullo/README.md).
The readings below are from layout text extraction and remain provisional,
not verified visual readings.

## Checked local terms of (B.4.2.2)

In (B.3.2.3), p. 606, the finite rectangle formula uses
$\Phi(\rho)\operatorname{Res}_\rho f$ where the residue theorem gives
$\operatorname{Res}_\rho(\Phi f)$. These differ for a higher pole: Take
$f(s)=1/(s-\rho)^2$ and $\Phi(s)=s-\rho$. The missing condition for this
substitution is that the poles be at most simple. In (B.4.2.2), p. 614,
Masullo applies the formula with $f=\Lambda'/\Lambda$ for the **completed**
function and uses the orders of $\Lambda$ as the coefficients. The first
unnumbered display in B.4.2.1 appears to have incompatible signs, so use
the numbered (B.4.2.2) and the actual meromorphic orders.

The faithful repair for this application is
[`Masullo.logDeriv_weighted_principalPart`](../../Proofs/Lemmas/TestedLogDeriv.lean).
An analytic unit times $(s-z)^n$ represents a meromorphic germ of finite
order $n$; its tested logarithmic derivative is $n\Phi(z)/(s-z)$ plus an
analytic remainder on the punctured germ. The correction term uses the
analytic divided difference of $\Phi$, including when $\Phi(z)=0$. The two
[public propositions](../../Proofs/Props/RationalExplicitFormulaResidues.lean)
`completedZeta_tested_zero_principalPart` and
`completedZeta_tested_pole_principalPart` apply this at each open-strip
zero with the full `zetaZeroOrder` multiplicity, and at $0,1$ with order
$-1$ for each pole. The meromorphic-order transfer uses
$\Lambda(s)=F(s)/[s(s-1)]$ off $0,1$, where the checked entire function $F$
satisfies $F(0)=F(1)=1$. The poles thus contribute $-\Phi(0)-\Phi(1)$,
not the residues of $\Lambda$ itself. Independent Yah statement review
checked the filter scope, order transfer requirements, multiplicities,
and signs against pp. 605–606 and 614–615.

**Verification:** In the integration workspace for
`fcf49e1d51df346eadec9c620559d41f1a22e3f0`, `lake --wfail build Proofs`
passed, and `lake env leanchecker` passed on `Lemmas.ZetaZeroOrders`,
`Lemmas.CompletedZetaOrders`, `Lemmas.TestedLogDeriv`, and
`Props.RationalExplicitFormulaResidues`. `#check` matched the punctured-germ
and reflection statements, and `#print axioms` reported only `propext`,
`Classical.choice`, and `Quot.sound` for the generic principal-part lemma
and all three public propositions. The changed Lean sources contained no
new axiom declarations, placeholders, or unsafe substitutes. The campaign
adopted that candidate.

Under the ordinary convention that $L'(1-s)$ evaluates a derivative at
$1-s$, the extracted plus sign in (B.4.2.3), p. 614, cannot be used. In
the rational case the conductor term vanishes and
`completedZeta_logDeriv_reflection` proves $f(s)=-f(1-s)$ off $0,1$ by
Mathlib's completed functional equation and the chain rule. Substituting
$s=1-a+it$ and changing $t$ to $-t$ in the absolutely convergent integral
changes the *subtracted* left-line term into an *added* right-line term
weighted by $\Phi(1-s)$, as in (B.4.2.4), p. 615. This change of variables
for the contour integral is not yet formalized.

## Upstream growth check: Use height rather than the sequence index

Definition B.3.1.1(1c)–(2), p. 604, gives $T_k=O(|k|^\alpha)$ and a bound
$|f(\sigma+iT_k)|\ll |k|^\beta$. The proof of (B.3.1.3), p. 605, needs
the opposite inequality on heights, $|T_k|\gg |k|^\gamma$ for some
$\gamma>0$, to absorb the growth in $k$ by Schwartz decay in $T_k$. The
upper bound on heights does not imply that lower bound. This is separate
from residue factorization.

For a control of the asymptotic reading, use $|k|\ge2$, as in the lemma.
Taken literally at $k=0$, the displayed bound in the definition instead
forces $f$ to vanish on a horizontal segment and hence identically;
replacing $|k|$ by $1+|k|$ fixes that issue but not the missing lower
bound. Take $f(s)=\exp(\cos(2\pi s))$, $\Phi(s)=\exp(s^2)$, and
$a=-3/4,b=7/8$. On the vertical lines at $\pm1/2$ the first function has
modulus $\exp(-\cosh(2\pi t))\le1$, and the test is uniformly Schwartz
on every bounded vertical strip. For $k\ge2$ choose $T_{\pm k}=\pm t_k$
with $\cosh(2\pi t_k)=\log(k+e)$, so $t_k\to\infty$ and
$t_k=O(\log\log k)$.
Throughout either horizontal segment $|f|\le k+e$, but on
$|\sigma|\le1/6$ the modulus of the product is at least
$\exp(\tfrac12\cosh(2\pi t_k)-t_k^2)$. Its absolute horizontal integral
therefore does not tend to zero, contrary to (B.3.1.2) with these witnesses.
This is a project counterexample to the extracted general implication,
not to the growth estimate for the completed zeta function.

For (B.4.2.2), it suffices to exhibit top and bottom heights tending to
$\pm\infty$ with a uniform bound $|f(\sigma+it)|\le C(1+|t|)^B$ on each
selected segment, with fixed vertical sides $1-a$ and $a$, $1<a<2$.
The manuscript explicitly cites Lang, *Algebraic Number Theory*, Ch. XVII,
Prop. 2.3, Cor. 2.5, and Prop. 2.7 for this step. Immediately before
Theorem B.6.1.7, p. 641, Masullo describes Prop. 2.7 as giving zero-free
horizontal segments with a bound polynomial in the **absolute ordinate**.
The corresponding Ch. XVII §2 passage in the
[University of Toronto scan](https://www.math.toronto.edu/~ila/Lang%20--%20Algebraic%20number%20theory.pdf),
printed pp. 334–336 (scan pp. 348–350), uses different proposition
numbering (scan SHA-256
`bf9dddfd85067766cb7a11477fb92d7f436fbbd6cd7e0efcf7f87fa6836eed97`).
Its OCR gives $T_m\in(m,m+1)$ with a zero-free margin of scale
$1/\log|m|$, a bound of order $(\log|m|)^2$ for the completed logarithmic
derivative on $[-b,1+b]+iT_m$ for $0<b<1$, and the right-edge bound from
the Euler product and Stirling. Lang's §3, pp. 336–337, consumes these
bounds on just those rectangles. This is provisional OCR evidence for
the corresponding argument, not a reading of the exact cited numbering.
A separate online copy returned HTTP 403 before text retrieval. Reopen the
edition match only with an accessible copy, starting with the statement of
Prop. 2.7 as the control.
Masullo's (B.6.1.39)–(B.6.1.42), p. 642, concerns instead the incomplete
Euler product with the factors in $S$ removed, including the Archimedean
factor. The completed bound and its vertical-line companion are still
unformalized.

## Checked finite rectangle with simple principal parts

[`Masullo.rectangleIntegral_eq_sum_simpleResidues`](../../Proofs/Props/RectangleResidue.lean)
proves the finite step of (B.3.2.3), p. 606. The contour is the closed
axis-aligned rectangle with strictly positive real and imaginary widths.
The finite pole set lies in its interior. Analyticity is required at
every other point of the closed rectangle. At a pole, the coefficient
and regular term are specified by an equality in the punctured germ, so
no totalized value of the integrand there is constrained.

The tested germ, not a product of separately computed residues, is the
input to this proposition. The [rational local terms](#checked-local-terms-of-b422)
provide these simple germs for (B.4.2.2), p. 614. Figure 3, p. 605,
specifies counterclockwise orientation. The signs of the two horizontal
terms in the extracted (B.3.2.4), p. 606, are reversed relative to that
orientation. The checked integral is bottom minus top plus $i$ times
right minus $i$ times left, with each real parameter increasing. The
horizontal signs cease to matter only once horizontal vanishing has
been proved.

The proof [patches the remainder at the poles](../../Proofs/Lemmas/SimplePrincipalParts.lean),
subtracting the other kernels from each assigned regular value. It applies
Mathlib's rectangle Cauchy–Goursat theorem and sums the single-kernel
integrals. The [kernel calculation](../../Proofs/Lemmas/RectangleCauchyKernel.lean)
uses principal log on the bottom, top, and right translated edges and
$\log(-(w-z))$ on the left. The right corners cancel and the signed
branch jumps at the left corners add to $2\pi i$. Independent Yah review
(`residue-review`) checked the hypotheses, orientation, and manuscript
locators with the digest-matched extraction, not rendered pages.

## Checked finite completed-zeta contour

[`Masullo.rectangleIntegral_completedZeta_logDeriv`](../../Proofs/Theorems/RationalExplicitFormulaContour.lean)
proves the finite-height step behind (B.4.2.2), p. 614, using
(B.3.2.3), p. 606. Take $1<a$ and $u<0<v$, with no critical-strip
zero at either height. The counterclockwise boundary integral of
$\Phi\Lambda'/\Lambda$ on $[1-a,a]\times[u,v]$, for $\Phi$ analytic at
every point of the closed rectangle, is $2\pi i$ times

$$-\Phi(0)-\Phi(1)+\sum_{u<\Im\rho<v} m_\rho\Phi(\rho).$$

The sum counts each distinct open-strip zero once with its full order.
The finite calculation allows asymmetric heights and needs no upper bound
on $a$; the later growth argument uses $1<a<2$. Masullo supplies the
contour and the logarithmic derivative. The [finite rectangle repair](#checked-finite-rectangle-with-simple-principal-parts)
takes the simple principal part of the *tested* integrand instead of
factoring the residue for arbitrary meromorphic functions. The existing
completed-zeta germs give the coefficients. The new
[`RationalCompletedZetaZeros`](../../Proofs/Lemmas/RationalCompletedZetaZeros.lean)
lemmas verify that this list is exhaustive: Analyticity off $0,1$,
comparison by the nonvanishing real gamma factor on $\Re s>0$,
Mathlib's nonvanishing for $\Re s\ge1$, and reflection for $\Re s\le0$.
Compactness gives finiteness of the distinct zero set between the heights.
Independent Yah statement review (`contour-statement`) checked the signed
boundary, full orders, two poles, and exact regularity hypotheses against
the digest-matched extraction of pp. 605–606 and 614, not rendered pages.
No horizontal or vertical edge bounds enter this result.

## Checked quantitatively separated ordinates

[`Masullo.exists_height_separated_from_zeta_zeros`](../../Proofs/Lemmas/ZetaContourHeights.lean)
proves one uniform $c>0$ and, for **every** integer $m$, a height
$T_m\in(m,m+1)$ satisfying $|T_m-\Im\rho|\ge c/(1+|m|)^2$ for all
open-strip zeros. This is a project replacement for the logarithmic
margin in Lang's height argument, invoked in (B.4.2.1), p. 614. It
includes both signs of $m$ and gives the zero-avoidance premise of the
finite contour. It does not supply a bound on $\Lambda'/\Lambda$.

Use the [checked quadratic summability](trace-divisor-summability.md#checked-dyadic-shell-summability)
with total weighted mass $S$. For ordinates in $(m-1,m+2)$, the
weight denominator is at most $6(1+|m|)^2$, so positivity of every
multiplicity bounds their distinct count by $6S(1+|m|)^2$. With
$c=1/(24(S+1))$, the union of open intervals of radius $c/(1+|m|)^2$
about these finitely many ordinates has Lebesgue measure at most $1/2$.
The other zeros have distance greater than $1$ from each point in
$(m,m+1)$. Independent Yah statement review (`height-statement`)
checked the scope against the extraction and caught that a denominator
constant of $5$ would not follow from this estimate at $m=0$. The
Lean proof uses $6$. The growth reading is still provisional OCR/text,
not rendered-page verification.

## Checked lower bound at the right-hand anchor

[`Masullo.entireZeta_right_anchor_lower_bound`](../../Proofs/Lemmas/ZetaContourAnchor.lean)
proves, for all real $t$ with $1\le |t|$,

$$\|\operatorname{entireZeta}(2+it)\|\ge (3\pi)^{-1}e^{-\pi |t|/4}.$$

Masullo invokes Lang for growth of the completed logarithmic derivative
in (B.4.2.1), p. 614. Lang's §2 (scan printed pp. 335–336) compares
logarithmic derivatives using the Weierstrass product and estimates the
right-edge derivative by the Euler product and Stirling. The Lean lemma
is a project replacement input for a local disk comparison, not Lang's
right-edge derivative estimate. It supplies center nonvanishing and
$-\log\|\operatorname{entireZeta}(2+it)\|\le \pi |t|/4+\log(3\pi)$.
Independent Yah review (`anchor-statement`) checked the statement and route
against the digest-matched Masullo extraction and the Lang OCR, not rendered
pages.

At $\Re s=2$, absolute convergence of the Dirichlet series bounds
$|\zeta(s)-1|$ by $\zeta(2)-1\le 2/3$. Gamma reflection, recurrence, and
conjugation at $z=it/2$ give
$|\Gamma(1+it/2)|^2 |\sin(\pi z)|=\pi |t|/2$. The last factor on the left
is at most $e^{\pi|t|/2}$, and the right-hand side is at least one.
The factor $\pi^{-s/2}$ has modulus $1/\pi$. The exposed existing lemma
`Masullo.completedZeta_eq_quotient` accounts for the pole-clearing factor
$s(s-1)$, of modulus at least one here. This bounds the entire numerator,
not the pole-subtracted `completedRiemannZeta₀` itself.

## Checked multiplicity count in the moving disk

[`Masullo.sum_zetaZeroOrder_le_moving_disk`](../../Proofs/Lemmas/ZetaZeroDiskCount.lean)
proves that one constant $K>0$ bounds the sum of `zetaZeroOrder` over any
finite set of open-strip zeros in $\overline B(c_t,5)$ by $K(1+|t|)$, where
$c_t=2+it$ and $1\le|t|$. This uses the full orders and includes zeros on the
radius-five boundary. It is an input to the project replacement of the
completed logarithmic-derivative growth cited in (B.4.2.1), p. 614, not a
bound on that derivative. The Lang scan's §2, Lemma 2 and Proposition 1
(printed pp. 333–334), use an elementary two-circle count at a right-hand
anchor with different bounds and radii. The scan's Proposition 2 on
pp. 335–336 uses a Weierstrass product comparison for the horizontal bound.

On the outer circle, $|\Re s|\le8$ and $\|s\|\le8+|t|$. Fixing $n=8$
in `completedZeta₀_factorial_growth` and expanding
$1+s(s-1)\operatorname{completedRiemannZeta}_0(s)$ gives the separate checked
estimate `Masullo.entireZeta_moving_circle_upper_bound`, with envelope
$M_t=C(1+|t|)^2$ for one $C\ge1$, now without a restriction on $|t|$.
Compare the actual orders to the nonnegative inner divisor, and apply
Mathlib's `AnalyticOnNhd.sum_divisor_le` with radii $5$ and $6$. The
[anchor bound](#checked-lower-bound-at-the-right-hand-anchor) and
$\log(1+|t|)\le |t|$ make $\log(M_t/\|\operatorname{entireZeta}(c_t)\|)$ at
most linear in $1+|t|$. Matching exponential decay on the outer circle
is not needed. Independent Yah review (`moving-disk-review`) checked the
statement, the role of the count, and the envelope against the
matching-digest Masullo text extraction and Lang scan OCR, not rendered
pages. The elementary Lang inequality by itself does not give the count
with radii $5$ and $6$; the checked argument uses Jensen.

## Next runnable obligation: Divide out the closed inner disk divisor

Prove the following factor-removal lemma in Lean. Given an entire $f$,
a finite set $A$ of points, and the exact finite analytic order $m_a$ of
$f$ at each $a\in A$, let $P(z)=\prod_{a\in A}(z-a)^{m_a}$. Construct an
**entire** $g$ with $f=P g$ everywhere and $g(a)\ne0$ for all $a\in A$.
Away from $A$, $g=f/P$; at each $a$ use the local nonvanishing analytic
factor supplied by `AnalyticAt.analyticOrderAt_eq_natCast` and divide by
the other, locally nonzero factors. One can patch those local germs or
remove the factors one at a time, preserving the order at the other
points. Do not use the raw totalized quotient as the analytic extension,
or extend a disk-only identity to its exterior without proof.

For $f=\operatorname{entireZeta}$ take $A$ to be all zeros in the closed
radius-five disk about $c_t$, with $N=\sum_{a\in A}m_a$. The existing
`completedZeta_eq_zero_iff_mem_criticalStripZetaZeros` and pole-clearing
identity identify all numerator zeros off $0,1$; the numerator equals
one at both poles. The factorization supplies a zero-free $g$ on the open
radius-five disk. **No choice of a zero-avoiding radius or Blaschke factors
is needed:** On the radius-six circle each $|z-a|\ge1$, hence $|g|\le M_t$
there and on the enclosed disk by `Complex.norm_le_of_forall_mem_frontier_norm_le`.
At the anchor, $|g(c_t)|\ge |f(c_t)|/5^N$. This ordinary-factor comparison
was independently reviewed as mathematics by `moving-disk-review`; it
is not yet checked in Lean.

For the subsequent derivative estimate, take a holomorphic logarithm
$H$ of $g/g(c_t)$ with $H(c_t)=0$. The pinned
`Complex.exists_continuousOn_eqOn_exp_comp` gives only continuity; prove
holomorphy by locally comparing $H(z)-H(w)$ with the principal log of
$g(z)/g(w)$ near each $w$ in the open disk. Its real part is bounded by
$B=\log(M_t/|f(c_t)|)+N\log 5$. Translate the center to zero and apply
`Complex.borelCaratheodory_zero` with $B+1$ to bound $|H|$ on the closed
radius-four disk. Cauchy on unit circles then gives $|H'|\le8(B+1)$ on
the closed radius-three disk. The factors add at most $N/\delta$ at
points of distance at least $\delta>0$ from the removed zeros. Subtract
$1/s+1/(s-1)$ to transfer from $f'/f$ to $\Lambda'/\Lambda$. This gives
the planned cubic horizontal bound on the separated-height segments
$[-1,2]+iT_m$, and a vertical bound at $2+it$ by zero distance at least
one. Use the checked reflection at $-1$ and compact continuity at
bounded heights. Using $a=2$ is allowed by the checked finite contour.

Absolute vertical integrability and exhaustion of the zero sum still
need to be checked. The target of (B.4.2.2) remains

$$
\frac{1}{2\pi}\left[\int_{\mathbb R}(\Phi f)(a+it)\,dt
-\int_{\mathbb R}(\Phi f)(1-a+it)\,dt\right]
= -\Phi(0)-\Phi(1)+\sum_{0<\Re\rho<1}m_\rho\Phi(\rho).
$$

The local Euler and Archimedean integral evaluations, and matching their
normalizations to (B.4.4.16), pp. 623–625, still follow this contour step.
None of this supplies the global $S$-piece comparison, RH over $\mathbb Q$,
or the general GRH endpoint.
