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

## Checked removal of the closed inner disk divisor

[`Masullo.entireZeta_moving_disk_factorization`](../../Proofs/Props/ZetaContourDisk.lean)
constructs a finite set $A$ of **all** open-strip zeros in the closed
radius-five disk about $c_t=2+it$, including the boundary. For each
$|t|\ge1$, it factors $f=\operatorname{entireZeta}=P g$ on the whole
plane, with $P(z)=\prod_{\rho\in A}(z-\rho)^{m_\rho}$ and $m_\rho$ the
full zeta order. The quotient $g$ is entire and zero-free on the closed
radius-five disk. With $N=\sum_{\rho\in A}m_\rho$ and uniform constants
$C,K$, the theorem gives

$$
\sup_{|z-c_t|\le6}|g(z)|\le C(1+|t|)^2,\qquad
|f(c_t)|\le 5^N|g(c_t)|,\qquad N\le K(1+|t|).
$$

Masullo cites Lang for growth on the completed contour in (B.4.2.1),
p. 614. In the corresponding Lang scan passage, Ch. XVII §2,
Proposition 2 and its proof (printed pp. 335–336), the comparison subtracts logarithmic
derivatives via the global Weierstrass product and uses the right-edge
estimate. The checked result instead prepares an ordinary **finite**
local factorization for the rational function. Neither the local
factorization nor the weaker bounds on it are attributed to Lang.

[`Masullo.entire_extract_finset_factors`](../../Proofs/Lemmas/EntireFiniteFactors.lean)
patches the raw quotient $f/P$ at each removed point: Mathlib's
`AnalyticAt.analyticOrderAt_eq_natCast` supplies the local nonvanishing
germ, and the other factors are nonzero there. This yields an entire
extension and the identity even at the canceled points. The zeta
proposition identifies all numerator zeros using the completed-zeta
zero classification and the numerator's value one at the poles. Each
removed factor has base modulus at least one on the radius-six circle
and at most five at the center. The maximum modulus principle extends
the upper bound to the closed outer disk. No moving radius or Blaschke
normalization is needed. This result does not bound the derivative.
Independent Yah statement review (`factor-statement`) confirmed the full
orders, closed-boundary scope, and sufficiency for a uniform linear
bound on the real part of the normalized log. The source check used
digest-matched Masullo text extraction and Lang scan OCR, not rendered
pages. The corresponding Lang scan uses different proposition numbering.

## Checked logarithmic derivative bound on the moving disk

[`Masullo.entireZeta_logDeriv_le_moving_disk`](../../Proofs/Props/ZetaContourLogDeriv.lean)
proves that there are uniform $D,K>0$ such that whenever $|t|\ge1$,
$|z-(2+it)|\le3$, and $z$ has distance at least $\delta>0$ from all
open-strip zeros,

$$
\left|\frac{f'(z)}{f(z)}\right|
\le D(1+|t|)+\frac{K(1+|t|)}{\delta},\qquad f=\operatorname{entireZeta}.
$$

In (B.4.2.1), p. 614, Masullo cites Lang for growth of the completed
logarithmic derivative in the sense of Definition B.3.1.1, p. 604.
The corresponding Lang Ch. XVII §2, Propositions 2 and 3 (scan printed
pp. 335–336), compare logarithmic derivatives from a global Weierstrass
product and estimate the right edge using the Euler product and
Stirling. The source comparison is provisional text extraction and OCR,
not a reading of rendered pages or a match of the exact cited numbering.
The checked local repair does not import Lang's bound: It estimates the
entire numerator directly and leaves the two pole terms to the transfer.

[`Masullo.norm_logDeriv_le_on_inner_ball`](../../Proofs/Lemmas/ZeroFreeDiskLogDeriv.lean)
uses Mathlib's continuous logarithm lift on the open radius-five disk.
Locally the lift difference agrees with the principal log of $g(w)/g(w_0)$
near $w_0$, where the quotient is one, so the lift is analytic. Normalize
the lift to vanish at the center $c_t$. Its real part is bounded by
$B=\log(M/|g(c_t)|)+1>0$. Borel–Carathéodory at radius four bounds
its modulus by $8B$. A full unit circle about any point of the closed
radius-three disk is contained in that radius-four disk, and Cauchy's
estimate gives $|g'/g|\le8B$ there. The [factorization](#checked-removal-of-the-closed-inner-disk-divisor)
and [anchor](#checked-lower-bound-at-the-right-hand-anchor) make $B$
at most linear in $1+|t|$; the finite sum of derivative terms from the
removed factors is bounded by $N/\delta$ with the full multiplicities.
Independent Yah statement review (`logdisk-review`) verified the constants,
boundary inclusion, and use of the full orders, and confirmed that the
selected-height consumer needs only actual-height polynomial growth. It
checked the matching-digest Masullo extraction and Lang OCR, not images.

## Checked growth on the completed-zeta contour edges

[`Props.ZetaContourEdges`](../../Proofs/Props/ZetaContourEdges.lean) proves
both edge estimates for the rational contour with $a=2$:

- `Masullo.completedZeta_logDeriv_eq_entireZeta`: Off the poles and zeros,
  $\Lambda'/\Lambda=f'/f-1/z-1/(z-1)$ for $f=\operatorname{entireZeta}$.
  The pole-clearing quotient agrees on an entire neighborhood, so its
  logarithmic derivative agrees there too. For $|\Im z|\ge1$ the two
  correction terms increase the norm bound by at most two.
- `Masullo.exists_height_completedZeta_logDeriv_le`: Each integer interval
  $(m,m+1)$ with $|m|\ge2$ has an ordinate $T_m$ at distance at least
  $c/(1+|m|)^2$ from every zero ordinate. One constant bounds the completed
  derivative by $C(1+|T_m|)^3$ on **all** of $[-1,2]+iT_m$. The segment
  fits in the already checked radius-three disk, and the ordinate margin
  bounds the complex distance from each zero. The estimate is in the
  actual height since $1+|m|\le2(1+|T_m|)$.
- `Masullo.completedZeta_logDeriv_le_vertical`: One constant bounds the
  completed derivative by $C(1+|t|)$ on **both** vertical lines for every
  $t\in\mathbb R$. At $2+it$, the real-part separation from the strip
  zeros is at least one; on $|t|\le1$ use analyticity and compactness.
  The checked reflection identity then gives the same bound at $-1+it$.

Masullo supplies the completed logarithmic derivative and invokes Lang's
edge estimates in (B.4.2.1), p. 614, to use the asymptotic residue theorem.
The corresponding Lang OCR (Ch. XVII §2, printed pp. 334–336, different
proposition numbering) uses a logarithmic separation margin and a global
product comparison for the horizontal bound on fixed strips
$[-b,1+b]$ with $0<b<1$, not the closed endpoint $[-1,2]$ by taking
$b=1$. The right-line source argument uses the Euler product and Stirling.
The checked rational repair uses the local disk estimate instead, with
weaker rates that suffice for the contour limit. The use of the actual
height also avoids the insufficient index-to-height implication in the
extracted (B.3.1.3), p. 605. Independent Yah statement review
(`edge-statement`) checked the signs, nonvanishing guards, both signs of
height, and the closed-edge scope against the digest-matched Masullo
layout extraction and Lang OCR. These source readings remain provisional,
not visual checks. The theorem does not claim bounds on every inward pair
of vertical lines or for other Hecke characters.

## Checked exhaustion of the rational completed-zeta contour

[`Masullo.completedZeta_contour_identity`](../../Proofs/Theorems/RationalExplicitFormulaExhaustion.lean)
proves (B.4.2.2), p. 614, over $\mathbb Q$ at $a=2$. Let
$G(s)=\Phi(s)\Lambda'(s)/\Lambda(s)$, with $\Phi$ entire and
$|\Phi(\sigma+it)|\le B/(1+|t|)^4$ uniformly on $-1\le\sigma\le2$.
Both vertical parameter integrands are integrable, the tested full-order
zero sum is absolutely summable, and

$$
\frac{1}{2\pi}\left[\int_{\mathbb R}G(2+it)\,dt
-\int_{\mathbb R}G(-1+it)\,dt\right]
= -\Phi(0)-\Phi(1)+\sum_{0<\Re\rho<1}m_\rho\Phi(\rho).
$$

Masullo supplies the limit argument in (B.3.2.3)–(B.3.2.5), p. 606:
Horizontal edges disappear and the absolutely convergent vertical integrals
remain. The uniform fourth-power bound is a sufficient input from the
vertical Schwartz property (B.2.2.1), p. 600, with $N=4$ on a closed
substrip of a larger open strip and compactness at the remaining heights.
Proposition B.2.1.9(1)–(2), pp. 598–599, is the manuscript's Mellin test
source; the theorem does not formalize that proposition.

The checked repair uses the actual-height [edge bounds](#checked-growth-on-the-completed-zeta-contour-edges)
in place of an index-to-height inference. It independently selects top
heights in $(n+2,n+3)$ and bottom heights in $(-n-2,-n-1)$, omitting all
zeros on the edges. The [finite contour theorem](#checked-finite-completed-zeta-contour)
uses the tested principal parts and counterclockwise orientation; the
reversed horizontal signs in the extraction of (B.3.2.4) do not affect
the limit. In [`Lemmas.ZetaContourExhaustion`](../../Proofs/Lemmas/ZetaContourExhaustion.lean),
the horizontal integrals are bounded by $3BC/(1+|t|)$ at the selected
heights. The inverse-cubic vertical majorant is integrable, and Mathlib's
`MeasureTheory.intervalIntegral_tendsto_integral` passes to each whole
line. The checked quadratic divisor weight dominates the tested orders.
`tendsto_sum_zetaZeros_boundedIm` passes from finite height windows to the
unconditional sum for any exhausting lower and upper endpoints, so the
asymmetric windows and the symmetric prescription in (B.4.2.2) have the
same limit. Finally $ds=i\,dt$ cancels $i$ from $2\pi i$.

Independent Yah statement review (`exhaustion-statement`) confirmed the
hypotheses, orientation, normalization, full orders, and limit plan
against the digest-matched layout extraction of pp. 598–600, 604–606,
and 614. This is not a rendered-page reading. The repaired growth rates suffice
for the limit. The declaration is a
rational specialization, not the explicit formula with the local
terms evaluated and not a global trace comparison.

## Checked reflection and splitting of the rational contour

[`Theorems.RationalExplicitFormulaRightLine`](../../Proofs/Theorems/RationalExplicitFormulaRightLine.lean)
keeps the hypotheses of the infinite contour identity. Write $s=2+it$,
$W(t)=\Phi(s)+\Phi(1-s)$, and
$Z=-\Phi(0)-\Phi(1)+\sum_\rho m_\rho\Phi(\rho)$ with the full open-strip
orders. Both declarations retain absolute summability of the zero sum.

- `Masullo.completedZeta_contour_reflected` proves the one-line form of
  (B.4.2.4), p. 615: $W\,\Lambda'/\Lambda$ is integrable on the right
  line and its integral divided by $2\pi$ is $Z$. The conductor factor
  for the rational trivial character is one. The plus sign in the
  extracted logarithmic derivative (B.4.2.3), p. 614, does not follow
  from the functional equation; the checked
  `completedZeta_logDeriv_reflection` supplies the chain-rule minus sign.
  Invariance of Lebesgue measure under $t\mapsto-t$ gives the actual
  reflected sample $\Phi(-1-it)$ and the addition in (B.4.2.4).
- `Masullo.completedZeta_contour_split` proves (B.4.2.5)–(B.4.2.9),
  p. 615, before evaluating the Mellin integrals. It gives

  $$
  \frac{1}{2\pi}\left[
    \int_{\mathbb R} W(t)\frac{\Gamma_{\mathbb R}'(s)}{\Gamma_{\mathbb R}(s)}\,dt
    -\sum_{n\ge1}\int_{\mathbb R} W(t)\frac{\Lambda_{\rm vM}(n)}{n^s}\,dt
  \right]=Z.
  $$

  The Gamma integrand is integrable, and the sum of the $L^1$ norms of
  the finite integrands is finite. Mathlib's von Mangoldt coefficient
  is $\log p$ on $p^m$ for $m>0$ and zero otherwise; `LSeries.term`
  also includes a zero term at $n=0$.

In [`Lemmas.ZetaRightLine`](../../Proofs/Lemmas/ZetaRightLine.lean),
`completedZeta_logDeriv_eq_gamma_add_zeta` proves the local product
identity as an identity of germs on $\Re s>1$, with both factors
nonzero there. Masullo invokes absolute uniform Euler-product convergence
and then dominated convergence. `vonMangoldt_right_line_integrals`
implements that step using Mathlib's logarithmic derivative and
summability theorems at $s=2$: The L-series term norm is independent of
$t$, so its weighted $L^1$ norm is exactly that constant times
$\int|W|$. This justifies the **combined** finite-place interchange for
both tests rather than just interchanging at one prime. The Gamma
integrability then follows by subtraction, without a separate Gamma
growth estimate.

Independent Yah statement review (`rightline-review`) checked the signs,
argument, conductor, and strength of the absolute convergence against
the digest-matched Masullo extraction of pp. 614–615. The extraction is
not a visual reading. The two local evaluations, and their independent
comparison with the global geometric distribution, are not proved here.

## Checked Mellin admissibility of compact log profiles

[`Props.CompactLogMellin`](../../Proofs/Props/CompactLogMellin.lean) proves
Proposition B.2.1.9(1)–(2), pp. 598–599, for compact log profiles. For
$g(x)=\phi(e^x)$, `Masullo.compactLogMellin g` is the whole-line integral
$\Phi_g(s)=\int_{\mathbb R}g(x)e^{sx}\,dx$ of (B.2.1.29), with the
positive exponent and no moment or half-line condition.

- `Masullo.analyticAt_compactLogMellin` proves entireness for continuous
  compactly supported $g$. After (B.2.1.30), Masullo gives uniform absolute
  convergence but leaves the step to holomorphy implicit. The Lean proof
  uses dominated differentiation, the strategy in Proposition B.2.1.5(1),
  p. 594. The compactly supported function
  $x\mapsto |g(x)e^{sx}|e^{3|x|}$ is bounded for each fixed $s$.
  `differentiable_compactLogMellin` uses this bound with the checked
  `hasDerivAt_logMellin_of_decay` to differentiate in a complex
  neighborhood, then complex differentiability gives analyticity.
- `Masullo.compactLogMellin_vertical_decay` gives one $B>0$ for each
  $A,N$ with $|\Phi_g(\sigma+it)|\le B/(1+|t|)^N$ for $|\sigma|\le A$,
  for smooth compactly supported $g$. The multiplication form of
  (B.2.1.31) is $\Phi_{g^{(N)}}(s)=(-s)^N\Phi_g(s)$. Compact support
  kills both whole-line boundary terms, and the estimate (B.2.1.34)
  applies to the differentiated profile. Near height zero, use the
  undifferentiated majorant (B.2.1.36), so the bound includes $t=0$.
  Take $A=2,N=4$ for `completedZeta_contour_split`, including its
  reflected sample at $-1-it$.

Independent Yah statement review (`compact-mellin-review`) confirmed the
sign, hypotheses, and exact strip consumer against the digest-matched
PDF text extraction and the accepted right-line theorem. The extraction
is not a rendered-page reading. This proves admissibility, not either
local evaluation or the global comparison.

## Checked finite-place evaluation by Fourier inversion

[`Theorems.RationalExplicitFormulaFinitePlaces`](../../Proofs/Theorems/RationalExplicitFormulaFinitePlaces.lean)
proves (B.4.2.10)–(11), p. 615, for smooth compact log profiles over
$\mathbb Q$. Write $\Phi=\Phi_g$, $s=2+it$, and $W(t)=\Phi(s)+\Phi(1-s)$.

- `Masullo.compactLogMellin_prime_power_evaluation` proves, for every real
  $n>0$, that $(2\pi)^{-1}\int W(t)n^{-s}\,dt=g(\log n)+n^{-1}g(-\log n)$.
- `Masullo.completedZeta_contour_finite_places` inserts these samples
  into the checked split contour. The expression is the normalized real
  Gamma integral **minus** the sum of the samples weighted by
  $\Lambda_{\rm vM}(n)$. It preserves both poles, absolute summability
  of both sums, and full zero multiplicities. The $n=0$ term vanishes on
  both sides; Mellin inversion is only applied at positive arguments.

Masullo supplies the Euler coefficients, the reflected argument, and the
Dirac evaluation idea. With ordinary point evaluation, extracted
(B.4.2.10) lacks $2\pi$ for unnormalized $dt$, and the upward $ds$ integral
in (B.4.2.11) needs $+2\pi i$, not $-i$. The inverse normalization in
(B.2.1.16), p. 596, gives the same check. The Euler minus sign belongs
in the contour, not in the reflected sample. The repair is
`compactLogMellin_reflected_inversion` in
[`Lemmas.CompactLogMellinInversion`](../../Proofs/Lemmas/CompactLogMellinInversion.lean):
Reflect $x\mapsto-x$ inside the second Mellin integral to get the inverse
Fourier transform of $h(x)=e^{2x}g(x)+e^xg(-x)$ at $t/(2\pi)$. Compact
support makes $h$ integrable and strip decay makes its transform
integrable. Changing the Lebesgue variable and applying Mathlib's
pointwise Fourier inversion supplies the exact Jacobian, then the
positive-base power contributes $n^{-2}$, leaving $n^{-1}$ on the
reflected sample. Absolute summability of the evaluated coefficients
follows from the checked sum of the finite integrands' $L^1$ norms.

Independent Yah statement review (`finite-eval-statement`) checked the
normalizations, signs, domain, and convergence against the digest-matched
Masullo extraction and the accepted split. Neither source reading is a
visual check. This does not evaluate the Gamma term or establish the
global geometric comparison.

<a id="next-runnable-obligation-prove-the-digamma-integral-needed-at-the-real-place"></a>

## Checked digamma integral for the real Gamma factor

Masullo invokes [Barner](https://gdz.sub.uni-goettingen.de/download/pdf/PPN243919689_0323/LOG_0011.pdf)
after (B.4.2.16), p. 616, to evaluate the real term. Barner starts from
Gauss's integral on p. 145 just before (19). Subtract the formula at $z$
from the one at $1$ and set $t=e^{-u}$ to get the subtracted form.
Barner's p. 146 Proposition (20) is instead a *tested integral*, which
p. 150 applies after shifting the contour, with the weighted test and
its reflection. It does not identify the global trace projection.

- [`Masullo.digamma_one_sub_eq_integral`](../../Proofs/Lemmas/DigammaIntegral.lean)
  proves absolute integrability on $(0,1)$ and
  $$
    \int_0^1\frac{t^{z-1}-1}{1-t}\,dt=\psi(1)-\psi(z),\qquad \Re z>0.
  $$
  Barner cites Gauss; pinned Mathlib defines $\psi=\Gamma'/\Gamma$ but
  does not supply that integral. The Lean repair derives it by
  subtracting $B(1,\varepsilon)$ from $B(z,\varepsilon)$ for real
  $\varepsilon>0$. The difference of the Beta integrands is the kernel
  times $(1-t)^\varepsilon$. The kernel is integrable near zero by the
  complex-power bound, and extends continuously across $1$ by the
  divided difference. Thus its norm dominates the regularized integrands.
  The Beta–Gamma identity, recurrence, and quotient rule compute the
  same limit as $\psi(1)-\psi(z)$.
- [`Masullo.logDeriv_GammaReal_eq_integral`](../../Proofs/Props/GammaRealLogDerivative.lean)
  differentiates Mathlib's actual rational real factor
  $\Gamma_{\mathbb R}(s)=\pi^{-s/2}\Gamma(s/2)$, giving
  $(-\log\pi+\psi(s/2))/2$. Substitution $t=e^{-2x}$ in the checked
  Gauss difference, with decreasing Jacobian of absolute value
  $2e^{-2x}$, and $\psi(1)=-\gamma$ give, on $\Re s>0$,
  $$
  \frac{\Gamma_{\mathbb R}'(s)}{\Gamma_{\mathbb R}(s)}
   = -\frac{\log\pi+\gamma}{2} + \int_0^\infty K(s,x)\,dx,
   \qquad K(s,x)=\frac{e^{-2x}-e^{-sx}}{1-e^{-2x}}.
  $$
  The statement includes absolute integrability of the combined kernel
  for each such $s$. It is the scalar input to (B.4.2.13), not the
  tested evaluation (B.4.2.15).

Independent Yah statement review (`digamma-statement`) checked both
endpoints against the pinned Mathlib interface, digest-matched Masullo
layout extraction, and Barner OCR (PDF ordinals 8, 9, and 13, printed
pp. 145, 146, and 150; SHA-256
`086a7885f8bd84029e6b8ae98b83ba9a1c172e7615a904d7636aa285c34a1f3b`).
Neither review is visual. The definition extracted at (3.2.1.4), p. 123,
agrees with the negative prefactor derivative, unlike the combination of
$-\alpha_v$ in (B.4.2.12) and negative $\alpha_v$ on p. 616. In the
central-line form the reflected multiplier on $\Phi(s)$ would be
$-\log\pi+[\psi(s/2)+\psi((1-s)/2)]/2$; the extracted (B.4.2.16) omits
both the constant and the half. The extracted (B.4.2.15) also has a
nonintegrable $g(0)/x$ tail for compact log profiles with $g(0)\ne0$.
Barner's p. 150 display retains $e^{-2x}$ in that term in the real case.
These are extraction-based discrepancies, not rendered-page findings.
The checked scalar normalization uses neither the manuscript's displayed
constant nor a contour shift.

<a id="next-runnable-obligation-evaluate-the-tested-real-gamma-term"></a>

## Checked real Gamma evaluation and rational explicit formula

[`Masullo.compactLogMellin_GammaReal_evaluation`](../../Proofs/Props/GammaRealMellin.lean)
evaluates (B.4.2.13), p. 616, on the right line for smooth compact log
profiles $g$. With $s=2+it$ and $W(t)=\Phi_g(s)+\Phi_g(1-s)$, it gives
absolute integrability of the combined $x$ kernel and

$$
 \frac{1}{2\pi}\int_{\mathbb R}W(t)\frac{\Gamma_{\mathbb R}'(2+it)}{\Gamma_{\mathbb R}(2+it)}\,dt
 = -(\log\pi+\gamma)g(0)+\int_0^\infty
 \frac{2g(0)e^{-2x}-g(x)-e^{-x}g(-x)}{1-e^{-2x}}\,dx.
$$

Masullo invokes Barner's tested digamma formula and Mellin inversion in
(B.4.2.14)–(B.4.2.16). The Lean proof uses the checked scalar
`logDeriv_GammaReal_eq_integral` and supplies joint domination before
Fubini. The estimate in
[`Lemmas.GammaRealRightLine`](../../Proofs/Lemmas/GammaRealRightLine.lean)
uses $|1-e^{-itx}|\le |t|x$ and $x\le\sinh x$ to give one product
majorant on the whole positive half-line: $|K(2+it,x)|\le |t|e^{-x}/2$.
Vertical strip decay gives the needed absolute moments of $W$.
`compactLogMellin_prime_power_evaluation` at $n=1$ and $n=e^x$ then
computes each fixed-$x$ slice. The singular $x$ terms are not integrated
separately, and the proof does not need the manuscript's contour shift.

With Barner's centered test $F(x)=e^{x/2}g(x)$, the nonlocal numerator
is $e^{-x/2}(F(x)+F(-x))$. Barner's Gauss subtraction at pp. 145–146,
150 retains $g(0)e^{-2x}/x$; its difference from our subtraction
integrates to $-\gamma g(0)$ by Gauss at $z=1$. The $-\log\pi\,g(0)$
term comes from the real prefactor. This explains the change of
subtraction in prose; the Lean endpoint uses the checked Beta–Gamma
route, not an assumed evaluation of Barner's subtraction.

[`Masullo.completedZeta_explicit_formula`](../../Proofs/Theorems/RationalExplicitFormula.lean)
substitutes this evaluation into the finite-place contour. This is the
rational trivial-character compact-log case of Theorem B.4.2.2,
(B.4.2.17), with the Mellin arguments unshifted. It retains both poles,
the minus von Mangoldt sum, and the absolutely summable, full-order
open-strip zero sum. The three new modules and their exported endpoints
are the scope of the Lake and axiom audit. Independent Yah review
(`real-term-statement`) checked the endpoint's constants, reflected
weight, measures, and scope against the accepted dependencies,
digest-matched Masullo layout extraction, and Barner OCR. These were
not visual readings. No idelic or global trace identification is
claimed.

## Local audit control

Use [`audit-local`](../../cmd/godel/README.md#checking-a-proof-candidate)
from the integration workspace with the full candidate ID, all changed
modules, and the independently reviewed endpoints. On the explicit-formula
proof tree from `81704cee`, the Lake build passed but the single
`leanchecker` invocation with all three modules exited 139. The pinned
checker schedules replay tasks together for multiple targets. Separate
processes for `Lemmas.GammaRealRightLine`, `Props.GammaRealMellin`, and
`Theorems.RationalExplicitFormula` all returned success. An end-to-end
control with the serial helper on the same unchanged proof tree passed
all three replays and the audit of all five public endpoints, each using
only `propext`, `Classical.choice`, and `Quot.sound`. The helper fails on
any individual replay error. This is a checking workflow change, not a
new statement review or proof.

## Checked real logarithmic Fourier kernel off the identity

In the pinned extraction, (B.4.4.1)–(B.4.4.2), pp. 619–620, define the
unnormalized-looking real term using the **negative** Fourier pairing
$-\int_{\mathbb R}\log|\xi|\,\widehat u(\xi)\,d\xi$, with
$u(z)=f(1+z)|1+z|^{-1/2}$ extended by zero near $z=-1$ and
$f(y)=F(\log|y|)$. Example A.3.1.5, p. 557, specifies the standard
$e^{-2\pi i z\xi}$ transform and self-dual Lebesgue measure. Equation
(B.4.4.20), p. 625, sends that pairing to the full-measure cutoff
in (B.4.3.13), p. 619, while (B.4.4.16) divides it by $M_\infty=2$.
Connes, *Trace Formula in Noncommutative Geometry and the Zeros of the
Riemann Zeta Function*, [arXiv:math/9811068v1](https://arxiv.org/abs/math/9811068v1),
Appendix II (30), (32)–(37), instead uses the same additive Fourier
pairing and the **normalized** multiplicative Haar ($dy/(2|y|)$),
including the constant $\lambda=\log(2\pi)+\gamma$. This is a
provisional text-based factor-of-two mismatch, already off the identity;
rescaling a measure in the cutoff does not rescale the additive pairing.

[`Masullo.real_log_fourier_off_zero`](../../Proofs/Props/RealPrincipalValue.lean)
proves, for smooth compactly supported complex $u$ vanishing near $0$,

$$
 -\int_{\mathbb R}\log|\xi|\,\widehat u(\xi)\,d\xi
   = \frac12\int_{\mathbb R}\frac{u(z)}{|z|}\,dz,
$$

including absolute integrability on both sides. Masullo supplies the
additive pairing and its transform convention; the Lean endpoint supplies
the corrected off-identity kernel. It keeps the subtraction together in
$k_a(\xi)-k_a(1)$, where $k_a(x)=a/(a^2+x^2)$, to represent the negative
log by an absolutely integrable scale exchange. At each positive scale,
Fourier inversion at zero cancels the subtracted term. The Fourier
transform of $e^{-2\pi a|z|}$ is $k_a(z)/\pi$; the bilinear Fourier
exchange uses $\mathcal F^2u(z)=u(-z)$ and the evenness of the exponential.
An independent spatial Fubini argument gives $1/(2|z|)$.

Independent Yah review matched the endpoint and both exchanges to
Connes (30), (34), reading the pinned Masullo PDF by text extraction.
Equation (B.4.3.13) instead appears to have twice the off-identity
magnitude; (B.4.4.20) may also omit the sign reversal required by
(B.4.4.1). The Lean theorem settles the coefficient of the additive
pairing, not the typography of those pages. A nonzero nonnegative log
bump supported in $(0,\log 2)$ detects the discrepancy, since the
identity term vanishes. Visual verification remains open. The two new
modules built with `lake --wfail build Props.RealPrincipalValue`; the
integration audit checks both modules and this endpoint with `audit-local`.

<a id="next-runnable-obligation-extend-the-real-kernel-to-tests-vanishing-at-zero"></a>

## Checked real logarithmic Fourier kernel for zero-value tests

[`Masullo.real_log_fourier_of_zero`](../../Proofs/Props/RealPrincipalValue.lean)
proves the same $1/2$ kernel for continuous $u$ with $u(0)=0$, assuming
absolute integrability of $u$, $\widehat u$, $\log|\xi|\,\widehat u(\xi)$,
and $u(z)/|z|$. It does not require a gap in the support, compactness,
or smoothness. This is the zero-value component of Connes Appendix II
(34), p. 74 of the arXiv v1 extraction, for Masullo's real additive
pairing (B.4.4.1), pp. 619–620. The earlier off-zero theorem now follows
by specialization. The extracted footnote 16 on p. 619 itself asks for
a recheck of the factors and of the contact coefficient. It does not
change the transform in A.3.1.5 or justify using unnormalized Haar for
the fixed additive pairing. The source statements here use the pinned
PDF's text, not rendered-page verification.

Continuity of the transform of an $L^1$ function justifies the frequency
measurability in the existing Cauchy exchange. Ordinary Fourier
inversion applies to continuous $u$ with both $L^1$ hypotheses, so the
subtraction again cancels at each positive scale. The spatial Fubini
argument uses exactly the absolute $u(z)/|z|$ pairing. The new Lean
helper `RealLogFourier.integrable_div_abs_of_local_bound` proves this
last integrability from $u\in L^1$ and $|u(z)|\le C|z|$ near zero,
bounding the quotient on a bounded interval and the tail by a multiple
of $|u|$. This is the estimate needed for the comparator remainder
below, which need not be differentiable at zero. Independent Yah review
(`real-zero-statement`) checked both statements, the two absolute Fubini
exchanges, and the comparator's remaining hypotheses against the pinned
Mathlib and the digest-verified Masullo extraction and Connes Appendix II.
The two modules and reviewed endpoints are the scope of `audit-local`.

<a id="next-runnable-obligation-calibrate-the-contact-term-in-the-real-cutoff"></a>

## Checked real logarithmic Fourier contact term

[`Masullo.real_log_fourier_unit_subtraction`](../../Proofs/Props/RealPrincipalValue.lean)
proves the real additive principal value on all complex Schwartz tests. With
$T(u)=-\int \log|\xi|\,\widehat u(\xi)\,d\xi$ in the standard additive
Fourier convention, Lean gives

$$
T(u)=\frac12\int_{\mathbb R}
  \frac{u(z)-u(0)\mathbf 1_{|z|\le1}}{|z|}\,dz
  +(\log(2\pi)+\gamma)u(0).
$$

Both pairings are absolutely integrable as written. Masullo supplies the
additive definition in (B.4.4.1), pp. 619–620, and refers from (B.4.3.13),
p. 619, to Connes Appendix II. Connes (32)–(35), pp. 73–74, fixes this
contact coefficient by a Gaussian calculation. Lean instead uses the
scale-one comparator $G(z)=e^{-2\pi|z|}$ to repair the doubled magnitude
in the provisionally extracted (B.4.3.13). The existing transform
calculation gives $\widehat G(\xi)=1/(\pi(1+\xi^2))$. On the positive
half-line, writing $\xi=e^s$ makes its log-weighted integral an odd
integrable function of $s$; even folding then gives $T(G)=0$.

In [`Lemmas.RealLogFourierContact`](../../Proofs/Lemmas/RealLogFourierContact.lean),
`laplace_unitSubtraction_contact` computes the half-weighted spatial
pairing of $G$ as $-\log(2\pi)-\gamma$. On the positive ray, with
$b=2\pi$ and $z=e^s$, use the density $be^{-bt}dt$ to express the
subtraction as the mean of
$\mathbf1_{s\le\log t}-\mathbf1_{s\le0}$. Its signed Lebesgue integral
is $\log t$ and its absolute integral is $|\log t|$. This gives an
absolute Fubini exchange; rescaling $t$ by $b$ then applies Mathlib's
integral for Euler's constant. The cusp comparator and its remainder
need not be smooth. The checked zero-value theorem applies to the
remainder $u-u(0)G$ by continuity, absolute integrability, and the local
first-order bound from differentiability of $u$ and the exponential
inequality. Independent Yah review (`contact-statement`) checked the
normalizations and hypotheses against the digest-verified Masullo
extraction and Connes (30), (32)–(37). The printed displays have not
been visually verified. The three changed Lean modules and the scalar
and Schwartz endpoints are the scope of `audit-local`.

<a id="next-runnable-obligation-prove-the-shrinking-cutoff-form"></a>

## Checked real shrinking-cutoff principal value

[`Masullo.real_log_fourier_cutoff`](../../Proofs/Props/RealPrincipalValue.lean)
proves for every complex Schwartz test $u$ that the spatial pairing is
absolutely integrable on each $|z|\ge\varepsilon>0$, and that

$$
\lim_{\varepsilon\to0^+}
\left(\frac12\int_{|z|\ge\varepsilon}\frac{u(z)}{|z|}\,dz
      +u(0)\log\varepsilon\right)
= -\int_{\mathbb R}\log|\xi|\,\widehat u(\xi)\,d\xi
  -(\log(2\pi)+\gamma)u(0).
$$

This is Connes (34)–(35), p. 74, with the contact term moved to the
right-hand side. It gives the cutoff for Masullo's additive pairing
(B.4.4.1), pp. 619–620, not the magnitude in the extracted (B.4.3.13).
For $0<\varepsilon\le1$, folding both rays gives
$\int_{\varepsilon\le|z|\le1}dz/|z|=-2\log\varepsilon$. Thus the
expression inside the limit equals half the integral of the absolute
unit-subtracted density over the same cutoff, with no leftover boundary
term. Dominated convergence applies to the cutoff indicators off the
null singleton. The Fourier pairing retains the sign and normalization
already checked above. Independent Yah review (`real-cutoff-review`)
matched the sign, measures, right-sided limit, and absolute integrability
against the digest-verified Masullo extraction and Connes (30), (34)–(37).
Only the text extraction, not the printed display, was checked. The local
integration audit covers `Lemmas.RealLogFourierContact`,
`Props.RealPrincipalValue`, and the new cutoff endpoint.

<a id="next-runnable-obligation-translate-the-cutoff-to-real-multiplicative-haar"></a>

## Checked real cutoff on multiplicative Haar

[`Props.RealLogProfileHaar`](../../Proofs/Props/RealLogProfileHaar.lean)
uses Masullo's translate (B.4.4.2), p. 620. For a smooth compactly
supported log profile $F$, put $f(y)=F(\log|y|)$ on $\mathbb R^\times$
and $u(z)=|1+z|^{-1/2}f(1+z)$, extended by zero at $-1$.
`real_log_profile_additive_test` proves that $u$ is smooth and compactly
supported, with $u(0)=F(0)$. Compact log support ensures an actual zero
neighborhood at $-1$, not just a removable point. For each $\varepsilon>0$,
`real_log_profile_haar_cutoff` proves absolute integrability and

$$
\frac12\int_{|z|\ge\varepsilon}\frac{u(z)}{|z|}\,dz
=\int_{\substack{y\in\mathbb R^\times\\|1-y|\ge\varepsilon}}
  f(y)\frac{|y|^{1/2}}{|1-y|}\,\frac{dy}{2|y|}.
$$

The Lean proof first translates Lebesgue measure and the cutoff by
$y=1+z$, then uses `map_realMultiplicativeHaar_val` for the density on
real units, with both signs retained. `real_log_profile_haar_principalValue`
transfers the right-sided limit: The Haar integral plus
$F(0)\log\varepsilon$ tends to the negative additive Fourier log pairing
of $u$ minus $(\log(2\pi)+\gamma)F(0)$. Thus the functional itself
includes the contact term; the limit alone does not.

Connes Appendix II (34)–(37), p. 74, supplies this normalization, also
consistent with Masullo Remark B.4.4.4, p. 620, on canonical real Haar.
In the provisional Masullo extraction, if retaining the external
$1/M_\infty=1/2$ in (B.4.4.16), p. 623, and the real $1/2$ in
(12.5.1.1), p. 519, the raw-Haar functional being scaled must be twice
the additive functional, not the literal (B.4.4.1). Equation (12.4.1.25),
p. 519, cites Lemma B.4.3.2 and uses the inverse argument before passing
to (12.5.1.1). Inversion does not preserve the finite physical cutoff;
this result does not identify the actual global $S$-piece, justify its
operator limit, or supply either Mellin subtraction. Independent Yah
review (`real-haar-review`) matched the three endpoint types to the
pinned extraction, Connes Appendix II, and the checked Haar and additive
interfaces. The printed displays have not been visually checked. The
local integration audit covers both new modules and the three endpoints.

Adopted as `852e57bfbd4870a6fb1b3818ad00ba23ac0ff506`. Its Lean inputs
match the earlier independently reviewed and audited candidate
`4f74603111803f89d05ae5e96040e5e7093ad2c9`, whose adoption went stale.
Restoring only its proof and handoff patch on the current base preserved
later non-proof work. With the [trusted Lake cache reuse procedure](../../cmd/godel/README.md#recovering-a-checked-but-unadopted-proof),
the exact new candidate passed the full Lake build, separate kernel
replay of both modules, endpoint type inspection, and all three axiom
checks (`propext`, `Classical.choice`, and `Quot.sound` only). The
`audit-local` command took about 11.5 seconds, versus about 101 seconds
for the prior cold audit. The replay and axiom checks were not skipped.

<a id="next-runnable-obligation-compare-physical-and-symmetric-log-cutoffs"></a>

## Checked comparison of physical and symmetric log cutoffs

[`Props.RealLogProfileHaar`](../../Proofs/Props/RealLogProfileHaar.lean)
now checks absolute integrability of the same half-Haar kernel on
$|\log|y||\ge\varepsilon>0$, that its integral minus the physical-cutoff
integral tends to zero, and that the compensated log cutoff has the same
Fourier pairing and contact term as the physical one. The three endpoints
are `real_log_profile_haar_log_cutoff_integrable`,
`real_log_profile_haar_cutoff_difference`, and
`real_log_profile_haar_log_principalValue`. No endpoint assumes $F(0)=0$.

Masullo supplies the physical cutoff (B.4.3.13), p. 619, and its translated
multiplicative coordinates (B.4.4.1)–(2), pp. 619–620. The extracted inverse
replacement after (12.4.1.25)–(28), p. 519, is asserted for the finite sums;
it does not identify the two finite cutoff domains. The project repair
`RealLogCutoff.tendsto_logAddSet_compensated` compares the cutoffs in the
additive coordinate $z=y-1$. The existing absolutely integrable unit
subtraction restores both deleted neighborhoods, at $z=0,-2$, by dominated
convergence. The singular model $F(0)\mathbf1_{|z|\le1}/|z|$ lives on the
nonnegative $y$ ray, and its two remaining integrals have endpoints
$a_+=e^\varepsilon-1$ and $a_-=1-e^{-\varepsilon}$. From the exact integrals
and $a_\pm/\varepsilon\to1$, the residual constant is zero. The cutoff
difference then follows by subtracting the two compensated limits, with
identical counterterms. This repair allows an inversion-invariant cutoff;
it does not establish the global finite-sum replacement or operator limit.

Independent Yah statement review (`log-cutoff-review`) checked both sign
components, the counterterm, and the proposed statements against the
accepted Lean interface and the digest-verified extraction. The manuscript
reading remains provisional until visual verification. The local audit
scope is `Lemmas.RealLogProfileHaar`, `Lemmas.RealLogCutoff`, and
`Props.RealLogProfileHaar`, with the three endpoints above.

<a id="next-runnable-obligation-match-the-rational-real-haar-and-gamma-terms"></a>

## Checked comparison of the rational real Haar and Gamma terms

[`Props.RealHaarGamma`](../../Proofs/Props/RealHaarGamma.lean) compares the
reflected right-line Gamma integral in (B.4.2.13)–(15), pp. 615–616, with
the real local term in (B.4.4.16), p. 623, on every smooth compact log
profile $F$. Put $g(x)=e^{-x/2}F(x)$ and use the translated test $u$ of
(B.4.4.2), p. 620, as formalized above. Let $G(g)$ be the integral of
$[\Phi_g(s)+\Phi_g(1-s)]\Gamma_{\mathbb R}'(s)/\Gamma_{\mathbb R}(s)$
against $dt/(2\pi)$ on $s=2+it$. The first endpoint,
`real_log_profile_fourier_eq_neg_gamma`, proves

$$
-\int_{\mathbb R}\log|\xi|\,\widehat u(\xi)\,d\xi=-G(g).
$$

The second endpoint, `real_log_profile_haar_log_tendsto_neg_gamma`,
identifies the right-sided limit explicitly: If $H_\varepsilon$ is the
integral of the Haar kernel over $|\log|y||\ge\varepsilon$ for **half**
the full real Haar measure, then

$$
H_\varepsilon+F(0)\log\varepsilon+(\log(2\pi)+\gamma)F(0)
\longrightarrow -G(g).
$$

No parity or zero-identity-value premise is imposed. The external minus
in (B.4.4.16) turns this local value into $+G(g)$ on the zero-sum side.
The external $1/M_\infty=1/2$ there normalizes full real Haar; applying it
again to the additive pairing would halve the term incorrectly.

Masullo supplies the reflected pairing and the translated additive test,
but not this convergence comparison with the corrected subtraction and
contact term. The proof uses `RealLogHaarFold.fold` to fold both signs and
both log rays at fixed positive cutoff into the kernel
$A(x)=e^{-x/2}(F(x)+F(-x))/(1-e^{-2x})$ on $x>\varepsilon$.
The checked `compactLogMellin_GammaReal_evaluation` supplies integrability
of the **combined** kernel $A-S$ on $x>0$, where
$S(x)=2F(0)e^{-2x}/(1-e^{-2x})$. The literal extracted subtraction in
(B.4.2.15) does not decay integrably at infinity; the exponential factor
in the checked subtraction fixes this. The proof integrates $S$ only at
positive cutoff, by the primitive $F(0)\log(1-e^{-2x})$. Thus
$\int_\varepsilon^\infty S+F(0)\log\varepsilon\to -F(0)\log 2$.
The previously checked Fourier contact term then leaves exactly
$(\log\pi+\gamma)F(0)$ in the complete local functional, with the sign
opposite to the tested Gamma constant. Independent Yah review
(`review-archimedean`) checked the proposed identity, the half twist,
and the contact and subtraction constants against the accepted interfaces
and the digest-verified extraction. The final statement review
(`review-final-arch`, output `5e91af6e2c1d7b84eaf4a6471953e8baaaf2e015`)
confirmed the rational trivial-character local scope. The manuscript
reading is provisional, not a visual check.

The exact adopted proof revision `d8c745d9cf6c8ef244b605f9d17c609f26d549c6`
passed `audit-local`: Full `lake --wfail build Proofs`, separate kernel
replay of `Lemmas.RealLogHaarFold` and `Props.RealHaarGamma`, and axiom and
provenance checks on both endpoints above. Both use only `propext`,
`Classical.choice`, and `Quot.sound`. The endpoint types were also
inspected in the built environment.

This closes the real local comparison only. It does not identify the
actual global $S$-piece, its operator limit, or its Mellin subtractions.

## Checked rational finite Haar shells and prime-power samples

The local subtracted Haar calculation for the trivial character over
$\mathbb Q$ is in [`Props.RationalFiniteHaar`](../../Proofs/Props/RationalFiniteHaar.lean).
Masullo defines the subtraction on the unit group in (B.4.4.14), pp. 622–623,
and uses the uniformizer sum in (B.4.4.22), p. 625, citing (D.1.2.1), p. 747.
For radial $f(x)=F(\log|x|_p)$ the subtracted kernel is zero throughout
that group. Lean uses its zero extension there, including at the identity;
it does not integrate the unsubtracted singularity. Formula (B.4.4.3),
p. 620, converts unit-mass Haar to canonical Haar by multiplication by
$\log p$; the rational different is trivial in (B.4.4.21), p. 625.
These locators follow the digest-verified PDF text extraction, not a
rendered-page review.

The printed sum leaves the zero shell subtraction implicit and uses two
measures. `RationalLocalNormShell.eq_translate` identifies the actual
valuation shells with translates of the image of the integral units;
`RationalLocalNormShell.measure` shows each has mass one, with no additive
dilation factor. `rationalLocalRadialHaar_shellPair` then checks the two
signs: The denominator is $1$ at norm $p^{-m}$ and $p^m$ at norm $p^m$.
Both signed shells have the same weight, and the normalized pair is

$$
(\log p)p^{-m/2}\bigl(F(-m\log p)+F(m\log p)\bigr),\qquad m\ge1.
$$

`rationalLocalRadialHaar_eq_shellSum` uses the disjoint measurable shell
cover and compact log support to prove absolute integrability and equality
to the sum of the pairs. Each individual shell outside the support bound
vanishes before pairing; finite support is not inferred from cancellation.
`rationalLocalRadialHaar_eq_primeSamples` identifies the full normalized
local integral with the eventually-zero sum of
$(\log p)(g(\log n)+g(-\log n)/n)$, where $n=p^m$ and
$g(x)=e^{-x/2}F(x)$. These are exactly the samples of
`compactLogMellin_prime_power_evaluation` for smooth compact $g$
((B.4.2.10)–(11), p. 615), with no extra $2\pi$ factor or relative minus
sign. Only compact support is used for the Haar evaluation. The outer
minus sign in the contour decomposition acts on the whole finite term.

Independent Yah statement review `finite-shell-review` (output
`4b6c77ebe6e6a7650a1bfdfd4745ba725952cc95`) checked both shell signs,
normalization, compact-support assembly, and matching with the contour
samples against the pinned text and accepted interfaces. This is a
per-place calculation. It neither establishes the primed additive Fourier
pairing in (B.4.4.21) nor identifies an actual global trace limit. The
translated unit-indicator calibration below now checks one case of the
additive Fourier identification independently of the Haar shell calculation.

## Checked translated rational unit-indicator pairing

The pinned PDF text gives the translated test in (B.4.4.2), p. 620, and
(B.4.4.7)–(9), p. 621. Lemma B.4.4.5 reduces (B.4.4.14), pp. 622–623,
to the case $f(1)=0$ and the unit indicator. For the latter, $|1+x|_p^{-1/2}$
is one on the support, and the translated test is zero at $x=-1$.
Masullo states the two-ball transform following (B.4.4.15), p. 623;
footnote 24 asks for a check of its right-hand side. That transform is
not yet the evaluation of the two logarithm-weighted integrals.
In particular, the vanishing of the logarithm on the original
multiplicative units does not evaluate its pairing with the transformed
test. We derive the signed transform and evaluate that pairing directly.
These are text-extraction locators, not a rendered-page review.

[`padicTranslatedUnits_log_fourier`](../../Proofs/Theorems/PadicLogFourier.lean)
proves, for every natural prime $p$, absolute integrability and exact
vanishing of

$$
\int_{\mathbb Q_p} J(\xi)\,\widehat{u_p}(\xi)\,d\nu(\xi),
\qquad J(\xi)=\frac{\log|\xi|_p}{\log p},\qquad
u_p(x)=\mathbf1_{\{|1+x|_p=1\}}(x).
$$

Here $\nu=\texttt{padicAddHaar}\ p$ gives $B=\mathbb Z_p$ mass one, and the
Fourier kernel is the conjugate of `padicStdAddChar p (x * ξ)`.
`padicTranslatedUnits_eq_sdiff` proves $u_p=\mathbf1_B-\mathbf1_{-1+pB}$
via the set difference and inclusion. Using the two checked ball
transforms gives $\widehat{u_p}=\mathbf1_B-p^{-1}\chi\mathbf1_{p^{-1}B}$,
where $\chi(\xi)=\overline{\psi_p(-\xi)}$. The conjugate kernel fixes the
phase convention independently of any overbar lost in extraction.
Reversing the frequency reflects the Fourier transform and preserves
this pairing since $J$ is even and additive Haar is invariant under
negation. A phase on the first term is equivalent here since $\chi=1$
on $B$.

The weighted integrals are explicit in Lean:

- `padicIntegralBall_log_moment` proves absolute integrability and the
  value $-1/(p-1)$ by summing the shells of mass $(1-p^{-1})p^{-k}$,
  where $J=-k$. The singleton at zero contributes zero by the value
  assigned by Lean's logarithm.
- `padicOuterBall_log_phase` proves absolute integrability on $p^{-1}B$.
  The unweighted phase integrates to zero there by scaling and the
  integral-ball transform at $-p^{-1}$. Subtracting the inner ball gives
  $-1$ for the phase integral on the outer shell, where $J=1$. The full
  weighted phase integral is consequently $-1/(p-1)-1$.

Combining the two weighted integrals gives
$(1-p^{-1})(-1/(p-1))+p^{-1}=0$. This is the integral before the
outer factors of (B.4.4.1) and (B.4.4.14). It verifies the correction
test only for rational local fields with their standard character and
trivial local different. It does not transfer the principal-value
formula for general profiles or any geometric trace limit.
Independent Yah review `review-calibration` (output
`95e78494d3aac7c747b0e73dac1a973f430679aa`) checked the four Lean
statements against the pinned extraction, including the translation,
frequency sign, Haar normalization, both moments, and scope.

## Checked logarithmic Fourier pairing on rational balls avoiding zero

Proposition B.4.3.1(2), (B.4.3.5), pp. 617–618, gives the restriction
of the Fourier transform of $J(\xi)=\log|\xi|_p/\log p$ to locally
constant compactly supported tests on the multiplicative group. Its
proof uses (B.4.3.3)–(4) for covariance, uniqueness of the invariant
functional, and the unshifted unit test (B.4.3.9)–(11) for the coefficient
$-1/\mu_v(O_v^\times)$. Lemma B.4.4.3, (B.4.4.8), p. 621,
applies this to the shifted test (B.4.4.7) when $f(1)=0$. The
translation/character reformulation is (B.4.4.9). This is a restriction
of a Fourier distribution, not an evaluation of $J$ on the spatial
support. These locators come from digest-verified text extraction;
no rendered-page reading was made.

[`padicTranslatedBall_log_fourier`](../../Proofs/Theorems/PadicLogBallFourier.lean)
proves the rational indicator instance directly, without assuming
covariance or uniqueness of the Fourier distribution. For
$S=a+p^n\mathbb Z_p$, $n\in\mathbb N$, and $|a|_p>p^{-n}$, it proves
absolute integrability and the value

$$
\int_{\mathbb Q_p} J(\xi)\widehat{\mathbf1_S}(\xi)\,d\nu(\xi)
 = -\frac{p^{-n}}{(1-p^{-1})|a|_p}.
$$

Here $\nu=\texttt{padicAddHaar}\ p$ has integral-ball mass one, and
$\widehat{\mathbf1_S}$ uses the conjugated standard character. The
right side is the negative of the integral of
$d\nu(x)/((1-p^{-1})|x|_p)$ over $S$: The norm there is $|a|_p$ by the
strict radius inequality, and its mass is $p^{-n}$. This matches the
unit normalization in (B.4.3.5) and (A.3.2.3)–(4), p. 560. The
identification of that density with the ambient Haar module is still
needed for the final comparison.

Example A.3.1.6, (A.3.1.5), p. 557, has an intermediate expression
that, as extracted, shifts the frequency support instead of supplying
a phase. The last expression has centered support. We use
`padicTranslatedBall_fourier`, not the intermediate expression, to
check the translation step. This reading of the discrepancy is
provisional. The checked translated Fourier formula yields the factor $p^{-n}$
and a centered frequency support of radius $p^n$. The discrete norms
make the rescaled radius $|a|_p p^n$ at least $p$. The supporting
`padic_log_phase_moment` changes variables by $\xi\mapsto-a\xi$; additive
Haar contributes $|a|_p^{-1}$, and the logarithm changes by a constant
away from the null singleton. On $p^{-1}\mathbb Z_p$ that constant's
pairing is zero, while `padicOuterBall_log_phase` gives
$-1/(p-1)-1$. The remaining radial tail is invariant under translation
by $p^{-1}$, which multiplies the normalized phase by a nontrivial
constant. Its integral is therefore zero for any larger cutoff. This
proves the value with absolute integrability of the inner ball and
tail separately, not by conditional cancellation at infinity.

## Logarithmic Fourier pairing on all rational off-zero tests

[`padicTest_log_fourier_off_zero`](../../Proofs/Theorems/PadicLogTestFourier.lean)
proves for every locally constant, compactly supported
$u:\mathbb Q_p\to\mathbb C$ with $u(0)=0$ that both integrands are
absolutely integrable and

$$
\int J(\xi)\widehat u(\xi)\,d\nu(\xi)
 = -\frac{1}{1-p^{-1}}\int\frac{u(x)}{|x|_p}\,d\nu(x).
$$

This is the additive-density form of (B.4.3.5), pp. 617–618. Masullo's
(B.4.3.3)–(4), (B.4.3.9)–(11) use covariance, uniqueness of the
invariant functional, and the unit calibration. The Lean proof replaces
that route for this restriction. `padicTest_eq_sum_closedBalls` takes a
common radius from a Lebesgue number for the open fibers on the compact
support. It deduplicates the finite cover and uses the ultrametric
property to get pairwise disjoint balls. The zero fiber is open and a
ball contained in a nonzero fiber does not contain zero, giving the
strict radius inequality including at $p=2$. `padicClosedBall_log_pair`
uses the checked off-zero ball evaluation and rewrites its value as the
integral of the inverse-norm density: The norm is constant on each ball
and its additive Haar mass follows by translation from
`padic_measure_dilatedBall`. Finite Bochner linearity gives the test
identity and the integrability statements. The empty support is covered
by the empty sum.

The kernel in Lean is conjugated, whereas (A.3.1.5), p. 557, displays
positive character evaluation in its final expression. At the level of
the logarithmic pairing this sign choice is immaterial: Negating
frequency preserves the weight and additive Haar. The proof does not
claim a positive-sign pointwise Fourier identity. The comparison is
based on the digest-verified PDF text extraction, not a rendered-page
review. Independent Yah statement review `review-off-zero-assembly`
checked the endpoint and its two helpers, including the normalization,
finite-ball argument, and scope.

The exact adopted revision `746ae9dc5d40257e3e095ea7b5c3cd5579db9d6a`
passed the full Lake build and separate kernel replay of
`Lemmas.PadicTestDecomposition`, `Lemmas.PadicLogPair`, and
`Theorems.PadicLogTestFourier`. The pairing endpoint and its three checked
helpers use only `propext`, `Classical.choice`, and `Quot.sound`.

## Checked density of rational finite-place multiplicative Haar

[`map_rationalLocalMultiplicativeHaar_val`](../../Proofs/Theorems/RationalLocalHaarDensity.lean)
proves (A.3.2.3)–(4), p. 560, over $\mathbb Q$ as an equality of Borel
measures in the value coordinate of the actual rational completion:

$$
(\mathrm{Units.val})_*\mu_v =
\frac{1}{1-p^{-1}}\frac{1}{|x|_v}\bigl(\nu_v|_{K_v\setminus\{0\}}\bigr).
$$

Here $p$ is the prime attached to $v$, $K_v=\mathbb Q_v$,
$\mu_v=\texttt{rationalLocalMultiplicativeHaar}\ v$, and
$\nu_v=\texttt{rationalLocalFieldAddHaar}\ v$. There is no extra
$\log p$ factor: The equation uses the unit-normalized measure from
(A.3.2.2), not the canonical modulated measure in (B.4.4.3).

Masullo uses the normalized absolute value to assert Haar invariance,
then subtracts the maximal-ideal mass from the integer-ball mass.
`RationalLocalHaarDensity.measure_preimage_mul` checks the invariance on
every Borel set: Additive Haar uniqueness extends the calibrated
integral-ball dilation to the full measure, and the inverse-norm density
cancels the scaling under the nonnegative change of variables.
`RationalLocalHaarDensity.onUnits_unitMass` computes the unnormalized
mass $1-p^{-1}$ by the discrete norm gap and the two ball masses.
The theorem transports invariance to units, applies the checked Haar
uniqueness at mass one, and pushes the resulting equality along the
measurable embedding. Its image is the punctured field. The proof does
not use the off-zero Fourier pairing to establish Haar invariance.
The pinned text extraction is provisional; independent Yah review
`density-statement-review` (output `101bc63eac85545cd94857354dcdcd5fb17cce8a`)
checked the normalization, domain, and scope against the text and the
accepted interfaces. Audit scope: `Lemmas.RationalLocalNormShell`,
`Lemmas.RationalLocalHaarDensity`, and `Theorems.RationalLocalHaarDensity`.

## Checked rational shifted Fourier pairing on tests vanishing at one

[`rationalLocalShifted_log_fourier`](../../Proofs/Theorems/RationalLocalShiftedFourier.lean)
proves (B.4.4.5), p. 620, for every finite place of $\mathbb Q$ and every
locally constant, compactly supported $f:K_v^\times\to\mathbb C$ with
$f(1)=0$. If $u(x)$ is $f(1+x)|1+x|_v^{-1/2}$, zero at $x=-1$, then both
integrands are absolutely integrable and

$$
-\int_{K_v} J(\xi)\widehat u(\xi)\,d\nu_v(\xi)
= \int_{K_v^\times}\frac{f(y)|y|_v^{1/2}}{|1-y|_v}\,d\mu_v(y).
$$

Masullo defines the shifted test in (B.4.4.1)–(2), pp. 619–620, and
uses the restriction of the logarithmic Fourier distribution and the
substitution $y=1+x$ in (B.4.4.7)–(8), p. 621. Lean checks the required
test conditions with `rationalLocalShiftedTest_properties`: Compact
support on the units gives local constancy across the deleted point
$x=-1$, and $u(0)=f(1)$ permits the off-zero computation.
`rationalLocalLogFourier_off_zero` supplies the needed restriction by
transporting the checked direct ball proof of (B.4.3.5) to the actual
completion in both Fourier variables. It uses the same additive Haar
in both variables, not a new choice of normalization. After translation,
`rationalLocalHaar_integral_density` applies (A.3.2.3) in Bochner form,
including the integrability implication. The coefficients
$-(1-p^{-1})^{-1}$ and $(1-p^{-1})^{-1}$ agree after the leading minus
of (B.4.4.1); there is no $\log p$ factor at this normalization. The
proof does not rely on the adjacent (B.4.4.6) or its shift phase (9).

Independent Yah `shifted-statement-review` (output
`7d0e9e4ac296e96050a539d71653860e89bde6a0`) checked the endpoint's
hypotheses, both integrability claims, and normalization against the
pinned PDF extraction (not rendered pages). The final proof preserves
the reviewed endpoint and normalization-bearing definitions. Audit
scope: `Lemmas.RationalLocalShiftedTest`,
`Lemmas.RationalLocalLogPairTransport`, and
`Theorems.RationalLocalShiftedFourier`.

## Checked rational finite-place principal value by unit subtraction

[`rationalLocalShifted_principal_value`](../../Proofs/Theorems/RationalLocalPrincipalValue.lean)
proves the rational case of (B.4.4.14), pp. 622–623, and hence the
per-place comparison (B.4.4.21), p. 625, for **all** locally constant,
compactly supported $f:K_v^\times\to\mathbb C$. Write $U_v$ for the
integral units and $u_f$ for the shifted test of (B.4.4.2), p. 620.
The two integrands are absolutely integrable, and

$$
-\log(p)\int_{K_v} J(\xi)\widehat{u_f}(\xi)\,d\nu_v(\xi)
= \log(p)\int_{K_v^\times}
    \frac{(f(y)-f(1)\mathbf1_{U_v}(y))|y|_v^{1/2}}{|1-y|_v}\,d\mu_v(y).
$$

Here $J(\xi)=\log|\xi|_v/\log p$ by (B.4.3.2), p. 617,
$\mu_v(U_v)=1$, and $\nu_v(O_v)=1$ with the standard rational additive
character. The leading minus is from (B.4.4.1), p. 619. The
subtraction is only on $U_v$, not on the whole multiplicative group.
The factor $\log p$ follows (B.4.4.3) and (B.4.4.21); the local different
is trivial. The extraction of the denominator in (B.4.4.14) does not
clearly retain the unit superscript. The adjacent definition of
$\mathrm{PF}_0$ and (B.4.4.21) use the mass of the integral units.
This reading remains provisional pending rendered-page review.

Masullo reduces to $f(1)=0$ and the integral-unit indicator on p. 623.
Lean uses (B.4.4.5) on the **subtracted** test. For the discarded term,
`rationalLocalUnitIndicator_properties` checks that the indicator is
locally constant, compactly supported, and one at the identity. The
shifted extension is exactly the indicator of $|1+x|_v=1$, including
at $x=-1$. `rationalLocalUnitIndicator_log_fourier` transports the
checked p-adic pairing, including its absolute integrability and value
zero, to the actual completion. This replaces the frequency display
after (B.4.4.15), p. 623, questioned in footnote 24. The proof uses
`rationalLocalShiftedFourier_add_mul` to restore the **original** test
on the additive side, checking integrability of the inner Fourier
integrals from continuity and compact support before applying Bochner
linearity.

Independent Yah `principal-value-statement-review` (output
`8a161bbba3b6bbe8e11370bcff4120b08d40cbdc`) approved the hypotheses,
unit subtraction, and sign and scalar of the endpoint against the
pinned extraction. The normalized $J$ is the explicit non-Archimedean
definition (B.4.3.2), not the unnormalized logarithm in the section
introduction. Audit scope: `Lemmas.RationalLocalPrincipalValue` and
`Theorems.RationalLocalPrincipalValue`.

## Checked rational radial Fourier value in prime-power samples

[`rationalLocalRadialFourier_eq_primeSamples`](../../Proofs/Theorems/RationalLocalRadialPrimeSamples.lean)
identifies the rational radial case of the normalized primed local
integral (B.4.4.21), p. 625, with the evaluated contour contribution
(B.4.2.10)–(11), p. 615. For a compactly supported log profile $F$, let
$f(y)=F(\log|y|_v)$ and $g(t)=e^{-t/2}F(t)$. The integrand of the
canonical shifted Fourier pairing is absolutely integrable, and its
negative integral is the sum of the finitely many nonzero terms

$$
\log p\left(g(\log p^k)+p^{-k}g(-\log p^k)\right),\qquad k\ge 1.
$$

Masullo restricts a global test to the local group and uses a
uniformizer expansion in (B.4.4.22), p. 625. The needed admissibility
is checked for the radial pullback by `rationalLocalRadialTest_properties`:
The norm is locally constant on field units, and bounded log support
meets only finitely many shells, each a compact translate of the
integral units. No continuity of $F$ is needed for this local result.
`rationalLocalShifted_principal_value` then converts the Fourier pairing
to the unit-subtracted Haar integral. The pointwise bridge
`rationalLocalRadial_subtraction` cancels the entire norm-one shell,
including the identity, and identifies the remaining square-root
weight with the checked radial kernel. Finally
`rationalLocalRadialHaar_eq_primeSamples` evaluates the Haar sum with the
correct reflected factor and `log p`. The result does not require
$F(0)=0$. It does not identify a global geometric trace or prove a
distribution-topology limit. The equality is with the evaluated sample
formula, not the literal inversion displays with their contour measures.
Independent Yah `radial-statement-review` (output
`8535408d49047bdf6ee4728db1094d46e9d032df`) approved the admissibility,
normalization, sign, and reflected factor against the digest-verified
text extraction. Rendered-page verification remains open.

Audit scope: `Lemmas.RationalLocalShiftedTest`,
`Lemmas.RationalLocalRadialTest`, and
`Theorems.RationalLocalRadialPrimeSamples`.

## Checked sum of the rational radial finite-place terms

[`rationalLocalRadialFourier_tsum_eq_vonMangoldt`](../../Proofs/Theorems/RationalLocalRadialSum.lean)
reindexes the entire family of canonical finite-place Fourier values by
natural prime powers for a single compact log profile $F$. It needs
neither smoothness nor $F(0)=0$. With $g(t)=e^{-t/2}F(t)$ the value is

$$
\sum_{n\ge 0}\Lambda(n)\left(g(\log n)+\frac{g(-\log n)}{n}\right),
$$

with zero summand at $n=0$ (and at $n=1$). Both the place-exponent samples
and the whole local values have finite support, hence are absolutely
summable. Local absolute integrability is in
`rationalLocalRadialFourier_eq_primeSamples`; the sum uses exactly its
negative logarithmic Fourier pairing, including $\log p$.

Masullo gives the uniformizer expansion and the large-place support
argument in (B.4.4.22), p. 625. Footnote 27 there asks to explain the
comparison with B.4.2.2. Lean supplies the rational radial reindexing:
The bound $|t|\le R$ on log support kills both samples if $n>e^R$.
Unique positive prime-power representation identifies the pairs
$(v,m)$ with the integers $p_v^{m+1}$, where $m\ge0$. On that image
$\Lambda(p_v^{m+1})=\log p_v$, and off it the coefficient vanishes.
The resulting positive sample sum matches
`completedZeta_contour_finite_places`, using the checked inversion
normalization for (B.4.2.10)–(11), p. 615. It appears with an **outer
minus** in (B.4.4.16), p. 623. These locators are based on a
digest-verified extraction, not a rendered-page reading. Independent
Yah review `radial-sum-statement-review` checked the draft statement
against those three pages and the two Lean inputs, and confirmed the
normalization, the outer sign, and the scope of the support argument.

For the radial case, subtraction cancels the whole norm-one shell,
including when $F(0)\ne0$. The large-place bound in (B.4.4.22) only
controls nonzero exponents. Applying it to a nonradial test would
separately require constancy on the integral units outside finitely many
places. Neither the general idelic distributional convergence nor the
Chapter 12 global geometric trace follows from this finite sum.

Audit scope: `Theorems.RationalLocalRadialSum`, endpoints
`rationalLocalRadialFourier` and `rationalLocalRadialFourier_tsum_eq_vonMangoldt`.

## Checked rational radial idelic explicit formula

[`rationalIdeleRadial_explicit_formula`](../../Proofs/Theorems/RationalIdeleRadialExplicitFormula.lean)
proves the scalar rational, trivial-compact-character case of
(B.4.4.16), p. 623, for smooth compact log profiles. With
$\phi(c)=F(\log|c|)$ and $M_F(s)=\int\phi(c)|c|^{s-1/2}\,d\mu(c)$ on the
actual rational idele class group, it proves

$$
\sum_{\rho}\operatorname{ord}_{\rho}(\zeta)M_F(\rho)
 =M_F(0)+M_F(1)-D_{\infty}(F)-\sum_v D_v(F).
$$

The open-strip zero sum is absolutely summable, the normalized finite
local values have finite support, and the real additive pairing is
absolutely integrable. The per-place finite integrability statement is
`rationalLocalRadialFourier_eq_primeSamples`. Both polar moments and
all the zero pairings are integrals against `rationalIdeleClassHaar`.
`rationalIdeleRadialMellin_eq_compactLogMellin` uses the checked log-norm
pushforward to prove integrability and translate each pairing to
$\Phi_g(s)$ with $g(t)=e^{-t/2}F(t)$, by (B.2.1.29), p. 599, and the
norm-one volume convention (A.3.2.1), p. 560.

Masullo gives both poles and prescribes counting zeros by order before
(B.4.2.2), p. 614, but (B.4.4.16) does not display the order factor.
Footnote 27, p. 625, asks for the passage between these formulas.
Lean starts with `completedZeta_contour_finite_places`, substitutes
`rationalLocalRadialFourier_tsum_eq_vonMangoldt` for the finite sum, and
uses `real_log_profile_fourier_eq_neg_gamma` for the real term. The
latter supplies the Fourier contact normalization and identifies the
negative additive pairing with the normalized principal value. As
extracted, (B.4.3.13), p. 619, purports to compute the positive
logarithmic pairing but uses full Haar. Negating its right side gives
twice the negative additive pairing of (B.4.4.1)–(2), including twice
the contact term. Footnote 16 asks to recheck these coefficients.
For the identification invoked in (B.4.4.20), p. 625, apply $1/2$
to the sign-adjusted **full multiplicative Haar** expression, not to
the already normalized additive pairing. The different correction of
(B.4.4.21) is zero over $\mathbb Q$.

Independent Yah `idelic-statement-review` checked this repaired scalar
comparison, the sign and weights, and the scope against the
digest-verified text extraction and accepted Lean dependencies.
At `9330ec2f38fe508354301080f8110dc70989458a`, the full warning-free
Lake build and separate kernel replay of
`Theorems.RationalIdeleRadialExplicitFormula` passed. The elaborated
types were inspected, and the provenance and axiom audit of
`rationalIdeleRadialMellin`, `rationalIdeleRadialMellin_eq_compactLogMellin`,
and `rationalIdeleRadial_explicit_formula` found only `propext`,
`Classical.choice`, and `Quot.sound`.

This checks scalar equality, not strong-dual convergence on
$\mathcal D(C_F)$, ramified local terms, nontrivial compact characters,
or the global geometric trace. Source locators are from the pinned text
extraction; rendered-page verification remains open.

### Next: Compare the actual global geometric contribution

The rational radial comparison with (B.4.4.16) now supplies the scalar
reference value for the [above-one control](trace-to-zeros.md#first-unmatched-geometric-evaluation-and-a-positive-log-control).
At a common positive width and allowed Sobolev degree, take the
profile $F=b'$ supported in $(0,\log 2)$ specified there. The idelic
formula gives $M_F(0)+M_F(1)-D_\infty(F)$ on this support; the finite
local sum vanishes by the support bound. For the **actual** globally
lifted diagonal, justify the shell split of (11.3.1.4), p. 494, on this
control and test the identification invoked on p. 520: With an
independently justified zero orbital contribution it requires the
$S$-piece to be $D_\infty(F)-M_F(0)-M_F(1)$. The checked scalar formula
cannot supply that operator identification or its cutoff limits. In
particular, it does not turn vanishing of finite local values into
vanishing of orbital traces.

### Separate open obligation: Ramified calibration

For ramified continuation, the second frequency ball in the display
after (B.4.4.15), p. 623, needs its own check. The extracted subscript
appears to have $\mathfrak m_v^{-1}\mathfrak d$, whereas the
annihilator of $\mathfrak m_v$ for the trace character of Example
A.3.1.10, p. 558, is $\mathfrak m_v^{-1}\mathfrak d^{-1}$. These
coincide over $\mathbb Q_p$. The typography is provisional pending
rendered-page review; a mathematical repair can use `Submodule.traceDual`
and `coeIdeal_differentIdeal` over the finite extension of $\mathbb Q_p$.
The concrete local obligation is to compute the Fourier integral of
the indicator of $\mathfrak m_v$ with the trace character and
self-dual measure: Its value on that trace-dual lattice is
$\nu_v(\mathfrak m_v)$, and it is zero off it by translation. This
requires the finite extension and its ring of integers in the actual
completion, not just the global different.
