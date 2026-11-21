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

## Next runnable obligation: Check the Fourier normalization of the real principal value

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

First prove the normalization control in Lean: For smooth compactly
supported $u$ vanishing near $0$,

$$
 -\int_{\mathbb R}\log|\xi|\,\widehat u(\xi)\,d\xi
   = \frac12\int_{\mathbb R}\frac{u(z)}{|z|}\,dz.
$$

A runnable route uses the Laplace difference for $-\log|\xi|$:
Integrate $(e^{-a|\xi|}-e^{-a})/a$ over truncated $a$ intervals, extend
by dominated convergence using $|\log|\xi||$, and discard the constant
on each truncated interval by $\int\widehat u=u(0)=0$. The Fourier
integral of $e^{-a|\xi|}$ is $2a/(a^2+4\pi^2z^2)$ by integrating
both half-lines. Off the support gap, Fubini and the elementary
$a$ integral give the displayed coefficient $1/2$. Test it on nonzero
nonnegative $g$ supported in $(0,\log 2)$; the inferred half-factor
discrepancy cannot be an identity-supported correction. Treat the
full cutoff normalization and its Fourier pairing as distinct until
this control is checked.

For the subsequent identity term, Connes (36)–(37) retains $\lambda$.
Use [`map_realMultiplicativeHaar_val`](../../Proofs/Theorems/RealMultiplicativeHaar.lean)
to track both signs and the division by two when starting with full Haar.
Folding $y=\pm e^{\pm x}$ gives the nonlocal weight
$e^{-x/2}/(1-e^{-2x})$. The physical cutoff $|1-y|\ge\varepsilon$
and the symmetric log cutoff differ by vanishing annular errors after
the cutoff radii are compared. The identity subtraction contributes
$-\log(1-e^{-2\varepsilon})+\log\varepsilon\to-\log 2$,
leaving $\log\pi+\gamma$. The full Fourier cutoff identity, the
finite-place idelic comparison, and the Chapter 12 global geometric
comparison are not checked by the rational explicit formula.
