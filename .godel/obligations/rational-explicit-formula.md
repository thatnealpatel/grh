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

## Next runnable obligation: A lower bound at the right-hand anchor

Lang's §2 argument (scan printed pp. 335–336) compares the completed
logarithmic derivative to its value on the right edge using a
Weierstrass product, then uses the Euler product and Stirling there.
For the rational contour, a fixed-radius disk comparison is a project
route to the weaker polynomial bound actually needed. Do not infer
that bound from separation alone. First prove the anchor estimate in
Lean, for all real $t$ with $1\le |t|$:

$$\|\operatorname{entireZeta}(2+it)\|\ge (3\pi)^{-1}e^{-\pi |t|/4}.$$

The Dirichlet series gives $|\zeta(2+it)-1|\le \zeta(2)-1$,
so `riemannZeta_two` and `Real.pi_lt_d2` give $|\zeta(2+it)|\ge1/3$.
At $z=it/2\ne0$, `Complex.Gamma_add_one`, `Complex.Gamma_conj`,
and `Complex.Gamma_mul_Gamma_one_sub` give
$|\Gamma(1+it/2)|^2=\pi |t|/(2\sinh(\pi |t|/2))$. The elementary
upper bound on $\sinh$ then gives $|\Gamma(1+it/2)|\ge e^{-\pi |t|/4}$.
The completion contributes a factor of modulus $1/\pi$, and clearing
the poles multiplies the norm by $|(2+it)(1+it)|\ge1$. These are
already relevant pinned Mathlib interfaces, not a checked anchor proof.

For the successor, center a disk at $2+it$, take a radius in $(4,5)$
avoiding the zero radii, and strip the disk's zeros with finite
Blaschke factors. The checked `completedZeta₀_factorial_growth` on a
fixed real strip bounds the outer norm of `entireZeta` by $C(1+|t|)^2$.
The factors preserve the boundary norm and only increase the norm at
the center after division. On the zero-free quotient use a branch of
logarithm, Borel–Carathéodory, and a fixed-radius Cauchy estimate to
bound the logarithmic derivative for $\|s-(2+it)\|\le3$. Pinned
Mathlib supplies `MeromorphicOn.extract_zeros_poles`,
`Complex.exists_continuousOn_eqOn_exp_comp`,
`Complex.borelCaratheodory_zero`, and
`Complex.norm_deriv_le_of_forall_mem_sphere_norm_le`; the disk
comparison is not yet formalized. Jensen at outer radius $6$ and the
anchor bound control the sum of the orders in radius $5$. The log
derivatives of the factors each cost $O(1+\delta^{-1})$ at distance
at least $\delta$ from the zeros, because the denominator of each
Blaschke factor stays bounded away from zero in the inner disk after
normalization. At $s=2+it$ the distance to each zero is at least $1$,
so this route can also bound that vertical edge (use the checked
reflection for the left edge at $-1$ and compact continuity at bounded
heights). This uses $a=2$, allowed for the finite rational contour,
whose vertical lines are already known to be regular.

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
