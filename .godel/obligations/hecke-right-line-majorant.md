# An absolute majorant for the Hecke right line

**Scope:** The finite Euler product differentiation, two-index
summation, integration, and Mellin inversion in (B.4.2.5)–(11),
for any number field,
without a completed or meromorphically continued Hecke L-function.

## Source and needed estimate

In the [pinned text](../sources/masullo/README.md), (3.2.1.1), p. 122,
gives the unramified finite Euler factor. Lemma 3.2.1.1, (3.2.1.2),
p. 123, gives absolute, compact-uniform product convergence and refers
to comparison with the rational zeta product. Definition 3.2.1.4,
(3.2.1.7), pp. 123–124, takes the product of those finite factors. In
(B.4.2.5)–(7), p. 615, Masullo invokes absolute and uniform convergence
on the right line and expands the local logarithmic derivatives as
geometric series. In (B.4.2.8)–(9) he uses dominated convergence at
one place. To perform this interchange **over all places at once**,
we supply a summable bound for the differentiated coefficients, with
the extra $\log q_v$, over both $v$ and $m$. The locators and signs
are provisional text-extraction evidence, not rendered-page review.

## Lean interface

[`Theorems.FiniteHeckeRightLine`](../../Proofs/Theorems/FiniteHeckeRightLine.lean)
contains `Masullo.finiteHecke_right_line_majorant` and
`Masullo.finiteHecke_right_line_integrals`. For arbitrary number field
$K$, the places are `HeightOneSpectrum (𝓞 K)`, $q_v$ is the real cast
of `v.asIdeal.absNorm`, and $m=k+1$ with $k\in\mathbb N$. For $a>1$,
the nonnegative real majorant $c_a(v,k)=(\log q_v)/q_v^{am}$ is
summable on the product index, and bounds the norms of
$(\log q_v)z_v^m\exp(-ms\log q_v)$ on $\Re s\ge a$ for every family
$|z_v|\le1$. Omitted places are encoded as zero coefficients;
conjugating a coefficient does not change the bound.

The proof uses Mathlib's linear asymptotic for the count of nonzero
integral ideals. It obtains summability of the Dirichlet series for
the ideal-count coefficients at $b=(1+a)/2$, then inserts the
logarithm using Mathlib's log-weighted L-series summability at $a>b$.
We sum all ideal norm fibers, then restrict along the injection sending a
place to its underlying prime ideal. Geometric
summation in $k$ costs at most $(1-2^{-a})^{-1}$ since $q_v\ge2$.

For an integrable weight $W(t)$ on $s=a+it$, the second theorem
bounds each weighted term by $c_a(v,k)|W(t)|$. It proves integrability
of every weighted term and the pointwise sum, summability of the
$L^1$ norms, and equality of the integral of the sum with the sum of
the integrals. The constant $i$ from $ds=i\,dt$ can be incorporated
in $W$. The leading minus sign of $L'_v/L_v$ in (B.4.2.7) is not
part of `finiteHeckeTerm`; the term represents the expansion of
$-L'_v/L_v$, as the following Lean theorem establishes.

**Independent review:** `hecke-majorant-review` (`jZTGrdY`, read-only
on `c20757d6ecd4e0634e2836bef2d6e79698f2d3fe`, Yah session
`01a200b7-0e16-7dd4-a8ab-32d787ae8d07` parent) checked the proposed
statements against SHA-256-verified extracts of pp. 122–124 and
615–616, including the exponent sign, positive power indexing,
real power convention, and scope of the two-index interchange. This
is a statement review, not visual verification or kernel evidence.

## Finite Euler product and its logarithmic derivative

[`Theorems.FiniteHeckeEulerProduct`](../../Proofs/Theorems/FiniteHeckeEulerProduct.lean)
has two endpoints. `Masullo.finiteHeckeEulerFactor_logDeriv` proves, for
$|z_v|\le1$ and $\Re s>0$, that $E_v(s)=(1-z_v\exp(-s\log q_v))^{-1}$
is nonzero and differentiable and that the local positive-power series
in (B.4.2.7) sums to $-\operatorname{logDeriv}E_v(s)$. At $z_v=0$ this
means $E_v=1$ and a zero series; there is no constant-power term.
`Masullo.finiteHeckeEulerProduct_logDeriv` proves nonvanishing and
differentiability of $P(s)=\prod_v E_v(s)$ for $\Re s>1$, and identifies
$-\operatorname{logDeriv}P(s)$ with the joint `HasSum` on places ×
$\mathbb N$, not just an iterated series or an enumerated product.

Masullo states compact-uniform convergence in Lemma 3.2.1.1,
(3.2.1.2), and uses convergence in (B.4.2.5)–(7). Convergence just on
the integration line would not justify complex differentiation, and
compact-uniform product convergence alone does not give a whole-line
majorant for the differentiated series. The Lean proof treats these
separately. On $\Re s\ge a>1$, $|E_v-1|\le 2q_v^{-a}$; the
first-power slice of the checked majorant bounds the sum of these
deviations, since $\log q_v\ge\log 2$. The bound supplies the locally
uniform net of finite products (`finiteHeckeEulerFactor_hasProdLocallyUniformlyOn`)
and the nonzero limit (`finiteHeckeEulerProduct_ne_zero`). Mathlib's
`logDeriv_tprod_eq_tsum` then applies on the open half-plane; the joint
majorant and absolute Fubini identify the resulting sum with the
positive-power series. The checked integration theorem applies to
this series with any integrable right-line weight.

**Independent review:** `hecke-euler-review` (`iwBtyxB`, read-only on
`861ddae46e7a84e194d99880844c5fc1e4c05f3a`, Yah parent session
`01a200c1-19b3-787f-899e-9af93b9f2bce`) checked the two statements
against the same pinned PDF and Mathlib. In particular, (3.2.1.1)
is the denominator, not the reciprocal; (B.4.2.7) says “every finite
place,” but the coefficient is defined in §3.2.1 only at unramified
places. The unit factor at an omitted place resolves this scope issue.
Extraction does not reliably distinguish conjugation bars; the
reflected character needs conjugate coefficients at the same $s$,
not conjugation of the whole function value at $s$. These source
findings are provisional pending rendered-page inspection.

## The finite product of an actual Hecke character

[`Theorems.FiniteHeckeCharacterEulerProduct`](../../Proofs/Theorems/FiniteHeckeCharacterEulerProduct.lean)
uses the pinned `NumberField.HeckeCharacter (𝓞 K) K`. Its
`finiteHeckeCoefficient` takes `χ.localValue v` if the character is
unramified at $v$, and is zero otherwise. The local restriction is
evaluation of the global character on the single-place idele class,
so unitarity implies the coefficient bound
`norm_finiteHeckeCoefficient_le_one`.

For (3.2.1.1), p. 122, Masullo uses the normalized absolute value of a
uniformizer. `norm_uniformizer_eq_inv_finitePlaceNorm` proves this
normalization in the pinned completion by computing the generator of
the discrete valuation, and `uniformizer_norm_cpow` passes to the
complex power with positive real base. Then
`finiteHecke_localPolynomial_eval_uniformizer` identifies Mathlib's
local polynomial evaluation with the manuscript's denominator
$1-\chi_v(\pi_v)|\pi_v|_v^s$ for **every** unramified uniformizer. For
(3.2.1.7), p. 124, `finiteHecke_localPolynomial_eval_inv` identifies
its reciprocal with the project Euler factor, and
`finiteHeckeEulerFactor_eq_one_of_ramified` supplies the unit factor
at a place omitted by Masullo. The all-$s$ identities use Lean's
totalized inversion; the analytic assertion is only on $\Re s>1$.

`finiteHeckeCharacterEulerProduct_logDeriv` applies the earlier project
repair for (B.4.2.5)–(7) to the actual character: On $\Re s>1$ the
product of the inverse evaluated local polynomials is nonzero and
complex differentiable, and the joint positive-power series sums to
its negative logarithmic derivative. Mathlib's `χ.LSeries` is an
arithmetic-function Dirichlet series; we do not identify it with this
product. Nor do these results identify the completed or continued
function in (3.2.1.2)–(6).

**Independent statement review:** `hecke-character-review` (`ZJmYXhV`,
read-only on `fb69586e959e4f31f38afdb73b7598a547a38219`, Yah parent
session `01a200ca-54f9-7555-a17d-d9120ad7f6ef`) checked the three
interfaces against the digest-verified pp. 122–124 and 615–616 and
pinned Mathlib. Its required normalization, unit-modulus consequence,
and explicit ramified-place convention are provided by the results
above. This was extracted-text review, not visual verification.

## Checked: Separate Mellin inversion of the finite right-line integrals

Masullo evaluates the two terms by Mellin/Fourier inversion in
(B.4.2.10)–(11), p. 615. Compare the upward-line convention in
(B.4.2.4) and the two local expansions in (B.4.2.7). Provisionally,
the extraction of (B.4.2.10) displays ordinary $dt$ without the
$1/(2\pi)$ needed for point evaluation, while (B.4.2.11) displays
$-i$ multiplying the sample for a positive unnormalized $ds$ term.
Neither should be used as printed in the extraction. Both integrals
in (B.4.2.4) have the same normalization $ds/(2\pi i)=dt/(2\pi)$;
the reflection in the weight does not reverse the upward line. This
is a mathematical normalization check, not a verified visual reading.

`compactLogMellin_right_line_evaluation` and
`compactLogMellin_reflected_right_line_evaluation` in
[`Lemmas.CompactLogMellinInversion`](../../Proofs/Lemmas/CompactLogMellinInversion.lean)
prove the separate scalar identities for all real $a,y$, with smooth
compact log profile $g$, $\Phi(s)=\int g(x)e^{sx}\,dx$, and $s=a+it$.
After multiplication by $e^{-sy}$ and integration against
$dt/(2\pi)$, the weights $\Phi(s)$ and $\Phi(1-s)$ give $g(y)$ and
$e^{-y}g(-y)$, respectively. The proof uses angular-frequency Fourier
inversion of the weighted profile, then the substitution $x\mapsto -x$
in the Mellin weight for the reflected evaluation. The earlier
combined rational formula shares the same rescaling proof.

[`Theorems.FiniteHeckeRightLineInversion`](../../Proofs/Theorems/FiniteHeckeRightLineInversion.lean)
uses the checked joint $L^1$ interchange before applying those
identities at $y=m\log q_v$, $m=k+1$. For every $a>1$ it evaluates
each integrable log-derivative term as a negative absolutely
summable joint series on places $\times\mathbb N$:

- `finiteHecke_direct_right_line`: $(\log q_v)z_\chi(v)^m g(y)$.
- `finiteHecke_reflected_right_line`: $(\log q_v)z_\psi(v)^m e^{-y}g(-y)$.

The minus sign on each sum is the one in (B.4.2.7), and the separate
unitary characters preserve the different coefficients. The proof
covers the finite product and smooth compact log tests; it does not
establish the rest of (B.4.2.17), p. 616, or the general test class.
For the shifted convention in that equation, taking
$g(x)=e^{-x/2}\varphi(e^x)$ gives $q_v^{-m/2}$ in both samples.

**Independent statement review:** `hecke-inversion-review` (`yfLWwpY`,
parent Yah session `01a200d7-35e1-7637-a950-298bbf2f3b00`, accepted
base `54d6c5b85297d0eda931e2ed551077449db713c3`) checked the two scalar
and character formulas against pp. 615–616 of the digest-verified
manuscript and the accepted Lean interfaces. It confirmed the same
normalized sign and reciprocal norm factor and distinguished the
standalone right-line results from the missing global contour link.
This was extracted-text review, not visual verification.

## Checked: Pair the finite legs with the conjugate character

The reflected term in (B.4.2.7), (B.4.2.11), p. 615, and (B.4.2.17),
p. 616, uses $\bar\chi$ from (3.2.1.6), p. 123, not a free character.
`heckeConjugate` realizes this as pointwise complex conjugation on
idele classes. `heckeConjugate_isUnramifiedAt_iff` proves that both
characters are trivial on the same finite local unit groups. At an
unramified place `finiteHeckeCoefficient_conjugate` compares the values
at the same uniformizer in (3.2.1.1), p. 122; at a ramified place both
coefficients are zero. No unitarity is needed for these identities.

`finiteHecke_paired_right_line` applies the two checked evaluations to
$\chi$ and $\bar\chi$ (unitarity is preserved) and adds the integrals
and the absolutely convergent joint sums. At $y=m\log q_v$ the result
is the negative sum of
$$
(\log q_v)\bigl(z_\chi(v)^m g(y)+
    \overline{z_\chi(v)}^{\,m}e^{-y}g(-y)\bigr).
$$
Here both integrands are on the upward line with $a>1$. This is not
an assertion that the left line of the completed contour equals the
reflected leg; that requires the functional equation and its epsilon
factor.

**Independent statement review:** `hecke-conjugate-review` (`AXLjKfH`,
Yah parent session `01a200df-d170-72c4-b615-4f74015dc623`, exact base
`6898a153192f7ca5adbbc77aa7a42700f49500d2`) checked the place
restriction, the omitted-factor convention, the signs and
normalization, and the scope of the paired endpoint against pinned
Mathlib and the digest-verified manuscript. It also independently
identified the Archimedean tail obstruction below. This was
extracted-text review, not visual verification.

## Checked: Shifted Archimedean digamma identity

The factors in (3.2.1.3)–(5), p. 123, retain real sign parity and
complex angular weight. The extracted (B.4.2.12) and (16), pp. 615–616,
use a purely imaginary shift, which cannot distinguish these weights.
Also, on a compact log profile with $g(0)\ne0$, both displaced samples
in (B.4.2.15) vanish for large $x$, while the displayed subtraction
$N_v\phi(1)/x$ is not integrable there. These are checks of the literal
extracted formulas, not visual readings of the equations.

[`Props.ArchimedeanGammaLogDerivative`](../../Proofs/Props/ArchimedeanGammaLogDerivative.lean)
starts from the factor $B^{-z}\Gamma(z)$ with $B>0$ and
$z=w/d$, $w=s+b+i\tau$, $d>0$, $b\ge0$, and $\tau\in\mathbb R$.
`archimedeanGammaFactor_real` and `archimedeanGammaFactor_complex`
match (3.2.1.4) and (5): Use $B=\pi$, $d=2$, $b\in\{0,1\}$ for
real parity, and $(B,d,b)=(2\pi,1,|n|/2)$ for the complex angular weight. The
complex factor is half of Mathlib's `Gammaℂ`. Here $\tau$ is the
radial exponent of the **normalized** local norm: If a complex
character is written using ordinary radius $r$ with power $r^{i\eta}$,
then $\tau=\eta/2$ under the squared-norm convention of §A.1, p. 539.
These identities do not classify actual local characters.

`analyticOnNhd_archimedeanGammaFactor` proves holomorphy on $\Re s>0$.
`logDeriv_archimedeanGammaFactor_eq_integral` proves nonvanishing
there and replaces the scalar digamma expression of (B.4.2.12) by
$$
-\frac{\log B+\gamma}{d}+\int_0^\infty K_{d,w}(x)\,dx,\qquad
K_{d,w}(x)=\frac{e^{-dx}-e^{-wx}}{1-e^{-dx}}.
$$
The integral is absolute. The actual prefactor contributes
$-\log B/d$ and the Gamma derivative contributes $\psi(z)/d$.
`digamma_sub_one_eq_exponential_integral` substitutes $t=e^{-dx}$
in the checked Gauss difference, preserving the subtraction at zero
and producing a decaying subtraction at infinity. The existing
`logDeriv_GammaReal_eq_integral` is now the unshifted real
specialization, with its statement unchanged. The Lean factor is
written with `Real.log B`, so its scalar derivative identity also
holds for the totalized expression at nonpositive $B$; identification
with the positive-base power only uses $B>0$.

**Independent statement review:** `arch-gamma-review` (`wTTTKPB`, Yah
parent session `01a200e8-a984-7963-8cd0-43194e3cfad9`, exact base
`f56270f6bd581e9d84c69bf27f36646d55509ec5`) checked the signs, scale,
local weights, and Mathlib's factor of two against the digest-verified
PDF and pinned definitions. It confirmed that the literal extracted
subtraction in (B.4.2.15) fails the compact-log tail test. This is
extracted-text review, not rendered-page verification.

## Checked: Contour reflection and the primitive Dirichlet conductor

Proposition 3.2.1.3(3), (3.2.1.6), p. 123 supplies the orientation
$G(1-s)=\epsilon(s)F(s)$ and a nowhere-zero entire factor. That
analytic property does not imply a constant logarithmic derivative.
The provisional text of (B.4.2.3), p. 614 has a plus before the
reflected logarithmic derivative and invokes a conductor power with
an open reference in footnote 13. The chain rule for $1-s$ requires a
minus. Taking $\epsilon(s)=C e^{\kappa(s-1/2)}$, $C\ne0$, gives
$(F'/F)(s)=-(G'/G)(1-s)-\kappa$ at ordinary nonzero points.

[`Props.HeckeContourReflection`](../../Proofs/Props/HeckeContourReflection.lean)
proves the local germ version (`completed_logDeriv_reflection`).
`completed_reflect_left_integral` takes absolute integrability of the
**reflected right-line** leg as input. It derives absolute integrability
of the left upward leg and the normalized equality
$I_{\rm left}=-I_{\rm reflected}-\kappa g(0)$ using $t\mapsto-t$ and
compact log Mellin inversion at zero. Subtraction of the left leg in
(B.4.2.2), p. 614 then gives the two plus signs for the reflected leg
and conductor contact in (B.4.2.4), p. 615. No residue theorem is used.

[`Theorems.DirichletContourReflection`](../../Proofs/Theorems/DirichletContourReflection.lean)
instantiates this with Mathlib's primitive Dirichlet completion (Gamma
factor included, conductor power not included) at modulus $N>1$. Its
functional equation for $\chi^{-1}$ gives $\kappa=\log N$ with the
orientation above. The integral theorem proves left-line nonvanishing
for $a>1$ from the primitive functional equation and Mathlib right
half-plane nonvanishing. The remaining input is absolute integrability
of $\Phi(1-s)(L'/L)(s,\chi^{-1})$ on $s=a+it$. This is not a proof
of contour exhaustion, or an identification of the Dirichlet and idelic
completions. The nonzero contact is detectable only on tests with
$g(0)\ne0$.

**Independent review:** `conductor-review` (`aDCFClN`, Yah session
`01a200ef-a91c-742a-abfd-1e1cdf9ae57b`) checked the source orientation,
conductor dependence, and endpoint scope. All manuscript comparisons
here are based on pinned chapter Markdown and numbered PDF layout
extraction, not independent inspection of rendered pages.

### Ramified local conductor power: The modulus-three test

**Scope of the source verdict:** The finite-place calculation is independent
of the printed real factor. Applying it to the printed $S$-local identity
also uses the product norm after (3.1.2.1), p. 120, the odd Gamma factor
(3.2.1.4), p. 123, and the constant real epsilon rule accompanying
(3.3.1.28), p. 135. These three readings remain provisional (pinned Markdown
and layout extraction). The rendered findings below are inherited from the
prior independent reviewers, not a new visual audit of this recovery.

**Rendered source.** In the [pinned edition](../sources/masullo/README.md),
(3.3.1.30), p. 136, prints only $N(\mathfrak d_v)^{s-1/2}$ outside the
Gauss sum. Although $\rho_0$ is written with a norm twist as an argument,
the displayed formula uses $N(\mathfrak f)^{-1/2}$, the fixed values
$\chi_v(u)$, and the additive phases at $u/\pi_v^{v(\mathfrak d_v\mathfrak f)}$.
It is independent of $s$. In (3.3.2.24), p. 141, the ramified factor
instead uses $N(\mathfrak d_v\mathfrak f_{\chi})^{s-1/2}\rho_0(\chi)$.
The rendered (3.3.1.2), p. 129, is forward over reflected, and (3.3.1.32),
p. 136, multiplies $\epsilon_S(c)$ by $L_S(c)/L_S(\widehat c)$, not
its reciprocal. The reading was checked independently in grayscale
Poppler pixel crops from the digest-verified PDF, with layout extraction
used only to locate the formulas. Source reviewer `slUqigK` and
independent reviewer `iIPBBIA` checked these equations in the prior modulus-three review.

**In-scope control.** On $\mathbb Q_3^\times$ take the nontrivial
character $\chi$ of $(\mathbb Z/3\mathbb Z)^\times$, extended by
$\chi(3)=1$. It has conductor $(3)$ (nontrivial on units, trivial on
$1+3\mathbb Z_3$), and $\mathbb Q_3/\mathbb Q_3$ has trivial different.
The product with the real sign is trivial on $\{\pm 3^n:n\in\mathbb Z\}$:
The two signs cancel at $-1$, and both values at $3$ are one. The
product norm is also trivial on this diagonal. Hence the norm twists
are characters of the printed $J_{\mathbb Q,\{\infty,3\}}$ (quotient
in §2.3, p. 99), and $s=1/4,3/4$ lie in the open strip. Reviewer
`iIPBBIA` inspected the quotient on the rendered page. The explicit
product norm immediately after (3.1.2.1), p. 120, remains a provisional
Markdown and layout reading.

**Two-coset computation.** The test is
$f=\chi^{-1}\mathbf1_{\mathbb Z_3^\times}
=\mathbf1_{1+3\mathbb Z_3}-\mathbf1_{2+3\mathbb Z_3}$.
The checked `padicTranslatedBall_fourier` in
[`Theorems.PadicIntegralBallFourier`](../../Proofs/Theorems/PadicIntegralBallFourier.lean)
with additive unit-ball mass one gives
$$
\widehat f(y)=\tfrac13(\overline{\psi(y)}-\overline{\psi(2y)})
                  \mathbf1_{3^{-1}\mathbb Z_3}(y).
$$
Both phases are one for integral $y$. For $y=u/3$ with $u$ a unit,
the two residues give $\widehat f(u/3)=A\chi(u)$, where
$A=(\zeta_3^{-1}-\zeta_3^{-2})/3=-i/\sqrt{3}$ for the conjugate of the
positive cyclic-residue character used in this Lean transform.
The rendered (A.3.1.5), p. 557, prints the unbarred phase in its
right-hand formula; using that phase instead conjugates $A$ and has no
effect on the comparison. The computation uses the checked support
formula, not the intermediate translated frequency expression on p. 557.
[`Theorems.PadicRamifiedThreeFourier`](../../Proofs/Theorems/PadicRamifiedThreeFourier.lean)
checks the actual additive Haar integral for all $y$ and that it is
nonzero exactly when $\lVert 3y\rVert_3=1$, including at $y=1/3$.
The shell is $3^{-1}\mathbb Z_3^\times$, not the whole dilated integral
ball. Independent reviewer `iIPBBIA` (Yah session
`01a20139-f336-7f57-8132-28ebf173ba5b`) checked the exact implementation
and statement against the test and kernel-replayed writer output
`674ae752f7fbcc647c9e93bd55b7dd6f582a838a`. The recovery preserves the
reviewed file byte for byte. The four public endpoints are listed in the
audit command below. The evaluation of $A$ is not a Lean endpoint.

Write $m>0$ for the mass of $\mathbb Z_3^\times$ under any fixed
multiplicative Haar. In (3.3.1.7), p. 130, the forward integral is $m$.
On the reflected shell, multiplication by $1/3$ preserves the mass,
$|u/3|_3=3$, and the character cancels since $\chi(3)=1$. The reflected
integral is $m A3^{1-s}$. Both integrals converge absolutely for every
complex $s$ by the compact supports away from zero. The forward-over-
reflected quotient is therefore $R_3(s)=A^{-1}3^{s-1}$, or
$i3^{s-1/2}$ in the checked convention. These Mellin evaluations are
ordinary mathematics using the checked additive formula.

**Discriminant.** Both $3$-adic Euler factors are one, by (3.2.1.2),
p. 123, and the ramified case stated in the proof after (3.3.1.33),
p. 137. The first omits the ramified place, and the second explicitly
sets the local factor to one. Both conventions were read on the
rendered pages. In the tensor with the real test
$h(t)=t e^{-\pi t^2}$, the two real zeta integrals are the odd Gamma
factors at $s$ and $1-s$, the latter times a constant nonzero Fourier
phase. For the negative Fourier kernel, $\widehat h=-ih$ and the real
forward/reflected quotient after Gamma normalization is $+i$. The
comparison does not require equality with the printed constant phase.
Dividing out the odd Gamma ratio from (3.2.1.4), p. 123, therefore leaves
only an $s$-independent real phase. Only the constant-in-$s$
feature of the printed real rule in the discussion of (3.3.1.28),
p. 135, is needed; that rule is a provisional text and layout reading.
In this normalized $S$-quotient, the ratio of the value at $3/4$ to
that at $1/4$ is $\sqrt{3}$, not the $1$ required by (3.3.1.30) and
(3.3.1.32), and not the $1/\sqrt{3}$ from the reversed conductor exponent.
It agrees with (3.3.2.24) in its conductor power, independently of
constant phases. Subject to the source-scope readings above, this is a
counterexample to compatibility of the printed formulas within their
common scope, not to the local functional equation with the repaired
factor. For this place and character, inserting $N(\mathfrak f)^{s-1/2}$
in (3.3.1.30) repairs the power; the comparison does not adjudicate the
manuscript's constant phase conventions.

**Appendix B interface.** The local contribution has logarithmic
derivative $+\log 3$. This is a forward-over-reflected **local zeta**
quotient; the exponential in (3.2.1.6), p. 123, is the
reflected-over-forward **completed $L$** quotient. If the global Poisson
identity and Euler normalization give that exponential the same
conductor power, its derivative contributes $-\log 3$ in the left-line
logarithmic derivative and $+\log 3$ to the contact in (B.4.2.4), p. 615,
after subtracting the left leg. This does not supply the exponential
functional equation input for `completed_logDeriv_reflection`.
The reflected parameter $\widehat c=|\cdot|c^{-1}$ (3.1.1.4), p. 119,
and the orientation of (3.2.1.6) were read on rendered pages. Independent
reviewer `iIPBBIA` also checked the real/finite tensor integral and local
zeta measure in (3.3.1.7), p. 130, and the $L_S$ product definition
(3.3.1.25), pp. 134–135, on the rendered pages. The global Euler
assembly and its identification with the global zeta integral are not
checked here; the source product description after (3.2.1.6), p. 123,
remains provisional for that purpose. The prior rendered review of
(B.4.2.3), p. 614, confirmed the sign issue explained above; the local
test does not justify that displayed differentiation.

### Primitive prime-power conductor shells over $\mathbb Q_p$

The [modulus-three calculation](#ramified-local-conductor-power-the-modulus-three-test)
was a two-coset control. The new [Lean proof](../../Proofs/Theorems/PadicConductorFourier.lean)
works for every prime $p$, every $n>0$, and every primitive
`DirichletCharacter ℂ (p ^ n)` (conductor equal to level). Write
$d=p^n$, let $\chi$ on $\mathbb Z_p^\times$ be reduction modulo $p^n$
followed by that character, and write $f=\chi^{-1}\mathbf1_{\mathbb Z_p^\times}$
with zero elsewhere. This is a locally constant, compactly supported
Schwartz–Bruhat test. `padicConductorTest_unit` and
`padicConductorTest_eq_zero_of_norm_ne_one` identify this test pointwise.
Use the complex conjugate of the standard additive character as kernel,
and additive Haar mass one on $\mathbb Z_p$.

- `padicConductorFourier_ne_zero_iff` proves $\widehat f(y)\ne0$ if and
  only if $|p^n y|_p=1$, for every $y\in\mathbb Q_p$.
- `padicConductorFourier_unit` proves
  $\widehat f(u/p^n)=\chi(u)\widehat f(1/p^n)$ for all local integral
  units $u$. This covariance endpoint does not require $n>0$.
- `padicConductorFourier_of_integral` reduces the integral, when
  $a=p^n y\in\mathbb Z_p$, to $p^{-n}$ times the counting-measure
  negative-sign DFT of the inverse residue character at $a\bmod p^n$.
  This reduction does not require primitivity or $n>0$. The translated
  ball formula gives zero outside $p^{-n}\mathbb Z_p$. Inside it,
  the primitive Gauss-sum identity kills nonunit residues and gives
  unit covariance. If the DFT at $1$ vanished, the same identity would
  make the entire DFT zero, contrary to finite inversion and $f(1)=1$.
- The [modulus-three control](../../Proofs/Theorems/PadicRamifiedThreeFourier.lean)
  identifies the pointwise test with the original signed cosets using
  the primitive quadratic character; the original computation is
  retained as an independent route.

**Local zeta quotient, not formalized.** Extend the unit character to
$\mathbb Q_p^\times$ by $\chi(p)=1$. It has conductor $p^n\mathbb Z_p$:
Reduction on units is onto with kernel $1+p^n\mathbb Z_p$, and a smaller
conductor would factor the residue character through a lower level
(through the trivial unit character for $n=1$). This gives the conductor
coset space $\mathbb Z_p^\times/(1+p^n\mathbb Z_p)$ appearing in the
Gauss sum definition below (3.3.1.30), p. 136. Finite-order unit values
and $\chi(p)=1$ give a unitary character.
The different of $\mathbb Q_p/\mathbb Q_p$ is the unit ideal. Let
$c_s=\chi|\cdot|_p^s$, $A=\widehat f(p^{-n})\ne0$, and let $m>0$ be
multiplicative Haar mass of $\mathbb Z_p^\times$. By the local zeta
integral (3.3.1.7), p. 130, and $\widehat c_s=|\cdot|_p c_s^{-1}$ in
(3.1.1.4), p. 119, the forward integral is $m$. On the reflected shell,
write $y=p^{-n}u$; its Haar mass is also $m$, $|y|_p=p^n$, and the
character from the Fourier transform cancels the inverse twist. The
reflected integral is therefore $mA p^{n(1-s)}$. Both integrals are
absolutely convergent for every complex $s$ on these compact supports
away from zero. In forward-over-reflected orientation,
$$
R_p(s)=A^{-1}p^{n(s-1)},\qquad R_p(3/4)/R_p(1/4)=p^{n/2}.
$$
Changing the sign of the Fourier phase replaces $A$ by $\chi(-1)A$,
and a fixed nonzero additive Haar rescaling multiplies $A$ by that
scalar, so neither can change this ratio. This calculation does not evaluate the
constant phase or identify it with either printed $\rho_0$.

**Printed route.** The factorization (3.3.1.2)–(3), p. 129, uses the
same orientation. The local identity in the proof below (3.3.1.32),
p. 136, is $\rho_v(c_v)=\epsilon_v(c_v)L_v(c_v)/L_v(\widehat c_v)$.
Both Euler factors are $1$ in the ramified case, as the proof states
on p. 137. The $s$-dependent notation for the Gauss sum in (3.3.1.30),
p. 136, does not change its defining summands: It uses the fixed unit
character and fixed additive phases at conductor denominators. With
trivial different, this route prints a constant factor (ratio $1$ if
nonzero), while (3.3.2.24), p. 141, prints the ramified power
$p^{n(s-1/2)}$ and predicts $p^{n/2}$. The defining-integral calculation
agrees with p. 141 **in the exponent**. It contradicts the constant
finite factor on p. 136, not an unspecified product of global factors.
The displayed (3.3.1.31) itself writes $L_S(\widehat f,\widehat c)$;
(3.3.1.33), p. 137, writes $Z_S(\widehat f,\widehat c)$. The verdict
uses the individual factor in the proof and does not assume those
printed numerators are literally the same.

**Independent review:** Yah session `01a201d1-b153-77f9-960b-0aa6dfd16c95`,
agent `WNdLLkJ`, inspected the rendered pages of the
[pinned edition](../sources/masullo/README.md), including the local dual,
measure, and kernel cross-references (3.1.1.4), p. 119, (A.3.1.2), p. 556,
Example A.3.1.6, p. 557, (A.3.2.2), p. 560, and (D.1.1.4), p. 746.
The reviewer separately derived the defining quotient from the shell,
read the two printed factor routes and the ramified Euler convention,
and matched the fresh-import Lean signatures against independently
elaborated statements. The quotient comparison does not use the
shifted-frequency expression in (A.3.1.5) or the real factor and product
norm needed for the broader, partly provisional $S$-local comparison
in the preceding modulus-three note.

### Central conductor Fourier modulus over $\mathbb Q_p$

The [Lean endpoints](../../Proofs/Theorems/PadicConductorFourier.lean)
add the size missing from the conductor-shell theorem. For every prime
$p$, every $n\ge 0$, and every primitive
`DirichletCharacter ℂ (p ^ n)`, `Masullo.padicConductorFourier_norm`
proves
$$
\left|\operatorname{padicConductorFourier}(p,\chi,p^{-n})\right|
=\frac{1}{\sqrt{p^n}}.
$$
This uses the inverse character, the negative-sign additive kernel, and
additive Haar mass one on $\mathbb Z_p$. At $n=0$ it gives modulus
one at frequency one; it does not assert the positive-level support
characterization at level one.

`Masullo.primitiveDirichletDFT_norm_one` is reusable at every positive
modulus $N$ (`[NeZero N]`), not just prime powers. Put
$B=\mathcal F(\chi^{-1})(1)$ for the unnormalized negative-sign DFT.
Primitivity gives $\mathcal F(\chi^{-1})=B\chi$. Conjugating its defining
sum at $1$ gives $\mathcal F(\chi)(-1)=\overline B$. Hence double DFT at
$-1$ gives $B\overline B=N\chi^{-1}(1)=N$. The integral reduction at
$a=1$ contributes the single factor $(p^n)^{-1}$. This proof does not
use a global functional equation.

**Manuscript scope.** For $n>0$, the unit-character conductor and
normalization comparison in the [shell note above](#primitive-prime-power-conductor-shells-over-mathbb-q_p)
apply, with trivial different and conductor norm $p^n$. The rendered
reading of Masullo's (3.3.2.24), PDF p. 141, the normalized Gauss sum
below (3.3.1.30), p. 136, and the relevant dual, Haar, and kernel
conventions are inherited from the accepted notes above, including the
review by `WNdLLkJ` (Yah `01a201d1-b153-77f9-960b-0aa6dfd16c95`).
The worker read the prose following (3.3.2.24) in grayscale crops:
It describes a root number of absolute value one independent of $s$.
The current reviewer corroborated this by extraction, not an independent
visual reading. The Lean result is independent of that prose reading.
In the earlier **informal** forward-over-reflected quotient,
$R_p(1/2)=p^{-n/2}/A$ with $A=\widehat f(p^{-n})$, so the new modulus
makes its absolute value one. This does not identify the phase with
Masullo's $\rho_0$, formalize either zeta integral, or treat finite
extensions.

**Statement review:** `ONimXXT` (transcript Yah
`01a2029a-53c8-7475-8440-d5a8540e1b74`) checked both statements, the
sign and residue-ball mass in the integral reduction, and why no
hypothesis $n>0$ is needed for the modulus alone.

### Exact conductor of the pulled-back unit character

Fix a prime $p$, put $O=\mathbb Z_p$, and set
$U_m=\{u\in O^\times : u-1\in p^m O\}$. The
[Lean endpoints](../../Proofs/Theorems/PadicConductorFourier.lean) use
exactly the pullback $u\mapsto\chi(u\bmod p^n)$ of
`padicConductorFourier_unit`. They now certify its local conductor:

- `Masullo.padicUnitReduction_eq_one_iff` identifies $U_m$ with the
  kernel of reduction $O^\times\to (\mathbb Z/p^m\mathbb Z)^\times$
  for every $m$. In particular, $U_0=O^\times$.
- `Masullo.padicConductorUnit_trivial_iff_conductor_dvd` proves that
  the pullback is trivial on $U_m$ exactly when the finite conductor
  of $\chi$ divides $p^m$. This works for all $m,n\ge0$ and every
  Dirichlet character modulo $p^n$ valued in a
  `CommMonoidWithZero`, with no primitivity assumption.
- `Masullo.padicConductorUnit_trivial_iff` specializes the right side
  to $n\le m$ when $\chi$ is primitive. For $n>0$ the conductor
  ideal is therefore $p^n O$, and the restriction to $U_0$ is
  nontrivial. For $n=1$ this rules out the only smaller level. For
  $n=0$ the theorem gives triviality already at level zero.

The ring kernel comes from `PadicInt.ker_toZModPow`. At positive
levels any finite unit has an integral lift by ring surjectivity, and
being a unit is detected modulo $p$; at level zero the target unit
group is trivial. For $m\le n$, compatibility of reductions and that
lifting property turn triviality on $U_m$ into triviality on the
finite kernel, equivalent to descent modulo $p^m$. For $n\le m$,
compatibility gives triviality directly, and the finite conductor
already divides $p^n$. A fresh import checks the $n=1$, $m=0$ witness,
the $n=0$ case, and the existential form of nontriviality for $m<n$.

**Manuscript scope.** The accepted [shell note](#primitive-prime-power-conductor-shells-over-mathbb-q_p)
records the independent rendered readings by `WNdLLkJ` (Yah
`01a201d1-b153-77f9-960b-0aa6dfd16c95`) of the Gauss sum below
(3.3.1.30), PDF p. 136, and the ramified factor (3.3.2.24), p. 141.
For the same residue character over $\mathbb Q_p$, the calculation
identifies the conductor subgroup for the printed coset space and the
conductor ideal in the ramified factor. The ramification criterion is
nontriviality on $O^\times$, using the unit-restriction convention after
(3.1.2.6), §3.1.2.3, p. 121. This is a result about the unit restriction;
it does not construct the continuous unitary character on
$\mathbb Q_p^\times$ with value one on $p$, prove the zeta quotient, or
identify the phase.

**Independent review:** `NkpINOg` (transcript Yah
`01a202a5-f688-75bf-848e-9695477371bb`) checked the three statements,
the use of the inherited readings, and the rendered unit-restriction
criterion on p. 121. The additive Fourier normalization is unchanged.

**Next bounded check:** Construct the multiplicative unit-part map
$\mathbb Q_p^\times\to O^\times$, $x\mapsto p^{-v_p(x)}x$, and check
that it fixes integral units and sends $p$ to one. This would supply
the algebraic input to extend the unit character with the printed
uniformizer normalization. Continuity and unitarity of the extension,
the local zeta identities, phase comparison, and finite-extension and
global steps are separate.

### Separate global Fourier sign

The [rendered rational theta check](theta-inversion-q.md#rendered-sign-check-a-translated-box-breaks-the-printed-theta-identity)
tests Theorem 2.2.3.2, p. 82 using (2.2.4.32), p. 92, and Examples
A.3.1.5–8, pp. 557–558. The printed kernel evaluates the reflected
finite coset, so the unmodified global Poisson step does not give the
claimed theta identity on all rational boxes. The repaired kernel
conjugates only the finite character factors. The [global Mellin sign
check](global-mellin-sign-q.md) verifies the relevant Chapter 3 passages
and tests (3.2.2.2), p. 124, on the global odd conductor-three character.
The continued left side and absolutely convergent printed right side have
opposite nonzero values. This is distinct from the local conductor power
above: A constant sign cancels on logarithmic differentiation, and the
test does not supply the exponential factor or the completed-product
identification in (B.4.2.4), p. 615.

### Separate relative 1-line integrability failure

The [calibrated rational Gaussian test](idele-relative-one-line-q.md)
admits the printed zeta integral (3.4.2.1), p. 145, as a complex
Lebesgue integral only for $\Re s>1$. The rendered domain includes
$1+2i$, where the integral of the modulus diverges. The cited
norm-ordered Euler product, (B.7.2.24), p. 653, does not supply this
integrability. This is independent of the sign and ramified power
issues and does not challenge the above-one product comparison or
analytic continuation. The boundary claim cannot be used as an
upstairs Lebesgue unfolding in the global identification.

## Checked: Evaluate the shifted Archimedean pair

[`Props.ArchimedeanGammaRightLine`](../../Proofs/Props/ArchimedeanGammaRightLine.lean)
proves the separate direct and reflected evaluations of (B.4.2.13)–(14),
p. 616, and the following corrected sum on smooth compact log profiles.
For $s=a+it$ with $a>0$, $\Phi(s)=\int g(x)e^{sx}\,dx$, and the
parameterized factors $F_{\tau}$ and $F_{-\tau}$ with the same $b$, it
integrates $\Phi(s)(F'_{\tau}/F_{\tau})(s)$ and
$\Phi(1-s)(F'_{-\tau}/F_{-\tau})(s)$ with the same upward normalization
$dt/(2\pi)$. Both line integrals and both subtracted position integrals
are absolute. The sum equals
$$
-\frac{2(\log B+\gamma)}{d}g(0)+
\int_0^\infty
\frac{2g(0)e^{-dx}-e^{-(b+i\tau)x}g(x)-e^{-(1+b-i\tau)x}g(-x)}
     {1-e^{-dx}}\,dx.
$$
Here $a>1$ is only needed when joining to the finite Euler product.
For the half-shifted convention, $g(x)=e^{-x/2}\phi(e^x)$ gives
$e^{-(1/2+b+i\tau)x}\phi(e^x)$ and
$e^{-(1/2+b-i\tau)x}\phi(e^{-x})$ as the displaced samples.

Masullo supplies the pairing and Mellin inversion idea, moving
through (B.4.2.16). The proof instead stays on the original line. The
checked scalar identity supplies the prefactor derivative and the
integrable Gauss difference, replacing the nondecaying subtraction
in the literal (B.4.2.15). Before Fubini,
`integrable_archimedeanGamma_rightLine_product` handles any measurable
weight with integrable $\|W(t)\|(1+|t|)$. It separates damping and
phase at $m=\min(d,a+b)>0$ and uses $1-e^{-dx}\ge dx/(1+dx)$, so the
kernel is bounded by $(1/d+x)e^{-mx}(|d-a-b|+|t+\tau|)$.
`integrable_compactLogMellin_vertical_first_moment` supplies that moment
on every vertical line from order-three Mellin decay. The direct proof
uses the accepted fixed-position inversion at $x$ and at $0$. The
reflected proof uses `compactLogMellin_reflect` to apply the same proof
to $e^{-x}g(-x)$ with the opposite radial parameter. There is no
separation of the singular terms in the joint position integral.

**Independent statement review:** `gamma-pair-review` (`GZKQWWb`, Yah
parent session `01a200f6-ceba-7622-963f-8bc1fe2cf743`, exact base
`41a17038c27c9ec7962e61a3cdf2b8048350dcf1`) checked the proposed
statements, damping bound, contact, reflected sample, and upward
normalization against the accepted Lean interfaces and digest-pinned
pp. 123 and 615–616. The review distinguished the arbitrary-weight
majorant from evaluation on Mellin weights. These manuscript readings
used chapter Markdown and PDF layout extraction, not rendered pages.

## Continuous one-parameter character classification

[The Lean foundation](../../Proofs/Lemmas/OneParameterCharacter.lean)
proves `Masullo.existsUnique_unitary_oneParameterCharacter`: A continuous
$h:\mathbb R\to\mathbb C$ with $h(0)=1$, $h(t+u)=h(t)h(u)$, and
$|h|=1$ has the form $h(t)=e^{i\tau t}$ for a unique real $\tau$.
Masullo gives the Archimedean factor formulas in (3.2.1.3)–(5),
p. 123, but does not derive this common classification there. This
project proof requires no choice of argument: A sufficiently short
positive interval has $J=\int_0^r h(u)\,du\ne 0$. For
$F(t)=\int_0^t h(u)\,du$, the identity
$J h(t)=F(t+r)-F(t)$ and the fundamental theorem of calculus give
$h'=kh$ for $k=(h(r)-1)/J$. An integrating factor gives $h(t)=e^{kt}$;
unit modulus at $t=1$ gives $\Re k=0$, and the derivative at zero
fixes $\tau$. The reading of the pinned text is provisional: The
Markdown and PDF layout extraction were read, not the rendered page.

The statement and proof strategy were independently reviewed by Yah
`character-review` (`rlvOLyV`, work session
`01a2010e-125b-7b4a-907b-8447e5b76a69`). The first work run checked the
proof in scratch but could not create a campaign workspace. Recovery
from `616c5a9723c8342162bd3f3647cd07a4fa84ad06` preserved the reviewed
proof and statement; the Lean sources and pins at that base were
unchanged from the review. See the
[recovery record](../experiments/character-proof-recovery/README.md).
The full local build, separate replay, and endpoint checks passed on
accepted `eba0e8a9fe1ad6a88f22b4f6ef6deeee8fcf9783`. Its built signature
matched the reviewed statement, and the only reported axioms were
`propext`, `Classical.choice`, and `Quot.sound`.

## Continuous Archimedean insertion and restriction

In §3.1.2.2, p. 121, Masullo calls $j_v:F_v^\times\to C_F$ a
continuous insertion homomorphism and uses $c_v=c\circ j_v$ in
(3.1.2.4). This reading used Markdown and the numbered PDF layout
extraction, not the rendered page. The two
[Lean endpoints](../../Proofs/Theorems/ArchimedeanHeckeRestriction.lean),
`Masullo.continuous_ideleClassGroup_ofCompletion` and
`Masullo.continuous_archimedeanHeckeRestriction`, supply continuity
for the existing Archimedean insertion and its composition with a
Mathlib Hecke character. In the product of completions, each
coordinate is the identity at $v$ or constant one; the finite adeles
coordinate is constant one. `Units.continuous_map` and then the
principal-subgroup quotient give continuity with the actual Mathlib
topologies. Neither endpoint supplies injectivity, a local analytic
isomorphism on character spaces, or any finite-place continuity claim.

Yah reviewer `arch-insertion-statement` (`xApQEDc`, session
`01a20114-4aae-7459-b5c8-bb52f9adc5cf`) independently approved and
elaborated the two statements. The local audit passed at
`1f06a6261f64ef06eedb7ea7ac01ad98c9fda691`, but adoption was stale.
The advancing base changed only `cmd/blitz` and its handoff. After
verifying identical Lean build inputs and reusing the trusted cache,
the full warning-as-error build (8,864 jobs), separate module
replay, and endpoint checks passed at accepted
`62a04cfe1c9a36ae86b6bfbf82a05f64508aee71`. The built statements matched
the independent review and used only `propext`, `Classical.choice`,
and `Quot.sound`.

## Real Archimedean restriction: Parity and radial frequency

[The Lean theorem](../../Proofs/Theorems/RealArchimedeanHeckeRestriction.lean)
`Masullo.exists_archimedeanHeckeRestriction_real` gives, for every unitary
Mathlib Hecke character and every real place $v$, one parity $b\in\{0,1\}$
and one frequency $\tau\in\mathbb R$ valid on all of $F_v^\times$:

$$
\chi(j_v(x))=\operatorname{sgn}(y)^b\exp(i\tau\log|y|),
\qquad y=\operatorname{extensionEmbeddingOfIsReal}(hv)(x).
$$

Masullo supplies the split of the real units in (3.1.2.3), the
restriction $\chi_v=\chi\circ j_v$ in (3.1.2.4), p. 121, and the two
parity cases in (3.2.1.4), p. 123. The project fills in the actual
unitary restriction calculation: Transport along the isometric real
completion equivalence, pull back to $t\mapsto e^t$ and apply the checked
one-parameter classification, then use $\chi_v(-1)^2=1$ and the split
$x=\operatorname{sgn}(y)|y|$ in real coordinates. Multiplying by the
norm power $|y|^s$ gives the real shift $s+i\tau$ before the parity shift
in the scalar Gamma argument. The theorem establishes the local character
identity, not an evaluation of its zeta integral or the character-space
analytic isomorphism. These source readings used Markdown and numbered PDF
layout, not rendered pages. The theorem elaborated with warnings as errors
and replayed in a separate `leanchecker` process in the writer workspace.

## Complex Archimedean restriction: Angular weight and radial frequency

`Masullo.exists_archimedeanHeckeRestriction_complex` applies to an actual
unitary Mathlib Hecke character and any complex place $v$. It gives one
$n\in\mathbb Z$ and one $\tau\in\mathbb R$ for all completion units $x$:

$$
\chi(j_v(x))=(z/\lVert z\rVert)^n
              \exp(i\tau\log(\lVert z\rVert^2)),
\qquad z=\operatorname{extensionEmbedding}_v(x).
$$

Masullo supplies the split and restriction map on p. 121,
(3.1.2.3)–(4), the squared-norm convention in §A.1, p. 539,
and the use of the integer angular weight on p. 123, (3.2.1.5).
The project derives the parameters: Transport to $\mathbb C^\times$,
apply the checked one-parameter classification on the real cover of the
circle, descend using the period $2\pi$, apply the classification again
along $t\mapsto e^{t/2}$, and recombine the polar factors. Thus the shift
in the scalar Gamma argument is $s+|n|/2+i\tau$, not
$s+|n|/2+2i\tau$. The local integral that realizes this factor is not
part of the theorem. Source readings used Markdown and numbered layout,
not rendered pages. The endpoint was independently reviewed by `CaWzqPh`
in Yah session `01a2012a-2b95-7bce-8dcc-d7ca7b125aa6`.

## Checked complex Gaussian recognition with the opposite angular weight

The [earlier rendered angular check](complex-gaussian-angular.md)
confirms that the bilinear integral of (3.3.1.7), p. 130, pairs the
printed angular weight $m$ with the same input weight in
(3.4.3.5)–(6), p. 152, and (3.4.3.12)–(13), p. 153. At $m=1$,
$s=2$, and radial frequency zero the absolutely convergent integral
vanishes by rotation, while the Gamma factor is positive. This is a
source check in ordinary mathematics, not a Lean counterexample.

**Checked local repair:** `Masullo.complexGaussianZetaDensity_integral`
in [`ComplexGaussianMellin.lean`](../../Proofs/Theorems/ComplexGaussianMellin.lean)
uses the opposite angular weight, retaining the printed $1/(2\pi)$.
With $r=\|z\|$ and $u=z/r$, its test off zero is

$$
E_n(z)=\frac{1}{2\pi}r^{|n|}u^{-n}e^{-2\pi r^2},
$$

implemented by the polynomial $\bar z^n$ for $n\ge 0$ or $z^{-n}$
for $n<0$ times the same Gaussian. For every $n\in\mathbb Z$,
$\tau\in\mathbb R$, and $\operatorname{Re}s>0$, Lean proves absolute
integrability and the exact value of the pairing

$$
\int_{\mathbb C^\times}E_n(z)u^n(r^2)^{s+i\tau}\,d^\times z
=(2\pi)^{-a}\Gamma(a),\qquad a=s+|n|/2+i\tau.
$$

The formal integral is over ordinary complex `volume`, with density
$2r^{-2}$ off zero and the integrand set to zero by totalized division
at zero. The density follows from Definitions A.3.1.2(2), p. 556, and
A.3.2.2(1), p. 560, with the squared norm in §A.1, p. 539. The Lean proof
cancels the angular factors pointwise, then uses polar change of
variables, the substitution $t=r^2$, and Euler's Gamma integral. The
angular integral cancels $1/(2\pi)$, and $2\,dr/r=dt/t$. The right-hand
side in Lean is `archimedeanGammaFactor (2 * Real.pi) 1 (|n|/2) τ s`,
matching (3.2.1.5), p. 123, with the radial frequency included.
Yah reviewer `TuyCYSe` in session `01a20131-bd05-7fe0-b8e3-88674066ebad`
independently reviewed the endpoint. This is the scalar local integral,
not a construction of multiplicative Haar on the actual completion units,
a proof that the product of local Gaussians gives the global test, or an
identity for its Fourier transform or eigendistribution.

## Checked real Gaussian pairing for both parities

Masullo gives the two tests $x^b e^{-\pi x^2}$, $b=0,1$, in
(3.4.3.3)–(4), p. 152. The bilinear pairing (3.3.1.7), p. 130, and
Definitions A.3.1.2(1) and A.3.2.2(1), pp. 556 and 560, specify
multiplication by the character and the density $dx/|x|$ off zero.
With the real-place classification above, the norm exponent is
$s+i\tau$, and (3.2.1.4), p. 123, supplies the target Gamma factor.
This is a provisional source reading from Markdown and PDF layout.

The project supplies the scalar integral and its absolute convergence,
needed for the local normalization in (3.4.3.12)–(13), p. 153.
[`Masullo.realGaussianZetaDensity_integral`](../../Proofs/Theorems/RealGaussianMellin.lean)
proves for both parities, all $\tau\in\mathbb R$, and $\Re s>0$ that

$$
\int_{\mathbb R^\times}x^b e^{-\pi x^2}\operatorname{sgn}(x)^b
    |x|^{s+i\tau}\,\frac{dx}{|x|}
= \pi^{-a}\Gamma(a),\qquad a=(s+b+i\tau)/2.
$$

The Lean endpoint uses additive `volume` on $\mathbb R$ with the
multiplicative density included in the integrand and a zero value at
the origin. It cancels the two sign factors, reflects the even
integrand onto the positive half-line, and uses the shared square
substitution: The Jacobian cancels the factor of two from reflection.
The absolute convergence follows from positive real part of $a$ and
the scaled Gamma density. The right-hand side is
`archimedeanGammaFactor Real.pi 2 (b : ℝ) τ s`. Yah reviewer `PEgotXT`
independently checked the statement and source correspondence in
session `01a2013b-713a-7232-b3a6-8f5ebb0898b2`. As in the complex case,
this is not measure transport to the completion units, a global
Schwartz–Bruhat test construction, or a Fourier identity.

## Checked completed Hecke Euler product on the right half-plane

Lemma 3.2.1.1 and Definition 3.2.1.2, p. 123, give the completed product
(3.2.1.2)–(5); (3.2.1.7), p. 124, gives its finite part. In
[`CompletedHeckeEulerProduct.lean`](../../Proofs/Theorems/CompletedHeckeEulerProduct.lean),
`localHeckeGammaFactor_real` and `localHeckeGammaFactor_complex` match
its Gamma factors to the actual completion restrictions of (3.1.2.4),
p. 121, choosing the parameters once per place. The real shift is the
parity $b$; the complex shift is $|n|/2$, with no extra factor of two.
Both retain $i\tau$ in the exponent of the normalized local norm.
The manuscript comparison is provisional (Markdown and PDF layout).

For every unitary Mathlib Hecke character of a number field and
$\Re s>1$, `completedHeckeEulerProduct_logDeriv` proves that the
product is nonzero and complex differentiable, and proves

$$
\logDeriv L(s,\chi) = \sum_{v\mid\infty}\logDeriv L_v(s,\chi)
  -\sum_{(v,m),\,v\nmid\infty,\,m>0}\operatorname{finiteHeckeTerm}(\chi,s,v,m).
$$

To justify the split in (B.4.2.5)–(7), p. 615, Lean uses the finite
product rule at infinity. Convergence on the integration line alone
does not justify differentiation. The accepted finite-product repair,
`finiteHeckeCharacterEulerProduct_logDeriv`, differentiates using
locally uniform convergence on the open half-plane. The joint
finite-place series is stated as `HasSum` with value the Archimedean sum
minus the completed logarithmic derivative. The existing finite
majorant supplies absolute domination; the new theorem does not infer
a uniform all-height bound on the Archimedean terms. Specializing to
`heckeConjugate χ`
gives the second split with the same local conventions. Yah reviewer
`ywHnZGk` independently reviewed the statement and its source
correspondence (review output `3b4c5ea7eeb3517288df10c6d3b69e336f2ce9dc`).

## Finite local zeta pairings with the Haar unit mass retained

[`Theorems.FiniteHeckeLocalZeta`](../../Proofs/Theorems/FiniteHeckeLocalZeta.lean)
evaluates both finite tests on the actual completion units:

- `Masullo.finiteHeckeLocalZeta_unramified` proves absolute integrability
  for a unitary Hecke character and $\Re s>0$, and gives $M_v L_v(s,\chi)$
  for the integer-ring indicator.
- `Masullo.finiteHeckeLocalZeta_ramified` gives absolute integrability and
  $M_v L_v(s,\chi)=M_v$ for the inverse-character test, for all complex
  $s$. Since this integrand is the local unit indicator after cancellation,
  the theorem requires neither unitarity nor measure invariance.

Here $M_v$ is the real mass of the norm-one set. The theorems assume
finite unit mass; its positivity is needed only to divide by it. The
[local shell lemmas](../../Proofs/Lemmas/FiniteLocalNormShell.lean) identify
that set with the image of the units of the **local** integer ring,
partition the punctured integer ring by nonnegative uniformizer powers,
and obtain the same mass on each shell by left invariance. The existing
uniformizer norm and local coefficient lemmas identify the geometric
ratio, so no Euler factor or convergence premise is added to the statement.

The [rendered finite normalization check](finite-gaussian-tamagawa.md)
settles the unramified-character test at $\mathbb Q_2(i)$: Under the
printed Tamagawa measure the norm-square pairing is $2/3$, whereas the
Euler factor is $4/3$, as also seen by the unit-mass control over
$\mathbb Q_2$. Reading (3.4.3.13) with the mass-weighted factor from a
raw Gaussian pairing removes this local scalar mismatch, but does not
identify the factor with the Euler convention of (3.2.1.1)–(2). Keep
the mass when assembling the restricted product, or rescale the test
if the desired value is the Euler factor. The separate ramified-character
Lean pairing above likewise retains the mass; this source check tests
the unramified-character branch of Theorem 3.4.3.3(1). Neither Lean
endpoint constructs the Tamagawa measure, evaluates its discriminant
mass, or establishes a meromorphic eigendistribution identity.
Independent Yah statement review of the Lean endpoints: `mlDzIRC`
(output `f48eaa338965ce0b79cba685588b9017d0f07526`).

## Archimedean Gaussian pairings on the completion-unit Haar measures

`Theorems.ArchimedeanCompletionGaussian` proves
`Masullo.realCompletionGaussianPair` and `Masullo.complexCompletionGaussianPair`.
For a unitary Mathlib Hecke character, choose one real parity or complex
angular weight at the place, independently of $s$. At each $\Re s>0$
the bilinear pairing of the Gaussian with the actual local restriction
of the character times the normalized norm to the power $s$ is absolutely
integrable on `v.Completionˣ`. Its value is `localHeckeGammaFactor χ hχ v s`,
the factor already used by `Theorems.CompletedHeckeEulerProduct`.

The domain and bilinear pairing come from (3.3.1.7), p. 130. Definitions
A.3.1.2(1)–(2), p. 556, and A.3.2.2(1), p. 560, give $dx/|x|$ and
$2\,dx\,dy/\|z\|^2$ off zero. `Lemmas.ArchimedeanCompletionHaar`
transports both densities, retaining both real signs and the complex
factor of two. Its real Haar instance transports the checked real-unit
measure without changing its scale. In the complex case,
`complexTamagawaDensity_map_mul` checks that the real Jacobian of
multiplication by $a\ne0$ is $\|a\|^2$, canceled by the inverse squared
norm. The completion-unit measure is then left-invariant and gives a
compact neighborhood of the identity finite positive mass.

The real tests of (3.4.3.3)–(4), p. 152, need no change in this scalar
evaluation. As confirmed by the [prior angular audit](complex-gaussian-angular.md),
`complexGaussianZetaDensity_integral` uses the opposite angular weight
in the same coordinate as the character, unlike the printed complex test.
The transferred result is pointwise in $s$ on the open half-plane, not
uniform down to $\Re s=0$ and not a distribution-valued continuation.
Independent Yah statement and text review: `ZTZcZfz` (output
`28497fba430c60d17edeb89e1d7540dbe164c462`), which used the pinned
Markdown and PDF layout. The rendered source evidence is in the
separate angular audit.

### Checked topology for the number-field stages

[`Theorems.IdeleFiniteStage`](../../Proofs/Theorems/IdeleFiniteStage.lean)
works in the actual `IdeleGroup (𝓞 K) K` for every number field `K`.
For each finite set $S$ of finite places, the stage is
$\prod_{v\mid\infty} K_v^\times\times\bigl(\prod_{v\in S} K_v^\times
\times\prod_{v\notin S}\mathcal O_v^\times\bigr)$, where the last product
is over finite places. The monoid homomorphism inserts the three sets of
coordinates literally, with no sign restriction at real places.
`range_ideleFiniteStageEmbedding` tests integrality of both the idele
and its inverse outside $S$. `isOpenEmbedding_ideleFiniteStageEmbedding`
uses the additive stage embedding and then the induced topology on
units. `iUnion_range_ideleFiniteStageEmbedding` takes the finite union
of the exceptions for the value and inverse, giving a cover. By the
range test, the cover still holds with only stages containing any fixed
finite set $E$: Enlarge each witnessing stage $S$ to $S\cup E$.

Definition A.1.3.1 and Lemma A.1.3.3, p. 541, supply the anti-diagonal
topology and the restricted-product identification. The stage restriction
used on p. 556 and in (A.3.2.5), p. 560, needs this exact coordinate and
topology interface. Lean fills it using the adelic stage and its units;
it does not take the identification as an assumption. The source reading
is provisional (Pinned Markdown and PDF layout, not rendered pages).
Independent Yah statement and source review: `lhUkGIq` (output
`c3697ad56a5ec7146950cf26bbb015d60ee19caf`). Audit the two modules from the
integration workspace with:

```sh
go run ./cmd/godel audit-local "$CANDIDATE" \
  Lemmas.AdeleFiniteStage Theorems.IdeleFiniteStage -- \
  Masullo.IdeleFiniteStage Masullo.ideleFiniteStageEmbedding \
  Masullo.ideleFiniteStageEmbedding_infinite \
  Masullo.ideleFiniteStageEmbedding_finite_mem \
  Masullo.ideleFiniteStageEmbedding_finite_notMem \
  Masullo.range_ideleFiniteStageEmbedding \
  Masullo.isOpenEmbedding_ideleFiniteStageEmbedding \
  Masullo.iUnion_range_ideleFiniteStageEmbedding
```

### Checked compact open local integer units

[`Lemmas.FiniteCompletionCompact`](../../Proofs/Lemmas/FiniteCompletionCompact.lean)
identifies $\mathcal O_K/\mathfrak p_v$ canonically with the residue
field of $\mathcal O_v$. A global integer reduces to zero precisely
when its valuation at $v$ is less than one. For surjectivity, approximate
an element of $\mathcal O_v$ first by a field element and then by a global
integer, both with valuation of the difference less than one. The first
approximant is integral at $v$ by the ultrametric inequality; the second
approximation uses the pinned Mathlib lemma for $v$-integral field elements.
The resulting residue field is finite. Completeness of the closed
valuation subring and its discrete valuation ring structure give
compactness; the units are compact in their value-and-inverse topology.
The unit map into $K_v^\times$ is an open embedding since its range tests
integrality of both the value and its inverse.

These are checked prerequisites, not a Haar comparison. Masullo assumes
compact open restricted-product factors on p. 556 and uses the residue
size in (A.3.2.4), p. 560; those passages do not provide these local
constructions. The manuscript correspondence is provisional (based on
pinned Markdown and PDF layout). The results use no local Haar scale.
Independent Yah statement review: `xWEXXXF` (output
`af715a5c9cc024ddceae6ee10b9ae870cf791577`). Reproduce the endpoint audit:

```sh
go run ./cmd/godel audit-local "$CANDIDATE" Lemmas.FiniteCompletionCompact -- \
  Masullo.finiteCompletionResidueEquiv Masullo.finiteCompletionResidueEquiv_mk \
  Masullo.compactSpace_finiteCompletionIntegers \
  Masullo.compactSpace_finiteCompletionIntegralUnits \
  Masullo.isOpenEmbedding_finiteCompletionIntegralUnits
```

### Checked restricted-product Haar for number fields

[`Theorems.IdeleRestrictedProductHaar`](../../Proofs/Theorems/IdeleRestrictedProductHaar.lean)
constructs regular Haar on the actual ideles from arbitrary Borel local
Haar measures with finite integral-unit mass one off a finite set $E$.
The comap to every stage $S\supseteq E$ is the product of the full
Archimedean measures (including both real signs), full active finite
measures, and the probability product of the inactive unit comaps.
These comaps determine the measure among **all** Borel measures. For
any positive compact Archimedean box $B$, the compact global box
with Archimedean coordinates in $B$ and all finite coordinates in
integer units has mass
$$(\bigotimes_{v\mid\infty}\mu_v)(B)\prod_{v\in E}\mu_v(\mathcal O_v^\times).$$

Lemma A.3.2.4 and (A.3.2.5), p. 560, invoke the restricted-product
identification; the prescription on p. 556 refers out for the
construction. For an inactive **probability** product one needs to
include the mass exceptions in $S$. A formula with a normalized tail
on a smaller stage would need the omitted masses as a scalar.
Lean instead compares the Haar restrictions to one common positive
compact box, retains the exceptional masses, and proves Borel
uniqueness on the cofinal countable open cover. This does not derive
(A.3.2.2)'s local discriminant masses or their finite exceptional
support, or identify the product with (A.3.2.1)'s separate quotient
normalization. The manuscript reading is provisional (pinned Markdown
and PDF layout, not rendered pages). Independent Yah statement review:
`SvSZHgF` (output `1a44475cac6933f9666c6701df476b9b8a3beba5`).
Replay the endpoint and the definitions of its factors and box:

```sh
go run ./cmd/godel audit-local "$CANDIDATE" \
  Lemmas.IdeleFiniteStageMeasure Theorems.IdeleRestrictedProductHaar -- \
  Masullo.finiteCompletionUnitMass Masullo.ideleFiniteStageProduct \
  Masullo.stageUnitBox Masullo.ideleCalibrationBox Masullo.image_ideleStageUnitBox \
  Masullo.ideleFiniteStageProduct_unitBox Masullo.exists_ideleRestrictedProductHaar
```

### Checked pure-tensor integration on the actual finite stages

[`Masullo.ideleFiniteStage_integral`](../../Proofs/Theorems/IdeleFiniteStageIntegral.lean)
applies to a Borel measure $\mu$ with the prescribed comap along the
actual open stage $j_S$, with local Haar measures and integral-unit
mass one off $S$. If a complex density $g$ pulls back pointwise to
$\prod_{v\mid\infty}a_v\prod_{v\in S}f_v$ and every factor is integrable
for its full local measure, then $g$ is integrable for
$\mu|_{\operatorname{range}j_S}$. Its complex integral and its real
integral of $\|g\|$ there are the products of the corresponding local
integrals. Nothing is assumed about $g$ off this stage, and no active
factor is rescaled. The Haar construction supplies the comap for every
$S$ containing its finite set of mass exceptions.

**Source and repair (provisional):** The proof of Theorem 3.3.1.1(1),
p. 130, factors the finite $S$-local pairing. For (3.2.2.1), p. 124,
Masullo uses the global absolute product (3.2.2.6), p. 126, and asserts
(3.4.1.6) in the right half-plane on p. 144, where footnote 3 asks for
further justification. The project's theorem factors the restriction
on the actual global topology, using the product prescription
(A.3.2.5), p. 560, with a probability tail and the actual active masses.
It does not assert either the global limit or independence of the printed
formula from the admissible set. The pinned Markdown and PDF layout
were read, but not the rendered pages. Independent endpoint review:
Yah session `01a2019b-59ea-7f53-972c-3bbcf75b3d17`, agent `QzOsmoe`.
Replay the build, modules, and built signatures from the candidate
workspace with:

```sh
go run ./cmd/godel audit-local "$CANDIDATE" \
  Lemmas.IdeleFiniteStageMeasure Theorems.IdeleFiniteStageIntegral -- \
  Masullo.ideleFiniteStage_integral
```

### Checked cofinal exhaustion of the stage integrals

[`Masullo.ideleFiniteStage_exhaust`](../../Proofs/Theorems/IdeleFiniteStageExhaustion.lean)
works on the actual ideles of any number field with any Borel measure
$\mu$. Fix a finite set $E$, a complex density $g$, and a real bound $B$.
If $g$ is integrable on every stage $U_S$ for $S\supseteq E$ and
$\int_{U_S}\|g\|\,d\mu\le B$ there, then $g$ is globally integrable with
$\int\|g\|\,d\mu\le B$. Both the complex and the absolute integrals over
$U_{E\cup S}$ tend to their global values as the finite sets $S$ grow
by inclusion. Neither global measurability nor global integrability is
an additional hypothesis.

**Source and repair (provisional):** The proof of Theorem 3.2.2.1(1)
invokes the global absolute product (3.2.2.6), p. 126, and the proof of
Theorem 3.4.1.1 asserts (3.4.1.6), p. 143, on the right half-plane, with
footnote 3 on p. 144 asking for a justification. From (A.3.2.5), p. 560, we use
open stages of the checked restricted product. Lean glues AE strong
measurability on their countable cover, bounds the global extended norm
integral by the supremum of the bounded stage integrals, and only then
passes the complex and absolute integrals to the limit. This is the
limit step, not a proof of the pointwise tensor identity, the Euler
bound, or the manuscript's quotient-normalized formula. The pinned
Markdown and PDF layout were read, not the rendered pages. Independent
Yah review: Session `01a201a4-3922-7a7b-93d2-0b24063b0682`, agent `meRjKLN`
(output `42f7e496a37b0a2cb85e45c69dc9256790a891e5`). The review also notes
that the cited Proposition 2.4.3.1, p. 113, controls a small-norm theta sum,
not the raw Archimedean absolute integral. The proof of Theorem 3.3.1.1(1),
p. 130, gives the local small-variable and Schwartz-tail argument instead.

Replay in the candidate workspace:

```sh
go run ./cmd/godel audit-local "$CANDIDATE" \
  Theorems.IdeleFiniteStageExhaustion -- Masullo.ideleFiniteStage_exhaust
```

### Finite-place absolute mass and positive Euler-tail bound

[The two Lean endpoints](../../Proofs/Theorems/FiniteHeckeAbsoluteZeta.lean)
fill the finite-place input to the absolute product in (3.2.2.6), p. 126,
and to the above-one argument for (3.4.1.6), pp. 143–144. Masullo invokes
Euler-product convergence and uses $1_{\mathcal O_v}$ on the standard
places; the cited convergence alone does not evaluate the local absolute
integral or bound all finite stages with their given Haar measures.
The readings here are provisional (Markdown and PDF layout).

- `Masullo.finiteHeckeLocalZeta_norm`: For any actual unitary Hecke
  character, the standard $1_{\mathcal O_v}$ density at $s$ is integrable
  for $\Re s>0$ and its absolute mass is
  $\mu_v(\mathcal O_v^\times)/(1-q_v^{-\Re s})$. There is no unramified
  hypothesis for this test. Lean identifies the modulus with the trivial
  character test at $\Re s$ and uses the local shell evaluation. The
  auxiliary `Masullo.continuous_finiteHeckeRestriction` verifies continuity
  on the completion units of the restriction (3.1.2.4), p. 121, for the
  actual Mathlib single-place insertion. This is not the ramified
  inverse-character test used to recognize a complex Euler factor.
- `Masullo.finiteHeckeRealEulerTail_hasProd`: For $\sigma>1$, the real
  factors $(1-q_v^{-\sigma})^{-1}$ off any finite $E$ and $1$ on $E$
  have a full finite-subset product limit. Every partial product is
  bounded by that limit. Lean passes to real parts in the checked
  complex Euler product with coefficients $0$ on $E$ and $1$ off $E$,
  then uses that every real factor is at least $1$.

Independent Yah statement review: Session
`01a201ac-2b60-76c9-bb56-a3e9f24caae6`, agent `YyMfvwr`, output
`9a48075cd271ef997cf9fe8f927a79fae5eda46e`. Replay in the candidate
workspace:

```sh
go run ./cmd/godel audit-local "$CANDIDATE" \
  Lemmas.FiniteHeckeRestriction Theorems.FiniteHeckeAbsoluteZeta -- \
  Masullo.continuous_finiteHeckeRestriction \
  Masullo.finiteHeckeLocalZeta_norm Masullo.finiteHeckeRealEulerTail_hasProd
```

### Character factorization on the open stages

[`Masullo.ideleFiniteStage_character_factor`](../../Proofs/Theorems/IdeleFiniteStageCharacter.lean)
states that for every number field, every stage $U_S$, and every
continuous Hecke character unramified at all finite places outside
$S$, the value at the class of a stage idele is the product of its
Archimedean and active finite-place restrictions at the corresponding
coordinates. It assumes neither unitarity nor a choice of measure.

**Source and repair (provisional):** Masullo states the character tensor
formula in §3.1.2, p. 120, defines the actual single-place restrictions
in (3.1.2.4), p. 121, and specifies unramifiedness outside $S$ and the
$S$-idele insertion in (3.1.2.6)–(8), p. 121. The local unit condition
alone does not algebraically remove the entire inactive tuple in the
stage used for (3.4.1.6), pp. 143–144. Lean checks that each stage
single-coordinate lift agrees with the actual Mathlib insertion,
including the inclusion of integral units at inactive places. Finite
truncations of the inactive tuple then all evaluate to one. Their net
converges coordinatewise in the product topology, so the continuous
character evaluates to one on the whole tuple. This proves the
character identity, not the zeta integral factorization.

Independent Yah statement review (Markdown and PDF layout, not rendered
pages): Session `01a201b3-c224-7ad7-94cc-97b479289ad9`, agent `EySkQXZ`,
output `a2f48d87bd3a9347c1e9077dada53eba3fba2128`. Replay from the
integration workspace:

```sh
go run ./cmd/godel audit-local "$CANDIDATE" \
  Lemmas.IdeleStageSinglePlace Theorems.IdeleFiniteStageCharacter -- \
  Masullo.ideleFiniteStage_character_factor
```

### Checked norm and raw zeta density on the open stages

[`IdeleFiniteStageZetaDensity`](../../Proofs/Theorems/IdeleFiniteStageZetaDensity.lean)
proves `Masullo.ideleFiniteStage_norm` for every number field, finite
stage $S$, and stage point $x$. It splits the norm of the actual embedded
idele into the product of the infinite norms raised to the place
multiplicities and the local norms for $v\in S$. Use (A.1.3.2)–(3), p. 541,
for the product and (3.1.2.3), p. 121, for the square at complex places.
The support argument uses that every inactive coordinate is an integral
unit, hence has norm one. No character or Haar hypothesis is needed.

`Masullo.ideleFiniteStage_zetaDensity` proves the pointwise step for the raw
integrand of (3.2.2.1), p. 124. The finite test is arbitrary on $E$ and is the
integral-ring indicator off $E$; the infinite test is grouped as in
(3.4.1.2), p. 143. For $E\subseteq S$ and a Hecke character unramified
outside $S$, pulling back the density is the grouped infinite density times
the product of active finite densities. The exponent is arbitrary complex,
and there is no unitarity, integrability, or Haar hypothesis. The proof
splits the test, the actual character, and the normalized norm separately.
The independent statement review (session
`01a201c0-5a94-7d3f-9f41-b27cb30f8e23`, child `review-stage-density`,
output `9f7bd86aa59c798dbbb31c926f08e7a0fc1cbd2c`) approved this scope.
The manuscript reading is provisional (Markdown and numbered PDF layout).
The proof of Theorem 3.4.1.1, pp. 143–144, does not supply the restricted-product
limit argument for (3.4.1.5)–(6) (see footnote 3 on p. 144). The two Lean
results fill the pointwise part, not the limit or Haar normalization.

```sh
go run ./cmd/godel audit-local "$CANDIDATE" \
  Lemmas.IdeleStageNormCoordinates Theorems.IdeleFiniteStageZetaDensity -- \
  Masullo.ideleFiniteStage_norm Masullo.ideleFiniteStage_zetaDensity
```

### Checked grouped zeta integrals on each stage

[`Masullo.ideleFiniteStage_zetaIntegral`](../../Proofs/Theorems/IdeleFiniteStageIntegral.lean)
proves integrability of the actual raw zeta density on the open stage $U_S$.
Its complex integral equals the single Archimedean integral times the
product of the active finite integrals. Its absolute integral is the same
product with the norm taken **inside** every local integral. The test is
arbitrary on the finite exceptional set $E$ and is $1_{\mathcal O_v}$ off
$E$. The hypotheses are $E\subseteq S$, unramifiedness and measure mass one
only off $S$, the exact stage comap identity, and integrability of the grouped
Archimedean density and each active local density. There is no unitarity or
half-plane restriction in this finite-stage theorem. The active measures,
including any exceptional unit masses, are unchanged.

**Source and repair (provisional):** The raw density is from (3.2.2.1),
p. 124, and the grouped factor is from (3.4.1.2), p. 143. The right-half-plane
assertion of (3.4.1.6) in the proof of Theorem 3.4.1.1, p. 144 (footnote 3),
does not justify the actual stage integrals or the passage to their limit.
Using the stage measures for (A.3.2.5), p. 560, Lean uses Fubini with the
whole infinite block and integrates the inactive probability out. It then
uses the pointwise `ideleFiniteStage_zetaDensity` on the actual embedding.
This supplies the stage integrals of the raw density, not the corrected
local factors in (3.4.1.3), the global limit, or the convergence of the
local factors for the full Schwartz–Bruhat class. The Markdown and
numbered PDF layout were read, not the rendered pages.

Independent Yah statement review: Session
`01a201ca-3e36-73bc-9843-c3a0773cff61`, child `review-grouped-zeta-stage`
(agent `cFpbJXV`). This also checked the unchanged pure-tensor endpoint.

Replay in the candidate workspace:

```sh
go run ./cmd/godel audit-local "$CANDIDATE" \
  Lemmas.IdeleFiniteStageMeasure Theorems.IdeleFiniteStageIntegral -- \
  Masullo.archimedeanHaar_sigmaFinite Masullo.ideleFiniteStageProduct_groupedTensor \
  Masullo.ideleFiniteStage_integral_grouped Masullo.ideleFiniteStage_integral \
  Masullo.ideleFiniteStage_zetaIntegral
```

### Checked: Exhaust the raw zeta integral above one

[`Masullo.ideleZetaIntegral_rightHalfPlane`](../../Proofs/Theorems/IdeleZetaIntegral.lean)
proves global integrability and factors both the complex integral and its
absolute mass for the grouped test above any number field. The unitary
Hecke character and the local unit masses are unramified and one,
respectively, **off** a finite base $T$ containing the test exception set
$E$. The upstairs measure has the exact stage restrictions for stages
containing $T$, as furnished by `exists_ideleRestrictedProductHaar`.
For $\Re s>1$, only the Archimedean block and the local factors on $T$
need separate integrability assumptions. Each of the two values is
the grouped Archimedean integral times the finite product of **raw**
integrals on $T$ times its own Euler tail off $T$. The real formula
integrates the pointwise norm, not the norm of the complex integral.

**Source and repair (provisional):** The raw integral and absolute
product are (3.2.2.1), p. 124, and (3.2.2.6), p. 126. For (3.4.1.6),
pp. 143–144, Lean bounds every stage mass by the positive Euler tail,
then uses exhaustion to pass to both limits. The complex factors use
`finiteHeckeCoefficient χ` off $T$ and zero coefficients on $T$; the
real factors use the trivial-character Euler factors at $\Re s$ off $T$
and one on $T$. This supplies the initial restricted-product argument
requested in footnote 3, p. 144, for the stated input class and raw
factors. It neither uses nor proves the printed admissible-set identity;
see the [separate rendered check](weil-admissible-set.md) for the
normalization defect. The source reading for this result used Markdown
and numbered PDF layout, not rendered pages.

Independent Yah statement review: Session
`01a201d2-0f82-7b09-ab55-c40a33b87e28`, child `review-global-raw-zeta`
(agent `ICDDbhs`, output `29c45b84c29406a1453f581b27009ec895024363`).
Replay in the candidate workspace:

```sh
go run ./cmd/godel audit-local "$CANDIDATE" \
  Lemmas.IdeleFiniteStageMeasure Theorems.IdeleZetaIntegral -- \
  Masullo.finiteCompletionUnitMass Masullo.ideleZetaIntegral_rightHalfPlane
```

## Checked raw Gaussian calibration above one

[`ideleHeckeGaussian_zetaIntegral`](../../Proofs/Theorems/IdeleHeckeGaussian.lean)
uses one test independent of $s$. It certifies absolute integrability
and the raw scalar pairing, for any number field, unitary Mathlib Hecke
character $\chi$, and $\Re s>1$:

$$
Z(E_\chi,\chi|\cdot|^s)=
 \left(\prod_{v\in T}\mu_v(\mathcal O_v^\times)\right)
 L_{\mathrm{Euler}}(s,\chi).
$$

Here $T$ contains character ramification and all exceptions to unit mass
one. The finite local measures are supplied Haar measures, the infinite
measures are the transported real and complex Haar measures, and the
upstairs measure has the corresponding exact restrictions to stages
containing $T$. `exists_ideleRestrictedProductHaar` gives such a measure.

Definition 3.4.3.2 and the following paragraph, p. 152, specify the tensor and the pairing
convention for the completion, while (3.2.1.1)–(5), pp. 122–123,
specifies the Euler product. The bilinear integral in (3.3.1.7), p. 130,
requires the [opposite-weight complex test](complex-gaussian-angular.md)
in place of (3.4.3.5)–(6); at a finite place, (A.3.2.2), p. 560,
requires the [actual unit mass](finite-gaussian-tamagawa.md), which is
also present when the ramified Euler factor is one. The new theorem
splits the grouped infinite density into the checked Gaussian pairings,
uses the exact-stage exhaustion above, and rejoins the local finite
Euler factors to the tail. It compares the two scalar conventions on
this one test; it does not prove the eigendistribution identity
(3.4.3.15), p. 153. This assembly reading used Markdown and numbered PDF
layout, not rendered pages; the linked local controls have separate
rendered evidence.

Independent Yah statement review: Session
`01a201d9-3a08-7336-b23f-ad0ce02c09fd`, child `review-gauss-statement`
(agent `TmlTVcA`).

Replay the two affected modules in the candidate workspace:

```sh
go run ./cmd/godel audit-local "$CANDIDATE" \
  Theorems.CompletedHeckeEulerProduct Theorems.IdeleHeckeGaussian -- \
  Masullo.completedHeckeEulerProduct Masullo.archimedeanCompletionHaar \
  Masullo.archimedeanCompletionHaar_isHaarMeasure Masullo.archimedeanHeckeGaussian \
  Masullo.finiteHeckeGaussian Masullo.ideleHeckeGaussian Masullo.ideleHeckeGaussian_zetaIntegral
```

### Checked: Arithmetic product of finite unit scales

[`DifferentUnitScales.lean`](../../Proofs/Theorems/DifferentUnitScales.lean)
uses the actual different $D=\mathrm{differentIdeal}\,\mathbb Z\,(\mathcal O_K)$.
For $v$ in the height-one spectrum of $\mathcal O_K$, put
$n_v=\mathrm{multiplicity}(v.\mathrm{asIdeal},D)$ and
$q_v=\mathrm{absNorm}(v.\mathrm{asIdeal})$. Lean proves finite support of
$n_v$ and, for **every** finite superset $T$ of that support,

$$
\prod_{v\in T}q_v^{n_v}=|\operatorname{disc}K|,\qquad
\prod_{v\in T}\bigl(\sqrt{q_v^{n_v}}\bigr)^{-1}
=\bigl(\sqrt{|\operatorname{disc}K|}\bigr)^{-1}.
$$

Masullo prescribes the local mass by the integral discriminant in
(A.3.2.2), p. 560, and uses the norm of the **local** different in the
unit calculation in the proof of Theorem 3.4.1.1, p. 144. Neither
display computes the product using the exponents of the **global**
different. The arithmetic bridge above takes absolute norms in its
Dedekind factorization and uses `NumberField.absNorm_differentIdeal`.
This comparison used Markdown and numbered PDF layout and is provisional;
the [separate finite Gaussian control](finite-gaussian-tamagawa.md)
has rendered-page evidence for the local normalization.

Independent Yah statement review: Session
`01a201e2-9be7-7e27-9cdf-b0edf12c9348`, child `review-different-product`
(agent `CXjwajI`, read-only output `7340854b9c63a1817e848c324487928495e638ab`).
The exact-candidate replay command is:

```sh
go run ./cmd/godel audit-local "$CANDIDATE" Theorems.DifferentUnitScales -- \
  Masullo.finite_differentIdeal_multiplicity_support \
  Masullo.prod_absNorm_pow_differentIdeal_multiplicity \
  Masullo.prod_differentIdeal_unit_scales
```

### The p-adic base of the actual finite completion

Appendix A.1.1.1, p. 539, uses $K_v$ as a finite extension of
$\mathbb Q_p$, and (A.3.2.2), p. 560, takes its discriminant over
$\mathbb Z_p$. These passages specify the objects; they do not give
compatible maps on the chosen Lean completion types. This reading was
checked against Markdown and numbered PDF layout, not newly rendered
pages. See the rendered normalization control linked above.

[`FiniteCompletionPadic.lean`](../../Proofs/Lemmas/FiniteCompletionPadic.lean)
constructs continuous ring embeddings $\mathbb Q_p\to K_v$ and
$\mathbb Z_p\to\mathcal O_{K_v}$ for every number field and finite place,
with $p$ the prime below $v$. The field map extends the canonical
rational map, and its inverse image of $\mathcal O_{K_v}$ is exactly the
base unit ball $\{x:\|x\|_p\le 1\}$. The integer map is its restriction.
The integer criterion follows by comparing the two clopen sets on the
dense rational image, where the valuations differ by the positive
ramification power. The induced scalar actions give the compatible
rational and integral towers. The image of $\mathbb Q_p\otimes_{\mathbb Q} K$
is finite-dimensional and closed, and contains the dense image of $K$,
so `finiteCompletion_moduleFinite` gives finite dimensionality for this
same scalar action.

Independent Yah statement and route review: Session
`01a201e9-bb5f-7b22-ae80-89d143d16a70`, child
`review-padic-completion-interface` (agent `wOQreHk`, read-only output
`a63eac6af49ab0c9471fa766d7b3035976f7accf`). The review distinguishes the
integrality test from a real norm identity and verifies that the finite
span uses the canonical rational square. Reproduce the endpoint audit:

```sh
go run ./cmd/godel audit-local "$CANDIDATE" Lemmas.FiniteCompletionPadic -- \
  Masullo.finiteCompletionBasePrime Masullo.finiteCompletionPadicMap \
  Masullo.continuous_finiteCompletionPadicMap \
  Masullo.finiteCompletionPadicMap_algebraMap \
  Masullo.finiteCompletionPadicMap_mem_integers_iff \
  Masullo.finiteCompletionPadicIntMap Masullo.coe_finiteCompletionPadicIntMap \
  Masullo.continuous_finiteCompletionPadicIntMap \
  Masullo.finiteCompletionRatPadicTower \
  Masullo.finiteCompletionPadicIntPadicTower \
  Masullo.finiteCompletionPadicIntIntegersTower \
  Masullo.finiteCompletionPadicContinuousSMul Masullo.finiteCompletion_moduleFinite
```

### Checked: The integral lattice in the actual finite completion

[`FiniteCompletionIntegralLattice.lean`](../../Proofs/Lemmas/FiniteCompletionIntegralLattice.lean)
proves that the actual completion integers $\mathcal O_{K_v}$ form a
finite free $\mathbb Z_p$-module for the compatible maps above. It also
proves that inverting the image of $\mathbb Z_p\setminus\{0\}$ in
$\mathcal O_{K_v}$ gives the actual field $K_v$. Hence a basis of the
integer ring localizes along its inclusion to a $\mathbb Q_p$-basis of
$K_v$ by `Module.Basis.localizationLocalization`.

In (A.3.2.2), p. 560, Masullo specifies the local integral discriminant
as the input to the Haar scale. This repair supplies the finite free
lattice and its relation to the local field, not the discriminant
comparison. In a field basis, compactness bounds each coordinate on
the integer ring. Rescaling by a power of $p$ in each coordinate gives
an injection into a finite power of $\mathbb Z_p$. Finite torsion-free
modules over this PID are free. For localization, $p^n\to0$ and openness
of $\mathcal O_{K_v}$ put $p^n z$ in that ring for any $z\in K_v$ and
sufficiently large $n$. This source comparison used Markdown and
numbered PDF layout, not a new rendered-page check.

Independent Yah statement review: Session
`01a201f2-efad-7219-b4a7-f2e365782b3c`, child
`review-local-integer-lattice` (agent `mSFmHgG`). Replay the checked
endpoints from the exact integration workspace:

```sh
go run ./cmd/godel audit-local "$CANDIDATE" Lemmas.FiniteCompletionIntegralLattice -- \
  Masullo.finiteCompletionIntegers_moduleFinite \
  Masullo.finiteCompletionIntegers_moduleFree \
  Masullo.finiteCompletionIntegers_isLocalization
```

### Checked: Prime-power quotients of the completion integers

[`FiniteCompletionPrimePow.lean`](../../Proofs/Lemmas/FiniteCompletionPrimePow.lean)
uses the canonical map $i_v:\mathcal O_K\to\mathcal O_{K_v}$. For every
$n\geq 0$, the contraction of $\mathfrak m_v^n$ is $v^n$, and $i_v$
induces the ring equivalence

$$\mathcal O_K/v^n\;\simeq\;\mathcal O_{K_v}/\mathfrak m_v^n,$$

with the explicit class-of-$x$ formula. The image of a global element
of valuation one in the additive valuation generates $\mathfrak m_v$,
not necessarily the global prime. This gives the kernel on every
power. For surjectivity the proof lifts a residue class using
`finiteCompletionResidueEquiv`, divides the error by that local
uniformizer, and inducts. Extension of any nonzero global ideal $I$
along $i_v$ gives $\mathfrak m_v^{\mathrm{multiplicity}(v,I)}$:
Distinct prime factors become unit ideals, while $v$ extends to
$\mathfrak m_v$.

Masullo gives the local different and discriminant as inputs to the
additive mass in (A.3.1.2), p. 556, and the local discriminant as input
to the multiplicative unit mass in (A.3.2.2), p. 560. The prime-power
and ideal comparisons are project results needed to realize these
inputs in the actual completions; they do not identify the local
trace-dual lattice. This reading used Markdown and numbered layout,
not new rendered-page inspection.

Independent Yah statement review: Session
`01a201fd-28c9-715d-95a7-3d1d8c0de9dd`, child
`review-prime-power-quotients` (agent `YqNjHen`, read-only output
`5d54a96cb6569e602b8d1467f375834791c19d9c`). The review confirmed the
uniformizer and quotient arguments, and suggested the residue-lifting
induction used in the proof. Reproduce the endpoint audit:

```sh
go run ./cmd/godel audit-local "$CANDIDATE" Lemmas.FiniteCompletionPrimePow -- \
  Masullo.comap_finiteCompletion_maximalIdeal_pow \
  Masullo.map_finiteCompletion_prime Masullo.map_finiteCompletion_ideal \
  Masullo.finiteCompletionPrimePowQuotientEquiv \
  Masullo.finiteCompletionPrimePowQuotientEquiv_mk
```

### Checked: Canonical reduction in the product of actual completions

[`FiniteCompletionCRT.lean`](../../Proofs/Lemmas/FiniteCompletionCRT.lean)
assembles the Dedekind-domain Chinese remainder equivalence on the
finitely many height-one places dividing a nonzero global ideal $I$.
In each coordinate it uses the checked prime-power quotient equivalence
and then rewrites the local prime power as $I\mathcal O_{K_v}$. Thus

$$\mathcal O_K/I\;\simeq\;\prod_{v\mid I}\mathcal O_{K_v}/I\mathcal O_{K_v},
\qquad [x]\longmapsto([i_v(x)])_v.$$

For a rational prime $p$, `finiteCompletionModPrimeEquiv` specializes
this to $I=p\mathcal O_K$ with target exactly modulo $p$ in each
completion. `finitePlace_dvd_primeSpan_iff` identifies the index
condition with $p\in v$ and `finiteCompletionModPrimeEquiv_mk` records
the class formula. This retains all $e_v$ layers at a ramified place,
not just the residue field. The general theorem includes the unit
ideal: The product over no places and the quotient by the unit ideal
are both trivial rings.

This is a project result, not a step proved by Masullo: He prescribes
the discriminant unit mass in (A.3.2.2), p. 560, and recalls the trace
character and inverse-different Fourier formula in Example A.3.1.10,
(A.3.1.8), p. 558. The latter locator is the numbered page in both
Markdown and layout. This source comparison is provisional; no new
rendered-page inspection. The quotient theorem supplies the reduction
needed for the integral base change, not the trace-dual lattice or
Haar scales.

Independent Yah statement review: Session
`01a20204-cd04-7861-b125-da6e2ed2104b`, child `review-completion-crt`
(agent `ggvYIbJ`, read-only output
`be4530c96fc602938a974e32e6be056d66675d21`). The review agreed with the
divisor-subtype generalization and the canonical class formula. For the
specialization Lean uses the divisor subtype together with the checked
membership equivalence; the local cast is the image of the global cast
by `map_natCast`. Reproduce the endpoint audit:

```sh
go run ./cmd/godel audit-local "$CANDIDATE" Lemmas.FiniteCompletionCRT -- \
  Masullo.finiteCompletionIdealQuotientEquiv \
  Masullo.finiteCompletionIdealQuotientEquiv_mk \
  Masullo.finitePlace_dvd_primeSpan_iff Masullo.finiteCompletionModPrimeEquiv \
  Masullo.finiteCompletionModPrimeEquiv_mk
```

### Checked: Fixed-prime integral base change

[`FiniteCompletionIntegralBaseChange.lean`](../../Proofs/Lemmas/FiniteCompletionIntegralBaseChange.lean)
constructs the canonical $\mathbb Z_p$-algebra isomorphism

$$\mathbb Z_p\otimes_{\mathbb Z}\mathcal O_K\simeq
  \prod_{v\mid p}\mathcal O_{K_v},\qquad
  a\otimes x\longmapsto (a\,i_v(x))_v.$$

The target uses the same divisor subtype as the reduction theorem. The
base-prime equality and `finiteCompletionOverPrimeAlgebra_algebraMap`
identify the scalar map with the canonical completed map at each place.
Reduction of a tensor modulo $p$ comes from a global integer, and CRT
both lifts target residues and detects zero source residues. Nakayama
lifts surjectivity on the finite target. The kernel is finite over the
Noetherian base and equals its $p$-multiple: Modulo-$p$ injectivity gives
divisibility in the source and $p$-torsion-freeness of each completion
keeps the divided element in the kernel. Another use of Nakayama
kills the kernel.

This is project support for the comparison required by (A.3.2.2),
p. 560, not a theorem attributed to Masullo. Example A.3.1.10,
(A.3.1.8), p. 558, recalls the standard trace character and its
inverse-different transform. It does not supply the integral
base-change map or the global-to-local comparison of differents.
This reading uses Markdown and numbered layout, not rendered pages,
and is provisional.

Independent Yah statement review: Session
`01a2020b-a0bf-7254-897a-c6c8fc79f5d4`, child
`review-integral-base-change` (agent `VQdUGlv`, read-only output
`511e38138950387bf13cd97f05536ded4e4b3d63`). The review confirmed
that the scalar action must be the completed base map transported along
the prime equality and that the pure tensor must evaluate coordinatewise.
Reproduce the endpoint audit:

```sh
go run ./cmd/godel audit-local "$CANDIDATE" \
  Lemmas.FiniteCompletionPadic Lemmas.FiniteCompletionIntegralBaseChange -- \
  Masullo.finiteCompletionBasePrime_val \
  Masullo.finiteCompletionBasePrime_eq_of_dvd_primeSpan \
  Masullo.finiteCompletionOverPrimeAlgebra \
  Masullo.finiteCompletionOverPrimeAlgebra_algebraMap \
  Masullo.finiteCompletionIntegralBaseChange \
  Masullo.finiteCompletionIntegralBaseChange_tmul
```

### Next: Identify the placewise discriminant scales

For $v$ over $p$, in the **actual** completion $K_v$ prove
$|\operatorname{disc}(\mathcal O_{K_v}/\mathbb Z_p)|_p=q_v^{-n_v}$.
One route is to prove that the image ideal of $D$ in $\mathcal O_{K_v}$
is the local different, identify it as $\mathfrak m_v^{n_v}$, and compute
the $p$-valuation of the local trace determinant as the length over
$\mathbb Z_p$ of the trace-dual lattice modulo $\mathcal O_{K_v}$.
The quotients by successive powers of $\mathfrak m_v$ have size $q_v$.
The norm meant on the determinant is the base $p$-adic norm, not the
normalized on-place norm extending a power of it. At the place over $2$
in $\mathbb Q(i)$ this must give $q_v^{-n_v}=1/4$ and unit mass $1/2$,
not unit mass one.

### Checked p-adic determinant and lattice index

[`PadicLatticeIndex.lean`](../../Proofs/Lemmas/PadicLatticeIndex.lean)
proves that an injective endomorphism $f$ of a finite free
$\mathbb Z_p$-module $M$ satisfies

$$|\det f|_p = \bigl(\#(M/fM)\bigr)^{-1}.$$

Use a Smith basis for the inclusion of $fM$. The determinant in those
coordinates differs from $\det f$ by a unit. Each nonzero diagonal entry
$a$ is associated to $p^{v_p(a)}$, and its quotient has exactly
$p^{v_p(a)}$ elements by reduction to $\mathbb Z/p^{v_p(a)}\mathbb Z$.
Multiplying the rank-one formulas proves the equality. This covers
unit entries, including rank zero, without a positive-length premise.

This is project support, not a manuscript proof step. Definition
A.3.1.2(3), (A.3.1.2), and Lemma A.3.1.3, PDF p. 556, use the local
determinant scale and its comparison with the different norm;
Definition A.3.2.2, (A.3.2.2), p. 560, uses the same scale for
multiplicative Haar. Example A.3.1.10, (A.3.1.8), p. 558, uses it for
the Fourier transform of the integer ball. The source reading is
provisional: Pinned Markdown and numbered PDF text, not rendered-page
inspection.

**Next use of this lemma:** For $O=\mathcal O_{K_v}$ and an integral
basis $b$, use the integral trace Gram matrix as the endomorphism in
basis coordinates. Its determinant is the integral discriminant;
localization of the trace and nondegeneracy give injectivity. Identify
its cokernel with $O^\vee/O$ by the field trace pairing, where
$O^\vee=\{x\in K_v:\operatorname{Tr}(xO)\subseteq\mathbb Z_p\}$. Then
identify the quotient cardinal with $\#(O/\mathfrak d_v)$ by the
fractional ideal quotient equivalence. The local different and
codifferent comparison is separate: Once $\mathfrak d_v$ is the
extension of the global different, the checked prime-power quotient
equivalence above identifies $\#(O/\mathfrak d_v)$ with $q_v^{n_v}$
using `Ideal.absNorm`. The trace Gram comparison and Haar construction
are not supplied by the index lemma.

Reproduce the endpoint audit in the integration workspace:

```sh
go run ./cmd/godel audit-local "$CANDIDATE" Lemmas.PadicLatticeIndex -- \
  Masullo.padicInt_norm_det_eq_inv_card_quotient_range
```

### Checked: Integral traces in the fixed-prime splitting

[`FiniteCompletionIntegralTrace.lean`](../../Proofs/Lemmas/FiniteCompletionIntegralTrace.lean)
proves for every $t\in A_p=\mathbb Z_p\otimes_{\mathbb Z}\mathcal O_K$
that $\operatorname{Tr}_{A_p/\mathbb Z_p}(t)$ equals the sum of the integral
traces of the coordinates of $\Phi_p(t)$, where $\Phi_p$ is the canonical
equivalence above. In particular, for every $x\in\mathcal O_K$,

$$\sum_{v\mid p}\operatorname{Tr}_{\mathcal O_{K_v}/\mathbb Z_p}(i_v(x))
  = (\operatorname{Tr}_{\mathcal O_K/\mathbb Z}(x):\mathbb Z_p).$$

The trace is invariant under $\Phi_p$. In the product basis indexed by
pairs of a place and a local basis vector, the diagonal of multiplication
has the local diagonals as its blocks. For $1\otimes x$, the canonical
tensor formula identifies the local arguments, and trace base change
identifies the global value. Applying the result to $tt'$ gives the
orthogonal block description of the integral trace pairing. No caller
assumption of freeness, finiteness, or choice of a local scalar map is
needed.

Masullo uses the local trace character and inverse-different transform
in (A.3.1.8), p. 558, and prescribes the local multiplicative Haar mass
in (A.3.2.2), p. 560. Neither passage supplies a comparison with the
global trace. The splitting is project support, not a theorem of the
manuscript. The passage reading is provisional (Markdown and numbered
layout, no rendered inspection).

Independent Yah statement review: Session
`01a20219-83c4-7160-8911-997347ffb8eb`, child `review-fixed-prime-trace`
(agent `XbuQqsQ`, read-only output
`0afd45eef0d4c5338391c7c428bcd8244613d1e3`). The review checked the exact
place subtype, the transported local scalars and finite-free lattices,
and both trace statements. Reproduce the endpoint audit with:

```sh
go run ./cmd/godel audit-local "$CANDIDATE" \
  Lemmas.FiniteCompletionIntegralBaseChange Lemmas.FiniteCompletionIntegralTrace -- \
  Masullo.finiteCompletionOverPrime_moduleFree \
  Masullo.finiteCompletionOverPrime_moduleFinite \
  Masullo.finiteCompletionOverPrimeFintype \
  Masullo.finiteCompletionIntegralBaseChange_trace \
  Masullo.finiteCompletionIntegralBaseChange_trace_global
```

### Checked fraction splitting and local trace-dual criterion

[`FiniteCompletionFractionBaseChange.lean`](../../Proofs/Lemmas/FiniteCompletionFractionBaseChange.lean)
extends the integral equivalence $\Phi_p$ for $A_p=\mathbb Z_p\otimes_{\mathbb Z}\mathcal O_K$.
It proves the $\mathbb Q_p$-algebra equivalence

$$\Psi_p:\mathbb Q_p\otimes_{\mathbb Z_p} A_p\;\simeq\;\prod_{v\mid p} K_v,
\qquad a\otimes t\longmapsto(a\,\Phi_p(t)_v)_{v\mid p}.$$

The pure-tensor formula uses the actual inclusions of the completion
integers. The accompanying scalar-map identities compare with the
checked completed field map and prove its compatibility with the
integral map. Each completion field localizes its integer lattice at
the nonzero base integers; tensor commutes with the finite product.

The trace of an arbitrary $x$ in the fraction algebra is the sum of
the traces of $\Psi_p(x)_v$. The trace against $1\otimes t$ belongs to
$\mathbb Z_p$ for every $t\in A_p$ if and only if at each $v$ the trace
of $\Psi_p(x)_v y$ belongs to $\mathbb Z_p$ for every $y\in\mathcal O_{K_v}$.
The forward implication lifts a test supported in one coordinate via
$\Phi_p^{-1}$; the reverse takes the finite sum. No caller-supplied
basis, scalar map, or assertion of separability is needed.

Masullo uses the trace character and inverse different in Example
A.3.1.10, (A.3.1.8), PDF p. 558, and prescribes the Haar mass in
(A.3.2.2), p. 560. He supplies neither this fraction comparison nor
the trace-dual criterion. They are project support. This source
reading is provisional: Markdown and numbered PDF text, not a
rendered-page review.

Independent statement review: Yah session
`01a20221-adf8-791f-a475-b13696c264e4`, child `review-fraction-splitting`
(agent `KfkbziE`, read-only output
`a1f71baf9d9136d6d7a4f20d99d2bf40fefacef5`).
Reproduce the endpoint audit in the integration workspace:

```sh
go run ./cmd/godel audit-local "$CANDIDATE" \
  Lemmas.FiniteCompletionIntegralBaseChange Lemmas.FiniteCompletionIntegralTrace \
  Lemmas.FiniteCompletionFractionBaseChange -- \
  Masullo.finiteCompletionOverPrime_isLocalization Masullo.algebraTrace_pi \
  Masullo.finiteCompletionOverPrimeFieldAlgebra \
  Masullo.finiteCompletionOverPrimeFieldAlgebra_algebraMap \
  Masullo.finiteCompletionOverPrime_algebraMap_int \
  Masullo.finiteCompletionFractionBaseChange \
  Masullo.finiteCompletionFractionBaseChange_tmul \
  Masullo.finiteCompletionFractionBaseChange_trace \
  Masullo.finiteCompletionFractionBaseChange_traceDual_iff
```

### Checked: The codifferent in each actual finite completion

[`FiniteCompletionCodifferent.lean`](../../Proofs/Lemmas/FiniteCompletionCodifferent.lean),
`Masullo.finiteCompletion_traceDual_iff_mem_span_globalCodifferent`, proves
for every number field $K$, rational prime $p$, place $v$ over $p$, and
$x\in K_v$, the equivalence

$$
  [\,\operatorname{Tr}_{K_v/\mathbb Q_p}(xy)\in\mathbb Z_p
       \text{ for all } y\in\mathcal O_{K_v}\,]
  \quad\Longleftrightarrow\quad
  x\in\operatorname{span}_{\mathcal O_{K_v}} i_v(\mathcal O_K^\vee).
$$

Here $i_v:K\to K_v$ is the canonical completion map and
$\mathcal O_K^\vee$ is `Submodule.traceDual ℤ ℚ (1 : Submodule (𝓞 K) K)`.
The `1` is the image of $\mathcal O_K$ in $K$, not the whole field.
The local trace uses `finiteCompletionOverPrimeFieldAlgebra` and the
same prime witness as the fraction splitting. No basis, separability,
or compatibility hypothesis is passed by the caller.

The proof cancels the two intermediate base changes and localizes
$\mathcal O_K$ to identify the fraction algebra with
$\mathbb Q_p\otimes_{\mathbb Q} K$. The equality of the coordinate map
with $i_v$ is checked on global integers using the pure-tensor formulas,
then on all of $K$ by localization. Trace base change gives the coordinates
on the extended global trace-dual basis; they are integral exactly when
all integral-tensor tests have integral trace. Lift a local dual vector
at just its own coordinate to use this criterion, and project the
resulting $\mathbb Z_p$-linear combination of dual basis vectors to
$K_v$. These combinations belong to the claimed $\mathcal O_{K_v}$-span.
Conversely, each canonical image of a global dual vector passes the
local trace tests, and the local trace dual is an $\mathcal O_{K_v}$-module.
This proof does not apply the field-only `Submodule.traceDual` to the
fraction product algebra.

Masullo's Example A.3.1.10, (A.3.1.8), PDF p. 558, uses the local trace
character and inverse different; Definition A.3.2.2(2), (A.3.2.2), PDF
p. 560, prescribes the discriminant-normalized unit mass. Neither gives
the global-to-local lattice comparison. The theorem above supplies
that comparison, not the Fourier formula or the measure normalization.
The source reading is provisional (Markdown and pinned numbered PDF
layout, without rendered-page inspection).

Independent statement review: Yah session
`01a2022a-68af-7f49-a9dd-5dacd7bc1baa`, child
`review-codifferent-statement` (agent `ZJOqyIO`, read-only output
`2852eafe028a812766f48a8a139d718f4da5b292`), against baseline
`de7f8b2c33d98af9280fd670307837cb158c15e6`. The reviewer confirmed the
corrected global lattice (`1`, not `⊤`), local base field, canonical
completion image, and the need for both local-integer span inclusions.
The writer's `lake --wfail build +Lemmas.FiniteCompletionCodifferent`,
`lake env leanchecker Lemmas.FiniteCompletionCodifferent`, and an import
probe with `#check` and `#print axioms` passed. The built signature matches
the corrected reviewed statement; axioms are `propext`, `Classical.choice`,
and `Quot.sound`. The recovered source is byte-identical to writer output
`ad1278d2f1ac7b12a758c168d3a0c3f475ebc88f`. Reproduce the full
warning-as-error build, separate module replay, and built endpoint
signature/axiom audit from the integration workspace:

```sh
go run ./cmd/godel audit-local "$CANDIDATE" Lemmas.FiniteCompletionCodifferent -- \
  Masullo.finiteCompletion_traceDual_iff_mem_span_globalCodifferent
```

**Global-to-local comparison:** See the [checked extension of the global
different](#checked-extension-of-the-global-different) for the canonical
completion and its exponent.

### Local discriminant as the trace-dual index

[`FiniteCompletionTraceIndex.lean`](../../Proofs/Lemmas/FiniteCompletionTraceIndex.lean)
works at every actual finite place $v$ of a number field. Write
$R=\mathbb Z_p$, $F=K_v$, $O=\mathcal O_{K_v}$, and
$D=\{x\in F:\operatorname{Tr}_{F/\mathbb Q_p}(xO)\subseteq R\}$.
The map $I:O\to D$ is the actual completion inclusion: Localization
identifies the field trace of a product of integers with the image of
its integral trace. For any finite $R$-basis $b$ of $O$, localize $b$
and take the field trace-dual basis. Its $R$-span is $D$, and the
coordinate map sends $x$ to $(\operatorname{Tr}(xb_i))_i$. On $I(O)$
this map is the integral Gram matrix acting on the coordinates in $b$.
It follows that the inverse coordinate map identifies the Gram cokernel
with $D/I(O)$; the representative equation checks the induced map.

The Gram map is injective since both the lattice inclusion and the
trace-coordinate map are injective. Apply the p-adic determinant/index
lemma to it and transport the cardinality across the equivalence:

$$\bigl\|\operatorname{disc}_R(b)\bigr\|_p
  = \frac{1}{\#(D/I(O))}.$$

The quotient is finite: If its totalized `Nat.card` were zero, the
identity would force the integral discriminant to vanish, but its image
is the nonzero discriminant of the localized field basis. No global
codifferent identification or measure hypothesis enters this proof.

Masullo prescribes the square root of the discriminant norm in
(A.3.1.2), PDF p. 556, and (A.3.2.2), p. 560, and uses it with the
inverse-different indicator in (A.3.1.8), p. 558. The lattice index
calculation above is project support, not a derivation in those
passages, and does not construct those Haar measures. The reading
here is provisional: Markdown and numbered PDF text, not rendered pages.

Independent statement review: Yah session
`01a20246-e109-7bf5-96da-9dfbadedc2b3`, children
`review-local-trace-index` (`IpUpRRd`, read-only output
`6469256dc6472ffd6ca1c1dc66f75e24e0031a45`) and
`review-trace-index-supplements` (`ncTdWcU`). Reproduce the endpoint
and kernel audit in the integration workspace:

```sh
go run ./cmd/godel audit-local "$CANDIDATE" Lemmas.FiniteCompletionTraceIndex -- \
  Masullo.finiteCompletionIntegersToTraceDual \
  Masullo.finiteCompletionTraceGramQuotientEquiv \
  Masullo.finiteCompletionTraceGramQuotientEquiv_symm_mk \
  Masullo.finiteCompletion_norm_discr_eq_inv_card_traceDual_quotient \
  Masullo.finite_finiteCompletionTraceDual_quotient
```

### Placewise discriminant and different norms

[`FiniteCompletionDifferentScale.lean`](../../Proofs/Theorems/FiniteCompletionDifferentScale.lean)
works at every finite place of a number field. Let $O_v$ be the ring of
integers in the actual completion over $\mathbb Q_p$, and write
$\mathfrak d_v=\mathrm{differentIdeal}(\mathbb Z_p,O_v)$,
$q_v=\#(\mathcal O_K/v)$, and
$\mathfrak d_v=\mathfrak m_v^{d_v}$. Lean defines $d_v$ by the
coheight of $\mathfrak d_v$ and proves the power formula, including
$d_v=0$.

[`FiniteCompletionDifferentQuotient.lean`](../../Proofs/Lemmas/FiniteCompletionDifferentQuotient.lean)
identifies the actual trace dual with $\mathfrak d_v^{-1}$ inside
$K_v$. For a generator $a$ of $\mathfrak d_v$, multiplication by $a$
is a $\mathbb Z_p$-linear equivalence from the trace dual to $O_v$;
it sends the canonical integer sublattice onto $\mathfrak d_v$.
The induced quotient equivalence has an inverse that sends the class
of $x\in O_v$ to the trace-dual class of $x/a$. The existing canonical
prime-power quotient equivalence and multiplicativity of `Ideal.absNorm`
give

$$
\#(O_v^\vee/O_v)=\#(O_v/\mathfrak d_v)=q_v^{d_v}.
$$

The [trace Gram index](#local-discriminant-as-the-trace-dual-index)
then gives $\|\operatorname{disc}_{\mathbb Z_p}(b)\|_p=(q_v^{d_v})^{-1}$
for every finite integral basis $b$. The norm is on the base $\mathbb Z_p$,
not the normalized norm on $K_v$.

Definition A.3.1.2(3), (A.3.1.2), PDF p. 556, specifies the additive mass
by the inverse square root of the local different norm and the square
root of the discriminant norm. Lemma A.3.1.3 on that page uses the
local different norms in an aggregate product; it does not give the
placewise lattice calculation. Definition A.3.2.2(2), (A.3.2.2),
PDF p. 560, prescribes the same discriminant scale on the local
multiplicative units. Example A.3.1.10, (A.3.1.8), PDF p. 558, uses the
inverse different as a Fourier support. The result here supplies the
arithmetic equality, not the Fourier assertion or any Haar construction.
The source reading is provisional: Pinned Appendix A Markdown and
numbered PDF layout, not rendered pages.

Independent statement review: Yah session
`01a20254-2b9e-7515-a29a-c1ce3c00cc87`, child
`review-local-different` (agent `cfEiqXO`, read-only output
`d3ea7c0bb9d6918976c7fa202898554f8e062fa5`). The review distinguishes
$O_v$-submodules for the inverse different, $\mathbb Z_p$-linear
quotients for the index, the residue-field size from the residue
characteristic, and the discriminant norm from its square root.

Reproduce the warning-as-error build, kernel replay, and signature and
axiom comparison in the exact integration workspace:

```sh
go run ./cmd/godel audit-local "$CANDIDATE" \
  Lemmas.FiniteCompletionTraceIndex Lemmas.FiniteCompletionDifferentQuotient \
  Theorems.FiniteCompletionDifferentScale -- \
  Masullo.coe_finiteCompletionIntegersToTraceDual \
  Masullo.finiteCompletion_traceDual_eq_inv_differentIdeal \
  Masullo.finiteCompletionTraceDualQuotientEquiv \
  Masullo.finiteCompletionTraceDualQuotientEquiv_symm_mk \
  Masullo.finiteCompletionDifferentExponent \
  Masullo.finiteCompletion_differentIdeal_eq_maximalIdeal_pow \
  Masullo.finiteCompletion_differentIdeal_eq_maximalIdeal_pow_iff \
  Masullo.finiteCompletion_card_quotient_differentIdeal \
  Masullo.finiteCompletion_card_traceDual_quotient \
  Masullo.finiteCompletion_norm_discr_eq_inv_residueNorm_pow
```

### Checked extension of the global different

[`FiniteCompletionDifferentExtension.lean`](../../Proofs/Theorems/FiniteCompletionDifferentExtension.lean)
proves that for every finite place $v$ of a number field $K$, with
canonical completion map $i_v : \mathcal O_K\to O_v$ and residue
characteristic $p$,

$$
\operatorname{map}_{i_v}(\mathfrak D_{K/\mathbb Q})
  = \mathfrak d_{O_v/\mathbb Z_p},\qquad
 d_v=\operatorname{mult}_v(\mathfrak D_{K/\mathbb Q}),\qquad
 \|\operatorname{disc}_{\mathbb Z_p}(b)\|_p
  = q_v^{-\operatorname{mult}_v(\mathfrak D_{K/\mathbb Q})}.
$$

Here $q_v=\#(\mathcal O_K/v)$, $b$ is any finite $\mathbb Z_p$-basis
of $O_v$, and the norm is the **base** $p$-adic norm. The supporting
lemma specializes the checked codifferent comparison to the canonical
$p$-adic scalar action by equality of the two algebra maps. The main
proof identifies the extended inverse different with the local trace
dual and inverts in the fractional ideal rings. The checked extension
formula for integral ideals and uniqueness of the maximal-ideal power
then match the two exponents.

**Source and repair (provisional):** (A.3.1.2), PDF p. 556, prescribes
the additive mass using the local discriminant and different norms.
The proof of Lemma A.3.1.3 on the same page uses the product of the
local different norms as the global different norm, without giving
the extension-of-differents comparison. (A.3.2.2), PDF p. 560,
prescribes the same arithmetic scale for the multiplicative unit mass.
Lean supplies the missing placewise comparison. The Markdown and
numbered PDF layout were read, but not the rendered pages. This does
not yet construct the measures or compare their quotient normalizations.

Independent Yah statement review: Session
`01a2025c-7915-73f1-8e02-7f052f349642`, child
`different-extension-review` (agent `aPvQkjI`, read-only output
`44dbb28de2704aa21a7c1727be74c1b3b765c311`). The review elaborated the
three endpoint propositions and checked the scalar transport needed for
the supporting equality. It identified the fractional-ideal inverse
comparison as the missing step and ruled out an integrality hypothesis
on the completion integers.

Replay the built declarations and both modules:

```sh
go run ./cmd/godel audit-local "$CANDIDATE" \
  Lemmas.FiniteCompletionCanonicalTraceDual Theorems.FiniteCompletionDifferentExtension -- \
  Masullo.finiteCompletion_traceDual_eq_span_globalCodifferent \
  Masullo.map_globalDifferent_eq_finiteCompletionDifferent \
  Masullo.finiteCompletionDifferentExponent_eq_global_multiplicity \
  Masullo.finiteCompletion_norm_discr_eq_inv_globalDifferent_residueNorm_pow
```

The comparison now feeds the [Haar construction below](#checked-discriminant-normalized-multiplicative-haar).

### Checked discriminant-normalized multiplicative Haar

[`FiniteCompletionMultiplicativeHaar.lean`](../../Proofs/Theorems/FiniteCompletionMultiplicativeHaar.lean)
constructs Haar on every actual $K_v^\times$ by taking the compact open
image of $O_v^\times$ as the unit-mass calibrator and multiplying the
measure by a finite positive scalar. Its mass on that subgroup is

$$
\mu_v(O_v^\times)
 = (\sqrt{q_v^{\operatorname{mult}_v(D_K)}})^{-1}
 = \sqrt{\|\operatorname{disc}_{\mathbb Z_p}(b)\|_p}
$$

for every finite integral basis $b$. Haar uniqueness with that unit mass
is checked. Off the support of $D_K$ the mass is one, and its product
over any finite superset of the support is $|\operatorname{disc}K|^{-1/2}$.

[`DiscriminantNormalizedIdeleHaar.lean`](../../Proofs/Theorems/DiscriminantNormalizedIdeleHaar.lean)
uses those finite measures and `archimedeanCompletionHaar` in the checked
restricted-product construction. The resulting regular Haar measure on
the actual ideles is characterized among Borel measures by its comaps to
all open stages containing the different support. For every compact
Archimedean box $B$ with nonempty interior, the box with coordinates
$B$ at infinity and integral units at all finite places has mass

$$
\left(\bigotimes_{v\mid\infty}\mu_v\right)(B)
\,|\operatorname{disc}K|^{-1/2}.
$$

**Source and project proof (provisional):** Definition A.3.2.2(2),
(A.3.2.2), PDF p. 560, fixes the finite unit mass. The norm comparison
above proves that the scalar used to construct Haar is exactly the one
in that prescription, without choosing an integral basis. Lemma A.3.2.4,
(A.3.2.5), p. 560, asserts the restricted-product formula by reference
and notes the unit masses off a finite set. The Lean endpoint verifies
this finite-exception condition via the global different, constructs
the product with exact stage restrictions, and computes its calibration.
It does **not** identify this measure with the one defined by the quotient
volume in (A.3.2.1), pp. 559–560. The pinned Appendix A Markdown and
numbered PDF layout were read, but not the rendered pages.

Independent Yah statement review: Session
`01a20265-3820-7b1b-a9b3-689b6d12a219`, child `review-calibrated-haar`
(agent `ZBxOiCT`, read-only outputs
`685a2e4d961ff3c8aadffa3aab0de8dadb803b83` and
`4e319c1b05814ace319d9e0e3c966af39bb95dd7`). It reviewed the local
ambient group, basis and uniqueness statements, product of real masses,
all Borel hypotheses, and the equivalent stage formulation with the
support constructed internally rather than supplied as a parameter.

```sh
go run ./cmd/godel audit-local "$CANDIDATE" \
  Theorems.FiniteCompletionMultiplicativeHaar Theorems.DiscriminantNormalizedIdeleHaar -- \
  Masullo.finiteCompletionMultiplicativeHaar \
  Masullo.finiteCompletionMultiplicativeHaar_isHaarMeasure \
  Masullo.finiteCompletionMultiplicativeHaar_unitMass \
  Masullo.finiteCompletionMultiplicativeHaar_unitMass_eq_sqrt_discr \
  Masullo.finiteCompletionMultiplicativeHaar_eq \
  Masullo.finiteCompletionMultiplicativeHaar_unitMass_eq_one \
  Masullo.prod_finiteCompletionMultiplicativeHaar_unitMass \
  Masullo.exists_discriminantNormalizedIdeleHaar
```

### Checked discriminant-normalized Gaussian pairing above one

[`FiniteHeckeRamification.lean`](../../Proofs/Theorems/FiniteHeckeRamification.lean)
proves `exists_finset_isUnramifiedAt` for every continuous Mathlib
Hecke character, not just unitary ones. Appendix B.6.1.2, PDF p. 636,
recalls finite ramification without proving it there. Definition
3.4.3.2(3), (3.4.3.8), p. 152, uses it. The project proof restricts the
character to the empty stage's product of integral units, with
Archimedean coordinates one. A basic product neighborhood inside the
preimage of the complex disk of radius $1/2$ about one contains every
single-coordinate subgroup outside finitely many places. Iterating
squaring shows that no nontrivial subgroup can remain in that disk.

[`DiscriminantNormalizedIdeleHeckeGaussian.lean`](../../Proofs/Theorems/DiscriminantNormalizedIdeleHeckeGaussian.lean)
uses the finite union of ramification and different support and the
constructed Haar above. One $T$ and one regular Haar measure work for
all $s$ with $\Re s>1$. The exact stage restrictions hold whenever $S$
contains the different support, independently of the ramification.
The actual raw pairing (3.2.2.1), p. 124, with the Gaussian of Definition
3.4.3.2, p. 152, is absolutely integrable and equals the completed Euler
product (3.2.1.1)–(5), pp. 122–123, times $|\operatorname{disc}K|^{-1/2}$.
This comparison uses the [opposite angular weight](complex-gaussian-angular.md)
and retains the finite unit masses (A.3.2.2), p. 560. It is not the
ramified eigendistribution normalization (3.4.3.11), p. 153, and does not
identify the measure defined by the quotient volume (A.3.2.1), pp. 559–560.
These new locators were checked in Markdown and numbered PDF layout only;
the readings are provisional.

Independent Yah statement review: Session
`01a2026c-66a3-70b3-8159-55693cdc85b0`, child `review-normalized-gaussian`
(agent `PoPVArY`, read-only output `de40e5837b3f1c4810ff05a8b1c16b1fd29d08fe`).
Review confirmed the unrestricted ramification theorem, the fixed stage
and measure, the Borel hypotheses and comaps, and the correctly signed
angular weight and discriminant scalar for the raw comparison.

```sh
go run ./cmd/godel audit-local "$CANDIDATE" \
  Lemmas.ComplexMultiplicativeNeighborhood Theorems.FiniteHeckeRamification \
  Theorems.DiscriminantNormalizedIdeleHeckeGaussian -- \
  Masullo.complex_eq_one_of_norm_pow_sub_one_lt \
  Masullo.exists_finset_isUnramifiedAt \
  Masullo.exists_discriminantNormalizedIdeleHeckeGaussian_zetaIntegral
```

**Shared normalization input:** The [single-place section](single-place-norm.md#archimedean-log-section-on-ideles-and-classes)
now gives (A.2.2.10), PDF p. 547, and its descent in (A.1.3.6),
p. 542, on the actual ideles and class group. The next step is the
topological product splitting (A.2.2.12). Norm-one compactness and the
quotient Haar calibration remain separate obligations.

**Still open:** Meromorphic continuation, divisor data, and contour
growth in (B.4.2.1)–(4), the broader test class, general ramified Fourier terms,
and global trace. The [local conductor test](#primitive-prime-power-conductor-shells-over-mathbb-q_p)
checks the power for primitive rational prime-power conductors, not the
exponential input to the reflection.
Before using the eigenspace claim, reconcile the
[rendered pullback action](complex-gaussian-angular.md#the-weight-one-control-and-its-scope)
$T(f\circ m_g)$ in (3.4.3.1), p. 151, with (3.3.1.7), p. 130:
Left invariance makes the bilinear pairing transform by $c(g)^{-1}$,
not the printed $c(g)$. Replacing $m_g$ by $m_{g^{-1}}$ changes the
action, so later uses must be checked with the same convention.

## Reproduce the endpoint audit

For the completion Haar transports and actual Gaussian pairings:

```sh
go run ./cmd/godel audit-local "$CANDIDATE" \
  Lemmas.ArchimedeanCompletionHaar Theorems.RealGaussianMellin Theorems.ComplexGaussianMellin \
  Theorems.ArchimedeanCompletionGaussian -- \
  Masullo.complexTamagawaDensity_map_mul \
  Masullo.realCompletionHaar_map Masullo.complexCompletionHaar_map \
  Masullo.realCompletionHaar_isHaarMeasure Masullo.complexCompletionHaar_isHaarMeasure \
  Masullo.realCompletionGaussianPair Masullo.complexCompletionGaussianPair
```


From the integration workspace, use the
[local audit workflow](../../cmd/godel/README.md#checking-a-proof-candidate)
with the exact candidate ID:

```sh
go run ./cmd/godel audit-local "$CANDIDATE" \
  Lemmas.FiniteHeckeEulerBounds Theorems.FiniteHeckeEulerProduct -- \
  Masullo.finiteHeckeEulerFactor_hasProdLocallyUniformlyOn \
  Masullo.finiteHeckeEulerFactor_logDeriv \
  Masullo.finiteHeckeEulerProduct_logDeriv

go run ./cmd/godel audit-local "$CANDIDATE" \
  Lemmas.FiniteHeckeLocalNormalization Theorems.FiniteHeckeCharacterEulerProduct -- \
  Masullo.norm_uniformizer_eq_inv_finitePlaceNorm \
  Masullo.norm_finiteHeckeCoefficient_le_one \
  Masullo.finiteHecke_localPolynomial_eval_uniformizer \
  Masullo.finiteHecke_localPolynomial_eval_inv \
  Masullo.finiteHeckeEulerFactor_eq_one_of_ramified \
  Masullo.finiteHeckeCharacterEulerProduct_logDeriv
```

For the separate evaluations and the unchanged combined rational scalar
statement, replay both changed modules:

```sh
go run ./cmd/godel audit-local "$CANDIDATE" \
  Lemmas.CompactLogMellinInversion Theorems.FiniteHeckeRightLineInversion -- \
  Masullo.compactLogMellin_right_line_evaluation \
  Masullo.compactLogMellin_reflected_right_line_evaluation \
  Masullo.compactLogMellin_reflected_inversion \
  Masullo.finiteHecke_direct_right_line \
  Masullo.finiteHecke_reflected_right_line

go run ./cmd/godel audit-local "$CANDIDATE" \
  Lemmas.HeckeCharacterConjugate Theorems.FiniteHeckeRightLineInversion -- \
  Masullo.heckeConjugate \
  Masullo.heckeConjugate_unitary \
  Masullo.heckeConjugate_restrict_unit \
  Masullo.heckeConjugate_isUnramifiedAt_iff \
  Masullo.finiteHeckeCoefficient_conjugate \
  Masullo.finiteHecke_paired_right_line
```

For the shifted scalar factors and the preserved rational specialization:

```sh
go run ./cmd/godel audit-local "$CANDIDATE" \
  Lemmas.DigammaExponential Props.ArchimedeanGammaLogDerivative Props.GammaRealLogDerivative -- \
  Masullo.digamma_sub_one_eq_exponential_integral \
  Masullo.archimedeanGammaFactor_real \
  Masullo.archimedeanGammaFactor_complex \
  Masullo.analyticOnNhd_archimedeanGammaFactor \
  Masullo.logDeriv_archimedeanGammaFactor_eq_integral \
  Masullo.logDeriv_GammaReal_eq_integral
```

```sh
go run ./cmd/godel audit-local "$CANDIDATE" \
  Props.HeckeContourReflection Theorems.DirichletContourReflection -- \
  Masullo.completed_logDeriv_reflection \
  Masullo.completed_reflect_left_integral \
  Masullo.completedDirichlet_logDeriv_reflection \
  Masullo.completedDirichlet_reflect_left_integral
```

For the signed unit-coset transform and its exact nonvanishing shell:

```sh
go run ./cmd/godel audit-local "$CANDIDATE" \
  Theorems.PadicRamifiedThreeFourier -- \
  Masullo.padicRamifiedThreeTest \
  Masullo.padicRamifiedThree_fourier \
  Masullo.padicRamifiedThree_fourier_ne_zero_iff \
  Masullo.padicRamifiedThree_fourier_at_inv_ne_zero
```

For the one-parameter classification and Archimedean restriction:

```sh
go run ./cmd/godel audit-local "$CANDIDATE" Lemmas.OneParameterCharacter -- \
  Masullo.existsUnique_unitary_oneParameterCharacter

go run ./cmd/godel audit-local "$CANDIDATE" Theorems.ArchimedeanHeckeRestriction -- \
  Masullo.continuous_ideleClassGroup_ofCompletion \
  Masullo.continuous_archimedeanHeckeRestriction

go run ./cmd/godel audit-local "$CANDIDATE" Theorems.RealArchimedeanHeckeRestriction -- \
  Masullo.exists_archimedeanHeckeRestriction_real

go run ./cmd/godel audit-local "$CANDIDATE" Theorems.ComplexArchimedeanHeckeRestriction -- \
  Masullo.exists_archimedeanHeckeRestriction_complex
```

For the complex Gaussian pairing:

```sh
go run ./cmd/godel audit-local "$CANDIDATE" \
  Lemmas.ComplexGaussianPolar Theorems.ComplexGaussianMellin -- \
  Masullo.complexGaussianZetaDensity_integral
```

For the real Gaussian pairing:

```sh
go run ./cmd/godel audit-local "$CANDIDATE" \
  Lemmas.EvenRealIntegral Theorems.RealGaussianMellin -- \
  Masullo.even_real_integral Masullo.realGaussianZetaDensity_integral
```

For the completed product and split logarithmic derivative:

```sh
go run ./cmd/godel audit-local "$CANDIDATE" Theorems.CompletedHeckeEulerProduct -- \
  Masullo.localHeckeGammaFactor Masullo.localHeckeGammaFactor_real \
  Masullo.localHeckeGammaFactor_complex Masullo.completedHeckeEulerProduct \
  Masullo.completedHeckeEulerProduct_logDeriv
```

For the compact-log tested shifted pair:

```sh
go run ./cmd/godel audit-local "$CANDIDATE" \
  Lemmas.ArchimedeanGammaDomination Lemmas.CompactLogMellinInversion Props.ArchimedeanGammaRightLine -- \
  Masullo.integrable_archimedeanGamma_rightLine_product \
  Masullo.integrable_compactLogMellin_vertical_first_moment \
  Masullo.compactLogMellin_reflect \
  Masullo.compactLogMellin_archimedeanGamma_direct \
  Masullo.compactLogMellin_archimedeanGamma_reflected \
  Masullo.compactLogMellin_archimedeanGamma_pair
```

For the finite local zeta evaluations, replay both modules:

```sh
go run ./cmd/godel audit-local "$CANDIDATE" \
  Lemmas.FiniteLocalNormShell Theorems.FiniteHeckeLocalZeta -- \
  Masullo.finiteLocalUnitSet_eq_range \
  Masullo.finiteHeckeLocalZeta_unramified \
  Masullo.finiteHeckeLocalZeta_ramified
```
