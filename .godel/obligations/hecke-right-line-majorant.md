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

### Open: Ramified local conductor power in the general reflection

The next general conductor obligation is not another reflection lemma.
At a ramified finite place, both local Euler factors are one, so
(3.3.1.32), p. 136, specialized to the place, requires
$\rho_v(c)=\epsilon_v(c)$. On the norm-twist line
$c=\chi_v|\cdot|_v^s$, the extracted (3.3.1.30), p. 136, puts only
$N(\mathfrak d_v)^{s-1/2}$ outside a Gauss sum with no displayed
$s$-dependence, whereas the ramified $\rho_v$ formula at p. 133 and
(3.3.2.24), p. 141, puts $N(\mathfrak d_v\mathfrak f_v)^{s-1/2}$
outside the root number. The factor $N(\mathfrak f_v)^{s-1/2}$
cannot be absorbed into a constant when $\mathfrak f_v$ is nontrivial.
This is a provisional mismatch of the two local formulas, not a
reading of the rendered typography or a disproof of the functional
equation. On the unramified and Archimedean components, (3.3.1.28)–(29),
p. 135, supplies the different powers and constant phases, respectively.

**Runnable control:** Start at $\mathbb Q_3$ with the nontrivial
character of $(\mathbb Z/3\mathbb Z)^\times$ extended by $\chi_v(3)=1$.
In (3.3.1.7), p. 130, take the unit-supported test
$f(u)=\chi_v(u)^{-1}$. Compute its additive Fourier transform on the
shell $3^{-1}\mathbb Z_3^\times$ and show it vanishes off that shell.
Using the same Haar measure on both multiplicative integrals, compare
$Z_v(f,\chi_v|\cdot|_v^s)$ and
$Z_v(\widehat f,\chi_v^{-1}|\cdot|_v^{1-s})$ and check their ratio
against $3^{s-1/2}\rho_0$ with constant $\rho_0\ne 0$. This separates
the two printed formulas since the different is trivial but the
conductor norm is $3$. Generalizing the shell computation and assembling
it for the actual completed Hecke function in (3.2.1.6) must still
prove $\epsilon(s)=C\exp(\log(A_\chi)(s-1/2))$ with
$A_\chi=|N(\mathfrak d_{F/\mathbb Q})|N(\mathfrak f_\chi)$ in the
manuscript's normalization. The Lean reflection needs only the germ of
this equality where the contour meets ordinary nonzero points.

**Unadopted modulus-three recovery (prior handoff):** The reviewed
`Proofs/Theorems/PadicRamifiedThreeFourier.lean` is preserved with the
note draft in `1080bf8534b18b6574115607db70f09046e97d73`, based on
`a575167bc66f178a8bc4d014d69e692f50fc6a80`; the independently
elaborated writer output is `674ae752f7fbcc647c9e93bd55b7dd6f582a838a`.
It checks the signed unit-coset transform at every frequency and
nonvanishing exactly on $3^{-1}\mathbb Z_3^\times$. The writer module
was kernel-replayed with only the three allowed axioms. The exact Gauss
phase and the ratio $\sqrt{3}$ of the two forward-over-reflected values
(with the real Gamma ratio removed) are ordinary calculations. Prior
review verified rendered pp. 136 and 141, (3.3.1.30), (3.3.1.32), and
(3.3.2.24); the product norm on p. 120 and constant real epsilon rule
at (3.3.1.28), p. 135, remain provisional. Integration of the saved
patch at `0ae987b585b5254b0e4920098e74eec919aba5b0` conflicted in this
note and was not audited or adopted. Recover the needed paths on a
fresh accepted base, preserving the intervening Gaussian work and note
updates, then run the exact-candidate audit and fresh-import checks.
This recovery is separate from the global sign result and does not
assemble the general conductor.

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

The local zeta integral in (3.3.1.7), p. 130, is bilinear in the
integrand factors $f$ and $c$: It integrates $f(z)c(z)$, not
$f(z)c(z)^{-1}$ or $f(z)\overline{c(z)}$. The global integral in
(3.2.2.1), §3.2.2, uses the same orientation. On the provisional
Markdown and layout reading, the test in (3.4.3.5)–(6), p. 152, has
angular weight $m$ for the input angular character of weight $m$.
But (3.4.3.12)–(13), p. 153, would evaluate that test at the *same*
character to give the nonzero factor (3.2.1.5). For a direct control,
take $m=1$, $s=2$, and $\tau=0$. Rotation by $i$ multiplies the
integrand by $-1$, so Haar invariance forces its absolutely convergent
integral to vanish. The scalar factor on p. 123 does not vanish there.
This is a text-based mathematical mismatch, not a rendered-page
finding or a checked Lean counterexample.

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

In the provisional Markdown and PDF-layout reading, (3.4.3.7)–(8),
p. 152, supply the two tests, and (3.3.1.7), p. 130, uses the local
multiplicative Tamagawa measure in the bilinear pairing. But
(A.3.2.2), p. 560, sets its unit mass to the local discriminant factor,
which need not be one even for an unramified **character**. Combining
(3.4.3.10)–(11) with (3.4.3.13), p. 153, would instead give the Euler
factor without this scalar. The repair at the checked pairings is to
retain the mass, or divide the test by it if the desired value is the
Euler factor. This local result does not construct the Tamagawa measure,
evaluate its discriminant mass in Lean, or establish the meromorphic
eigendistribution identity. Independent Yah statement review: `mlDzIRC`
(output `f48eaa338965ce0b79cba685588b9017d0f07526`). No rendered-page
verification is claimed.

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

The real tests of (3.4.3.3)–(4), p. 152, need no change. The provisional
same-weight reading of (3.4.3.5)–(6), p. 152, would give zero in the complex
weight-one control, not the nonzero value required by (3.4.3.12)–(13),
p. 153. At the scalar evaluation, `complexGaussianZetaDensity_integral`
uses the opposite angular weight in the same coordinate as the character.
The transferred result is pointwise in $s$ on the open half-plane, not
uniform down to $\Re s=0$ and not a distribution-valued continuation.
Independent Yah statement and text review: `ZTZcZfz` (output
`28497fba430c60d17edeb89e1d7540dbe164c462`). The pinned Markdown and PDF
layout were checked, but no rendered-page verification is claimed.

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

### Next: Identify the restricted-product zeta pairing

Construct the Haar measure with the exact stage restrictions prescribed
by (A.3.2.5), p. 560, for the checked embeddings. Start with given local
Haar measures and a finite set $E$ such that the integral-unit mass is
one outside $E$. For every $S\supseteq E$, prove that the comap is the
product of the full Archimedean and active finite factors, and the
product probability of the pulled-back integral-unit restrictions off
$S$. Do not normalize away the masses of (A.3.2.2) inside $E$: On a
calibration product with all finite coordinates integral units, the
mass must include $\prod_{v\in E}\mu_v(\mathcal O_v^\times)$ times its
Archimedean mass. This factor is independent of $S$. This suggests
scaling upstairs Haar by one common positive compact box and applying
`Measure.IsHaarMeasure.comap` and `Measure.haarMeasure_eq_iff` on each
stage, rather than gluing measures. `RationalIdeleFiniteStageHaar` is a
comparison pattern, not the general-field result. Establishing the
actual discriminant masses and their finite exceptional support for
(A.3.2.2), and identifying the product with the separate quotient
normalization (A.3.2.1), are distinct obligations. Character ramification
is not the exceptional set for these masses.

Then use the local pairings on a tensor test, increasing the stage, to
identify the absolutely integrable global zeta pairing for $\Re s>1$,
with the product of those masses or with the corresponding scaled tests.

**Still open:** Meromorphic continuation, divisor data, and contour
growth in (B.4.2.1)–(4), the broader test class, ramified Fourier terms,
and global trace. The [local conductor obligation](#open-ramified-local-conductor-power-in-the-general-reflection)
remains upstream of the checked reflection. Before using the eigenspace
claim, reconcile the provisional pullback action $T(f\circ m_g)$ in
(3.4.3.1), p. 151, with (3.3.1.7), p. 130: Left invariance makes the
bilinear pairing transform by $c(g)^{-1}$ under this pullback. Replacing
$m_g$ by $m_{g^{-1}}$ changes the action, so later uses must be checked
with the same convention.

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
