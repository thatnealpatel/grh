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

## Next: Recognize the actual Archimedean restrictions

The scalar repair still takes $b$ and $\tau$ as parameters. To use it
in (3.2.1.3)–(5), p. 123, obtain them from the restriction of a unitary
Hecke character. Pinned `HeckeCharacter.restrict` is finite-only, but
`IdeleClassGroup.ofCompletion` gives the infinite-place hom on units
and `InfinitePlace.Completion.ringEquivRealOfIsReal` identifies a real
completion. Prove continuity of the restriction along that inclusion
before using continuous character classification; the inclusion is
currently a `MonoidHom`.

**Runnable shared substep:** For continuous $h:\mathbb R\to\mathbb C$
with $h(0)=1$, $h(t+u)=h(t)h(u)$, and $|h|=1$, prove that there is a
unique real $\tau$ with $h(t)=e^{i\tau t}$. Use an interval $[0,r]$
where $\Re h>1/2$, so $J=\int_0^r h(u)\,du\ne0$. Then
$h(t)J=\int_t^{t+r}h(u)\,du$ and the fundamental theorem of calculus
gives $h'=kh$ for $k=(h(r)-1)/J$. Differentiate $e^{-kt}h(t)$, and use
unit modulus to get $\Re k=0$. Apply first on the positive real ray
via log, and recover parity from the value at $-1$. The same lemma on
the complex angular circle, pulled back along `Circle.exp`, yields
integer weight by $2\pi$-periodicity; treat complex radial exponents
in the squared-norm scale of §A.1, p. 539. This is a classification
obligation, not a consequence of the scalar Gamma calculation.

**Still open:** Actual character identification and the assembled
completed product, continuation, divisor data, and contour growth
in (B.4.2.1)–(4). The local pair does not establish the full test class
of (B.4.2.15) or (17), the ramified Fourier terms, or the global trace
comparison. See the separate
[local conductor obligation](#open-ramified-local-conductor-power-in-the-general-reflection)
for the missing epsilon factor upstream of the checked reflection.

## Reproduce the endpoint audit

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
