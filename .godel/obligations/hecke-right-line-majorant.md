# An absolute majorant for the Hecke right line

**Scope:** The finite Euler product differentiation, two-index
summation, and integration in (B.4.2.5)–(9), for any number field,
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

## Next: Evaluate the two finite right-line integrals

In (B.4.2.10)–(11), p. 615, Masullo invokes Mellin inversion to turn
both vertical integrals into point samples. Check the extracted
constants and orientation against an upward contour with
$ds=i\,dt$ and normalization $1/(2\pi i)$ in (B.4.2.4). A runnable
project obligation for any number field is as follows. Take
$a>1$, $s=a+it$, $\Phi(s)=\int_{\mathbb R}g(x)e^{sx}\,dx$ for smooth
compactly supported $g$, and let $y=m\log q_v$ with $m=k+1$.
Separate the two right-line profiles, $g(x)e^{ax}$ and
$g(-x)e^{(a-1)x}$. For the two weights $\Phi(s)$ and $\Phi(1-s)$,
respectively, show that integrating $e^{-sy}$ with $dt/(2\pi)$
gives $g(y)$ and $e^{-y}g(-y)$. This gives a common normalization,
with no relative minus sign at the scalar inversion step. The
negative sign on each prime-power term comes from the logarithmic
derivatives. Apply `finiteHecke_right_line_integrals` separately to
the two coefficient families and use the character theorem to obtain
the finite-part formula as an absolutely summable joint series. The
two families can be independent unitary Hecke characters at this
stage; identifying the reflected one with the conjugate via the
functional equation is not needed for these right-line evaluations.

Start from `Lemmas.CompactLogMellinInversion` and
`compactLogMellin_prime_power_evaluation` in
`Theorems.RationalExplicitFormulaFinitePlaces`. Those give the
Fourier rescaling and inversion at $a=2$ for the **sum** of the two
weights; do not apply the summed identity with a single coefficient
when the characters differ. `compactLogMellin_vertical_decay` in
`Props.CompactLogMellin` controls both profiles on any fixed pair of
lines. The proposed step covers smooth compact log tests, not the
full test class in Theorem B.4.2.2. The shifted test convention of
(B.4.2.17) uses $g(x)=e^{-x/2}\varphi(e^x)$, so both samples then
have the factor $q_v^{-m/2}$.

**Still open:** The Archimedean factors in (3.2.1.3)–(5), completed
product, continuation, divisor and conductor data, and contour
growth premises in (B.4.2.1)–(4) are not provided by the finite series.
Neither are the ramified Fourier terms or the global trace
comparison. For the contour reflection, check the orientation of
(3.2.1.6) against (B.4.2.3): Differentiating
$L(1-s,\bar\chi)=\epsilon(s,\chi)L(s,\chi)$ gives a minus sign on the
reflected logarithmic derivative before contour reversal.

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
