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

## Next: Identify the reflected coefficients of the conjugate character

The reflected term in (B.4.2.7), (B.4.2.11), p. 615, and (B.4.2.17),
p. 616, uses $\bar\chi$, not a free character. Construct it by
postcomposing the continuous multiplicative map `HeckeCharacter`
with complex conjugation. Prove it is unitary when $\chi$ is, has
the same `IsUnramifiedAt` predicates, and satisfies
`finiteHeckeCoefficient (conjugate χ) v = conj (finiteHeckeCoefficient χ v)`
for every place. Use `HeckeCharacter.isUnramifiedAt_iff` on local
units and `IsUnramifiedAt.localValue_eq` at a common uniformizer;
`MulChar.ofUnitHom_coe` controls restriction on local units, and the
omitted places have two zero coefficients. Instantiate the reflected
endpoint and combine the two finite integrals for this single pair.
This is runnable without analytic continuation or a functional equation.

**Still open:** The Archimedean factors in (3.2.1.3)–(5), the completed
product, continuation, divisor and conductor data, and contour growth
premises in (B.4.2.1)–(4) do not follow from these finite evaluations.
Neither do the ramified Fourier terms or the global trace comparison.
For the contour, the cited (3.2.1.6), p. 123, gives an everywhere
nonvanishing entire epsilon factor, not its constant logarithmic
derivative on its own. Away from zeros and poles, differentiation
of $L(1-s,\bar\chi)=\epsilon(s,\chi)L(s,\chi)$ gives
$(L'/L)(s,\chi)=-(L'/L)(1-s,\bar\chi)-\epsilon'/\epsilon$.
The provisional extraction of (B.4.2.3), p. 614, has a plus sign
on the reflected derivative. The consuming contour subtracts the
left upward integral before substituting $t\mapsto -t$, yielding
a plus on the new upward reflected leg in (B.4.2.4). The conductor
term still needs a checked epsilon formula with the correct sign.

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
```
