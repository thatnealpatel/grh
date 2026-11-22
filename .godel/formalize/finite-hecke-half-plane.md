# The finite Hecke Euler product on the closed right half-planes

This handoff concerns the chapter-01 §1.2 notation for the finite part of the
completed Hecke product, including the convergence stated in Appendix B.1.1.
It does not concern convergence on the line `Re(s) = 1`.

## Printed statement and normalization

Edition read: Masullo, *The Music of the Primes*, 940 pages, SHA-256
`e039d3f6cf0a4b14f03c7edb85097752dd65c0a2fe543c76fe992be234f97bf5`.
The writer checked the PDF bytes against the [edition pin](../sources/masullo/README.md),
located the passages with `pdftotext -layout`, and inspected their rendered
pages and raster crops. All page numbers below are both printed page numbers
and one-based PDF ordinals. For example, to rerender the appendix statement
from a verified local copy, use `pdftoppm -f 588 -l 588 -r 150 "$pdf" /tmp/masullo-b11`.

- **§1.2 opening, p. 12:** for `χ ∈ Ĉ_F`, `L(s,χ)` is the completed Hecke
  function. The unnumbered display on `s ∈ ℂ_{>1}` defines the finite part
  `L_f(s,χ) = ∏_{v ∈ Σ_{F,f}} L_v(χ_v |·|_v^s)`. “Finite” describes the
  places, not the cardinality of the product. This opening supplies no proof.
- **(3.1.1.2), p. 119; §3.1.2 and §3.1.2.1, p. 120:** the abscissa of
  `χ |·|_F^s` is `Re(s)` for a unitary base point `χ`. The local restriction
  is via insertion at that place followed by the quotient to the idele class
  group. For a finite place, `q_v = |π_v|_v^{-1}` for any uniformizer `π_v`.
- **§3.2.1, (3.2.1.1), p. 122:** write `c_v = χ_v |·|_v^s`, with `S_χ`
  the finite ramified set. Outside it at a finite place, `χ(p_v)` is the
  uniformizer-independent `χ_v(π_v)`. The display is
  `1 − χ(p_v) q_v^{-s} = 1 − c_v(π_v)`.
- **Lemma 3.2.1.1 and Definition 3.2.1.2, p. 123:** (3.2.1.2) multiplies the
  inverse denominators outside `S_χ ∪ S_∞` by `Γ_F(s,χ)`, the product over
  the infinite places in (3.2.1.3). The lemma says absolute convergence,
  uniformly on compact subsets of the component of abscissa greater than one.
  The proof paragraph cites comparison with the Riemann zeta Euler product
  on its half-plane of absolute convergence, deferring details to [RV].
  Definition 3.2.1.2 uses that product to define `L(s,χ)` there.
- **(3.2.1.4)–(5), p. 123:** the real displays have the two parities,
  `π^{-s/2} Γ(s/2)` and `π^{-(s+1)/2} Γ((s+1)/2)`; the complex display is
  `(2π)^{-(s+|n|/2)} Γ(s+|n|/2)` with no extra factor of 2. The associated
  prose prints `(r,θ) ↦ r^s e^{inθ}` for `χ_{n,s}`; if `r` means the
  ordinary polar radius, its exponent is not the exponent of the normalized
  complex norm `r²` (cf. Appendix A.1 opening, p. 539, on the square of the
  complex Euclidean norm). The existing Lean Gamma factors take the variable
  and radial frequency in the normalized norm, not ordinary radius: e.g.,
  an ordinary-radius unitary exponent `iη` contributes the shift `iη/2`
  in a squared-norm parameter. The finite-place convergence result does not
  rely on identifying those two radial conventions or change the existing
  Archimedean factors.
- **Definition 3.2.1.4, end of p. 123 and start of p. 124:** (3.2.1.7)
  is `L_f(s,χ) = ∏_{v ∈ Σ_{F,f} − S_χ} (1 − χ(p_v)(Np_v)^{-s})^{-1}`,
  absolutely and locally uniformly convergent.
- **Appendix B.1.1 opening, p. 588:** the displayed product is over prime
  ideals `p ⊂ O_F`, with `χ(p) := 0` if ramified. The line immediately
  below the display says absolute convergence for `Re(s) > 1` and uniform
  convergence on `Re(s) ≥ 1 + ε` for each `ε > 0`. Uniformity on the entire
  closed half-plane, not only on compact subsets, is therefore printed.

## Checked construction

For `[Field K] [NumberField K]`, use Mathlib's actual
`HeckeCharacter (𝓞 K) K`, a continuous monoid homomorphism out of
`IdeleClassGroup (𝓞 K) K` into `ℂ`. The hypothesis `∀ x, ‖χ x‖ = 1`
is precisely the unitary condition, with no extra conductor or local
character assumptions. `HeightOneSpectrum (𝓞 K)` indexes the nonzero prime
ideals and `finitePlaceNorm v` is `v.asIdeal.absNorm`, cast to `ℝ`.
Write `E v s` for the inverse evaluation of `χ.localPolynomial v` at
`exp(-s log q_v)`. The existing `finiteHecke_localPolynomial_eval_uniformizer`
uses *any* uniformizer of an unramified place and
`norm_uniformizer_eq_inv_finitePlaceNorm` / `uniformizer_norm_cpow` give the
normalized absolute value in that expression. At a ramified place,
`finiteHecke_localPolynomial_eval_inv` and
`finiteHeckeEulerFactor_eq_one_of_ramified` give `E v s = 1`. Thus one need
not invoke finiteness of the ramified set to pass to the all-place product.

The public result `Masullo.finiteHeckeCharacterEulerProduct_convergesOn`
gives, for every `a > 1`, `HasProdUniformlyOn E (finiteHeckeCharacterEulerProduct χ)
{s | a ≤ s.re}` and `∃ M, Summable M ∧ ∀ v s, a ≤ s.re → ‖E v s − 1‖ ≤ M v`.
The target is the existing infinite product, not a separate limit definition.
The partial products are indexed by all finite subsets of places ordered by
inclusion. Given any individual `s` with `1 < s.re`, take `a = s.re` and use
summable comparison to obtain `Summable (fun v ↦ ‖E v s − 1‖)`.

Here is the convergence argument, independent of the completion. For
coefficients `z v` of norm at most one, put `w = z v exp(-s log q_v)`.
On `Re(s) ≥ a > 1`, `‖w‖ ≤ q_v^{-a} ≤ 1/2`, so the factors `(1−w)^{-1}`
are nonzero and `‖(1−w)^{-1} − 1‖ ≤ 2 q_v^{-a}`. The project proves the
summability of this majorant by a subseries of the accepted
`summable_finitePlace_log_powers` (it uses ideal counting and `log q_v ≥ log 2`,
not continuation of a Hecke function). With `u_v = E_v − 1`, the same bound
is eventually at most `1/2` in the cofinite filter; the uniform estimate for
`log(1+u_v)` there makes the net of logarithm sums uniformly convergent.
Uniform convergence alone would not justify exponentiating on the unbounded
half-plane. The real part of each logarithm is at most `‖E_v − 1‖`, since
`log ‖E_v‖ ≤ ‖E_v‖ − 1 ≤ ‖E_v − 1‖`. Thus the real part of the sum is
bounded above by the sum of the majorant; Mathlib's
`hasProdUniformlyOn_of_clog` exponentiates uniformly and identifies the limit
with the pointwise `tprod`. The earlier compact-uniform result is now a
restriction of this theorem. For `χ`, `norm_finiteHeckeCoefficient_le_one`
supplies the coefficient hypothesis from unitarity and the local formulas
transport the conclusions to `E`.

The existing `Masullo.completedHeckeEulerProduct` uses *this same* finite
product times `∏ v : InfinitePlace K, localHeckeGammaFactor χ hχ v s` by
definition. Its `localHeckeGammaFactor_real` and `localHeckeGammaFactor_complex`
use the restrictions of the actual character, with real parity and its
radial shift or complex absolute angular weight and normalized radial shift.
No claim is made here about uniformity of the completed partial-product net
on an unbounded set, equality to a global zeta integral or to `χ.LSeries`,
continuation, the 1-line, or zeros. The assigned definition and finite-place
convergence require none of those assertions.

## Reproduction

Owning coordinator Yah session: `01a205a3-36c7-7d6c-bd2e-cc1de919806b`.
Its campaign handoff is the durable reference for the exact integrated
candidate and base, build results, built signatures and axiom reports,
ordinary-import client result, independent review, and adoption disposition.
The writer checks below are not integration or adoption checks.

Writer base: `b066a806e08fdcc782c1dd91fcdd7c0207b9bec1`. Lean v4.36.0; no
Lean/Lake pins changed. The writer ran this build successfully (8019 jobs):

```sh
lake build --wfail +Lemmas.FiniteHeckeEulerBounds +Theorems.FiniteHeckeEulerProduct \
  +Theorems.FiniteHeckeCharacterEulerProduct +Theorems.FiniteHeckeLocalZeta \
  +Theorems.HeckeDirichletFactorization +Theorems.FiniteHeckeEulerProductLowerBound \
  +Theorems.FiniteHeckeRightLineInversion +Theorems.CompletedHeckeEulerProduct
```

Run the Lean block below as a fresh scratch file with `lake env lean`. It uses
ordinary imports and gets the asserted finite-subset uniform limit, pointwise
absolute convergence, literal local factors, and completion identity for a
parameter of actual Mathlib character type. All listed axiom reports in the
writer workspace were `[propext, Classical.choice, Quot.sound]`.

```lean
import Lemmas.FiniteHeckeEulerBounds
import Theorems.FiniteHeckeCharacterEulerProduct
import Theorems.CompletedHeckeEulerProduct

#check @Masullo.finiteHeckeEulerFactor_norm_sub_one_majorant
#print axioms Masullo.finiteHeckeEulerFactor_norm_sub_one_majorant
#check @Masullo.finiteHeckeEulerFactor_hasProdUniformlyOn
#print axioms Masullo.finiteHeckeEulerFactor_hasProdUniformlyOn
#check @Masullo.finiteHeckeEulerFactor_hasProdLocallyUniformlyOn
#print axioms Masullo.finiteHeckeEulerFactor_hasProdLocallyUniformlyOn
#check @Masullo.finiteHeckeCharacterEulerProduct_convergesOn
#print axioms Masullo.finiteHeckeCharacterEulerProduct_convergesOn
#check @Masullo.finiteHeckeCharacterEulerProduct_logDeriv
#print axioms Masullo.finiteHeckeCharacterEulerProduct_logDeriv
#check @Masullo.finiteHecke_localPolynomial_eval_uniformizer
#print axioms Masullo.finiteHecke_localPolynomial_eval_uniformizer
#check @Masullo.finiteHeckeEulerFactor_eq_one_of_ramified
#print axioms Masullo.finiteHeckeEulerFactor_eq_one_of_ramified
#check @Masullo.completedHeckeEulerProduct
#print axioms Masullo.completedHeckeEulerProduct

open IsDedekindDomain NumberField Masullo

variable {K : Type*} [Field K] [NumberField K]
variable (χ : HeckeCharacter (𝓞 K) K)
local notation "Places" => HeightOneSpectrum (𝓞 K)
local notation "E" => fun (v : Places) (s : ℂ) ↦
  (Polynomial.eval (Complex.exp (-s * (Real.log (finitePlaceNorm v) : ℂ)))
    (HeckeCharacter.localPolynomial χ v))⁻¹

example (hχ : ∀ x : IdeleClassGroup (𝓞 K) K, ‖χ x‖ = 1) {ε : ℝ} (hε : 0 < ε) :
    TendstoUniformlyOn (fun F : Finset Places ↦ fun s : ℂ ↦ ∏ v ∈ F, E v s)
      (finiteHeckeCharacterEulerProduct χ) Filter.atTop {s : ℂ | 1 + ε ≤ s.re} :=
  (finiteHeckeCharacterEulerProduct_convergesOn χ hχ (lt_add_of_pos_right 1 hε)).1.tendstoUniformlyOn

example (hχ : ∀ x : IdeleClassGroup (𝓞 K) K, ‖χ x‖ = 1) {s : ℂ} (hs : 1 < s.re) :
    HasProd (fun v : Places ↦ E v s) (finiteHeckeCharacterEulerProduct χ s) ∧
    Summable (fun v : Places ↦ ‖E v s - 1‖) := by
  obtain ⟨hp, M, hM, hbound⟩ := finiteHeckeCharacterEulerProduct_convergesOn χ hχ hs
  exact ⟨hp.hasProd (show s.re ≤ s.re from le_rfl),
    hM.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun v ↦ hbound v s le_rfl)⟩

example (v : Places) (s : ℂ) (hv : ¬χ.IsUnramifiedAt v) : E v s = 1 := by
  dsimp only
  rw [finiteHecke_localPolynomial_eval_inv, finiteHeckeEulerFactor_eq_one_of_ramified χ v s hv]

example (v : Places) (s : ℂ) (hv : χ.IsUnramifiedAt v)
    (π : v.adicCompletion K) (hπ : Valued.v.IsUniformizer π) :
    E v s = (1 - χ.restrict v π * (‖π‖ : ℂ) ^ s)⁻¹ := by
  dsimp only
  rw [finiteHecke_localPolynomial_eval_uniformizer χ v s hv π hπ]

example (hχ : ∀ x : IdeleClassGroup (𝓞 K) K, ‖χ x‖ = 1) (s : ℂ) :
    completedHeckeEulerProduct χ hχ s =
      (∏ v : InfinitePlace K, localHeckeGammaFactor χ hχ v s) *
        finiteHeckeCharacterEulerProduct χ s := rfl
```
