module

public import Theorems.FiniteHeckeEulerProduct
public import Lemmas.FiniteHeckeLocalNormalization

/-!
# The finite Euler product of a unitary Hecke character

In (3.2.1.1), p. 122, Masullo evaluates the local character at a
uniformizer. The norm of a uniformizer is the inverse ideal norm, so
this gives the stated denominator with Mathlib's local polynomial.
Definition 3.2.1.4, (3.2.1.7), omits ramified places, which here have
unit Euler factors and zero series coefficients. The finite part of
(B.4.2.5)–(7), p. 615, is then the checked logarithmic derivative of
this product. This does not identify the product with `χ.LSeries` or
include the Archimedean factors.
-/

open IsDedekindDomain NumberField

namespace Masullo

variable {K : Type*} [Field K] [NumberField K]
local notation "Places" => HeightOneSpectrum (𝓞 K)
variable (χ : HeckeCharacter (𝓞 K) K)

/-- The coefficient in (3.2.1.7), extended by zero at omitted places. -/
@[expose] public noncomputable def finiteHeckeCoefficient (v : Places) : ℂ := by
  classical
  exact if χ.IsUnramifiedAt v then χ.localValue v else 0

/-- The coefficients of a unitary Hecke character satisfy the joint majorant's bound. -/
public theorem norm_finiteHeckeCoefficient_le_one
    (hχ : ∀ x : IdeleClassGroup (𝓞 K) K, ‖χ x‖ = 1) (v : Places) :
    ‖finiteHeckeCoefficient χ v‖ ≤ 1 := by
  classical
  by_cases h : χ.IsUnramifiedAt v
  · obtain ⟨π, hπ⟩ := (Valued.v : Valuation (v.adicCompletion K)
      (WithZero (Multiplicative ℤ))).exists_isUniformizer_of_isCyclic_of_nontrivial
    rw [finiteHeckeCoefficient, ite_eq_left h, h.localValue_eq π hπ,
      norm_heckeRestrict_of_unitary χ hχ v hπ.ne_zero]
  · simp [finiteHeckeCoefficient, h]

private theorem localPolynomial_eq (v : Places) :
    χ.localPolynomial v = 1 - Polynomial.C (finiteHeckeCoefficient χ v) * Polynomial.X := by
  classical
  by_cases h : χ.IsUnramifiedAt v <;> simp [HeckeCharacter.localPolynomial, finiteHeckeCoefficient, h]

/-- The normalized local denominator in (3.2.1.1), for any choice of uniformizer. -/
public theorem finiteHecke_localPolynomial_eval_uniformizer (v : Places) (s : ℂ)
    (h : χ.IsUnramifiedAt v) (π : v.adicCompletion K) (hπ : Valued.v.IsUniformizer π) :
    (χ.localPolynomial v).eval (Complex.exp (-s * (Real.log (finitePlaceNorm v) : ℂ))) =
      1 - χ.restrict v π * (‖π‖ : ℂ) ^ s := by
  classical
  rw [localPolynomial_eq, uniformizer_norm_cpow v π hπ s]
  simp [finiteHeckeCoefficient, h, h.localValue_eq π hπ]

/-- The inverse local polynomial evaluated at `q_v^(-s)` is the factor in (3.2.1.7).
In particular, the constant polynomial at a ramified place gives the unit factor. -/
public theorem finiteHecke_localPolynomial_eval_inv (v : Places) (s : ℂ) :
    ((χ.localPolynomial v).eval (Complex.exp (-s * (Real.log (finitePlaceNorm v) : ℂ))))⁻¹ =
      finiteHeckeEulerFactor (finiteHeckeCoefficient χ) v s := by
  rw [localPolynomial_eq]
  simp [finiteHeckeEulerFactor, finiteHeckeMonomial]

/-- A ramified place is omitted from (3.2.1.7): Its factor in the product is one. -/
public theorem finiteHeckeEulerFactor_eq_one_of_ramified (v : Places) (s : ℂ)
    (h : ¬χ.IsUnramifiedAt v) : finiteHeckeEulerFactor (finiteHeckeCoefficient χ) v s = 1 := by
  classical
  simp [finiteHeckeEulerFactor, finiteHeckeMonomial, finiteHeckeCoefficient, h]

/-- The finite product in (3.2.1.7), using Mathlib's local polynomials. -/
@[expose] public noncomputable def finiteHeckeCharacterEulerProduct (s : ℂ) : ℂ :=
  ∏' v : Places,
    ((χ.localPolynomial v).eval (Complex.exp (-s * (Real.log (finitePlaceNorm v) : ℂ))))⁻¹

private theorem finiteHeckeCharacterEulerProduct_eq :
    finiteHeckeCharacterEulerProduct χ = finiteHeckeEulerProduct (finiteHeckeCoefficient χ) := by
  funext s
  unfold finiteHeckeCharacterEulerProduct finiteHeckeEulerProduct
  exact tprod_congr fun v ↦ finiteHecke_localPolynomial_eval_inv χ v s

/-- The finite product for a unitary Hecke character converges uniformly on each
closed half-plane `a ≤ Re s` with `1 < a` (B.1.1). The same majorant bounds the
absolute deviations from one at every argument in that half-plane. -/
public theorem finiteHeckeCharacterEulerProduct_convergesOn
    (hχ : ∀ x : IdeleClassGroup (𝓞 K) K, ‖χ x‖ = 1) {a : ℝ} (ha : 1 < a) :
    HasProdUniformlyOn
      (fun (v : Places) s ↦
        ((χ.localPolynomial v).eval (Complex.exp (-s * (Real.log (finitePlaceNorm v) : ℂ))))⁻¹)
      (finiteHeckeCharacterEulerProduct χ) {s : ℂ | a ≤ s.re} ∧
    ∃ M : Places → ℝ, Summable M ∧ ∀ v s, a ≤ s.re →
      ‖((χ.localPolynomial v).eval (Complex.exp (-s * (Real.log (finitePlaceNorm v) : ℂ))))⁻¹
        - 1‖ ≤ M v := by
  rw [finiteHeckeCharacterEulerProduct_eq]
  simp only [finiteHecke_localPolynomial_eval_inv]
  exact ⟨finiteHeckeEulerFactor_hasProdUniformlyOn ha (norm_finiteHeckeCoefficient_le_one χ hχ),
    finiteHeckeEulerFactor_norm_sub_one_majorant ha (norm_finiteHeckeCoefficient_le_one χ hχ)⟩

/-- The finite-place part of (B.4.2.5)–(7) for a unitary Hecke character. -/
public theorem finiteHeckeCharacterEulerProduct_logDeriv
    (hχ : ∀ x : IdeleClassGroup (𝓞 K) K, ‖χ x‖ = 1) {s : ℂ} (hs : 1 < s.re) :
    finiteHeckeCharacterEulerProduct χ s ≠ 0 ∧
    DifferentiableAt ℂ (finiteHeckeCharacterEulerProduct χ) s ∧
    HasSum (finiteHeckeTerm (finiteHeckeCoefficient χ) s)
      (-logDeriv (finiteHeckeCharacterEulerProduct χ) s) := by
  rw [finiteHeckeCharacterEulerProduct_eq]
  exact finiteHeckeEulerProduct_logDeriv (norm_finiteHeckeCoefficient_le_one χ hχ) hs

end Masullo
