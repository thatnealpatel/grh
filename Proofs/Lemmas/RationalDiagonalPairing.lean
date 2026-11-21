module

public import Mathlib.Topology.Algebra.PontryaginDual
public import Lemmas.RationalIntegralAdeles

import Theorems.RationalAdeleAnnihilator

/-! # Finite tests for the rational diagonal pairing -/

open NumberField IsDedekindDomain
open scoped BigOperators

namespace Masullo

local notation "A" => AdeleRing (𝓞 ℚ) ℚ
local notation "D" => rationalDiagonal
local notation "R" => Multiplicative D
local notation "ι" => algebraMap ℚ A

private noncomputable def phase (x : A) : Circle :=
  ⟨rationalAdeleAddChar x, mem_sphere_zero_iff_norm.mpr (norm_rationalAdeleAddChar x)⟩

private theorem continuous_phase : Continuous phase :=
  continuous_rationalAdeleAddChar.subtype_mk _

private theorem phase_add (x y : A) : phase (x + y) = phase x * phase y :=
  Circle.coe_injective (rationalAdeleAddChar.map_add_eq_mul x y)

/-- Pair with an adele and restrict the resulting character to the rational diagonal. -/
public noncomputable def rationalAdeleRestrictChar : A →+ Additive (PontryaginDual R) where
  toFun a := Additive.ofMul ({
    toFun := fun r : R ↦ phase (a * (r.toAdd : A))
    map_one' := Circle.coe_injective (by
      change rationalAdeleAddChar (a * 0) = 1
      simp)
    map_mul' := fun r s ↦ by
      change phase (a * ((r.toAdd : A) + (s.toAdd : A))) = _
      rw [mul_add, phase_add]
    continuous_toFun := continuous_phase.comp <| continuous_const.mul continuous_subtype_val
  } : R →ₜ* Circle)
  map_zero' := PontryaginDual.ext fun _ ↦ Circle.coe_injective (by
    change rationalAdeleAddChar (0 * _) = 1
    simp)
  map_add' a b := PontryaginDual.ext fun r ↦ by
    change phase ((a + b) * (r.toAdd : A)) = phase (a * (r.toAdd : A)) * _
    rw [add_mul, phase_add]
    rfl

@[simp] public theorem rationalAdeleRestrictChar_apply (a : A) (r : R) :
    ((rationalAdeleRestrictChar a).toMul r : ℂ) = rationalAdeleAddChar (a * (r.toAdd : A)) := by
  rw [rationalAdeleRestrictChar]
  rfl

public theorem continuous_rationalAdeleRestrictChar : Continuous rationalAdeleRestrictChar := by
  change Continuous (fun a ↦ (rationalAdeleRestrictChar a).toMul : A → PontryaginDual R)
  apply ContinuousMonoidHom.continuous_of_continuous_uncurry
  exact continuous_phase.comp <| continuous_fst.mul (continuous_subtype_val.comp continuous_snd)

public theorem ker_rationalAdeleRestrictChar : rationalAdeleRestrictChar.ker = D := by
  ext a
  change rationalAdeleRestrictChar a = 0 ↔ ∃ q : ℚ, ι q = a
  rw [← exists_congr (fun _ ↦ eq_comm), ← rationalAdele_orthogonal_iff]
  constructor
  · intro h q
    have he := congrArg (fun χ : Additive (PontryaginDual R) ↦
      (χ.toMul (Multiplicative.ofAdd (rationalDiagonalEquiv q)) : ℂ)) h
    rw [rationalAdeleRestrictChar_apply] at he
    change rationalAdeleAddChar (a * (rationalDiagonalEquiv q : A)) = 1 at he
    rwa [rationalDiagonalEquiv_apply] at he
  · intro h
    change (rationalAdeleRestrictChar a).toMul = (1 : PontryaginDual R)
    apply PontryaginDual.ext
    intro r
    obtain ⟨q, hq⟩ := rationalDiagonalEquiv.surjective r.toAdd
    apply Circle.coe_injective
    rw [rationalAdeleRestrictChar_apply, ← hq, rationalDiagonalEquiv_apply, h]
    rfl

/-- The element of the multiplicatively tagged additive diagonal at a rational input. -/
@[expose] public noncomputable def rationalDiagonalInput (r : ℚ) : R :=
  Multiplicative.ofAdd (rationalDiagonalEquiv r)

private theorem diag_zpow (r : ℚ) (n : ℤ) :
    rationalDiagonalInput r ^ n = rationalDiagonalInput (n • r) := by
  change (n • rationalDiagonalEquiv r : D) = rationalDiagonalEquiv (n • r)
  apply Subtype.ext
  change n • ((rationalDiagonalEquiv r : D) : A) = (rationalDiagonalEquiv (n • r) : A)
  rw [rationalDiagonalEquiv_apply, rationalDiagonalEquiv_apply, map_zsmul]

/-- On any finite list of rational inputs it suffices to match the character
at the reciprocal of a common denominator. -/
public theorem exists_rationalAdele_matching_diagonal_tests (χ : PontryaginDual R) (s : Finset ℚ) :
    ∃ a : A, ∀ r ∈ s,
      (rationalAdeleRestrictChar a).toMul (rationalDiagonalInput r) = χ (rationalDiagonalInput r) := by
  let d : ℕ := ∏ r ∈ s, r.den
  have hd : d ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun _ _ ↦ Rat.den_ne_zero _)
  let u : ℚ := 1 / d
  have hu : (u : ℝ) ≠ 0 := by simp [u, hd]
  obtain ⟨θ, hθ⟩ := Circle.exp_surjective (χ (rationalDiagonalInput u))
  let t := θ / (2 * Real.pi * (u : ℝ))
  let a : A := (rationalIntegralAdelesHomeomorph (t, 0) : rationalIntegralAdeles)
  have hreal : rationalAdeleReal (a * ι u) = t * (u : ℝ) := by
    rw [rationalAdeleReal_apply, Prod.fst_mul, Pi.mul_apply, map_mul,
      ← rationalAdeleReal_apply, ← rationalAdeleReal_apply, rationalIntegralAdelesHomeomorph_real,
      rationalAdeleReal_algebraMap]
  have hfin (v : HeightOneSpectrum (𝓞 ℚ)) : (a * ι u).2 v ∈ v.adicCompletionIntegers ℚ := by
    change a.2 v * (ι u).2 v ∈ _
    rw [rationalIntegralAdelesHomeomorph_finite]
    change (0 : v.adicCompletion ℚ) * _ ∈ _
    rw [zero_mul]
    exact (v.adicCompletionIntegers ℚ).zero_mem
  have hmatch :
      (rationalAdeleRestrictChar a).toMul (rationalDiagonalInput u) = χ (rationalDiagonalInput u) := by
    apply Circle.coe_injective
    rw [rationalAdeleRestrictChar_apply, show ((rationalDiagonalInput u).toAdd : A) = ι u from
      rationalDiagonalEquiv_apply u, ← hθ, Circle.coe_exp]
    rw [rationalAdeleAddChar_eq_prod _ ∅ (fun v _ ↦ hfin v), hreal,
      Finset.prod_empty, mul_one]
    have ht : 2 * Real.pi * (t * (u : ℝ)) = θ := by
      dsimp [t]
      field_simp [Real.pi_ne_zero, hu]
    exact congrArg Complex.exp (by rw [← ht]; push_cast; ring)
  refine ⟨a, fun r hr ↦ ?_⟩
  obtain ⟨k, hk⟩ : r.den ∣ d := Finset.dvd_prod_of_mem (fun q : ℚ ↦ q.den) hr
  let n : ℤ := r.num * (k : ℤ)
  have hk' : k ≠ 0 := by
    intro h
    simp [h] at hk
    exact hd hk
  have hru : n • u = r := by
    rw [zsmul_eq_mul, ← r.num_div_den]
    dsimp [n, u]
    rw [hk]
    push_cast
    field_simp [show (r.den : ℚ) ≠ 0 by exact_mod_cast r.den_ne_zero,
      show (k : ℚ) ≠ 0 by exact_mod_cast hk']
  rw [← hru, ← diag_zpow, map_zpow, map_zpow, hmatch]

end Masullo
