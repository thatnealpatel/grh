module

public import Theorems.PadicConductorFourier

import Mathlib.Algebra.GroupWithZero.Indicator
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import Lemmas.PadicBallPartition

/-!
# The signed unit-coset Fourier test over `ℚ_[3]`

The nontrivial character of the two unit residues modulo three gives the
signed indicator of `1 + 3ℤ_[3]` and `2 + 3ℤ_[3]`. We use the conjugate of
the standard additive character with additive Haar mass one on `ℤ_[3]`.
-/

open scoped Padic
open MeasureTheory Set

namespace Masullo

local notation "C[" a "]" => Set.ofPred (fun x : ℚ_[3] ↦ ‖(3 : ℚ_[3])⁻¹ * (x - a)‖ ≤ 1)
local notation "T" => Set.ofPred (fun y : ℚ_[3] ↦ ‖3 * y‖ ≤ 1)
local notation "ψ" => padicStdAddChar 3
local notation "μ" => padicAddHaar 3

/-- The indicator of `1 + 3ℤ_[3]` minus that of `2 + 3ℤ_[3]`. -/
@[expose] public noncomputable def padicRamifiedThreeTest (x : ℚ_[3]) : ℂ :=
  (C[1]).indicator (fun _ ↦ 1) x - (C[2]).indicator (fun _ ↦ 1) x

/-- The Fourier integral of the signed unit-coset indicator. The factor
`1/3` is the additive Haar mass of each coset. -/
public theorem padicRamifiedThree_fourier (y : ℚ_[3]) :
    (∫ x, padicRamifiedThreeTest x * star (ψ (x * y)) ∂μ) =
      (3 : ℂ)⁻¹ * (star (ψ y) - star (ψ (2 * y))) *
        (T).indicator (fun _ ↦ (1 : ℂ)) y := by
  let k := fun x : ℚ_[3] ↦ star (ψ (x * y))
  have hk : Continuous k :=
    ((continuous_padicStdAddChar 3).comp (continuous_id.mul continuous_const)).star
  have hcompact (a : ℚ_[3]) : IsCompact (C[a]) := by
    have hball : C[a] = Metric.closedBall a ‖(3 : ℚ_[3])‖ := by
      ext x
      change ‖(3 : ℚ_[3])⁻¹ * (x - a)‖ ≤ 1 ↔ x ∈ Metric.closedBall a ‖(3 : ℚ_[3])‖
      rw [Metric.mem_closedBall, dist_eq_norm, mul_comm ((3 : ℚ_[3])⁻¹), ← div_eq_mul_inv,
        norm_div, div_le_one₀ (norm_pos_iff.mpr (by norm_num))]
    rw [hball]
    exact isCompact_closedBall _ _
  have hmeas (a : ℚ_[3]) : MeasurableSet (C[a]) := (hcompact a).isClosed.measurableSet
  have hi (a : ℚ_[3]) : Integrable ((C[a]).indicator k) μ :=
    (integrable_indicator_iff (hmeas a)).mpr (hk.continuousOn.integrableOn_compact (hcompact a))
  have hterm (a x : ℚ_[3]) :
      (C[a]).indicator (fun _ ↦ (1 : ℂ)) x * k x = (C[a]).indicator k x := by
    simpa only [one_mul] using (indicator_mul_left C[a] (fun _ ↦ (1 : ℂ)) k (i := x)).symm
  have hs (x : ℚ_[3]) : padicRamifiedThreeTest x * k x =
      (C[1]).indicator k x - (C[2]).indicator k x := by
    simp only [padicRamifiedThreeTest, sub_mul, hterm]
  have hf (a : ℚ_[3]) :
      (∫ x in C[a], k x ∂μ) = (3 : ℂ)⁻¹ * star (ψ (a * y)) *
        (T).indicator (fun _ ↦ (1 : ℂ)) y := by
    let B := Set.ofPred (fun x : ℚ_[3] ↦ ‖x‖ ≤ 1)
    have hind : (T).indicator (fun _ ↦ (1 : ℂ)) y =
        B.indicator (fun _ ↦ (1 : ℂ)) (3 * y) := by
      change ((fun z : ℚ_[3] ↦ 3 * z) ⁻¹' B).indicator (fun _ ↦ (1 : ℂ)) y = _
      exact indicator_comp_right (fun z : ℚ_[3] ↦ 3 * z) (g := fun _ ↦ (1 : ℂ))
    rw [hind]
    simpa only [pow_one, Nat.cast_ofNat] using (padicTranslatedBall_fourier 3 1 a y)
  change (∫ x, padicRamifiedThreeTest x * k x ∂μ) = _
  simp_rw [hs]
  rw [integral_sub (hi 1) (hi 2), integral_indicator (hmeas 1), integral_indicator (hmeas 2),
    hf, hf, one_mul, ← sub_mul, ← mul_sub]

/-- The signed unit-coset transform is nonzero exactly on the shell
`3⁻¹ℤ_[3]ˣ`. -/
public theorem padicRamifiedThree_fourier_ne_zero_iff (y : ℚ_[3]) :
    (∫ x, padicRamifiedThreeTest x * star (ψ (x * y)) ∂μ) ≠ 0 ↔ ‖3 * y‖ = 1 := by
  have hsmall : ‖3 * y‖ < 1 ↔ ‖y‖ ≤ 1 := by
    have hnorm : ‖(3 : ℚ_[3])‖ = (3 : ℝ)⁻¹ := Padic.norm_p (p := 3)
    rw [norm_mul, hnorm, inv_mul_lt_iff₀ (by norm_num : (0 : ℝ) < 3), mul_one]
    simpa using (Padic.norm_le_pow_iff_norm_lt_pow_add_one (p := 3) y 0).symm
  have hψ : ψ y ≠ 0 := norm_ne_zero_iff.mp (by rw [norm_padicStdAddChar]; exact one_ne_zero)
  have hphase : star (ψ y) - star (ψ (2 * y)) = 0 ↔ ‖y‖ ≤ 1 := by
    rw [sub_eq_zero, star_injective.eq_iff, two_mul, AddChar.map_add_eq_mul, eq_comm,
      mul_eq_left₀ hψ, padicStdAddChar_eq_one_iff]
  rw [padicRamifiedThree_fourier]
  by_cases h : y ∈ T
  · have hy : ‖3 * y‖ ≤ 1 := h
    rw [indicator_of_mem h, mul_one, mul_ne_zero_iff, and_iff_right (by norm_num : (3 : ℂ)⁻¹ ≠ 0),
      Ne, hphase, ← hsmall]
    exact ⟨fun hh ↦ le_antisymm hy (not_lt.mp hh), fun hh ↦ hh.not_lt⟩
  · have hy : ¬ ‖3 * y‖ ≤ 1 := h
    rw [indicator_of_notMem h, mul_zero]
    exact ⟨fun hz ↦ (hz rfl).elim, fun heq ↦ (hy heq.le).elim⟩

/-- No evaluation of the complex phase is needed to show the transform is
nonzero at frequency `1/3`. -/
public theorem padicRamifiedThree_fourier_at_inv_ne_zero :
    (∫ x, padicRamifiedThreeTest x * star (ψ (x * (3 : ℚ_[3])⁻¹)) ∂μ) ≠ 0 := by
  rw [padicRamifiedThree_fourier_ne_zero_iff, mul_inv_cancel₀ (by norm_num), norm_one]

/-- The quadratic character modulo three, viewed as a complex character. -/
public def padicRamifiedThreeCharacter : DirichletCharacter ℂ (3 ^ 1) :=
  (quadraticChar (ZMod 3)).ringHomComp (Int.castRingHom ℂ)

private theorem padicRamifiedThreeCharacter_two : padicRamifiedThreeCharacter 2 = -1 := by
  have h : ¬ IsSquare (2 : ZMod 3) := by
    rintro ⟨b, hb⟩
    fin_cases b <;> revert hb <;> decide
  change (↑(quadraticChar (ZMod 3) 2) : ℂ) = -1
  rw [quadraticChar_neg_one_iff_not_isSquare.mpr h, Int.cast_neg, Int.cast_one]

/-- The quadratic character modulo three has conductor three. -/
public theorem padicRamifiedThreeCharacter_isPrimitive : padicRamifiedThreeCharacter.IsPrimitive := by
  have h := padicRamifiedThreeCharacter.conductor_dvd_level
  change padicRamifiedThreeCharacter.conductor ∣ 3 at h
  rcases (Nat.dvd_prime (by decide : Nat.Prime 3)).mp h with h | h
  · have he := DirichletCharacter.eq_one_iff_conductor_eq_one.mpr h
    have hu : IsUnit (2 : ZMod (3 ^ 1)) := by
      exact ⟨-1, by decide⟩
    have he₂ := DFunLike.congr_fun he (2 : ZMod (3 ^ 1))
    rw [padicRamifiedThreeCharacter_two, MulChar.one_apply hu] at he₂
    norm_num at he₂
  · exact h

/-- The general residue-character test specializes to the signed coset test,
pointwise and with the same normalization. -/
public theorem padicRamifiedThreeTest_eq_conductorTest :
    padicRamifiedThreeTest = padicConductorTest 3 padicRamifiedThreeCharacter := by
  funext x
  have hm (j : ZMod (3 ^ 1)) :
      x ∈ C[(j.val : ℚ_[3])] ↔ ∃ a : ℤ_[3], (a : ℚ_[3]) = x ∧ PadicInt.toZModPow 1 a = j := by
    change ‖(3 : ℚ_[3])⁻¹ * (x - (j.val : ℚ_[3]))‖ ≤ 1 ↔ _
    have he := padic_residue_coset 3 1 j x
    change ‖((3 : ℚ_[3]) ^ 1)⁻¹ * (x - (j.val : ℚ_[3]))‖ ≤ 1 ↔ _ at he
    simpa only [pow_one] using he
  have h₁ : (1 : ZMod (3 ^ 1)).val = 1 := rfl
  have h₂ : (2 : ZMod (3 ^ 1)).val = 2 := rfl
  have hc₁ := hm 1
  have hc₂ := hm 2
  rw [h₁, Nat.cast_one] at hc₁
  rw [h₂, Nat.cast_ofNat] at hc₂
  by_cases hx : ‖x‖ ≤ 1
  · let a : ℤ_[3] := ⟨x, hx⟩
    have hs (j : ZMod (3 ^ 1)) :
        (∃ b : ℤ_[3], (b : ℚ_[3]) = x ∧ PadicInt.toZModPow 1 b = j) ↔
          PadicInt.toZModPow 1 a = j := by
      constructor
      · rintro ⟨b, hb, hbj⟩
        rwa [PadicInt.coe_inj.mp (show (b : ℚ_[3]) = (a : ℚ_[3]) from hb)] at hbj
      · exact fun h ↦ ⟨a, rfl, h⟩
    let j := PadicInt.toZModPow 1 a
    rw [padicRamifiedThreeTest, padicConductorTest, dite_eq_left hx]
    change (C[1]).indicator (fun _ ↦ (1 : ℂ)) x - (C[2]).indicator (fun _ ↦ 1) x =
      padicRamifiedThreeCharacter⁻¹ j
    have hcases : ∀ j : ZMod (3 ^ 1), j = 0 ∨ j = 1 ∨ j = 2 := by decide
    have hmem₁ : x ∈ C[1] ↔ j = 1 := hc₁.trans (hs 1)
    have hmem₂ : x ∈ C[2] ↔ j = 2 := hc₂.trans (hs 2)
    rcases hcases j with h | h | h
    · rw [indicator_of_notMem (mt hmem₁.mp (h.trans_ne (by decide : (0 : ZMod (3 ^ 1)) ≠ 1))),
        indicator_of_notMem (mt hmem₂.mp (h.trans_ne (by decide : (0 : ZMod (3 ^ 1)) ≠ 2))), h]
      have hzero : ¬IsUnit (0 : ZMod (3 ^ 1)) := by
        change ¬IsUnit (0 : ZMod 3)
        exact not_isUnit_zero
      rw [MulChar.map_nonunit _ hzero, sub_zero]
    · rw [indicator_of_mem (hmem₁.mpr h),
        indicator_of_notMem (mt hmem₂.mp (h.trans_ne (by decide : (1 : ZMod (3 ^ 1)) ≠ 2))), h]
      simp
    · rw [indicator_of_notMem (mt hmem₁.mp (h.trans_ne (by decide : (2 : ZMod (3 ^ 1)) ≠ 1))),
        indicator_of_mem (hmem₂.mpr h), h, MulChar.inv_apply_eq_inv', padicRamifiedThreeCharacter_two]
      simp
  · have hn (j : ZMod (3 ^ 1)) : ¬ ∃ a : ℤ_[3], (a : ℚ_[3]) = x ∧ PadicInt.toZModPow 1 a = j := by
      rintro ⟨a, rfl, _⟩
      exact hx a.2
    rw [padicRamifiedThreeTest, padicConductorTest, dite_eq_right hx,
      indicator_of_notMem (mt hc₁.mp (hn 1)), indicator_of_notMem (mt hc₂.mp (hn 2)), sub_self]

-- Recover the original shell from the general conductor theorem.
example (y : ℚ_[3]) :
    (∫ x, padicRamifiedThreeTest x * star (ψ (x * y)) ∂μ) ≠ 0 ↔ ‖3 * y‖ = 1 := by
  rw [padicRamifiedThreeTest_eq_conductorTest]
  change padicConductorFourier 3 padicRamifiedThreeCharacter y ≠ 0 ↔ ‖3 * y‖ = 1
  simpa only [pow_one, Nat.cast_ofNat] using
    padicConductorFourier_ne_zero_iff 3 Nat.one_pos padicRamifiedThreeCharacter
      padicRamifiedThreeCharacter_isPrimitive y

end Masullo
