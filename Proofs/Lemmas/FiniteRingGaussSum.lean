module

public import Mathlib.NumberTheory.GaussSum
public import Mathlib.Analysis.Complex.Norm

import Mathlib.Tactic.Ring

/-! # The inverse-character Gauss sum over a finite ring -/

open AddChar Finset

namespace Masullo

variable {R : Type*} [CommRing R] [Fintype R]

/-- For a primitive additive character, an inverse-character Gauss transform
has the expected covariance and squared modulus if every nonunit is fixed
by a unit on which the multiplicative character is nontrivial. -/
public theorem finiteRingGaussSum_profile (χ : MulChar R ℂ) (ψ : AddChar R ℂ) (hp : ψ.IsPrimitive)
    (hs : ∀ b : R, ¬ IsUnit b → ∃ u : Rˣ, b * (u : R) = b ∧ χ u ≠ 1) :
    (∀ b : R, gaussSum χ⁻¹ (ψ.mulShift b) = χ b * gaussSum χ⁻¹ ψ) ∧
    ‖gaussSum χ⁻¹ ψ‖ ^ 2 = (Fintype.card R : ℝ) ∧
    (∀ b : R, gaussSum χ⁻¹ (ψ.mulShift b) ≠ 0 ↔ IsUnit b) := by
  classical
  have hcov (b : R) : gaussSum χ⁻¹ (ψ.mulShift b) = χ b * gaussSum χ⁻¹ ψ := by
    by_cases hb : IsUnit b
    · obtain ⟨u, rfl⟩ := hb
      simpa using gaussSum_mulShift_eq χ⁻¹ ψ u
    obtain ⟨u, hbu, hu⟩ := hs b hb
    have h := gaussSum_mulShift_eq χ⁻¹ (ψ.mulShift b) u
    simp only [mulShift_mulShift, hbu, inv_inv] at h
    rw [χ.map_nonunit hb, zero_mul]
    exact (mul_eq_zero.mp (show (χ u - 1) * gaussSum χ⁻¹ (ψ.mulShift b) = 0 by
      rw [sub_mul, one_mul, ← h, sub_self])).resolve_left (sub_ne_zero.mpr hu)
  -- Extract the coefficient at 1 by summing the transform against `ψ (-b)`.
  have hh : (∑ b, gaussSum χ⁻¹ (ψ.mulShift b) * ψ (-b)) = Fintype.card R := by
    simp only [gaussSum, mulShift_apply, sum_mul, mul_assoc, ← map_add_eq_mul]
    simp_rw [show ∀ a b : R, b * a + -b = b * (a - 1) by intros; ring]
    rw [sum_comm]
    simp_rw [← mul_sum, sum_mulShift _ hp]
    simp [mul_ite, sub_eq_zero]
  have hconj : star (gaussSum χ⁻¹ ψ) = ∑ b, χ b * ψ (-b) := by
    rw [star_gaussSum_eq, inv_inv]
    rfl
  simp_rw [hcov, show ∀ a b c : ℂ, a * b * c = b * (a * c) by intros; ring] at hh
  rw [← mul_sum, ← hconj] at hh
  have hnorm : ‖gaussSum χ⁻¹ ψ‖ ^ 2 = (Fintype.card R : ℝ) := by
    simpa only [sq, norm_mul, norm_star, Complex.norm_natCast] using congrArg norm hh
  have hne : gaussSum χ⁻¹ ψ ≠ 0 := by
    intro hz
    have hc : (0 : ℝ) < Fintype.card R := Nat.cast_pos.mpr Fintype.card_pos
    exact hc.ne (by simpa [hz] using hnorm)
  exact ⟨hcov, hnorm, fun b ↦ by rw [hcov, mul_ne_zero_iff, and_iff_left hne,
    MulChar.apply_ne_zero_iff]⟩

end Masullo
