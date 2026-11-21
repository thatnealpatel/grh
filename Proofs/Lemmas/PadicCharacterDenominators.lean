module

public import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
public import Mathlib.NumberTheory.Padics.RingHoms

/-!
# Clearing denominators for the standard character of `ℚ_[p]`

Increasing a `p`-power denominator scales the integral numerator by the
same factor. This gives the transition identity for the finite cyclic
characters used in `Theorems.PadicStandardCharacter`.
-/

open scoped Padic

namespace Masullo

variable (p : ℕ) [Fact p.Prime]

/-- Each `p`-adic number has a `p`-power denominator with integral numerator. -/
public theorem exists_padic_integral_numerator (x : ℚ_[p]) :
    ∃ n : ℕ, ∃ a : ℤ_[p], (a : ℚ_[p]) = (p : ℚ_[p]) ^ n * x := by
  by_cases hx : ‖x‖ ≤ 1
  · exact ⟨0, ⟨x, hx⟩, by simp⟩
  have hx0 : x ≠ 0 := fun h ↦ hx (by simp [h])
  rw [Padic.norm_le_one_iff_val_nonneg, not_le] at hx
  let n := (-x.valuation).toNat
  have hn : (n : ℤ) = -x.valuation := Int.toNat_of_nonneg (by omega)
  have hp : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne p)
  have h : ‖(p : ℚ_[p]) ^ n * x‖ ≤ 1 := by
    rw [norm_mul, Padic.norm_p_pow, Padic.norm_eq_zpow_neg_valuation hx0,
      ← zpow_add₀ hp, hn, neg_neg, add_neg_cancel, zpow_zero]
  exact ⟨n, ⟨_, h⟩, rfl⟩

private theorem stdAddChar_natCast {N : ℕ} [NeZero N] (j : ℕ) :
    ZMod.stdAddChar (j : ZMod N) = Complex.exp (2 * Real.pi * Complex.I * j / N) := by
  simpa using ZMod.stdAddChar_coe (N := N) (j : ℤ)

private theorem padicResidueChar_scale (n k : ℕ) (a : ℤ_[p]) :
    ZMod.stdAddChar (PadicInt.toZModPow (n + k) ((p : ℤ_[p]) ^ k * a)) =
      ZMod.stdAddChar (PadicInt.toZModPow n a) := by
  let j := a.appr n
  have hj : (p : ℤ_[p]) ^ n ∣ a - j :=
    Ideal.mem_span_singleton.mp (PadicInt.appr_spec n a)
  have hscaled : (p : ℤ_[p]) ^ (n + k) ∣ (p : ℤ_[p]) ^ k * a - (p ^ k * j : ℕ) := by
    rw [pow_add, Nat.cast_mul, Nat.cast_pow, ← mul_sub, mul_comm ((p : ℤ_[p]) ^ n)]
    exact mul_dvd_mul_left _ hj
  have hres : PadicInt.toZModPow (n + k) ((p : ℤ_[p]) ^ k * a) =
      ((p ^ k * j : ℕ) : ZMod (p ^ (n + k))) :=
    PadicInt.zmod_congr_of_sub_mem_span _ _ _ _ (PadicInt.appr_spec _ _)
      (Ideal.mem_span_singleton.mpr hscaled)
  rw [hres, stdAddChar_natCast]
  change _ = ZMod.stdAddChar (j : ZMod (p ^ n))
  rw [stdAddChar_natCast, Nat.cast_mul, Nat.cast_pow, Nat.cast_pow, Nat.cast_pow, pow_add]
  have hp : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne p)
  congr 1
  field_simp

/-- Passing to a larger `p`-power denominator leaves the residue character unchanged. -/
public theorem padicResidueChar_eq_of_le {x : ℚ_[p]} {n m : ℕ} {a b : ℤ_[p]}
    (hnm : n ≤ m) (ha : (a : ℚ_[p]) = (p : ℚ_[p]) ^ n * x)
    (hb : (b : ℚ_[p]) = (p : ℚ_[p]) ^ m * x) :
    ZMod.stdAddChar (PadicInt.toZModPow n a) = ZMod.stdAddChar (PadicInt.toZModPow m b) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hnm
  have hb' : b = (p : ℤ_[p]) ^ k * a := by
    apply PadicInt.coe_inj.mp
    rw [PadicInt.coe_mul, PadicInt.coe_pow, PadicInt.coe_natCast, ha, hb, pow_add]
    ring
  rw [hb', padicResidueChar_scale]

end Masullo
