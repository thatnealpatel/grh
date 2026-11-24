module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.NumberTheory.LegendreSymbol.ZModChar
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic

/-!
# A finite numerical budget for the mod-eight character

The finite sums are over `[1, N]`, including the upper endpoint. The final
inequality uses only one-sided tail estimates, without specifying analytic
interpretations of the two values being estimated.
-/

open Finset Real

namespace Chi8Budget

/-- The integer-valued mod-eight character, evaluated on naturals and cast to `ℝ`. -/
@[expose] public noncomputable def w (n : ℕ) : ℝ := (ZMod.χ₈ (n : ZMod 8) : ℝ)

/-- The partial sum of the character weighted by `1/n`. -/
@[expose] public noncomputable def S (N : ℕ) : ℝ := ∑ n ∈ Icc 1 N, w n / (n : ℝ)

/-- The partial sum with the logarithmic derivative weight. -/
@[expose] public noncomputable def D (N : ℕ) : ℝ :=
  ∑ n ∈ Icc 1 N, -w n * (log (n : ℝ) / (n : ℝ))

/-- A rational lower bound for the reciprocal sum at the cutoff. -/
public theorem S32_lower : 62 / 100 ≤ S 32 := by
  unfold S
  rw [← Ico_add_one_right_eq_Icc, sum_Ico_eq_sum_range]
  norm_num [sum_range_succ, w, ZMod.χ₈_nat_eq_if_mod_eight]

-- For `b = 2^⌊log₂ n⌋`, this is the Taylor parameter for `log (n/b)`.
private noncomputable def t (n : ℕ) : ℝ :=
  ((n : ℝ) - 2 ^ n.log2) / ((n : ℝ) + 2 ^ n.log2)

private noncomputable def logLower (n : ℕ) : ℝ :=
  n.log2 * (693 / 1000) + 2 * (t n + t n ^ 3 / 3)

private noncomputable def logUpper (n : ℕ) : ℝ :=
  n.log2 * (694 / 1000) + 2 * (t n + t n ^ 3 / 3 + t n ^ 5 / (1 - t n ^ 2))

-- Two terms of the Taylor expansion suffice after dyadic range reduction.
private theorem log_bounds {n : ℕ} (hn : 1 ≤ n) :
    logLower n ≤ log (n : ℝ) ∧ log (n : ℝ) ≤ logUpper n := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hb : (0 : ℝ) < 2 ^ n.log2 := by positivity
  have hbn : (2 : ℝ) ^ n.log2 ≤ n := by
    exact_mod_cast Nat.log2_self_le (by omega : n ≠ 0)
  have hden : (0 : ℝ) < n + 2 ^ n.log2 := add_pos hn' hb
  have ht₀ : 0 ≤ t n := div_nonneg (sub_nonneg.mpr hbn) hden.le
  have ht₁ : t n < 1 := by
    rw [t, div_lt_one hden]
    linarith
  have harg : (1 + t n) / (1 - t n) = n / (2 : ℝ) ^ n.log2 := by
    unfold t
    field_simp
    ring
  have hlo := sum_range_le_log_div ht₀ ht₁ 2
  have hhi := log_div_le_sum_range_add ht₀ ht₁ 2
  rw [harg, log_div hn'.ne' hb.ne', log_pow] at hlo hhi
  norm_num [sum_range_succ] at hlo hhi
  have h₂lo : (693 / 1000 : ℝ) ≤ log 2 := by linarith [log_two_gt_d9]
  have h₂hi : log 2 ≤ (694 / 1000 : ℝ) := by linarith [log_two_lt_d9]
  constructor
  · unfold logLower
    linarith [mul_le_mul_of_nonneg_left h₂lo (Nat.cast_nonneg n.log2 : (0 : ℝ) ≤ n.log2)]
  · unfold logUpper
    linarith [mul_le_mul_of_nonneg_left h₂hi (Nat.cast_nonneg n.log2 : (0 : ℝ) ≤ n.log2)]

-- Use the lower log enclosure when the coefficient `-w n` is nonpositive.
private noncomputable def dUpper (n : ℕ) : ℝ :=
  -w n * ((if 0 ≤ w n then logLower n else logUpper n) / (n : ℝ))

private theorem d_le_dUpper {n : ℕ} (hn : 1 ≤ n) :
    -w n * (log (n : ℝ) / (n : ℝ)) ≤ dUpper n := by
  have hn' : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  unfold dUpper
  split_ifs with hw
  · exact mul_le_mul_of_nonpos_left (div_le_div_of_nonneg_right (log_bounds hn).1 hn')
      (neg_nonpos.mpr hw)
  · exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right (log_bounds hn).2 hn')
      (neg_nonneg.mpr (le_of_not_ge hw))

/-- A rational upper bound for the logarithmically weighted sum at the cutoff. -/
public theorem D32_upper : D 32 ≤ 42 / 100 := by
  calc
    D 32 ≤ ∑ n ∈ Icc 1 32, dUpper n :=
      sum_le_sum fun _ hn ↦ d_le_dUpper (mem_Icc.mp hn).1
    _ ≤ 42 / 100 := by
      rw [← Ico_add_one_right_eq_Icc, sum_Ico_eq_sum_range]
      -- Expand the sum and resolve the signs before unfolding `log2` on numerals.
      norm_num [sum_range_succ, dUpper, w, ZMod.χ₈_nat_eq_if_mod_eight]
      norm_num [logLower, logUpper, t, Nat.log2_def]

/-- Numerical budget from one-sided tails. No Euler constant term is needed. -/
public theorem endpoint_bound (L D' : ℝ) (hL : S 32 - 1 / 32 ≤ L)
    (hD : D' ≤ D 32 + Real.log 32 / 32) :
    Real.log (8 / Real.pi) - 2 * Real.log 2 + 2 * D' / L < 3 / 2 := by
  have hlog32 : log 32 ≤ 7 / 2 := by
    rw [show (32 : ℝ) = 2 ^ (5 : ℕ) by norm_num, log_pow]
    norm_num
    linarith [log_two_lt_d9]
  have hL' : (62 / 100 : ℝ) - 1 / 32 ≤ L := by linarith [S32_lower]
  have hpos : 0 < L := by linarith
  have hD' : D' ≤ 42 / 100 + (7 / 2) / 32 := by linarith [D32_upper]
  have hratio : 2 * D' / L < 11 / 6 := by
    rw [div_lt_iff₀ hpos]
    linarith
  have hlog : log (2 / π) ≤ -(1 / 3) := by
    have hfrac : (2 : ℝ) / π ≤ 2 / 3 := by
      gcongr
      exact pi_gt_three.le
    linarith [log_le_sub_one_of_pos (show 0 < 2 / π by positivity)]
  have heq : log (8 / π) - 2 * log 2 = log (2 / π) := by
    rw [log_div (by norm_num : (8 : ℝ) ≠ 0) pi_ne_zero,
      log_div (by norm_num : (2 : ℝ) ≠ 0) pi_ne_zero,
      show (8 : ℝ) = 2 ^ (3 : ℕ) by norm_num, log_pow]
    ring
  rw [heq]
  linarith

/-- Absolute-error form of `endpoint_bound`. -/
public theorem endpoint_bound_of_abs (L D' : ℝ) (hL : |L - S 32| ≤ 1 / 32)
    (hD : |D' - D 32| ≤ Real.log 32 / 32) :
    Real.log (8 / Real.pi) - 2 * Real.log 2 + 2 * D' / L < 3 / 2 := by
  apply endpoint_bound L D'
  · linarith [(abs_le.mp hL).1]
  · linarith [(abs_le.mp hD).2]

end Chi8Budget
