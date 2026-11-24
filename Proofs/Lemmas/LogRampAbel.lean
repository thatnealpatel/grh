module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.NumberTheory.AbelSummation
import Mathlib.Tactic.FieldSimp

/-! # Abel summation for the logarithmic ramp -/

open MeasureTheory Set

namespace PrimeSquareRamp

/-- The finite sum with logarithmic ramp weight `log (Y / n)`. -/
public noncomputable def logRamp (a : ℕ → ℝ) (Y : ℝ) :=
  ∑ n ∈ Finset.Ioc 1 ⌊Y⌋₊, Real.log (Y / n) * a n

private theorem ne_zero_of_mem_Icc_one {Y t : ℝ} (ht : t ∈ Icc 1 Y) : t ≠ 0 :=
  (zero_lt_one.trans_le ht.1).ne'

private theorem continuousOn_inv (Y : ℝ) : ContinuousOn (fun t : ℝ ↦ t⁻¹) (Icc 1 Y) :=
  continuous_id.continuousOn.inv₀ fun _ ht ↦ ne_zero_of_mem_Icc_one ht

/-- The partial sums divided by `t` are interval integrable on `[1, Y]`. -/
public theorem partialSum_div_intervalIntegrable (a : ℕ → ℝ) {Y : ℝ} (hY : 1 ≤ Y) :
    IntervalIntegrable (fun t : ℝ => (∑ n ∈ Finset.Icc 0 ⌊t⌋₊, a n) / t)
      MeasureTheory.volume 1 Y := by
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hY]
  simpa only [div_eq_mul_inv, mul_comm] using
    integrableOn_mul_sum_Icc (m := 0) a zero_le_one
      ((continuousOn_inv Y).integrableOn_compact isCompact_Icc)

/-- Abel summation turns the logarithmic weight into division by `t` in the integral. -/
public theorem logRamp_eq_integral (a : ℕ → ℝ) (h0 : a 0 = 0) (h1 : a 1 = 0)
    {Y : ℝ} (hY : 1 ≤ Y) :
    logRamp a Y = ∫ t in (1 : ℝ)..Y, (∑ n ∈ Finset.Icc 0 ⌊t⌋₊, a n) / t := by
  have hY0 : Y ≠ 0 := (zero_lt_one.trans_le hY).ne'
  have hd (t : ℝ) (ht : t ∈ Icc 1 Y) :
      HasDerivAt (fun x : ℝ ↦ Real.log (Y / x)) (-(t⁻¹)) t := by
    have ht0 := ne_zero_of_mem_Icc_one ht
    have h := ((hasDerivAt_const t Y).fun_div (hasDerivAt_id t) ht0).log (div_ne_zero hY0 ht0)
    simp only [id_eq, zero_mul, mul_one, zero_sub] at h
    convert h using 1
    field_simp
  have hint : IntegrableOn (deriv (fun x : ℝ ↦ Real.log (Y / x))) (Icc 1 Y) :=
    ((continuousOn_inv Y).neg.integrableOn_compact isCompact_Icc).congr_fun
      (fun t ht ↦ (hd t ht).deriv.symm) measurableSet_Icc
  have hab := sum_mul_eq_sub_sub_integral_mul a zero_le_one hY
    (fun t ht ↦ (hd t ht).differentiableAt) hint
  have hsum : (∑ n ∈ Finset.Icc 0 1, a n) = 0 := by
    rw [show Finset.Icc 0 1 = ({0, 1} : Finset ℕ) by decide]
    simp [h0, h1]
  rw [Nat.floor_one, div_self hY0, Real.log_one, zero_mul, hsum, mul_zero, sub_zero,
    zero_sub, ← intervalIntegral.integral_of_le hY] at hab
  rw [logRamp, hab, ← intervalIntegral.integral_neg]
  apply intervalIntegral.integral_congr
  rw [uIcc_of_le hY]
  intro t ht
  dsimp only
  rw [(hd t ht).deriv, neg_mul, neg_neg, div_eq_mul_inv, mul_comm]

end PrimeSquareRamp
