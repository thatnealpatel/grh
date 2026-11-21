module

public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-! # An exponential majorant for the compact-strip Hardy–Sobolev weight -/

open MeasureTheory

namespace Masullo

private theorem integrable_exp_neg_abs : Integrable (fun x : ℝ ↦ Real.exp (-|x|)) := by
  have hleft := (integrableOn_exp_mul_Iic (a := 1) one_pos 0).congr_fun
    (g := fun x : ℝ ↦ Real.exp (-|x|))
    (fun x hx ↦ by simp only [one_mul, abs_of_nonpos (show x ≤ 0 from hx), neg_neg])
    measurableSet_Iic
  have hright := (integrableOn_exp_mul_Ioi (a := -1) (by norm_num) 0).congr_fun
    (g := fun x : ℝ ↦ Real.exp (-|x|))
    (fun x hx ↦ by simp only [neg_one_mul, abs_of_pos (show 0 < x from hx)])
    measurableSet_Ioi
  simpa only [Set.Iic_union_Ioi, integrableOn_univ] using hleft.union hright

/-- One sufficiently fast exponential decay bound controls the squared norm
integrand for the compact-strip weight (9.2.2.4), p. 412, in log coordinates. -/
public theorem integrable_hardySobolevWeight_mul_norm_sq {f : ℝ → ℂ} (hf : Continuous f)
    {α β s C N : ℝ} (hs : 0 ≤ s) (hN : 2 * max |α| |β| + s + 1 ≤ 2 * N)
    (hdecay : ∀ x : ℝ, ‖f x‖ ≤ C * Real.exp (-N * |x|)) :
    Integrable (fun x : ℝ ↦ ‖f x‖ ^ 2 *
      max (Real.exp (2 * α * x)) (Real.exp (2 * β * x)) * (1 + x ^ 2) ^ (s / 2)) := by
  let A := max |α| |β|
  refine (integrable_exp_neg_abs.const_mul (C ^ 2)).mono' ?_ (ae_of_all _ fun x ↦ ?_)
  · apply Continuous.aestronglyMeasurable
    exact ((hf.norm.pow 2).mul (Continuous.max (by fun_prop) (by fun_prop))).mul
      ((show Continuous (fun x : ℝ ↦ 1 + x ^ 2) by fun_prop).rpow_const
        (fun _ ↦ Or.inr (by positivity)))
  · rw [Real.norm_of_nonneg (by positivity)]
    have hExp (d : ℝ) (hd : |d| ≤ A) :
        Real.exp (2 * d * x) ≤ Real.exp (2 * A * |x|) := by
      apply Real.exp_le_exp.mpr
      calc
        2 * d * x ≤ 2 * (|d| * |x|) := by
          simpa only [mul_assoc, abs_mul] using
            mul_le_mul_of_nonneg_left (le_abs_self (d * x)) (by norm_num : (0 : ℝ) ≤ 2)
        _ ≤ 2 * A * |x| := by rw [mul_assoc]; gcongr
    have hWeight : (1 + x ^ 2) ^ (s / 2) ≤ Real.exp (s * |x|) := by
      calc
        _ ≤ ((Real.exp |x|) ^ 2) ^ (s / 2) := by
          apply Real.rpow_le_rpow (by positivity) _ (by positivity)
          calc
            1 + x ^ 2 ≤ (|x| + 1) ^ 2 := by
              rw [add_sq, sq_abs]
              have := abs_nonneg x
              linarith
            _ ≤ (Real.exp |x|) ^ 2 := by gcongr; exact Real.add_one_le_exp _
        _ = Real.exp (s * |x|) := by
          rw [← Real.exp_nat_mul, ← Real.exp_mul]
          congr 1
          push_cast
          ring
    calc
      _ ≤ (C * Real.exp (-N * |x|)) ^ 2 * Real.exp (2 * A * |x|) *
          Real.exp (s * |x|) := by
        gcongr
        · exact hdecay x
        · exact max_le (hExp α (le_max_left ..)) (hExp β (le_max_right ..))
      _ = C ^ 2 * Real.exp ((-2 * N + 2 * A + s) * |x|) := by
        rw [mul_pow, ← Real.exp_nat_mul, mul_assoc, ← Real.exp_add, mul_assoc, ← Real.exp_add]
        congr 2
        norm_num
        ring
      _ ≤ C ^ 2 * Real.exp (-|x|) := by
        gcongr
        exact (mul_le_mul_of_nonneg_right (by linarith : -2 * N + 2 * A + s ≤ -1)
          (abs_nonneg x)).trans_eq (neg_one_mul _)

end Masullo
