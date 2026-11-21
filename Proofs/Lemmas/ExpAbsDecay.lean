module

public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-! # Integrability of an exponential on the two log tails -/

open MeasureTheory

namespace Masullo

/-- A strictly decaying exponential in the absolute value is integrable on the real line. -/
public theorem integrable_exp_neg_mul_abs {r : ℝ} (hr : 0 < r) :
    Integrable (fun x : ℝ ↦ Real.exp (-r * |x|)) := by
  have hlo := (integrableOn_exp_mul_Iic hr 0).congr_fun
    (g := fun x : ℝ ↦ Real.exp (-r * |x|))
    (fun x hx ↦ by simp only [abs_of_nonpos (show x ≤ 0 from hx), neg_mul_neg]) measurableSet_Iic
  have hhi := (integrableOn_exp_mul_Ioi (neg_lt_zero.mpr hr) 0).congr_fun
    (g := fun x : ℝ ↦ Real.exp (-r * |x|))
    (fun x hx ↦ by simp only [abs_of_pos (show 0 < x from hx)]) measurableSet_Ioi
  simpa only [Set.Iic_union_Ioi, integrableOn_univ] using hlo.union hhi

end Masullo
