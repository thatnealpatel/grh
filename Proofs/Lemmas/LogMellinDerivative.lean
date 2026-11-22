module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Lemmas.ExpAbsDecay

/-! # Differentiating a Mellin integral in log coordinates -/

open MeasureTheory

namespace Masullo

/-- Exponential decay of the weighted profile at `z` supplies an integrable
majorant for differentiation in a complex neighborhood of `z`. -/
public theorem hasDerivAt_logMellin_of_measurable_decay {f : ℝ → ℂ} (hf : Measurable f) (z : ℂ)
    {r C : ℝ} (hr : 0 < r) (hC : 0 ≤ C)
    (hdecay : ∀ x : ℝ, ‖f x * Complex.exp (z * x)‖ ≤ C * Real.exp (-(3 * r) * |x|)) :
    Integrable (fun x : ℝ ↦ f x * Complex.exp (z * x)) ∧
    Integrable (fun x : ℝ ↦ (x : ℂ) * (f x * Complex.exp (z * x))) ∧
    HasDerivAt (fun w : ℂ ↦ ∫ x : ℝ, f x * Complex.exp (w * x))
      (∫ x : ℝ, (x : ℂ) * (f x * Complex.exp (z * x))) z := by
  let F (w : ℂ) (x : ℝ) := f x * Complex.exp (w * x)
  let D (w : ℂ) (x : ℝ) := (x : ℂ) * F w x
  have hF (w : ℂ) : Measurable (F w) :=
    hf.mul (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)).measurable
  have hD : Measurable (D z) := Complex.continuous_ofReal.measurable.mul (hF z)
  have hdec := integrable_exp_neg_mul_abs hr
  have hbase : Integrable (F z) := by
    refine (hdec.const_mul C).mono' (hF z).aestronglyMeasurable (ae_of_all _ fun x ↦ ?_)
    refine (hdecay x).trans ?_
    gcongr
    nlinarith [abs_nonneg x]
  refine ⟨hbase, hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := F) (F' := D) (Metric.ball_mem_nhds z hr)
    (Filter.Eventually.of_forall fun w ↦ (hF w).aestronglyMeasurable) hbase
    hD.aestronglyMeasurable (ae_of_all _ fun x w hw ↦ ?_)
    (hdec.const_mul (C / r)) (ae_of_all _ fun x w _ ↦ ?_)⟩
  · have hnear : |(w - z).re| ≤ r :=
      (Complex.abs_re_le_norm _).trans (by simpa only [dist_eq_norm] using (Metric.mem_ball.mp hw).le)
    have hshift : ‖Complex.exp ((w - z) * (x : ℂ))‖ ≤ Real.exp (r * |x|) := by
      rw [Complex.norm_exp, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
        sub_zero, Real.exp_le_exp]
      calc
        _ ≤ |(w - z).re| * |x| := by rw [← abs_mul]; exact le_abs_self _
        _ ≤ r * |x| := by gcongr
    have hx : |x| ≤ Real.exp (r * |x|) / r := by
      apply (le_div_iff₀ hr).2
      have := Real.add_one_le_exp (r * |x|)
      linarith
    have hsplit : w * (x : ℂ) = z * (x : ℂ) + (w - z) * (x : ℂ) := by ring
    dsimp only [D, F]
    rw [hsplit, Complex.exp_add, ← mul_assoc (f x), norm_mul, norm_mul,
      Complex.norm_real, Real.norm_eq_abs]
    calc
      _ ≤ (Real.exp (r * |x|) / r) * (C * Real.exp (-(3 * r) * |x|) *
          Real.exp (r * |x|)) := by gcongr; exact hdecay x
      _ = (C / r) * Real.exp (-r * |x|) := by
        rw [show -r * |x| = r * |x| + (-(3 * r) * |x| + r * |x|) by ring]
        simp only [Real.exp_add]
        ring
  · have hlin : HasDerivAt (fun y : ℂ ↦ y * (x : ℂ)) (x : ℂ) w := by
      simpa only [id_eq, one_mul] using (hasDerivAt_id w).mul_const (x : ℂ)
    have hExp : HasDerivAt (fun y : ℂ ↦ Complex.exp (y * x))
        (Complex.exp (w * x) * x) w :=
      (Complex.hasDerivAt_exp (w * x)).comp w hlin
    have hval : D w x = f x * (Complex.exp (w * x) * x) := by
      dsimp only [D, F]
      ring
    rw [hval]
    exact hExp.const_mul (f x)

/-- The continuous-profile case of differentiation under the log Mellin integral. -/
public theorem hasDerivAt_logMellin_of_decay {f : ℝ → ℂ} (hf : Continuous f) (z : ℂ)
    {r C : ℝ} (hr : 0 < r) (hC : 0 ≤ C)
    (hdecay : ∀ x : ℝ, ‖f x * Complex.exp (z * x)‖ ≤ C * Real.exp (-(3 * r) * |x|)) :
    Integrable (fun x : ℝ ↦ f x * Complex.exp (z * x)) ∧
    Integrable (fun x : ℝ ↦ (x : ℂ) * (f x * Complex.exp (z * x))) ∧
    HasDerivAt (fun w : ℂ ↦ ∫ x : ℝ, f x * Complex.exp (w * x))
      (∫ x : ℝ, (x : ℂ) * (f x * Complex.exp (z * x))) z :=
  hasDerivAt_logMellin_of_measurable_decay hf.measurable z hr hC hdecay

end Masullo
