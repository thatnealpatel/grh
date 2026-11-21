module

public import Theorems.RationalThetaMellin
import Lemmas.LogMellinDerivative

/-! # Differentiation of rational theta log moments -/

open MeasureTheory
open scoped FourierTransform SchwartzMap

namespace Masullo

/-- With both zero modes removed, every log moment is integrable and its
parameter derivative is the next log moment. -/
public theorem hasDerivAt_rationalTheta_mellin_logMoment (b : 𝓢(ℝ, ℂ))
    (hb : b 0 = 0) (hFourier : (𝓕 b) 0 = 0) (m : ℕ) (z : ℂ) :
    Integrable (fun x : ℝ ↦ (x : ℂ) ^ m * rationalTheta b (Real.exp x) *
      Complex.exp (z * x)) ∧
    HasDerivAt (fun w : ℂ ↦ ∫ x : ℝ, (x : ℂ) ^ m * rationalTheta b (Real.exp x) *
      Complex.exp (w * x))
      (∫ x : ℝ, (x : ℂ) ^ (m + 1) * rationalTheta b (Real.exp x) * Complex.exp (z * x)) z := by
  obtain ⟨N : ℕ, hN⟩ := exists_nat_ge (|z.re| + 4)
  obtain ⟨C, hC, htail⟩ := rationalTheta_uniform_log_bound
    (Bornology.isVonNBounded_singleton (𝕜 := ℂ) b) N
  have hcont : Continuous (fun x : ℝ ↦ (x : ℂ) ^ m * rationalTheta b (Real.exp x)) :=
    (Complex.continuous_ofReal.pow m).mul
      ((rationalTheta_continuousOn b).comp_continuous Real.continuous_exp Real.exp_pos)
  have hdecay (x : ℝ) :
      ‖(x : ℂ) ^ m * rationalTheta b (Real.exp x) * Complex.exp (z * x)‖ ≤
        ((m.factorial : ℝ) * C) * Real.exp (-(3 * 1) * |x|) := by
    have hpoly : |x| ^ m ≤ (m.factorial : ℝ) * Real.exp |x| := by
      have h := (div_le_iff₀ (show 0 < (m.factorial : ℝ) by positivity)).mp
        (Real.pow_div_factorial_le_exp |x| (abs_nonneg x) m)
      simpa only [mul_comm] using h
    have hweight : z.re * x ≤ |z.re| * |x| := by
      rw [← abs_mul]
      exact le_abs_self _
    rw [norm_mul, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp,
      Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    calc
      _ ≤ ((m.factorial : ℝ) * Real.exp |x|) * (C * Real.exp (-(N : ℝ) * |x|)) *
          Real.exp (|z.re| * |x|) := by
        gcongr
        exact htail b (Set.mem_singleton b) hb hFourier x
      _ = ((m.factorial : ℝ) * C) * Real.exp ((1 + |z.re| - (N : ℝ)) * |x|) := by
        rw [show (1 + |z.re| - (N : ℝ)) * |x| =
          |x| + (-(N : ℝ) * |x|) + |z.re| * |x| by ring, Real.exp_add, Real.exp_add]
        ring
      _ ≤ _ := by
        gcongr
        linarith
  obtain ⟨hint, _, hderiv⟩ := hasDerivAt_logMellin_of_decay hcont z (r := 1) one_pos
    (mul_nonneg (Nat.cast_nonneg _) hC.le) hdecay
  refine ⟨hint, ?_⟩
  simpa only [pow_succ', mul_assoc] using hderiv

end Masullo
