module

public import Theorems.RationalThetaMellin
import Lemmas.LogMellinDerivative

/-!
# Entire rational theta Mellin transform with both zero modes removed

This is the rational unramified lattice model of Masullo's Theorem
3.2.2.1(2)(a) and (3)(a), pp. 124–125, for the trivial compact isotype.
Here we differentiate the log-norm integral directly using the two-tail
bound, rather than proving holomorphy by locally uniform truncation.
-/

open MeasureTheory
open scoped FourierTransform SchwartzMap

namespace Masullo

/-- Both zero modes vanish, so the theta Mellin integrand and its parameter
derivative are absolutely integrable at every complex parameter. The derivative
of the integral inserts the factor `x`, the logarithm of the norm. -/
public theorem hasDerivAt_rationalTheta_mellin (b : 𝓢(ℝ, ℂ))
    (hb : b 0 = 0) (hFourier : (𝓕 b) 0 = 0) (z : ℂ) :
    Integrable (fun x : ℝ ↦ rationalTheta b (Real.exp x) * Complex.exp (z * x)) ∧
    Integrable (fun x : ℝ ↦ (x : ℂ) * (rationalTheta b (Real.exp x) * Complex.exp (z * x))) ∧
    HasDerivAt (fun w : ℂ ↦ ∫ x : ℝ, rationalTheta b (Real.exp x) * Complex.exp (w * x))
      (∫ x : ℝ, (x : ℂ) * (rationalTheta b (Real.exp x) * Complex.exp (z * x))) z := by
  obtain ⟨N : ℕ, hN⟩ := exists_nat_ge (|z.re| + 3)
  obtain ⟨C, hC, htail⟩ := rationalTheta_uniform_log_bound
    (Bornology.isVonNBounded_singleton (𝕜 := ℂ) b) N
  have hcont := (rationalTheta_continuousOn b).comp_continuous Real.continuous_exp Real.exp_pos
  refine hasDerivAt_logMellin_of_decay hcont z (r := 1) one_pos hC.le fun x ↦ ?_
  have hweight : z.re * x ≤ |z.re| * |x| := by
    rw [← abs_mul]
    exact le_abs_self _
  rw [norm_mul, Complex.norm_exp, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, sub_zero]
  calc
    _ ≤ C * Real.exp (-(N : ℝ) * |x|) * Real.exp (|z.re| * |x|) :=
      mul_le_mul (htail b (Set.mem_singleton b) hb hFourier x) (Real.exp_le_exp.mpr hweight)
        (Real.exp_pos _).le (by positivity)
    _ = C * Real.exp ((|z.re| - (N : ℝ)) * |x|) := by
      rw [mul_assoc, ← Real.exp_add]
      congr 2
      ring
    _ ≤ _ := by
      gcongr
      linarith

/-- The two-moment rational theta Mellin transform is entire. -/
public theorem differentiable_rationalTheta_mellin (b : 𝓢(ℝ, ℂ))
    (hb : b 0 = 0) (hFourier : (𝓕 b) 0 = 0) :
    Differentiable ℂ (fun z : ℂ ↦ ∫ x : ℝ,
      rationalTheta b (Real.exp x) * Complex.exp (z * x)) :=
  fun z ↦ (hasDerivAt_rationalTheta_mellin b hb hFourier z).2.2.differentiableAt

end Masullo
