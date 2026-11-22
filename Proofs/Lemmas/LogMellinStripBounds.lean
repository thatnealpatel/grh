module

public import Mathlib.Analysis.Complex.Trigonometric

/-! # Pointwise norm bounds on a vertical strip -/

namespace Masullo

/-- The two real endpoints dominate the weighted log-Mellin integrand on the strip. -/
public theorem norm_logMellinIntegrand_le_endpoints (p : ℝ → ℂ) {a b : ℝ} {s : ℂ}
    (ha : a ≤ s.re) (hb : s.re ≤ b) (x : ℝ) :
    ‖p x * Complex.exp (s * x)‖ ≤
      ‖p x * Complex.exp ((a : ℂ) * x)‖ + ‖p x * Complex.exp ((b : ℂ) * x)‖ := by
  simp only [Complex.norm_mul, Complex.norm_exp, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, sub_zero]
  by_cases hx : 0 ≤ x
  · exact (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hb hx))
      (norm_nonneg _)).trans (le_add_of_nonneg_left (by positivity))
  · exact (mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_right ha (le_of_not_ge hx)))
      (norm_nonneg _)).trans (le_add_of_nonneg_right (by positivity))

/-- Each shifted linear factor costs at most one power of the height on the strip. -/
public theorem norm_sub_le_verticalStrip {a b : ℝ} {s : ℂ} (z : ℂ)
    (ha : a ≤ s.re) (hb : s.re ≤ b) :
    ‖s - z‖ ≤ (1 + |a| + |b| + ‖z‖) * (1 + |s.im|) := by
  have hre : |s.re| ≤ |a| + |b| := abs_le.mpr
    ⟨by linarith [neg_abs_le a, abs_nonneg b], by linarith [le_abs_self b, abs_nonneg a]⟩
  calc
    ‖s - z‖ ≤ ‖s‖ + ‖z‖ := norm_sub_le _ _
    _ ≤ |s.re| + |s.im| + ‖z‖ := add_le_add (Complex.norm_le_abs_re_add_abs_im _) le_rfl
    _ ≤ (1 + |a| + |b| + ‖z‖) * (1 + |s.im|) := by
      nlinarith only [hre, mul_nonneg (show 0 ≤ |a| + |b| + ‖z‖ by positivity) (abs_nonneg s.im)]

end Masullo
