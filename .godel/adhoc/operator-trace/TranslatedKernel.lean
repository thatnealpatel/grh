import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.MeasureTheory.Integral.DominatedConvergence

open MeasureTheory Filter
open scoped ComplexConjugate

namespace AdHoc
variable {L : ℝ} [Fact (0 < L)] {μ : Measure ℝ}

omit [Fact (0 < L)] in
private theorem fourier_difference (n : ℤ) (x y : AddCircle L) :
    fourier n (x - y) = fourier n x * conj (fourier n y) := by
  simp only [fourier_apply, sub_eq_add_neg, zsmul_add, zsmul_neg, AddCircle.toCircle_add,
    AddCircle.toCircle_neg, Circle.coe_mul, Circle.coe_inv_eq_conj]

/-- Integrate the translated periodic kernel against an arbitrary integrable
complex density. The frequency sign here determines the input Riesz vector. -/
theorem hasSum_translated_integral (f : C(AddCircle L, ℂ)) (hf : Summable (fourierCoeff f))
    {g : ℝ → ℂ} (hg : Integrable g μ) (x : AddCircle L) :
    HasSum (fun n : ℤ => (fourierCoeff f n * (∫ y, conj (fourier n (y : AddCircle L)) * g y ∂μ)) *
      fourier n x) (∫ y, f (x - (y : AddCircle L)) * g y ∂μ) := by
  let F (n : ℤ) (y : ℝ) := fourierCoeff f n * fourier n (x - (y : AddCircle L)) * g y
  have hcont (n : ℤ) : Continuous (fun y : ℝ => fourierCoeff f n * fourier n (x - (y : AddCircle L))) :=
    continuous_const.mul ((fourier n).continuous.comp (continuous_const.sub (AddCircle.continuous_mk' L)))
  have hmeas n : AEStronglyMeasurable (F n) μ := (hcont n).aestronglyMeasurable.mul hg.1
  have hn (n : ℤ) (y : ℝ) : ‖F n y‖ = ‖fourierCoeff f n‖ * ‖g y‖ := by
    simp only [F, norm_mul, fourier_apply, Circle.norm_coe, mul_one]
  have h := hasSum_integral_of_dominated_convergence (μ := μ)
    (fun n y => ‖fourierCoeff f n‖ * ‖g y‖) hmeas (fun n => ae_of_all _ (fun y => (hn n y).le))
    (ae_of_all _ (fun y => hf.norm.mul_right ‖g y‖))
    (by simpa only [tsum_mul_right] using hg.norm.const_mul (∑' n, ‖fourierCoeff f n‖))
    (ae_of_all _ (fun y => (has_pointwise_sum_fourier_series_of_summable hf (x - (y : AddCircle L))).mul_right (g y)))
  convert h using 1
  funext n
  rw [← integral_const_mul, ← integral_mul_const]
  simp only [F, fourier_difference]
  apply integral_congr_ae
  filter_upwards with y
  ring

end AdHoc
