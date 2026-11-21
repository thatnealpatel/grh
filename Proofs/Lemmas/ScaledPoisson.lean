module

public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.Fourier.PoissonSummation
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.PSeries
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# Poisson summation on a scaled real lattice

Analytic ingredients for the rational unramified model of Masullo's
(2.2.3.2), p. 82.
-/

open MeasureTheory
open scoped FourierTransform SchwartzMap

namespace Masullo

private noncomputable def dilateSchwartz (b : 𝓢(ℝ, ℂ)) (t : ℝ) (ht : t ≠ 0) : 𝓢(ℝ, ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (ContinuousLinearEquiv.unitsEquivAut ℝ (Units.mk0 t ht)) b

private theorem dilateSchwartz_apply (b : 𝓢(ℝ, ℂ)) (t : ℝ) (ht : t ≠ 0) (x : ℝ) :
    dilateSchwartz b t ht x = b (t * x) := by
  simp [dilateSchwartz, mul_comm]

private theorem fourier_dilateSchwartz (b : 𝓢(ℝ, ℂ)) {t : ℝ} (ht : 0 < t) (u : ℝ) :
    𝓕 (dilateSchwartz b t ht.ne') u = t⁻¹ • 𝓕 b (t⁻¹ * u) := by
  simp only [SchwartzMap.fourier_coe, Real.fourier_real_eq_integral_exp_smul,
    dilateSchwartz_apply]
  -- Change variables by the positive factor `t⁻¹` on the right-hand side.
  rw [← abs_of_pos (inv_pos.mpr ht), ← Measure.integral_comp_mul_left]
  congr 1
  funext x
  congr 2
  rw [abs_of_pos (inv_pos.mpr ht)]
  field_simp

/-- A Schwartz function has absolutely summable samples on any nonzero real dilation
of the integer lattice. -/
public theorem summable_norm_schwartz_int_mul (b : 𝓢(ℝ, ℂ)) {t : ℝ} (ht : t ≠ 0) :
    Summable (fun n : ℤ ↦ ‖b (t * (n : ℝ))‖) := by
  have hs : Summable (fun n : ℤ ↦ b (t * (n : ℝ))) := by
    apply summable_of_isBigO (Real.summable_abs_int_rpow one_lt_two)
    simpa only [Function.comp_def, dilateSchwartz_apply, Real.norm_eq_abs] using
      ((dilateSchwartz b t ht).isBigO_cocompact_rpow (-2)).comp_tendsto
        Int.tendsto_coe_cofinite
  exact hs.norm

/-- Poisson summation at zero for the dilated Schwartz function. -/
public theorem schwartz_scaled_poisson (b : 𝓢(ℝ, ℂ)) {t : ℝ} (ht : 0 < t) :
    (∑' n : ℤ, b (t * n)) = t⁻¹ • ∑' n : ℤ, 𝓕 b (t⁻¹ * n) := by
  simpa [dilateSchwartz_apply, fourier_dilateSchwartz _ ht, tsum_mul_left] using
    (dilateSchwartz b t ht.ne').tsum_eq_tsum_fourier 0

end Masullo
