module

public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import Mathlib.Analysis.LocallyConvex.WithSeminorms
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

/-- The lattice sum is bounded by a fixed summable majorant times the appropriate
Schwartz seminorm and inverse power of the scale. -/
private theorem norm_tsum_schwartz_int_mul_nonzero_le (b : 𝓢(ℝ, ℂ)) (N : ℕ) {t : ℝ}
    (ht : 1 ≤ t) :
    ‖∑' n : {n : ℤ // n ≠ 0}, b (t * (n : ℤ))‖ ≤
      (SchwartzMap.seminorm ℂ (N + 2) 0 b / t ^ N) *
        ∑' n : {n : ℤ // n ≠ 0}, (|((n : ℤ) : ℝ)| ^ 2)⁻¹ := by
  have ht0 : 0 < t := zero_lt_one.trans_le ht
  let p := SchwartzMap.seminorm ℂ (N + 2) 0 b
  have hs : Summable (fun n : {n : ℤ // n ≠ 0} ↦ (|((n : ℤ) : ℝ)| ^ 2)⁻¹) := by
    have h : Summable (fun n : ℤ ↦ (|(n : ℝ)| ^ 2)⁻¹) := by
      simpa only [Real.rpow_neg (abs_nonneg _), Real.rpow_two] using
        (Real.summable_abs_int_rpow one_lt_two)
    exact h.subtype (fun n : ℤ ↦ n ≠ 0)
  have hnorm := (summable_norm_schwartz_int_mul b ht0.ne').subtype (fun n : ℤ ↦ n ≠ 0)
  refine (norm_tsum_le_tsum_norm hnorm).trans ?_
  rw [← tsum_mul_left]
  refine hnorm.tsum_le_tsum ?_ (hs.mul_left _)
  intro n
  have hn : (1 : ℝ) ≤ |((n : ℤ) : ℝ)| := by exact_mod_cast Int.one_le_abs n.property
  have hn0 : 0 < |((n : ℤ) : ℝ)| := zero_lt_one.trans_le hn
  rw [← div_eq_mul_inv, le_div_iff₀ (pow_pos hn0 _), div_eq_mul_inv,
    le_mul_inv_iff₀ (pow_pos ht0 _)]
  have hp : ‖t * ((n : ℤ) : ℝ)‖ ^ (N + 2) * ‖b (t * (n : ℤ))‖ ≤ p := by
    simpa [p, norm_iteratedFDeriv_zero] using b.le_seminorm ℂ (N + 2) 0 (t * (n : ℤ))
  have hpower : t ^ N * |((n : ℤ) : ℝ)| ^ 2 ≤ ‖t * ((n : ℤ) : ℝ)‖ ^ (N + 2) := by
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos ht0, mul_pow]
    exact mul_le_mul (pow_le_pow_right₀ ht (Nat.le_add_right N 2))
      (pow_le_pow_right₀ hn (Nat.le_add_left 2 N)) (by positivity) (by positivity)
  calc
    ‖b (t * (n : ℤ))‖ * |((n : ℤ) : ℝ)| ^ 2 * t ^ N =
        (t ^ N * |((n : ℤ) : ℝ)| ^ 2) * ‖b (t * (n : ℤ))‖ := by ring
    _ ≤ ‖t * ((n : ℤ) : ℝ)‖ ^ (N + 2) * ‖b (t * (n : ℤ))‖ := by gcongr
    _ ≤ p := hp

/-- The large-scale lattice estimate is uniform on bounded subsets of Schwartz space. -/
public theorem exists_uniform_schwartz_lattice_bound {B : Set 𝓢(ℝ, ℂ)}
    (hB : Bornology.IsVonNBounded ℂ B) (N : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ b ∈ B, ∀ t : ℝ, 1 ≤ t →
      ‖∑' n : {n : ℤ // n ≠ 0}, b (t * (n : ℤ))‖ ≤ C / t ^ N := by
  obtain ⟨P, hP, hBP⟩ := ((schwartz_withSeminorms ℂ ℝ ℂ).isVonNBounded_iff_seminorm_bounded
    |>.mp hB) (N + 2, 0)
  let D := ∑' n : {n : ℤ // n ≠ 0}, (|((n : ℤ) : ℝ)| ^ 2)⁻¹
  have hD : 0 ≤ D := tsum_nonneg fun _ ↦ by positivity
  refine ⟨P * D + 1, by positivity, fun b hb t ht ↦ ?_⟩
  have ht0 : 0 < t := zero_lt_one.trans_le ht
  calc
    _ ≤ (SchwartzMap.seminorm ℂ (N + 2) 0 b / t ^ N) * D :=
      norm_tsum_schwartz_int_mul_nonzero_le b N ht
    _ ≤ (P / t ^ N) * D := by
      exact mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right (hBP b hb).le (by positivity)) hD
    _ = (P * D) / t ^ N := by ring
    _ ≤ (P * D + 1) / t ^ N := div_le_div_of_nonneg_right (by linarith) (by positivity)

end Masullo
