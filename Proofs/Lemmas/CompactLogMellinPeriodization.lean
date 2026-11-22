module

public import Lemmas.CompactLogMellin
public import Theorems.MonogenicPeriodizationSection
public import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.Fourier.PoissonSummation
import Mathlib.Tactic.FieldSimp

/-! # Fourier coefficients and uniqueness for compact log Mellin profiles

These give the Fourier steps in the compact-away repair of Masullo's
Lemma 5.3.4.2(2), p. 260, at period `log 3`. They do not assert pole
removal or identify an adelic lift.
-/

open ContinuousMap Function MeasureTheory Set TopologicalSpace
open scoped FourierTransform

namespace Masullo

-- On each compact, only finitely many integer translates can meet the support.
private theorem summable_norm_restrict_int_translate {f : C(ℝ, ℂ)}
    (hf : HasCompactSupport (f : ℝ → ℂ)) (K : Compacts ℝ) :
    Summable fun k : ℤ ↦ ‖(f.comp (ContinuousMap.addRight k)).restrict K‖ := by
  obtain ⟨A, hA⟩ := hf.bddAbove_image continuous_abs.continuousOn
  obtain ⟨B, hB⟩ := K.isCompact.bddAbove_image continuous_abs.continuousOn
  apply summable_of_hasFiniteSupport
  refine (isCompact_iff_finite.mp (isCompact_closedBall (0 : ℤ) (A + B))).subset ?_
  intro k hk
  by_contra hbound
  apply hk
  simp only [norm_eq_zero]
  ext x
  change f ((x : ℝ) + (k : ℝ)) = 0
  by_contra hx
  have h1 := hA (mem_image_of_mem _ (subset_tsupport _ hx))
  have h2 := hB (mem_image_of_mem _ x.property)
  apply hbound
  rw [Metric.mem_closedBall, Int.dist_eq, Int.cast_zero, sub_zero]
  have h := abs_sub_le ((x : ℝ) + (k : ℝ)) 0 (x : ℝ)
  rw [sub_zero, add_sub_cancel_left, zero_sub, abs_neg] at h
  linarith

private theorem fourier_rescale_neg {L : ℝ} (hL : 0 < L) (g : ℝ → ℂ) (n : ℤ) :
    𝓕 (fun u : ℝ ↦ g (L * u)) (((-n : ℤ) : ℝ)) =
      compactLogMellin g (2 * (Real.pi : ℂ) * n * Complex.I / (L : ℂ)) / (L : ℂ) := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  let F (x : ℝ) := g x * Complex.exp ((2 * (Real.pi : ℂ) * n * Complex.I / (L : ℂ)) * x)
  have h (u : ℝ) : Complex.exp ((↑(-2 * Real.pi * u * ((-n : ℤ) : ℝ)) : ℂ) * Complex.I) •
      g (L * u) = F (L * u) := by
    simp only [smul_eq_mul, F, mul_comm (Complex.exp _) (g _)]
    congr 2
    push_cast
    field_simp [Complex.ofReal_ne_zero.mpr hL.ne']
  simp_rw [h]
  rw [Measure.integral_comp_mul_left, abs_of_pos (inv_pos.mpr hL), Complex.real_smul,
    Complex.ofReal_inv, div_eq_inv_mul]
  rfl

/-- The normalized Fourier coefficient at `-n` of the `L`-periodization of a
continuous compact log profile is its positive imaginary Mellin sample divided by `L`. -/
public theorem fourierCoeffOn_logPeriodization_neg {L : ℝ} (hL : 0 < L) {g : ℝ → ℂ}
    (hg : Continuous g) (hc : HasCompactSupport g) (n : ℤ) :
    fourierCoeffOn (a := 0) hL (logPeriodization L g) (-n) =
      compactLogMellin g (2 * (Real.pi : ℂ) * n * Complex.I / (L : ℂ)) / (L : ℂ) := by
  let f : C(ℝ, ℂ) := ⟨fun u ↦ g (L * u), hg.comp (continuous_const.mul continuous_id)⟩
  have hf : HasCompactSupport (f : ℝ → ℂ) :=
    hc.comp_homeomorph (Homeomorph.mulLeft₀ L hL.ne')
  have hs := summable_norm_restrict_int_translate hf
  have hs' : Summable fun k : ℤ ↦ f.comp (ContinuousMap.addRight (k : ℝ)) :=
    summable_of_locally_summable_norm hs
  let P₁ := (f.periodic_tsum_comp_add_zsmul 1).lift
  have hP (u : ℝ) : P₁ (u : UnitAddCircle) = logPeriodization L g (L * u) := by
    simp only [P₁, Periodic.lift_coe, zsmul_one, logPeriodization]
    rw [← ContinuousMap.tsum_apply hs']
    congr 1
    funext k
    change g (L * (u + k)) = g (L * u + (k : ℝ) * L)
    congr 1
    ring
  have hchar (u : ℝ) : fourier n (u : UnitAddCircle) =
      fourier n ((L * u : ℝ) : AddCircle L) := by
    simp only [fourier_coe_apply, Complex.ofReal_one, div_one, Complex.ofReal_mul]
    congr 1
    field_simp [Complex.ofReal_ne_zero.mpr hL.ne']
  have hcoeff : fourierCoeff P₁ (-n) =
      fourierCoeffOn (a := 0) hL (logPeriodization L g) (-n) := by
    rw [fourierCoeff_eq_intervalIntegral _ _ 0, fourierCoeffOn_eq_integral]
    simp only [neg_neg, zero_add, div_one, one_smul, sub_zero, one_div]
    simp_rw [hP, hchar]
    let F (x : ℝ) := fourier n (x : AddCircle L) • logPeriodization L g x
    simpa only [F, mul_zero, mul_one, fourier_coe_apply, sub_zero] using
      (intervalIntegral.integral_comp_mul_left (a := 0) (b := 1) F hL.ne')
  rw [← hcoeff]
  exact (Real.fourierCoeff_tsum_comp_add hs (-n)).trans (fourier_rescale_neg hL g n)

/-- A continuous compact log profile with zero Mellin samples on the imaginary
lattice of period `L` has identically zero `L`-periodization. -/
public theorem logPeriodization_eq_zero_of_compactLogMellin_samples_eq_zero {L : ℝ} (hL : 0 < L)
    {g : ℝ → ℂ} (hg : Continuous g) (hc : HasCompactSupport g)
    (hM : ∀ n : ℤ, compactLogMellin g (2 * (Real.pi : ℂ) * n * Complex.I / (L : ℂ)) = 0)
    (x : ℝ) : logPeriodization L g x = 0 := by
  let f : C(ℝ, ℂ) := ⟨fun u ↦ g (L * u), hg.comp (continuous_const.mul continuous_id)⟩
  have hf : HasCompactSupport (f : ℝ → ℂ) :=
    hc.comp_homeomorph (Homeomorph.mulLeft₀ L hL.ne')
  have hF (n : ℤ) : 𝓕 (f : ℝ → ℂ) (n : ℝ) = 0 := by
    simpa only [f, ContinuousMap.coe_mk, neg_neg, hM, zero_div] using fourier_rescale_neg hL g (-n)
  have hsum : Summable fun n : ℤ ↦ 𝓕 (f : ℝ → ℂ) (n : ℝ) := by
    simp only [hF, summable_zero]
  have hP := Real.tsum_eq_tsum_fourier (summable_norm_restrict_int_translate hf) hsum (x / L)
  simp only [hF, zero_mul, tsum_zero] at hP
  have harg (k : ℤ) : L * (x / L + k) = x + (k : ℝ) * L := by
    rw [mul_add, mul_comm L (x / L), div_mul_cancel₀ _ hL.ne', mul_comm L (k : ℝ)]
  simpa only [f, ContinuousMap.coe_mk, harg, logPeriodization] using hP

end Masullo
