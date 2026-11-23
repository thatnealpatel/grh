module

public import Props.RealLogProfileHaar
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! # Small sharp radii and a nonzero half-Haar witness -/

open Filter MeasureTheory Set
open scoped ContDiff FourierTransform SchwartzMap Topology

namespace Masullo

/-- The normalized sharp upper scalar in (12.4.1.24) over `ℚ`, summed
across real unit signs when `u` is the two-sign log-profile test. -/
@[expose] public noncomputable def realSharpCutScalar (u : ℝ → ℂ) (K : ℝ) : ℂ :=
  ∫ w in {w | |w| ≤ K}, ((Real.log K - Real.log |w| : ℝ) : ℂ) * 𝓕 u w

private theorem realSharpCutScalar_tendsto_zero {u : ℝ → ℂ}
    (huf : Integrable (𝓕 u))
    (hlog : Integrable (fun w ↦ (Real.log |w| : ℂ) * 𝓕 u w)) :
    Tendsto (realSharpCutScalar u) (𝓝[>] 0) (𝓝 0) := by
  let s (K : ℝ) : Set ℝ := {w | |w| ≤ K}
  let g (w : ℝ) : ℂ := (Real.log |w| : ℂ) * 𝓕 u w
  have hm (K : ℝ) : MeasurableSet (s K) := measurableSet_le (by fun_prop) measurable_const
  have h (K : ℝ) : realSharpCutScalar u K = ∫ w, (s K).indicator
      (fun w ↦ ((Real.log K - Real.log |w| : ℝ) : ℂ) * 𝓕 u w) w :=
    (integral_indicator (hm K)).symm
  change Tendsto (fun K ↦ realSharpCutScalar u K) (𝓝[>] 0) (𝓝 0)
  simp_rw [h]
  rw [← integral_zero (α := ℝ) (G := ℂ) (μ := volume)]
  refine tendsto_integral_filter_of_dominated_convergence (fun w ↦ ‖g w‖) ?_ ?_ hlog.norm ?_
  · exact .of_forall fun K ↦
      ((huf.const_mul (Real.log K : ℂ)).sub hlog).aestronglyMeasurable.indicator (hm K) |>.congr
        (Eventually.of_forall fun w ↦ by
          congr 1
          funext x
          simp only [Pi.sub_apply, Complex.ofReal_sub, sub_mul])
  · have hK : ∀ᶠ K : ℝ in 𝓝[>] 0, K ∈ Ioo (0 : ℝ) 1 := Ioo_mem_nhdsGT zero_lt_one
    filter_upwards [hK] with K hK
    filter_upwards [volume.ae_ne (0 : ℝ)] with w hw
    by_cases hmem : w ∈ s K
    · rw [indicator_of_mem hmem, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
        Real.norm_eq_abs, Real.norm_eq_abs]
      have hlogwk := Real.log_le_log (abs_pos.mpr hw) hmem
      have hlogk := Real.log_nonpos hK.1.le hK.2.le
      rw [abs_of_nonneg (sub_nonneg.mpr hlogwk), abs_of_nonpos (hlogwk.trans hlogk)]
      exact mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
    · rw [indicator_of_notMem hmem, norm_zero]
      exact norm_nonneg _
  · filter_upwards [volume.ae_ne (0 : ℝ)] with w hw
    refine tendsto_const_nhds.congr' ?_
    have hnear : ∀ᶠ K in 𝓝 (0 : ℝ), K < |w| := Iio_mem_nhds (abs_pos.mpr hw)
    filter_upwards [hnear.filter_mono nhdsWithin_le_nhds] with K hK
    exact (indicator_of_notMem (not_le.mpr hK) _).symm

public theorem logProfile_sharpCut_tendsto_zero {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) :
    Tendsto (realSharpCutScalar (realLogProfileAdditive (fun t ↦ f (-t))))
      (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨hd, hk, _⟩ := real_log_profile_additive_test (hf.comp contDiff_neg)
    (hc.comp_homeomorph (Homeomorph.neg ℝ))
  let v := hk.toSchwartzMap hd
  exact realSharpCutScalar_tendsto_zero (𝓕 v).integrable (RealLogFourier.log_fourier_integrable v)

public theorem exists_nonzero_half_haar :
    ∃ f : ℝ → ℂ, ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧ f 0 = 0 ∧
      ((1 / 2 : ℂ) * ∫ z, realLogProfileAdditive (fun t ↦ f (-t)) z / ((|z| : ℝ) : ℂ)) ≠ 0 := by
  let bump : ContDiffBump (1 : ℝ) := ⟨1/4, 1/2, by norm_num, by norm_num⟩
  let f (t : ℝ) : ℂ := bump t
  have hf : ContDiff ℝ ∞ f := Complex.ofRealCLM.contDiff.comp bump.contDiff
  have hc : HasCompactSupport f := bump.hasCompactSupport.comp_left Complex.ofReal_zero
  have hzero : f 0 = 0 := by
    have hz : (0 : ℝ) ∉ Function.support bump := by
      rw [bump.support_eq]
      norm_num [bump, Metric.mem_ball, Real.dist_eq]
    simp [f, Function.notMem_support.mp hz]
  let u := realLogProfileAdditive (fun t ↦ f (-t))
  obtain ⟨hd, hk, huz⟩ := real_log_profile_additive_test (hf.comp contDiff_neg)
    (hc.comp_homeomorph (Homeomorph.neg ℝ))
  change u 0 = f (-0) at huz
  simp only [neg_zero, hzero] at huz
  have hi : Integrable (fun z ↦ u z / ((|z| : ℝ) : ℂ)) := by
    let v := hk.toSchwartzMap hd
    simpa only [huz, zero_mul, sub_zero] using
      RealLogFourier.remainder_div_integrable (u := u) hd.continuous
        v.differentiable.differentiableAt v.integrable
  let g (z : ℝ) : ℝ := (u z / ((|z| : ℝ) : ℂ)).re
  have hgi : Integrable g := Complex.reCLM.integrable_comp hi
  have hgn : 0 ≤ g := by
    intro z
    simp only [g, u, realLogProfileAdditive]
    split_ifs with hz
    · simp
    · rw [← Complex.ofReal_mul, ← Complex.ofReal_div, Complex.ofReal_re]
      exact div_nonneg (mul_nonneg (Real.rpow_nonneg (abs_nonneg _) _) bump.nonneg) (abs_nonneg _)
  let x := Real.exp (-1) - 1
  have hx : x < 0 := sub_neg.mpr (Real.exp_lt_one_iff.mpr (by norm_num))
  have hxc : ContinuousAt g x :=
    Complex.reCLM.continuous.continuousAt.comp (hd.continuous.continuousAt.div
      (Complex.ofRealCLM.continuous.comp continuous_abs).continuousAt
      (Complex.ofReal_ne_zero.mpr (abs_pos.mpr hx.ne).ne'))
  have hgx : g x ≠ 0 := by
    have hx' : 1 + x = Real.exp (-1) := by dsimp [x]; ring
    have hb : bump 1 = 1 := bump.one_of_mem_closedBall (Metric.mem_closedBall_self bump.rIn_pos.le)
    dsimp only [g, u, realLogProfileAdditive]
    rw [hx', ite_eq_right (Real.exp_pos _).ne', abs_of_pos (Real.exp_pos _), Real.log_exp]
    change ((↑(Real.exp (-1) ^ (-(1/2) : ℝ)) * ↑(bump (-(-1))) / ((|x| : ℝ) : ℂ)).re : ℝ) ≠ 0
    rw [neg_neg, hb, ← Complex.ofReal_mul, ← Complex.ofReal_div, Complex.ofReal_re, mul_one]
    exact (div_pos (Real.rpow_pos_of_pos (Real.exp_pos _) _) (abs_pos.mpr hx.ne)).ne'
  have hgpos : 0 < ∫ z, g z :=
    (integral_pos_iff_support_of_nonneg hgn hgi).2
      ((volume : Measure ℝ).measure_pos_of_mem_nhds (hxc.eventually_ne hgx))
  have hcomm : (∫ z, g z) = (∫ z, u z / ((|z| : ℝ) : ℂ)).re :=
    Complex.reCLM.integral_comp_comm hi
  exact ⟨f, hf, hc, hzero,
    mul_ne_zero (by norm_num) (fun h ↦ hgpos.ne' (by rw [hcomm, h, Complex.zero_re]))⟩

end Masullo
