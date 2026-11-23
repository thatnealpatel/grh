module

public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

/-! # Analyticity of compactly carried translation averages -/

open Filter MeasureTheory Metric Set
open scoped Topology

namespace Masullo

private theorem add_ofReal_mem_rightHalfPlane {z : ℂ} {u : ℝ}
    (hz : 0 < z.re) (hu : 0 ≤ u) : 0 < (z + (u : ℂ)).re := by
  rw [Complex.add_re, Complex.ofReal_re]
  exact add_pos_of_pos_of_nonneg hz hu

private theorem integrable_translate_of_ae_mem_Icc {μ : Measure ℝ} [IsFiniteMeasure μ]
    {D : ℝ} (hμ : ∀ᵐ u ∂μ, u ∈ Icc 0 D) {G : ℂ → ℂ}
    (hG : ContinuousOn G {z : ℂ | 0 < z.re}) {z : ℂ} (hz : 0 < z.re) :
    Integrable (fun u : ℝ ↦ G (z + (u : ℂ))) μ := by
  have hcont : ContinuousOn (fun u : ℝ ↦ G (z + (u : ℂ))) (Icc 0 D) :=
    hG.comp' (continuous_const.add Complex.continuous_ofReal).continuousOn
      (fun _ hu ↦ add_ofReal_mem_rightHalfPlane hz hu.1)
  have hint := hcont.integrableOn_compact (μ := μ) isCompact_Icc
  rw [IntegrableOn, Measure.restrict_eq_self_of_ae_mem hμ] at hint
  exact hint

/-- The complex average is holomorphic throughout the open right half-plane. -/
private theorem compactLogAverage_complex_analyticOnNhd {μ : Measure ℝ} [IsFiniteMeasure μ]
    {D : ℝ} (hμ : ∀ᵐ u ∂μ, u ∈ Icc 0 D) {H : ℂ → ℂ}
    (hH : AnalyticOnNhd ℂ H {z : ℂ | 0 < z.re}) :
    AnalyticOnNhd ℂ (fun z : ℂ ↦ ∫ u, H (z + (u : ℂ)) ∂μ) {z : ℂ | 0 < z.re} := by
  have hopen : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  refine DifferentiableOn.analyticOnNhd (fun z hz ↦ ?_) hopen
  obtain ⟨r, hr, hball⟩ := nhds_basis_closedBall.mem_iff.mp (hopen.mem_nhds hz)
  let s := closedBall z r
  have hs : s ∈ 𝓝 z := closedBall_mem_nhds z hr
  let shift (p : ℂ × ℝ) : ℂ := p.1 + (p.2 : ℂ)
  have hshift : Continuous shift := continuous_fst.add (Complex.continuous_ofReal.comp continuous_snd)
  have hshift_mem : MapsTo shift (s ×ˢ Icc 0 D) {z : ℂ | 0 < z.re} :=
    fun _ hp ↦ add_ofReal_mem_rightHalfPlane (hball hp.1) hp.2.1
  have hK : IsCompact (s ×ˢ Icc 0 D) := (isCompact_closedBall z r).prod isCompact_Icc
  have hcont' := hH.deriv.continuousOn
  -- Compactness bounds the shifted derivatives uniformly, even for an empty carrier.
  have hcontK := hcont'.comp' hshift.continuousOn hshift_mem
  obtain ⟨C, hC⟩ := (hK.image_of_continuousOn hcontK).isBounded.exists_norm_le
  have hint (w : ℂ) (hw : w ∈ s) : Integrable (fun u : ℝ ↦ H (w + (u : ℂ))) μ :=
    integrable_translate_of_ae_mem_Icc hμ hH.continuousOn (hball hw)
  have hmeas : ∀ᶠ w in 𝓝 z, AEStronglyMeasurable (fun u : ℝ ↦ H (w + (u : ℂ))) μ :=
    (show ∀ᶠ w in 𝓝 z, w ∈ s from hs).mono fun w hw ↦ (hint w hw).aestronglyMeasurable
  have hzball : z ∈ s := mem_closedBall_self hr.le
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun w (u : ℝ) ↦ H (w + (u : ℂ)))
    (F' := fun w (u : ℝ) ↦ deriv H (w + (u : ℂ)))
    hs hmeas (hint z hzball)
    (integrable_translate_of_ae_mem_Icc hμ hcont' hz).aestronglyMeasurable
    ?_ (integrable_const C) ?_).2.differentiableAt.differentiableWithinAt
  · exact hμ.mono fun u hu w hw ↦ hC _ ⟨(w, u), ⟨hw, hu⟩, rfl⟩
  · refine hμ.mono fun u hu w hw ↦ ?_
    have hderiv := (hH _ (hshift_mem (x := (w, u)) ⟨hw, hu⟩)).differentiableAt.hasDerivAt
    simpa only [Function.comp_def, shift, mul_one] using
      hderiv.comp w ((hasDerivAt_id' w).add_const (u : ℂ))

/-- Taking the real part of the compactly carried average gives a real analytic function
on the positive real line. If the carrier is empty, the carrying condition forces the measure
to vanish; the proof uses no nonemptiness assumption. -/
public theorem compactLogAverage_analyticOnNhd {μ : Measure ℝ} [IsFiniteMeasure μ] {D : ℝ}
    (hμ : μ (Icc 0 D)ᶜ = 0) {H : ℂ → ℂ}
    (hH : AnalyticOnNhd ℂ H {z : ℂ | 0 < z.re}) :
    AnalyticOnNhd ℝ (fun t : ℝ ↦ ∫ u, (H (Complex.ofReal (t + u))).re ∂μ) (Ioi 0) := by
  have hcarrier : ∀ᵐ u ∂μ, u ∈ Icc 0 D := ae_iff.mpr hμ
  have hanalytic := compactLogAverage_complex_analyticOnNhd hcarrier hH
  intro t ht
  have ht' : 0 < (t : ℂ).re := by simpa only [Complex.ofReal_re] using mem_Ioi.mp ht
  refine (hanalytic (t : ℂ) ht').re_ofReal.congr ?_
  filter_upwards [isOpen_Ioi.mem_nhds ht] with x hx
  have hx' : 0 < (x : ℂ).re := by simpa only [Complex.ofReal_re] using mem_Ioi.mp hx
  have hint := integrable_translate_of_ae_mem_Icc hcarrier hH.continuousOn hx'
  simpa only [Complex.ofReal_add, Complex.reCLM_apply] using
    (Complex.reCLM.integral_comp_comm hint).symm

end Masullo
