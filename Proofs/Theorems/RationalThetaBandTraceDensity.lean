module

public import Theorems.FixedAnnulusTraceDensity
public import Theorems.RationalThetaBandClosure

/-!
# The fixed-position trace density in the global rational theta chart

For the rational trivial isotype, (10.4.1.6–7), p. 457, and (11.2.1.8–10),
p. 489, motivate compact position localization and a right band projection.
We use the repaired weighted rational theta levels of `RationalThetaBandClosure`,
not the local one-place level of `fixedAnnulus_traceDensity`. Unlike the cited
condensation theorem, the construction permits tests below norm one. It
constructs the chart model of `Mρ A QY`; comparison to the printed
`Mρ P_geom A QY` needs the full geometric range invariance separately.
In the `L²(dx)`
chart, ordinary log convolution acquires one weight on the output and its
reciprocal on the input. An additional right multiplier acts *before* the band
projector. No input mask is commuted through the projector.
-/

open MeasureTheory Set InnerProductSpace
open scoped InnerProductSpace ENNReal

namespace Masullo.OperatorTrace

local notation "H" => Lp ℂ 2 (volume : Measure ℝ)

/-- At fixed annulus and band, the chart form of localized convolution after
projection onto the rational global theta band has an integrable basis-trace
density, also representing every further right-multiplied trace. The density
comes from the rank-one presentation, not restriction of an a.e. kernel to the
Haar diagonal. This theorem takes neither cutoff limit. -/
public theorem rationalThetaBand_traceDensity (a α s Y : ℝ) (hs : 0 ≤ s) (hα : 0 ≤ α)
    {ρ φ : ℝ → ℂ} (hρ : Continuous ρ) (hρK : HasCompactSupport ρ)
    (hφ : ContDiff ℝ 2 φ) (hφK : HasCompactSupport φ) :
    let w := symmetricStripWeightRoot α s
    let P := (rationalThetaWeightedEvenImage a hs hα {ξ | |ξ| ≤ Y}).toSubmodule.starProjection
    ∃ (B : H →L[ℂ] H) (d : ℝ → ℂ),
      (∀ z : H, (B z : ℝ → ℂ) =ᵐ[volume] fun x =>
        (ρ x * (w x : ℂ)) * ∫ y, φ (x - y) * (P z) y * (w y : ℂ)⁻¹) ∧
      Integrable d volume ∧
      (∀ {ι : Type*} (b : HilbertBasis ι ℂ H),
        HasSum (fun i => ⟪b i, B (b i)⟫_ℂ) (∫ x, d x)) ∧
      ∀ {m : ℝ → ℂ} (hm : MemLp m ∞ volume),
        Integrable (fun x => m x * d x) volume ∧
        ∀ {ι : Type*} (b : HilbertBasis ι ℂ H),
          HasSum (fun i => ⟪b i, B (logMultiplier hm (b i))⟫_ℂ) (∫ x, m x * d x) := by
  let w := symmetricStripWeightRoot α s
  let P := (rationalThetaWeightedEvenImage a hs hα {ξ | |ξ| ≤ Y}).toSubmodule.starProjection
  let p (x : ℝ) := ρ x * (w x : ℂ)
  let v (x : ℝ) := (w x : ℂ)⁻¹
  have hc : Continuous (fun x => (w x : ℂ)) :=
    Complex.continuous_ofReal.comp (continuous_symmetricStripWeightRoot α s)
  have hv : Continuous v := hc.inv₀ fun x =>
    Complex.ofReal_ne_zero.mpr (symmetricStripWeightRoot_pos α s x).ne'
  have hpK : HasCompactSupport p := hρK.mul_right
  have hp : MemLp p 2 volume := (hρ.mul hc).memLp_of_hasCompactSupport hpK
  obtain ⟨R, hR, hRsub⟩ := (hpK.union hφK).isBounded.subset_closedBall_lt 0 (0 : ℝ)
  rw [Real.closedBall_eq_Icc, zero_sub, zero_add] at hRsub
  have hpR : Function.support p ⊆ Icc (-R) R := fun _ hx => hRsub (Or.inl (subset_tsupport _ hx))
  have hφR : Function.support φ ⊆ Icc (-R) R := fun _ hx => hRsub (Or.inr (subset_tsupport _ hx))
  let D := Icc (-(2 * R)) (2 * R)
  have hq : MemLp (D.indicator v) 2 volume := by
    obtain ⟨C, hC⟩ := isCompact_Icc.bddAbove_image (f := fun y => ‖v y‖) hv.norm.continuousOn
    have : IsFiniteMeasure ((volume : Measure ℝ).restrict D) :=
      isFiniteMeasure_restrict.mpr (isCompact_Icc.measure_lt_top (μ := volume)).ne
    apply (memLp_indicator_iff_restrict measurableSet_Icc.nullMeasurableSet).2
    apply MemLp.of_bound hv.aestronglyMeasurable C
    filter_upwards [ae_restrict_mem (μ := (volume : Measure ℝ)) (s := D) measurableSet_Icc] with y hy
    exact hC (mem_image_of_mem _ hy)
  let q : H := hq.toLp _
  have hqint (F : ℝ → ℂ) : (∫ y, F y * star (q y)) = ∫ y in D, F y * v y := by
    rw [← integral_indicator measurableSet_Icc]
    apply integral_congr_ae
    filter_upwards [hq.coeFn_toLp] with y hy
    change q y = D.indicator v y at hy
    rw [hy]
    change F y * star (D.indicator v y) = D.indicator (fun y => F y * v y) y
    by_cases h : y ∈ D <;> simp [h, v]
  let : Fact (0 < 8 * R) := ⟨by positivity⟩
  obtain ⟨f, hmatch, hf⟩ := exists_circleProfile_of_support (T := 8 * R) (a := -(4 * R))
    hφ hφR (by linarith) (by linarith)
  let B := (windowKernel (hp.toLp p) q f).comp P
  let d := windowKernelTraceDensity (hp.toLp p) q f P
  refine ⟨B, d, ?_, (windowKernel_traceDensity_integrable (hp.toLp p) q f hf P).1,
    fun b => windowKernel_traceDensity b (hp.toLp p) q f hf P, ?_⟩
  · intro z
    simpa only [B, ContinuousLinearMap.comp_apply, p, v] using
      annulus_kernel_ae_input_mul p φ v hp hpR hφR q hqint f hf (fun t ht =>
        hmatch ⟨by linarith [(abs_le.mp ht).1], by linarith [(abs_le.mp ht).2]⟩) P z
  · intro m hm
    refine ⟨hm.integrable_mul (memLp_one_iff_integrable.2
      (windowKernel_traceDensity_integrable (hp.toLp p) q f hf P).1),
      fun b => (windowKernel_localized_traceDensity b (hp.toLp p) q f hf P hm).2⟩

end Masullo.OperatorTrace
