module

public import Lemmas.AnnulusKernel
public import Lemmas.CircleSynthesis
import Mathlib.Analysis.Normed.Group.Tannery

/-! # One Fourier window for a localized weighted convolution

The window and its summable Fourier coefficients are fixed before choosing any
right projection. This lets one dominate the scalar trace series uniformly.
-/

open Filter MeasureTheory Set InnerProductSpace
open scoped InnerProductSpace Topology

namespace Masullo.OperatorTrace

local notation "H" => Lp ℂ 2 (volume : Measure ℝ)

/-- Periodize the test on a single finite annulus independently of the input vector,
and include the weight and reciprocal weight in the output and input windows. -/
public theorem exists_weightedAnnulus_window {w : ℝ → ℝ} (hw : Continuous w)
    (hwpos : ∀ x, 0 < w x) {ρ φ : ℝ → ℂ}
    (hρ : Continuous ρ) (hρK : HasCompactSupport ρ)
    (hφ : ContDiff ℝ 2 φ) (hφK : HasCompactSupport φ) :
    ∃ (L : ℝ) (_hL : Fact (0 < L)) (p q : H) (f : C(AddCircle L, ℂ)),
      Summable (fourierCoeff f) ∧
      ∀ z : H, (windowKernel p q f z : ℝ → ℂ) =ᵐ[volume] fun x =>
        (ρ x * (w x : ℂ)) * ∫ y, φ (x - y) * z y * (w y : ℂ)⁻¹ := by
  let p (x : ℝ) := ρ x * (w x : ℂ)
  let v (x : ℝ) := (w x : ℂ)⁻¹
  have hc : Continuous (fun x => (w x : ℂ)) :=
    Complex.continuous_ofReal.comp hw
  have hv : Continuous v := hc.inv₀ fun x =>
    Complex.ofReal_ne_zero.mpr (hwpos x).ne'
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
  refine ⟨8 * R, inferInstance, hp.toLp p, q, f, hf, fun z => ?_⟩
  simpa only [ContinuousLinearMap.id_apply, p, v] using
    annulus_kernel_ae_input_mul p φ v hp hpR hφR q hqint f hf (fun t ht =>
      hmatch ⟨by linarith [(abs_le.mp ht).1], by linarith [(abs_le.mp ht).2]⟩)
      (ContinuousLinearMap.id ℂ H) z

/-- The scalar trace series of the window kernel is continuous under strongly
convergent right composition by contractions. -/
public theorem tendsto_windowKernel_trace {L : ℝ} [Fact (0 < L)] (p q : H)
    (f : C(AddCircle L, ℂ)) (hf : Summable (fourierCoeff f))
    {Q : ℕ → H →L[ℂ] H} {P : H →L[ℂ] H}
    (hQ : ∀ z, Tendsto (fun n => Q n z) atTop (𝓝 (P z)))
    (hQc : ∀ n z, ‖Q n z‖ ≤ ‖z‖) :
    Tendsto (fun n => ∑' k : ℤ, ⟪W q (fourier (T := L) k), Q n (outputMode p f k)⟫_ℂ)
      atTop (𝓝 (∑' k : ℤ, ⟪W q (fourier (T := L) k), P (outputMode p f k)⟫_ℂ)) := by
  refine tendsto_tsum_of_dominated_convergence ((hf.norm.mul_right ‖p‖).mul_right ‖q‖)
    (fun k => ((innerSL ℂ (W q (fourier (T := L) k))).continuous.tendsto _).comp
      (hQ (outputMode p f k))) (Eventually.of_forall fun n k => ?_)
  calc
    _ ≤ ‖W q (fourier (T := L) k)‖ * ‖Q n (outputMode p f k)‖ := norm_inner_le_norm _ _
    _ ≤ ‖q‖ * ‖outputMode p f k‖ := by
      gcongr
      · exact norm_W_fourier_le q k
      · exact hQc n _
    _ ≤ ‖q‖ * (‖fourierCoeff f k‖ * ‖p‖) := by
      rw [outputMode, norm_smul]
      gcongr
      exact norm_W_fourier_le p k
    _ = _ := mul_comm _ _

end Masullo.OperatorTrace
