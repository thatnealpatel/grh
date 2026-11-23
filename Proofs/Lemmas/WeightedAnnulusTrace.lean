module

public import Lemmas.AnnulusKernel
public import Lemmas.CircleSynthesis
import Mathlib.Analysis.Normed.Group.Tannery

/-! # One Fourier window for a localized weighted convolution

The window and its summable Fourier coefficients are fixed before choosing any
right projection. This lets one dominate the scalar trace series uniformly.
-/

open Filter MeasureTheory Set InnerProductSpace
open scoped ComplexConjugate InnerProductSpace Topology

namespace Masullo.OperatorTrace

local notation "H" => Lp ℂ 2 (volume : Measure ℝ)

/-- Periodize the test on a single finite annulus independently of the input vector,
and include the weight and reciprocal weight in the output and input windows. -/
private theorem exists_weightedAnnulus_window_diagonal {w : ℝ → ℝ} (hw : Continuous w)
    (hwpos : ∀ x, 0 < w x) {ρ φ : ℝ → ℂ}
    (hρ : Continuous ρ) (hρK : HasCompactSupport ρ)
    (hφ : ContDiff ℝ 2 φ) (hφK : HasCompactSupport φ) :
    ∃ (L : ℝ) (_hL : Fact (0 < L)) (p q : H) (f : C(AddCircle L, ℂ)),
      Summable (fourierCoeff f) ∧ f 0 = φ 0 ∧ ⟪q, p⟫_ℂ = (∫ x, ρ x) ∧
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
  have hzero : f 0 = φ 0 := by
    simpa only [AddCircle.coe_zero] using hmatch (show (0 : ℝ) ∈ Icc (-(4 * R)) (-(4 * R) + 8 * R) by
      constructor <;> linarith)
  have hinner : ⟪q, hp.toLp p⟫_ℂ = ∫ x, ρ x := by
    rw [MeasureTheory.L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hq.coeFn_toLp, hp.coeFn_toLp] with x hqx hpx
    change q x = D.indicator v x at hqx
    rw [hqx, hpx]
    by_cases hx : x ∈ D
    · simp only [Set.indicator_of_mem hx, RCLike.inner_apply, v, p, map_inv₀,
        Complex.conj_ofReal]
      have hn : (w x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hwpos x).ne'
      calc
        _ = ρ x * ((w x : ℂ) * (w x : ℂ)⁻¹) := by ring
        _ = _ := by rw [mul_inv_cancel₀ hn, mul_one]
    · have hρx : ρ x = 0 := by
        by_contra hne
        have hxR := hpR (show p x ≠ 0 from
          mul_ne_zero hne (Complex.ofReal_ne_zero.mpr (hwpos x).ne'))
        exact hx ⟨by linarith [hxR.1], by linarith [hxR.2]⟩
      simp [hx, hρx]
  refine ⟨8 * R, inferInstance, hp.toLp p, q, f, hf, hzero, hinner, fun z => ?_⟩
  simpa only [ContinuousLinearMap.id_apply, p, v] using
    annulus_kernel_ae_input_mul p φ v hp hpR hφR q hqint f hf (fun t ht =>
      hmatch ⟨by linarith [(abs_le.mp ht).1], by linarith [(abs_le.mp ht).2]⟩)
      (ContinuousLinearMap.id ℂ H) z

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
  obtain ⟨L, hL, p, q, f, hf, _, _, hA⟩ :=
    exists_weightedAnnulus_window_diagonal hw hwpos hρ hρK hφ hφK
  exact ⟨L, hL, p, q, f, hf, hA⟩

private theorem windowMode_inner {L : ℝ} [Fact (0 < L)] (p q : H) (k : ℤ) :
    ⟪W q (fourier (T := L) k), W p (fourier (T := L) k)⟫_ℂ = ⟪q, p⟫_ℂ := by
  rw [MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [W_apply_ae p (fourier (T := L) k), W_apply_ae q (fourier (T := L) k)]
    with x hp hq
  rw [hp, hq]
  let e := fourier (T := L) k (x : AddCircle L)
  have he : ‖e‖ = 1 := Circle.norm_coe _
  have he' : conj e * e = 1 := by simp [RCLike.conj_mul, he]
  simp only [RCLike.inner_apply]
  change (p x * e) * conj (q x * e) = p x * conj (q x)
  rw [map_mul]
  calc
    _ = (p x * conj (q x)) * (conj e * e) := by ring
    _ = _ := by rw [he', mul_one]

/-- The ambient basis trace of localized conjugated convolution is the test
value at zero times the mass of the cutoff. No restriction of an a.e. kernel
representative to the diagonal is used. -/
public theorem weightedAnnulus_ambient_trace {w : ℝ → ℝ} (hw : Continuous w)
    (hwpos : ∀ x, 0 < w x) {ρ φ : ℝ → ℂ}
    (hρ : Continuous ρ) (hρK : HasCompactSupport ρ)
    (hφ : ContDiff ℝ 2 φ) (hφK : HasCompactSupport φ)
    {A : H →L[ℂ] H} (hA : ∀ z : H, (A z : ℝ → ℂ) =ᵐ[volume] fun x =>
      (ρ x * (w x : ℂ)) * ∫ y, φ (x - y) * z y * (w y : ℂ)⁻¹)
    {ι : Type*} (b : HilbertBasis ι ℂ H) :
    HasSum (fun i => ⟪b i, A (b i)⟫_ℂ) (φ 0 * ∫ x, ρ x) := by
  obtain ⟨L, hL, p, q, f, hf, hzero, hinner, hwin⟩ :=
    exists_weightedAnnulus_window_diagonal hw hwpos hρ hρK hφ hφK
  let _ := hL
  have heq : A = windowKernel p q f := by
    ext1 z
    exact Lp.ext ((hA z).trans (hwin z).symm)
  have hsum : (∑' k : ℤ, fourierCoeff f k) = φ 0 := by
    apply HasSum.tsum_eq
    rw [← hzero]
    simpa [ContinuousMap.smul_apply, smul_eq_mul, fourier_apply, Circle.coe_one] using
      has_pointwise_sum_fourier_series_of_summable hf 0
  have htrace := (windowKernel_trace b p q f hf (ContinuousLinearMap.id ℂ H)).2
  simp only [ContinuousLinearMap.id_apply, outputMode, inner_smul_right,
    windowMode_inner, hinner, tsum_mul_right, hsum] at htrace
  exact heq ▸ htrace

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
