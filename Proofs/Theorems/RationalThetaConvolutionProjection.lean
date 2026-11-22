module

public import Lemmas.RationalThetaWeightedLog
import Lemmas.ExpAbsDecay
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Prod

/-! # Compact log convolution in the full rational theta image

Positive dilation preserves both zero modes and evenness. Thus every translated
raw theta profile, weighted at the *output* coordinate, is a genuine generator
of the full closed image. Bochner integration preserves that image. The
representative of the integral is identified by testing on finite-measure sets,
not by evaluating an `L²` equivalence class at a point.
-/

open MeasureTheory Set Filter
open scoped FourierTransform SchwartzMap Topology InnerProductSpace

namespace Masullo

local notation "H" => Lp ℂ 2 (volume : Measure ℝ)
local notation "h₀" => (le_refl (0 : ℝ))

/-- A genuine generator belongs to its closed frequency image before taking
any band limit. -/
public theorem rationalThetaWeightedLog_mem_evenImage (a : ℝ) {α s : ℝ}
    (hs : 0 ≤ s) (hα : 0 ≤ α) (freq : Set ℝ) (b : RationalThetaInput)
    (he : Function.Even (⇑b.val)) (hb : ∀ ξ ∉ freq, (𝓕 b.val) ξ = 0) :
    rationalThetaWeightedLog a hs hα b ∈ (rationalThetaWeightedEvenImage a hs hα freq).toSubmodule := by
  change rationalThetaWeightedLog a hs hα b ∈ (rationalThetaWeightedEvenImage a hs hα freq : Set H)
  rw [coe_rationalThetaWeightedEvenImage]
  exact subset_closure ⟨b, ⟨he, hb⟩, rfl⟩

/-- The band projection fixes every genuine generator with the corresponding
Fourier support. -/
public theorem rationalThetaWeightedLog_starProjection_eq_self (a : ℝ) {α s : ℝ}
    (hs : 0 ≤ s) (hα : 0 ≤ α) (freq : Set ℝ) (b : RationalThetaInput)
    (he : Function.Even (⇑b.val)) (hb : ∀ ξ ∉ freq, (𝓕 b.val) ξ = 0) :
    (rationalThetaWeightedEvenImage a hs hα freq).toSubmodule.starProjection
      (rationalThetaWeightedLog a hs hα b) = rationalThetaWeightedLog a hs hα b :=
  Submodule.starProjection_eq_self_iff.mpr (rationalThetaWeightedLog_mem_evenImage a hs hα freq b he hb)

private noncomputable def logDilate (b : RationalThetaInput) (y : ℝ) : RationalThetaInput :=
  ⟨dilateSchwartz b.val (Real.exp (-y)) (Real.exp_pos _).ne', by
    constructor
    · simp [dilateSchwartz_apply, b.property.1]
    · rw [fourier_dilateSchwartz _ (Real.exp_pos _), mul_zero, b.property.2, smul_zero]⟩

private theorem logDilate_even (b : RationalThetaInput) (he : Function.Even (⇑b.val)) (y : ℝ) :
    Function.Even (⇑(logDilate b y).val) := by
  intro u
  simpa only [logDilate, dilateSchwartz_apply, mul_neg] using he (Real.exp (-y) * u)

private theorem rationalTheta_logDilate (b : RationalThetaInput) (x y : ℝ) :
    rationalTheta (logDilate b y).val (Real.exp x) = rationalTheta b.val (Real.exp (x - y)) := by
  simp only [rationalTheta, logDilate, dilateSchwartz_apply, ← mul_assoc, ← Real.exp_add]
  rw [neg_add_eq_sub]

private noncomputable def rawLog (b : RationalThetaInput) (x : ℝ) : ℂ :=
  rationalTheta b.val (Real.exp x)

private theorem continuous_rawLog (b : RationalThetaInput) : Continuous (rawLog b) :=
  (rationalTheta_continuousOn b.val).comp_continuous Real.continuous_exp Real.exp_pos

private noncomputable def weightedShift (s : ℝ) (b : RationalThetaInput) (y x : ℝ) : ℂ :=
  (symmetricStripWeightRoot 0 s x : ℂ) * rawLog b (x - y)

private theorem continuous_weightedShift (s : ℝ) (b : RationalThetaInput) :
    Continuous (fun p : ℝ × ℝ ↦ weightedShift s b p.1 p.2) :=
  ((Complex.continuous_ofReal.comp (continuous_symmetricStripWeightRoot 0 s)).comp
    continuous_snd).mul ((continuous_rawLog b).comp (continuous_snd.sub continuous_fst))

private theorem weightedLog_logDilate_ae {s : ℝ} (hs : 0 ≤ s) (b : RationalThetaInput) (y : ℝ) :
    (rationalThetaWeightedLog 0 hs h₀ (logDilate b y) : ℝ → ℂ) =ᵐ[volume] weightedShift s b y := by
  filter_upwards [(memLp_rationalTheta_weighted (logDilate b y) 0 0 s hs h₀).coeFn_toLp]
    with x hx
  simpa [rationalThetaWeightedLog, weightedShift, rawLog, rationalTheta_logDilate] using hx

private theorem weight_le_exp {s : ℝ} (hs : 0 ≤ s) (x : ℝ) :
    symmetricStripWeightRoot 0 s x ≤ Real.exp ((s / 2) * |x|) := by
  rw [symmetricStripWeightRoot_apply, zero_mul, Real.exp_zero, one_mul]
  calc
    (1 + x ^ 2) ^ (s / 4) ≤ ((Real.exp |x|) ^ 2) ^ (s / 4) := by
      apply Real.rpow_le_rpow (by positivity) _ (by positivity)
      calc
        1 + x ^ 2 ≤ (|x| + 1) ^ 2 := by
          rw [add_sq, sq_abs]
          linarith [abs_nonneg x]
        _ ≤ (Real.exp |x|) ^ 2 := by gcongr; exact Real.add_one_le_exp _
    _ = Real.exp ((s / 2) * |x|) := by
      rw [← Real.exp_nat_mul, ← Real.exp_mul]
      push_cast
      ring_nf

private theorem exists_weightedShift_bound {s : ℝ} (hs : 0 ≤ s) (b : RationalThetaInput) :
    ∃ C N : ℝ, 0 < C ∧ 0 ≤ N ∧ ∀ y x,
      ‖weightedShift s b y x‖ ≤ (C * Real.exp (N * |y|)) * Real.exp (-|x|) := by
  obtain ⟨n, hn⟩ := exists_nat_gt (s / 2 + 1)
  obtain ⟨C, hC, htail⟩ := rationalTheta_uniform_log_bound
    (Bornology.isVonNBounded_singleton (𝕜 := ℂ) b.val) n
  refine ⟨C, n, hC, Nat.cast_nonneg _, fun y x ↦ ?_⟩
  have hxy : |x| ≤ |x - y| + |y| := by
    simpa only [sub_add_cancel] using abs_add_le (x - y) y
  rw [weightedShift, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (symmetricStripWeightRoot_pos ..).le]
  calc
    _ ≤ Real.exp ((s / 2) * |x|) * (C * Real.exp (-(n : ℝ) * |x - y|)) :=
      mul_le_mul (weight_le_exp hs x)
        (htail b.val (mem_singleton _) b.property.1 b.property.2 (x - y))
        (norm_nonneg _) (Real.exp_pos _).le
    _ = C * Real.exp ((s / 2) * |x| - (n : ℝ) * |x - y|) := by
      rw [mul_left_comm, ← Real.exp_add, neg_mul, ← sub_eq_add_neg]
    _ ≤ C * Real.exp ((n : ℝ) * |y| + -|x|) := by
      gcongr
      nlinarith [mul_le_mul_of_nonneg_left hxy (Nat.cast_nonneg (α := ℝ) n),
        mul_nonneg (sub_nonneg.mpr hn.le) (abs_nonneg x)]
    _ = _ := by rw [Real.exp_add, mul_assoc]

private theorem norm_sq_L2 (u : H) : ‖u‖ ^ 2 = ∫ x : ℝ, ‖u x‖ ^ 2 := by
  rw [norm_sq_eq_re_inner (𝕜 := ℂ), L2.inner_def]
  change Complex.reCLM (∫ x : ℝ, ⟪u x, u x⟫_ℂ) = _
  rw [← Complex.reCLM.integral_comp_comm (L2.integrable_inner (𝕜 := ℂ) u u)]
  simp only [inner_self_eq_norm_sq_to_K]
  exact integral_congr_ae (ae_of_all _ fun x ↦ RCLike.re_ofReal_pow (K := ℂ) ‖u x‖ 2)

private theorem continuous_weightedLog_logDilate {s : ℝ} (hs : 0 ≤ s) (b : RationalThetaInput) :
    Continuous (fun y ↦ rationalThetaWeightedLog 0 hs h₀ (logDilate b y)) := by
  let U (y : ℝ) := rationalThetaWeightedLog 0 hs h₀ (logDilate b y)
  change Continuous U
  obtain ⟨C, N, hC, hN, hbound⟩ := exists_weightedShift_bound hs b
  apply continuous_iff_continuousAt.2
  intro y
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  have hn (z : ℝ) : ‖U z - U y‖ ^ 2 =
      ∫ x : ℝ, ‖weightedShift s b z x - weightedShift s b y x‖ ^ 2 := by
    rw [norm_sq_L2]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub (U z) (U y), weightedLog_logDilate_ae hs b z,
      weightedLog_logDilate_ae hs b y] with x hsub hz hy
    change U z x = _ at hz
    change U y x = _ at hy
    simp only [hsub, Pi.sub_apply, hz, hy]
  let A := C * Real.exp (N * (|y| + 1))
  have hBd {z : ℝ} (hz : |z| ≤ |y| + 1) (x : ℝ) :
      ‖weightedShift s b z x‖ ≤ A * Real.exp (-|x|) := by
    refine (hbound z x).trans ?_
    dsimp [A]
    gcongr
  have hcont (x : ℝ) : Continuous (fun z ↦ ‖weightedShift s b z x - weightedShift s b y x‖ ^ 2) :=
    ((((continuous_weightedShift s b).comp (continuous_id.prodMk continuous_const)).sub
      continuous_const).norm).pow 2
  have ht : Tendsto (fun z ↦ ∫ x : ℝ, ‖weightedShift s b z x - weightedShift s b y x‖ ^ 2)
      (𝓝 y) (𝓝 (∫ x : ℝ, ‖weightedShift s b y x - weightedShift s b y x‖ ^ 2)) := by
    refine tendsto_integral_filter_of_dominated_convergence
      (fun x : ℝ ↦ (2 * A) ^ 2 * Real.exp (-(2 : ℝ) * |x|)) ?_ ?_
      ((integrable_exp_neg_mul_abs (by norm_num : (0 : ℝ) < 2)).const_mul _) ?_
    · exact Eventually.of_forall fun z ↦
        ((((continuous_weightedShift s b).comp (continuous_const.prodMk continuous_id)).sub
          ((continuous_weightedShift s b).comp (continuous_const.prodMk continuous_id))).norm.pow
          2).aestronglyMeasurable
    · filter_upwards [Metric.ball_mem_nhds y (show 0 < (1 : ℝ) by norm_num)] with z hz
      have hz' : |z| ≤ |y| + 1 := calc
        |z| ≤ |z - y| + |y| := by simpa only [sub_add_cancel] using abs_add_le (z - y) y
        _ ≤ |y| + 1 := by
          have hz'' : |z - y| < 1 := by simpa [Metric.mem_ball, Real.dist_eq] using hz
          linarith
      refine ae_of_all _ fun x ↦ ?_
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      have hnorm := (norm_sub_le (weightedShift s b z x) (weightedShift s b y x)).trans
        (add_le_add (hBd hz' x) (hBd (by linarith : |y| ≤ |y| + 1) x))
      calc
        _ ≤ (2 * A * Real.exp (-|x|)) ^ 2 := by
          apply pow_le_pow_left₀ (norm_nonneg _) _
          linarith
        _ = _ := by rw [mul_pow, ← Real.exp_nat_mul]; push_cast; ring_nf
    · exact ae_of_all _ (fun x ↦ (hcont x).continuousAt)
  have ht' : Tendsto (fun z ↦ ‖U z - U y‖ ^ 2) (𝓝 y) (𝓝 0) := by
    simpa only [hn, sub_self, norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0), integral_zero] using ht
  have hSqrt (z : ℝ) : √(‖U z - U y‖ ^ 2) = ‖U z - U y‖ := Real.sqrt_sq (norm_nonneg _)
  simpa only [Function.comp_def, Real.sqrt_zero, hSqrt] using
    (Real.continuous_sqrt.tendsto 0).comp ht'

/-- The weighted output of raw log convolution, formed as a Bochner integral
of weighted theta generators with dilated inputs. -/
public noncomputable def rationalThetaWeightedLogConvolution {s : ℝ} (hs : 0 ≤ s)
    (f : ℝ → ℂ) (b : RationalThetaInput) : H :=
  ∫ y : ℝ, f y • rationalThetaWeightedLog 0 hs h₀ (logDilate b y)

private theorem integrable_weightedLogConvolution {s : ℝ} (hs : 0 ≤ s) (f : ℝ → ℂ)
    (b : RationalThetaInput) (hf : Continuous f) (hfc : HasCompactSupport f) :
    Integrable (fun y : ℝ ↦ f y • rationalThetaWeightedLog 0 hs h₀ (logDilate b y)) :=
  (hf.smul (continuous_weightedLog_logDilate hs b)).integrable_of_hasCompactSupport hfc.smul_right

/-- The integral can be taken in the full closed image itself: its subtype
inclusion commutes with Bochner integration. -/
public theorem rationalThetaWeightedLogConvolution_mem_evenImage {s : ℝ} (hs : 0 ≤ s)
    (f : ℝ → ℂ) (b : RationalThetaInput) (he : Function.Even (⇑b.val)) :
    rationalThetaWeightedLogConvolution hs f b ∈
      (rationalThetaWeightedEvenImage 0 hs h₀ univ).toSubmodule := by
  let G₀ := rationalThetaWeightedEvenImage 0 hs h₀ univ
  let G := G₀.toSubmodule
  let _ : CompleteSpace G := inferInstanceAs (CompleteSpace G₀)
  let v (y : ℝ) : G := ⟨f y • rationalThetaWeightedLog 0 hs h₀ (logDilate b y),
    G.smul_mem _ (rationalThetaWeightedLog_mem_evenImage 0 hs h₀ univ (logDilate b y)
      (logDilate_even b he y) (by simp))⟩
  change (∫ y : ℝ, G.subtypeₗᵢ (v y)) ∈ G
  rw [G.subtypeₗᵢ.integral_comp_comm v]
  exact (∫ y : ℝ, v y).property

/-- At the full zero-line level the actual ambient orthogonal projection
fixes the compact log convolution of a genuine even two-mode input. -/
public theorem rationalThetaWeightedLogConvolution_starProjection_eq_self {s : ℝ} (hs : 0 ≤ s)
    (f : ℝ → ℂ) (b : RationalThetaInput) (he : Function.Even (⇑b.val)) :
    (rationalThetaWeightedEvenImage 0 hs h₀ univ).toSubmodule.starProjection
      (rationalThetaWeightedLogConvolution hs f b) = rationalThetaWeightedLogConvolution hs f b :=
  Submodule.starProjection_eq_self_iff.mpr (rationalThetaWeightedLogConvolution_mem_evenImage hs f b he)

/-- The `L²` representative is weight times convolution of the **raw** log
profile. In particular the weight is taken at `x`, not at `x - y`. -/
public theorem rationalThetaWeightedLogConvolution_ae {s : ℝ} (hs : 0 ≤ s) (f : ℝ → ℂ)
    (b : RationalThetaInput) (hf : Continuous f) (hfc : HasCompactSupport f) :
    (rationalThetaWeightedLogConvolution hs f b : ℝ → ℂ) =ᵐ[volume]
      fun x ↦ (symmetricStripWeightRoot 0 s x : ℂ) *
        ∫ y : ℝ, f y * rationalTheta b.val (Real.exp (x - y)) := by
  let K (y x : ℝ) : ℂ := f y * weightedShift s b y x
  have hK : Integrable (Function.uncurry K) ((volume : Measure ℝ).prod volume) := by
    obtain ⟨C, N, hC, _, hbound⟩ := exists_weightedShift_bound hs b
    let d (y : ℝ) := C * Real.exp (N * |y|)
    have hd : Continuous d := by dsimp [d]; fun_prop
    have hi : Integrable (fun y ↦ ‖f y‖ * d y) (volume : Measure ℝ) :=
      (hf.norm.mul hd).integrable_of_hasCompactSupport hfc.norm.mul_right
    have hExp : Integrable (fun x : ℝ ↦ Real.exp (-|x|)) := by
      simpa only [neg_mul, one_mul] using integrable_exp_neg_mul_abs one_pos
    refine (hi.mul_prod hExp).mono' ((hf.comp continuous_fst).mul
      (continuous_weightedShift s b)).aestronglyMeasurable (ae_of_all _ fun p ↦ ?_)
    change ‖f p.1 * weightedShift s b p.1 p.2‖ ≤ (‖f p.1‖ * d p.1) * Real.exp (-|p.2|)
    rw [norm_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hbound p.1 p.2) (norm_nonneg _)
  have h_eval (x : ℝ) : (∫ y : ℝ, K y x) = (symmetricStripWeightRoot 0 s x : ℂ) *
        ∫ y : ℝ, f y * rationalTheta b.val (Real.exp (x - y)) := by
    rw [← integral_const_mul]
    exact integral_congr_ae (ae_of_all _ fun y ↦ by dsimp [K, weightedShift, rawLog]; ring)
  simp_rw [← h_eval]
  let u := rationalThetaWeightedLogConvolution hs f b
  change (u : ℝ → ℂ) =ᵐ[volume] fun x ↦ ∫ y : ℝ, K y x
  refine ae_eq_of_forall_setIntegral_eq_of_sigmaFinite
    (fun t _ ht ↦ integrableOn_Lp_of_measure_ne_top u one_le_two ht.ne)
    (fun _ _ _ ↦ hK.integral_prod_right.integrableOn) ?_
  intro t ht hμt
  let L : H →L[ℂ] ℂ := innerSL ℂ (indicatorConstLp 2 ht hμt.ne 1)
  have hL (v : H) : L v = ∫ x in t, v x := L2.inner_indicatorConstLp_one ht hμt.ne v
  rw [← hL u]
  change L (∫ y : ℝ, f y • rationalThetaWeightedLog 0 hs h₀ (logDilate b y)) = _
  rw [← L.integral_comp_comm (integrable_weightedLogConvolution hs f b hf hfc)]
  calc
    _ = ∫ y : ℝ, ∫ x in t, K y x := by
      apply integral_congr_ae
      refine ae_of_all _ fun y ↦ ?_
      change L (f y • rationalThetaWeightedLog 0 hs h₀ (logDilate b y)) = ∫ x in t, K y x
      rw [hL]
      apply integral_congr_ae
      filter_upwards [ae_restrict_of_ae (Lp.coeFn_smul (f y)
        (rationalThetaWeightedLog 0 hs h₀ (logDilate b y))),
        ae_restrict_of_ae (weightedLog_logDilate_ae hs b y)] with x hsmul hx
      rw [hsmul, Pi.smul_apply, hx, smul_eq_mul]
    _ = _ := integral_integral_swap (hK.mono_measure (Measure.prod_mono le_rfl Measure.restrict_le_self))

/-- The projected output has the same a.e. representative as the weighted raw
convolution. -/
public theorem rationalThetaWeightedLogConvolution_starProjection_ae {s : ℝ} (hs : 0 ≤ s)
    (f : ℝ → ℂ) (b : RationalThetaInput) (he : Function.Even (⇑b.val))
    (hf : Continuous f) (hfc : HasCompactSupport f) :
    ((rationalThetaWeightedEvenImage 0 hs h₀ univ).toSubmodule.starProjection
      (rationalThetaWeightedLogConvolution hs f b) : ℝ → ℂ) =ᵐ[volume]
      fun x ↦ (symmetricStripWeightRoot 0 s x : ℂ) *
        ∫ y : ℝ, f y * rationalTheta b.val (Real.exp (x - y)) := by
  rw [rationalThetaWeightedLogConvolution_starProjection_eq_self hs f b he]
  exact rationalThetaWeightedLogConvolution_ae hs f b hf hfc

end Masullo
