module

public import Lemmas.FinitePlaceSupport
public import Lemmas.IdeleClassTraceLocal
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Theorems.ComplexMultiplicativeHaarLogPolar
import Theorems.IdeleClassArchimedeanTrace
import Mathlib.Analysis.Complex.Poisson

/-!
# Complex-place trace of a positive-log radial profile

For a test supported on a compact positive log interval, the physical displacement
cutoff is inactive for sufficiently small radii. In the complex log-polar chart,
`x = 2 log r` and the trace coefficient gives angle measure `dθ / (2π)`.
-/

open Filter MeasureTheory NumberField InfinitePlace.Completion Set
open scoped Classical ContDiff ENNReal Topology

namespace Masullo

private theorem complexTrace_circleAverage (r : ℝ) (hr : 1 < r) :
    Real.circleAverage (fun z : ℂ ↦ ((r / ‖1 - z‖ ^ 2 : ℝ) : ℂ)) 0 r =
      ((r / (r ^ 2 - 1) : ℝ) : ℂ) := by
  let k : ℂ := ((r / (r ^ 2 - 1) : ℝ) : ℂ)
  have hk : DiffContOnCl ℂ (fun _ : ℂ ↦ k) (Metric.ball (0 : ℂ) r) := diffContOnCl_const
  have hw : (1 : ℂ) ∈ Metric.ball 0 r := by simpa [Metric.mem_ball, dist_zero_right] using hr
  refine (Real.circleAverage_congr_sphere (f₂ := fun z : ℂ ↦
    ((‖z - 0‖ ^ 2 - ‖(1 : ℂ) - 0‖ ^ 2) / ‖(z - 0) - (1 - 0)‖ ^ 2) • k) ?_).trans
    (hk.circleAverage_poissonKernel_smul' hw)
  intro z hz
  have hz' : ‖z‖ = r := by
    simpa [Metric.mem_sphere, dist_zero_right, abs_of_pos (zero_lt_one.trans hr)] using hz
  simp only [sub_zero, norm_one, one_pow, hz', Complex.real_smul, k, norm_sub_rev (1 : ℂ) z]
  push_cast
  have h : (r : ℂ) ^ 2 - 1 ≠ 0 := by exact_mod_cast (by nlinarith : r ^ 2 - 1 ≠ 0)
  field_simp [h]

private theorem circleAverage_eq_openAngle (g : ℂ → ℂ) (r : ℝ) :
    Real.circleAverage g 0 r =
      (1 / (2 * Real.pi) : ℝ) • ∫ θ in Ioo (-Real.pi) Real.pi, g (circleMap 0 r θ) := by
  rw [Real.circleAverage_eq_integral_add (-Real.pi),
    intervalIntegral.integral_comp_add_right (fun θ ↦ g (circleMap 0 r θ)), zero_add,
    show 2 * Real.pi + -Real.pi = Real.pi by ring,
    intervalIntegral.integral_of_le (by linarith [Real.pi_pos] : -Real.pi ≤ Real.pi),
    setIntegral_congr_set (Ioo_ae_eq_Ioc (μ := volume)), one_div]

private theorem complexTrace_radialWeight {x : ℝ} (hx : 0 < x) :
    Real.exp (x / 2) / (Real.exp (x / 2) ^ 2 - 1) =
      Real.exp (-x / 2) / (1 - Real.exp (-x)) := by
  have hsq : Real.exp (x / 2) ^ 2 = Real.exp x := by
    rw [pow_two, ← Real.exp_add, show x / 2 + x / 2 = x by ring]
  have hr : 1 < Real.exp (x / 2) := Real.one_lt_exp_iff.mpr (by positivity)
  rw [show -x / 2 = -(x / 2) by ring, Real.exp_neg, Real.exp_neg, ← hsq]
  field_simp [show Real.exp (x / 2) ^ 2 - 1 ≠ 0 by nlinarith]

private noncomputable def complexLogPolarKernel (F : ℝ → ℂ) (p : ℝ × ℝ) : ℂ :=
  F p.1 * ((Real.exp (p.1 / 2) / ‖1 - circleMap 0 (Real.exp (p.1 / 2)) p.2‖ ^ 2 : ℝ) : ℂ)

private theorem integrable_complexLogPolarKernel {F : ℝ → ℂ} (hF : Continuous F)
    {a b : ℝ} (ha : 0 < a) (hs : Function.support F ⊆ Icc a b) :
    Integrable (complexLogPolarKernel F)
      ((volume : Measure ℝ).prod (volume.restrict (Ioo (-Real.pi) Real.pi))) := by
  have hz : Continuous (fun p : ℝ × ℝ ↦ circleMap 0 (Real.exp (p.1 / 2)) p.2) := by
    simp only [circleMap_zero]
    fun_prop
  have hnum : Continuous (fun p : ℝ × ℝ ↦ Real.exp (p.1 / 2)) := by fun_prop
  have hden : Continuous (fun p : ℝ × ℝ ↦ ‖1 - circleMap 0 (Real.exp (p.1 / 2)) p.2‖ ^ 2) :=
    (continuous_const.sub hz).norm.pow 2
  have hcont : ContinuousOn (complexLogPolarKernel F) (Icc a b ×ˢ Icc (-Real.pi) Real.pi) := by
    refine (hF.comp continuous_fst).continuousOn.mul
      (Complex.continuous_ofReal.comp_continuousOn (hnum.continuousOn.div hden.continuousOn ?_))
    intro p hp h
    have hrad : 1 < Real.exp (p.1 / 2) :=
      Real.one_lt_exp_iff.mpr (half_pos (ha.trans_le hp.1.1))
    have hn : ‖circleMap 0 (Real.exp (p.1 / 2)) p.2‖ = Real.exp (p.1 / 2) :=
      (norm_circleMap_zero _ _).trans (abs_of_pos (Real.exp_pos _))
    have he : circleMap 0 (Real.exp (p.1 / 2)) p.2 = 1 :=
      (sub_eq_zero.mp (norm_eq_zero.mp ((pow_eq_zero_iff (by decide : (2 : ℕ) ≠ 0)).mp h))).symm
    rw [he, norm_one] at hn
    exact hrad.ne hn
  refine (integrableOn_iff_integrable_of_support_subset (s := Icc a b ×ˢ (univ : Set ℝ)) ?_).mp ?_
  · intro p hp
    refine ⟨hs (fun h ↦ hp ?_), mem_univ _⟩
    simp [complexLogPolarKernel, h]
  · rw [IntegrableOn, ← Measure.prod_restrict, Measure.restrict_restrict MeasurableSet.univ,
      univ_inter, Measure.prod_restrict]
    exact (hcont.integrableOn_compact (μ := (volume : Measure ℝ).prod volume)
      (isCompact_Icc.prod isCompact_Icc)).mono_set (prod_mono_right Ioo_subset_Icc_self)

private theorem integral_complexLogPolarKernel {F : ℝ → ℂ} {a b : ℝ} (ha : 0 < a)
    (hs : Function.support F ⊆ Icc a b)
    (hG : Integrable (complexLogPolarKernel F)
      ((volume : Measure ℝ).prod (volume.restrict (Ioo (-Real.pi) Real.pi)))) :
    (1 / (2 * Real.pi) : ℝ) • (∫ p, complexLogPolarKernel F p
      ∂((volume : Measure ℝ).prod (volume.restrict (Ioo (-Real.pi) Real.pi)))) =
      ∫ x : ℝ, F x * ((Real.exp (-x / 2) / (1 - Real.exp (-x)) : ℝ) : ℂ) := by
  rw [integral_prod _ hG, ← integral_smul]
  refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
  by_cases hx : F x = 0
  · simp [complexLogPolarKernel, hx]
  have hx₀ : 0 < x := ha.trans_le (hs hx).1
  have hr : 1 < Real.exp (x / 2) := Real.one_lt_exp_iff.mpr (half_pos hx₀)
  simp only [complexLogPolarKernel, integral_const_mul, ← smul_mul_assoc, Complex.real_smul,
    mul_comm ((1 / (2 * Real.pi) : ℝ) : ℂ) (F x), mul_assoc]
  rw [← Complex.real_smul, ← circleAverage_eq_openAngle
      (fun z : ℂ ↦ ((Real.exp (x / 2) / ‖1 - z‖ ^ 2 : ℝ) : ℂ)) (Real.exp (x / 2)),
    complexTrace_circleAverage _ hr, complexTrace_radialWeight hx₀]

/-- At a complex place, the actual trace of a radial log-norm profile supported in
`[a,b] ⊂ (0,∞)` is the positive-log gamma-kernel integral. The local calculation
needs continuity only; in particular it applies to short smooth radial bumps. -/
public theorem hasArchimedeanTraceValue_complexRadial {K : Type*} [Field K] [NumberField K]
    {v : InfinitePlace K} (hv : v.IsComplex) {F : ℝ → ℂ} (hF : Continuous F)
    {a b : ℝ} (ha : 0 < a) (hs : Function.support F ⊆ Icc a b) :
    HasArchimedeanTraceValue v
      (fun c : IdeleClassGroup (𝓞 K) K ↦ F (Real.log (ideleClassNorm c)))
      (∫ x : ℝ, F x * ((Real.exp (-x / 2) / (1 - Real.exp (-x)) : ℝ) : ℂ)) := by
  let : MeasurableSpace v.Completionˣ := borel _
  let : BorelSpace v.Completionˣ := ⟨rfl⟩
  let μ := complexCompletionHaar hv
  let ν := (volume : Measure ℝ).prod (volume.restrict (Ioo (-Real.pi) Real.pi))
  let c : ℝ := 1 / (2 * Real.pi)
  let D (u : v.Completionˣ) := ‖1 - (u : v.Completion)‖ ^ 2
  let q (u : v.Completionˣ) : ℝ × ℝ :=
    (2 * Real.log ‖u.val‖, Complex.arg (extensionEmbedding v u.val))
  let f (u : v.Completionˣ) : ℂ :=
    F (2 * Real.log ‖u.val‖) * (‖u.val‖ : ℂ) / (D u : ℂ)
  have hq : MeasurePreserving q μ ν :=
    ⟨(measurable_const.mul (Real.measurable_log.comp
      (continuous_norm.comp Units.continuous_val).measurable)).prodMk
      (Complex.measurable_arg.comp (complexCompletionEmbedding hv).measurable),
      complexCompletionHaar_map_logPolar hv⟩
  have hr (u : v.Completionˣ) : Real.exp ((q u).1 / 2) = ‖u.val‖ := by
    change Real.exp ((2 * Real.log ‖u.val‖) / 2) = _
    rw [show (2 * Real.log ‖u.val‖) / 2 = Real.log ‖u.val‖ by ring,
      Real.exp_log (norm_pos_iff.mpr u.ne_zero)]
  have hn (z : v.Completion) : ‖extensionEmbedding v z‖ = ‖z‖ :=
    (isometry_extensionEmbedding v).norm_map_of_map_zero (map_zero _) z
  -- The radial projection and argument reconstruct the unit, pointwise even on the cut ray.
  have hker : f = complexLogPolarKernel F ∘ q := by
    funext u
    have hz : circleMap 0 (Real.exp ((q u).1 / 2)) (q u).2 = extensionEmbedding v u.val := by
      rw [hr, ← hn u.val]
      exact circleMap_zero_norm_arg _
    have hd : ‖1 - extensionEmbedding v u.val‖ = ‖1 - u.val‖ := by
      rw [← map_one (extensionEmbedding v), ← map_sub, hn]
    simp only [f, Function.comp_apply, complexLogPolarKernel, D, Complex.ofReal_div, mul_div_assoc]
    rw [hz, hd, hr]
  have hG : Integrable (complexLogPolarKernel F) ν := integrable_complexLogPolarKernel hF ha hs
  have hfi : Integrable f μ := hker ▸ hq.integrable_comp_of_integrable hG
  -- The chart already uses `2 log r`; only the trace coefficient remains to be applied.
  have hvalue : (∫ u, f u ∂(ENNReal.ofReal c • μ)) =
      ∫ x : ℝ, F x * ((Real.exp (-x / 2) / (1 - Real.exp (-x)) : ℝ) : ℂ) := by
    rw [integral_smul_measure, ENNReal.toReal_ofReal (by positivity : 0 ≤ c)]
    have hmap : (∫ p, complexLogPolarKernel F p ∂ν) = ∫ u, f u ∂μ := by
      rw [hker, ← hq.map_eq]
      exact integral_map hq.measurable.aemeasurable (hq.map_eq.symm ▸ hG.aestronglyMeasurable)
    rw [← hmap]
    exact integral_complexLogPolarKernel ha hs hG
  have hreal : ¬ v.IsReal := InfinitePlace.not_isReal_iff_isComplex.mpr hv
  unfold HasArchimedeanTraceValue
  dsimp only
  simp only [dite_eq_right hreal, hv.mult_eq_two, ideleClassNorm_ofCompletion, Real.log_pow,
    Nat.cast_ofNat, Real.sqrt_sq (norm_nonneg _)]
  change (∀ ε > 0, IntegrableOn f {u | ε ≤ D u} (ENNReal.ofReal c • μ)) ∧
    Tendsto (fun ε ↦ ∫ u in {u | ε ≤ D u}, f u ∂(ENNReal.ofReal c • μ)) (𝓝[>] 0) _
  refine ⟨fun _ _ ↦ (hfi.smul_measure ENNReal.ofReal_ne_top).integrableOn, ?_⟩
  rw [← hvalue]
  let δ := (Real.exp (a / 2) - 1) ^ 2
  have hδ₁ : 0 < Real.exp (a / 2) - 1 := sub_pos.mpr (Real.one_lt_exp_iff.mpr (half_pos ha))
  have hδ : 0 < δ := pow_pos hδ₁ _
  apply tendsto_const_nhds.congr'
  filter_upwards [Ioc_mem_nhdsGT hδ] with ε hε
  symm
  refine setIntegral_eq_integral_of_forall_compl_eq_zero fun u hu ↦ ?_
  by_contra hfu
  have hFx : F (q u).1 ≠ 0 := by
    intro hx
    exact hfu (by simp [f, q, hx])
  have hrad : Real.exp (a / 2) ≤ ‖u.val‖ := by
    rw [← hr u]
    exact Real.exp_le_exp.mpr (div_le_div_of_nonneg_right (hs hFx).1 (by norm_num))
  have hdist : ‖u.val‖ - 1 ≤ ‖1 - u.val‖ := by
    simpa only [norm_one, norm_sub_rev u.val 1] using norm_sub_norm_le u.val 1
  exact hu (hε.2.trans (pow_le_pow_left₀ hδ₁.le ((sub_le_sub_right hrad 1).trans hdist) 2))

/-- Any value supplied by the complex-place trace condition for this profile is
forced to equal the gamma-kernel integral. -/
public theorem hasArchimedeanTraceValue_complexRadial_iff {K : Type*} [Field K] [NumberField K]
    {v : InfinitePlace K} (hv : v.IsComplex) {F : ℝ → ℂ} (hF : Continuous F)
    {a b : ℝ} (ha : 0 < a) (hs : Function.support F ⊆ Icc a b) (A : ℂ) :
    HasArchimedeanTraceValue v
      (fun c : IdeleClassGroup (𝓞 K) K ↦ F (Real.log (ideleClassNorm c))) A ↔
      A = ∫ x : ℝ, F x * ((Real.exp (-x / 2) / (1 - Real.exp (-x)) : ℝ) : ℂ) := by
  have hvalue := hasArchimedeanTraceValue_complexRadial hv hF ha hs
  constructor
  · intro h
    exact tendsto_nhds_unique h.2 hvalue.2
  · rintro rfl
    exact hvalue

namespace ShortPositiveLogBump

/-- The lower log endpoint of the short bump. -/
@[expose] public noncomputable def a : ℝ := Real.log 2 / 3
/-- The upper log endpoint of the short bump. -/
@[expose] public noncomputable def b : ℝ := 2 * a
/-- The nonnegative smooth radial profile supported between the short log endpoints. -/
@[expose] public noncomputable def profile (x : ℝ) : ℝ := expNegInvGlue ((x - a) * (b - x))
private noncomputable def weight (x : ℝ) : ℝ := Real.exp (-x / 2) / (1 - Real.exp (-x))
/-- The positive-log complex gamma term of the short bump, in real scalars. -/
@[expose] public noncomputable def gammaIntegral : ℝ :=
  ∫ x in Ioo a b, profile x * (Real.exp (-x / 2) / (1 - Real.exp (-x)))

/-- The short bump is separated from log norm zero. -/
public theorem a_pos : 0 < a := div_pos (Real.log_pos (by norm_num)) (by norm_num)

/-- The short log interval is nonempty. -/
public theorem a_lt_b : a < b := by
  unfold b
  linarith [a_pos]

/-- The whole short log interval lies below `log 2`. -/
public theorem b_lt_log_two : b < Real.log 2 := by
  unfold b a
  linarith [Real.log_pos (show (1 : ℝ) < 2 by norm_num)]

/-- The explicit exponential formula for the smooth profile, with zero at both endpoints. -/
public theorem profile_eq (x : ℝ) : profile x =
    if x ∈ Ioo a b then Real.exp (-1 / ((x - a) * (b - x))) else 0 := by
  by_cases hx : x ∈ Ioo a b
  · have hp := mul_pos (sub_pos.mpr hx.1) (sub_pos.mpr hx.2)
    simp [profile, expNegInvGlue, hp.not_ge, hx, div_eq_mul_inv]
  · have hn : (x - a) * (b - x) ≤ 0 := by
      by_cases h : x ≤ a
      · exact mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr h)
          (sub_nonneg.mpr (h.trans a_lt_b.le))
      · have hab : b ≤ x := le_of_not_gt (fun hxb ↦ hx ⟨lt_of_not_ge h, hxb⟩)
        exact mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr (a_lt_b.le.trans hab))
          (sub_nonpos.mpr hab)
    simp [profile, expNegInvGlue.zero_of_nonpos hn, hx]

/-- The cutoff at the endpoints of the bump is smooth. -/
public theorem contDiff_profile : ContDiff ℝ ∞ profile :=
  expNegInvGlue.contDiff.comp
    ((contDiff_id.sub contDiff_const).mul (contDiff_const.sub contDiff_id))

/-- The pointwise support of the bump lies strictly between its log endpoints. -/
public theorem support_profile_subset : Function.support profile ⊆ Ioo a b := by
  intro x hx
  by_contra hn
  exact hx (by simp [profile_eq, hn])

private theorem weight_pos {x : ℝ} (hx : 0 < x) : 0 < weight x :=
  div_pos (Real.exp_pos _) (sub_pos.mpr (Real.exp_lt_one_iff.mpr (neg_neg_of_pos hx)))

/-- The local trace of this bump is strictly positive as a real scalar. -/
public theorem gammaIntegral_pos : 0 < gammaIntegral := by
  let g (x : ℝ) := profile x * weight (max a x)
  have hg_eq (x : ℝ) : profile x * weight x = g x := by
    by_cases h : profile x = 0
    · simp [g, h]
    · simp only [g, max_eq_right (support_profile_subset h).1.le]
  have hW : Continuous (fun x ↦ weight (max a x)) := by
    unfold weight
    have hcont : Continuous (fun x : ℝ ↦ max a x) := continuous_const.max continuous_id
    exact (Real.continuous_exp.comp (hcont.neg.div_const 2)).div
      (continuous_const.sub (Real.continuous_exp.comp hcont.neg)) (fun x ↦
        (sub_pos.mpr (Real.exp_lt_one_iff.mpr
          (neg_neg_of_pos (a_pos.trans_le (le_max_left a x))))).ne')
  have hcont : Continuous g := contDiff_profile.continuous.mul hW
  have hcompact : HasCompactSupport g := HasCompactSupport.of_support_subset_isCompact
      (isCompact_Icc (a := a) (b := b)) (fun x hx ↦ by
        refine Ioo_subset_Icc_self (support_profile_subset (fun h ↦ hx ?_))
        change profile x * weight (max a x) = 0
        rw [h, zero_mul])
  have hJ : gammaIntegral = ∫ x, g x := by
    change (∫ x in Ioo a b, profile x * weight x) = _
    simp_rw [hg_eq]
    exact setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx ↦ by
      change profile x * weight (max a x) = 0
      rw [profile_eq, ite_eq_right hx, zero_mul]
  have hx : (a + b) / 2 ∈ Ioo a b := ⟨by linarith [a_lt_b], by linarith [a_lt_b]⟩
  rw [hJ]
  apply integral_pos_of_integrable_nonneg_ne_zero hcont
    (hcont.integrable_of_hasCompactSupport hcompact)
  · intro x
    exact mul_nonneg (expNegInvGlue.nonneg _) (weight_pos (a_pos.trans_le (le_max_left a x))).le
  · exact (mul_pos (expNegInvGlue.pos_of_pos (mul_pos (sub_pos.mpr hx.1) (sub_pos.mpr hx.2)))
      (weight_pos (a_pos.trans_le (le_max_left _ _)))).ne'

/-- The actual local cutoff trace of the short bump is its gamma term, uniquely. -/
public theorem hasArchimedeanTraceValue_iff {K : Type*} [Field K] [NumberField K]
    {v : InfinitePlace K} (hv : v.IsComplex) (A : ℂ) :
    HasArchimedeanTraceValue v (fun c : IdeleClassGroup (𝓞 K) K ↦
      (profile (Real.log (ideleClassNorm c)) : ℂ)) A ↔ A = (gammaIntegral : ℂ) := by
  have hF : Continuous (fun x ↦ (profile x : ℂ)) :=
    Complex.continuous_ofReal.comp contDiff_profile.continuous
  have hsub : Function.support (fun x ↦ (profile x : ℂ)) ⊆ Icc a b :=
    fun _ h ↦ Ioo_subset_Icc_self (support_profile_subset (fun hzero ↦ h (by simp [hzero])))
  rw [hasArchimedeanTraceValue_complexRadial_iff hv hF a_pos hsub]
  change _ = (∫ x : ℝ, (profile x : ℂ) * (weight x : ℂ)) ↔ _
  have hh : (∫ x : ℝ, (profile x : ℂ) * (weight x : ℂ)) =
      Complex.ofReal (∫ x : ℝ, profile x * weight x) := by
    simpa only [Complex.ofReal_mul] using
      (integral_complex_ofReal (μ := volume) (f := fun x ↦ profile x * weight x))
  rw [hh]
  change _ ↔ A = Complex.ofReal (∫ x in Ioo a b, profile x * weight x)
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (s := Ioo a b)
    (f := fun x ↦ profile x * weight x) (fun x hx ↦ by rw [profile_eq, ite_eq_right hx, zero_mul])]

end ShortPositiveLogBump

end Masullo
