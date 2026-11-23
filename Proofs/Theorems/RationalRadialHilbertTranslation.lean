module

public import Theorems.RationalRadialHilbertQuotient
public import Lemmas.InteriorLogJet
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! # Bounded left translation on the rational radial theta quotient

The log coordinate uses the normalized rational Haar measure. The theta range
is the global two-mode LF image with its half twist, not the real S-local
image. This checks bounded descent, not any trace-ideal property.
-/

open Filter MeasureTheory NumberField Set
open scoped SchwartzMap ContDiff Topology Pointwise

namespace Masullo

noncomputable section

/-- The weight bound for translation by `y` in the symmetric interval model. -/
@[expose] public def rationalRadialTranslationBound (α s y : ℝ) : ℝ :=
  2 ^ (s / 4) * symmetricStripWeightRoot α s y

private theorem translationBound_nonneg (α s y : ℝ) :
    0 ≤ rationalRadialTranslationBound α s y := by
  unfold rationalRadialTranslationBound
  exact mul_nonneg (by positivity) (symmetricStripWeightRoot_pos ..).le

private theorem root_add_le {α s : ℝ} (hα : 0 ≤ α) (hs : 0 ≤ s) (x y : ℝ) :
    symmetricStripWeightRoot α s (x + y) ≤
      rationalRadialTranslationBound α s y * symmetricStripWeightRoot α s x := by
  have hxy : 1 + (x + y) ^ 2 ≤ 2 * (1 + y ^ 2) * (1 + x ^ 2) := by
    nlinarith [sq_nonneg (x - y), sq_nonneg (y * x)]
  have he : Real.exp (α * |x + y|) ≤ Real.exp (α * |y|) * Real.exp (α * |x|) := by
    rw [← Real.exp_add, ← mul_add]
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left
      ((abs_add_le x y).trans_eq (add_comm |x| |y|)) hα)
  have hp : (1 + (x + y) ^ 2) ^ (s / 4) ≤
      2 ^ (s / 4) * (1 + y ^ 2) ^ (s / 4) * (1 + x ^ 2) ^ (s / 4) := by
    refine (Real.rpow_le_rpow (by positivity) hxy (by positivity)).trans_eq ?_
    rw [Real.mul_rpow (by positivity) (by positivity), Real.mul_rpow (by positivity) (by positivity)]
  unfold rationalRadialTranslationBound
  simp only [symmetricStripWeightRoot_apply]
  exact (mul_le_mul he hp (by positivity) (by positivity)).trans_eq (by ring)

private theorem root_sq_eq_weight {α : ℝ} (hα : 0 ≤ α) (s x : ℝ) :
    symmetricStripWeightRoot α s x ^ 2 = logSobolevWeight (-α) α s x := by
  simpa only [logSobolevWeight, zero_add, zero_mul, Real.exp_zero, mul_one] using
    symmetricStripWeightRoot_mul_exp_sq hα s 0 x

private theorem weight_add_le {α s : ℝ} (hα : 0 ≤ α) (hs : 0 ≤ s) (x y : ℝ) :
    logSobolevWeight (-α) α s (x + y) ≤
      rationalRadialTranslationBound α s y ^ 2 * logSobolevWeight (-α) α s x := by
  rw [← root_sq_eq_weight hα, ← root_sq_eq_weight hα, ← mul_pow]
  exact pow_le_pow_left₀ (symmetricStripWeightRoot_pos ..).le (root_add_le hα hs x y) 2

private theorem stageWeight_shift (a x y : ℝ) :
    logStageWeight a x = logStageWeight a y * logStageWeight a (x - y) := by
  rw [logStageWeight, logStageWeight, logStageWeight, ← Complex.ofReal_mul, ← Real.exp_add]
  congr 2
  ring

/-- Inverse left translation in the log coordinate: `u(x-y)`. -/
@[expose] public def rationalRadialProfileTranslate (y : ℝ) :
    logWeightedProfiles univ →ₗ[ℂ] logWeightedProfiles univ where
  toFun f := ⟨fun x ↦ f.val (x - y), f.property.1.comp (contDiff_id.sub contDiff_const), by
    intro a
    obtain ⟨g, hg⟩ := f.property.2 a
    refine ⟨logStageWeight a y • g.compSubConstCLM ℂ y, fun x ↦ ?_⟩
    simp only [smul_apply, SchwartzMap.compSubConstCLM_apply, hg, smul_eq_mul]
    rw [← mul_assoc, ← stageWeight_shift]⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] public theorem rationalRadialProfileTranslate_apply (y : ℝ) (f : logWeightedProfiles univ)
    (x : ℝ) : (rationalRadialProfileTranslate y f).val x = f.val (x - y) := rfl

private theorem norm_inclusion_dx {a b : ℝ} (hab : a ≤ b) (s : ℝ) (u : logWeightedProfiles univ) :
    ‖rationalRadialHilbertInclusion hab s u‖ =
      Real.sqrt (∫ x, logSobolevWeight a b s x * ‖u.val x‖ ^ 2) := by
  let f : logWeightedProfiles (Icc a b) := ⟨u.val, u.property.1,
    fun w ↦ u.property.2 ⟨w, mem_univ _⟩⟩
  have he : logSobolevAllToLp hab s u = logSobolevToLp hab s f :=
    Lp.ext ((logSobolevAllToLp_ae_eq hab s u).trans (logSobolevToLp_ae_eq hab s f).symm)
  change ‖logSobolevAllToLp hab s u‖ = _
  rw [he]
  exact norm_logSobolevToLp hab s f

private theorem integrable_profile_norm {a b : ℝ} (hab : a ≤ b) (s : ℝ)
    (u : logWeightedProfiles univ) :
    Integrable (fun x ↦ logSobolevWeight a b s x * ‖u.val x‖ ^ 2) :=
  integrable_logSobolevWeight_mul_norm_sq hab
    ⟨u.property.1, fun w ↦ u.property.2 ⟨w, mem_univ _⟩⟩

local notation "negLe" h => (neg_le_self h)

private theorem bound_inclusion_translate {α s : ℝ} (hα : 0 ≤ α) (hs : 0 ≤ s)
    (y : ℝ) (u : logWeightedProfiles univ) :
    ‖rationalRadialHilbertInclusion (negLe hα) s (rationalRadialProfileTranslate y u)‖ ≤
      rationalRadialTranslationBound α s y * ‖rationalRadialHilbertInclusion (negLe hα) s u‖ := by
  rw [norm_inclusion_dx, norm_inclusion_dx,
    ← Real.sqrt_sq (translationBound_nonneg α s y), ← Real.sqrt_mul (sq_nonneg _)]
  apply Real.sqrt_le_sqrt
  rw [← integral_const_mul]
  let g : ℝ → ℝ := fun t ↦ rationalRadialTranslationBound α s y ^ 2 *
    (logSobolevWeight (-α) α s t * ‖u.val t‖ ^ 2)
  have hg : Integrable g := (integrable_profile_norm (negLe hα) s u).const_mul _
  have hy := measurePreserving_sub_right (volume : Measure ℝ) y
  change (∫ x, logSobolevWeight (-α) α s x * ‖u.val (x - y)‖ ^ 2) ≤ ∫ x, g x
  rw [← hy.integral_comp (MeasurableEquiv.subRight y).measurableEmbedding g]
  refine integral_mono (integrable_profile_norm (negLe hα) s (rationalRadialProfileTranslate y u))
    ((hy.integrable_comp hg.aestronglyMeasurable).2 hg) fun x ↦ ?_
  change logSobolevWeight (-α) α s x * ‖u.val (x - y)‖ ^ 2 ≤ g (x - y)
  simp only [g, ← mul_assoc]
  exact mul_le_mul_of_nonneg_right (by simpa using weight_add_le hα hs (x - y) y) (sq_nonneg _)

/-- The bounded extension of inverse left translation on the actual middle term. -/
public def rationalRadialHilbertTranslate {α s : ℝ} (hα : 0 ≤ α) (_hs : 0 ≤ s) (y : ℝ) :
    rationalRadialHilbert (negLe hα) s →L[ℂ] rationalRadialHilbert (negLe hα) s :=
  ((rationalRadialHilbertInclusion (negLe hα) s).comp (rationalRadialProfileTranslate y)).extendOfNorm
    (rationalRadialHilbertInclusion (negLe hα) s)

public theorem rationalRadialHilbertTranslate_inclusion {α s : ℝ} (hα : 0 ≤ α) (hs : 0 ≤ s)
    (y : ℝ) (u : logWeightedProfiles univ) :
    rationalRadialHilbertTranslate hα hs y (rationalRadialHilbertInclusion (negLe hα) s u) =
      rationalRadialHilbertInclusion (negLe hα) s (rationalRadialProfileTranslate y u) :=
  LinearMap.extendOfNorm_eq (denseRange_rationalRadialHilbertInclusion (negLe hα) s)
    ⟨_, bound_inclusion_translate hα hs y⟩ u

public theorem norm_rationalRadialHilbertTranslate_le {α s : ℝ} (hα : 0 ≤ α) (hs : 0 ≤ s) (y : ℝ) :
    ‖rationalRadialHilbertTranslate hα hs y‖ ≤ rationalRadialTranslationBound α s y :=
  LinearMap.opNorm_extendOfNorm_le (denseRange_rationalRadialHilbertInclusion (negLe hα) s)
    (translationBound_nonneg α s y) (bound_inclusion_translate hα hs y)

private theorem continuous_weight {α : ℝ} (hα : 0 ≤ α) (s : ℝ) :
    Continuous (logSobolevWeight (-α) α s) := by
  have he : logSobolevWeight (-α) α s = fun x ↦ symmetricStripWeightRoot α s x ^ 2 :=
    funext fun x ↦ (root_sq_eq_weight hα s x).symm
  rw [he]
  exact (continuous_symmetricStripWeightRoot α s).pow 2

private theorem denseRange_compact_inclusion {a b : ℝ} (hab : a ≤ b) (s : ℝ) :
    DenseRange (fun u : {u : logWeightedProfiles univ // HasCompactSupport u.val} ↦
      rationalRadialHilbertInclusion hab s u.val) := by
  intro v
  rw [closure_subtype, ← range_comp]
  have hv : v.val ∈ (rationalRadialHilbert hab s : Set _) := v.property
  rw [coe_rationalRadialHilbert] at hv
  refine closure_minimal ?_ isClosed_closure hv
  rintro _ ⟨f, rfl⟩
  obtain ⟨u, huc, hu⟩ := exists_logSobolevAllToLp_tendsto hab s f
  exact mem_closure_of_tendsto hu (Eventually.of_forall fun n ↦ ⟨⟨u n, huc n⟩, rfl⟩)

private theorem continuous_translate_compact {α s : ℝ} (hα : 0 ≤ α) (hs : 0 ≤ s)
    (u : logWeightedProfiles univ) (huc : HasCompactSupport u.val) :
    Continuous (fun y ↦ rationalRadialHilbertTranslate hα hs y
      (rationalRadialHilbertInclusion (negLe hα) s u)) := by
  simp only [rationalRadialHilbertTranslate_inclusion]
  refine continuous_iff_continuousAt.mpr fun y ↦ ?_
  apply tendsto_iff_norm_sub_tendsto_zero.2
  let w := logSobolevWeight (-α) α s
  let F (z x : ℝ) := w x * ‖u.val (x - z) - u.val (x - y)‖ ^ 2
  have hw := continuous_weight hα s
  have hcu := u.property.1.continuous
  let K := tsupport u.val + Icc (y - 1) (y + 1)
  have hK : IsCompact K := (show IsCompact (tsupport u.val) from huc).add isCompact_Icc
  obtain ⟨g, hg⟩ := u.property.2 ⟨0, mem_univ _⟩
  let M := SchwartzMap.seminorm ℝ 0 0 g
  have hM (x : ℝ) : ‖u.val x‖ ≤ M := by
    simpa only [hg, logStageWeight, zero_mul, Real.exp_zero, Complex.ofReal_one, one_mul] using
      SchwartzMap.norm_le_seminorm ℝ g x
  have hbound : ∀ᶠ z in 𝓝 y, ∀ᵐ x ∂(volume : Measure ℝ),
      ‖F z x‖ ≤ K.indicator (fun t ↦ w t * (2 * M) ^ 2) x := by
    filter_upwards [Icc_mem_nhds (show y - 1 < y by linarith) (show y < y + 1 by linarith)] with z hz
    refine ae_of_all _ fun x ↦ ?_
    have hw₀ : 0 ≤ w x := by
      change 0 ≤ logSobolevWeight (-α) α s x
      rw [← root_sq_eq_weight hα]
      positivity
    change ‖w x * ‖u.val (x - z) - u.val (x - y)‖ ^ 2‖ ≤ _
    rw [Real.norm_of_nonneg (mul_nonneg hw₀ (sq_nonneg _))]
    by_cases hx : x ∈ K
    · rw [indicator_of_mem hx]
      apply mul_le_mul_of_nonneg_left _ hw₀
      apply pow_le_pow_left₀ (norm_nonneg _) _ 2
      calc
        _ ≤ ‖u.val (x - z)‖ + ‖u.val (x - y)‖ := norm_sub_le _ _
        _ ≤ 2 * M := by linarith [hM (x - z), hM (x - y)]
    · rw [indicator_of_notMem hx]
      have ho (t : ℝ) (ht : t ∈ Icc (y - 1) (y + 1)) : u.val (x - t) = 0 := by
        apply image_eq_zero_of_notMem_tsupport
        intro hx'
        exact hx ⟨x - t, hx', t, ht, sub_add_cancel x t⟩
      have hy : y ∈ Icc (y - 1) (y + 1) := ⟨by linarith, by linarith⟩
      simp [ho z hz, ho y hy]
  have hI : Tendsto (fun z ↦ ∫ x, F z x) (𝓝 y) (𝓝 0) := by
    have hD := tendsto_integral_filter_of_dominated_convergence
      (F := F) (f := fun _ ↦ (0 : ℝ)) (μ := volume)
      (K.indicator (fun t ↦ w t * (2 * M) ^ 2))
      (Eventually.of_forall fun z ↦ (hw.mul (((hcu.comp (continuous_id.sub continuous_const)).sub
        (hcu.comp (continuous_id.sub continuous_const))).norm.pow 2)).aestronglyMeasurable)
      hbound (((hw.mul continuous_const).continuousOn.integrableOn_compact hK).integrable_indicator
        hK.measurableSet)
    simp only [integral_zero] at hD
    apply hD
    refine ae_of_all _ fun x ↦ ?_
    have hF : Continuous (fun z ↦ F z x) := continuous_const.mul
      (((hcu.comp (continuous_const.sub continuous_id)).sub continuous_const).norm.pow 2)
    simpa only [F, sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0), mul_zero] using (hF.tendsto y)
  have h := Real.continuous_sqrt.continuousAt.tendsto.comp hI
  rw [Real.sqrt_zero] at h
  convert h using 1
  funext z
  rw [← map_sub, norm_inclusion_dx]
  rfl

/-- In the strong operator topology, log translations are continuous at every real shift. -/
public theorem continuous_rationalRadialHilbertTranslate {α s : ℝ} (hα : 0 ≤ α) (hs : 0 ≤ s)
    (u : rationalRadialHilbert (negLe hα) s) :
    Continuous (fun y ↦ rationalRadialHilbertTranslate hα hs y u) := by
  refine continuous_iff_continuousAt.mpr fun y ↦ ?_
  apply continuousAt_of_locally_uniform_approx_of_continuousAt
  intro S hS
  obtain ⟨ε, hε, hεS⟩ := Metric.mem_uniformity_dist.mp hS
  let B := rationalRadialTranslationBound α s y + 1
  have hB : 0 < B := by unfold B; linarith [translationBound_nonneg α s y]
  have hBc : Continuous (rationalRadialTranslationBound α s) :=
    continuous_const.mul (continuous_symmetricStripWeightRoot α s)
  have hN : {z | rationalRadialTranslationBound α s z < B} ∈ 𝓝 y :=
    hBc.continuousAt (Iio_mem_nhds (by simp [B]))
  obtain ⟨v, hv⟩ := (Metric.mem_closure_range_iff.mp (denseRange_compact_inclusion (negLe hα) s u))
    (ε / B) (div_pos hε hB)
  let V := rationalRadialHilbertInclusion (negLe hα) s v.val
  refine ⟨_, hN, (fun z ↦ rationalRadialHilbertTranslate hα hs z V),
    (continuous_translate_compact hα hs v.val v.property).continuousAt, fun z hz ↦ hεS ?_⟩
  change dist (rationalRadialHilbertTranslate hα hs z u) (rationalRadialHilbertTranslate hα hs z V) < ε
  calc
    _ ≤ ‖rationalRadialHilbertTranslate hα hs z‖ * dist u V :=
      (rationalRadialHilbertTranslate hα hs z).dist_le_opNorm u V
    _ ≤ B * dist u V := mul_le_mul_of_nonneg_right
      ((norm_rationalRadialHilbertTranslate_le hα hs z).trans hz.le) dist_nonneg
    _ < ε := by
      change dist u V < ε / B at hv
      exact (mul_comm B _).trans_lt ((lt_div_iff₀ hB).mp hv)

set_option linter.concreteInstances false

local notation "A" => AdeleRing (𝓞 ℚ) ℚ
variable [MeasurableSpace A] [BorelSpace A]
  [MeasurableSpace (A ⧸ rationalDiagonal)] [BorelSpace (A ⧸ rationalDiagonal)]

/-- The global LF lift of the inverse left translation of a half-twisted profile.
The dilation is at `-y`, and the correcting factor is `exp(-y/2)`. -/
public theorem rationalRadialProfileTranslate_theta (y : ℝ) (f : RationalThetaRadialInput) :
    rationalRadialProfileTranslate y (rationalRadialThetaProfiles f) =
      rationalRadialThetaProfiles ((Real.exp (-y / 2) : ℂ) • rationalThetaRadialInputTranslate (-y) f) := by
  apply Subtype.ext
  funext x
  rw [rationalRadialProfileTranslate_apply, map_smul]
  change (rationalRadialThetaProfiles f).val (x - y) =
    (Real.exp (-y / 2) : ℂ) * (rationalRadialThetaProfiles (rationalThetaRadialInputTranslate (-y) f)).val x
  simp only [rationalRadialThetaProfiles_apply, rationalThetaRadialTwistedProfile_apply,
    rationalThetaRadialProfile_translate, ← sub_eq_add_neg, ← mul_assoc, ← Complex.ofReal_mul,
    ← Real.exp_add]
  rw [show -y / 2 + 1 / 2 * x = 1 / 2 * (x - y) by ring]

/-- Left translation preserves the closure of the actual global theta image. -/
public theorem rationalRadialHilbertTranslate_mem_thetaClosure {α s : ℝ}
    (hα : 0 ≤ α) (hs : 0 ≤ s) (y : ℝ) {u : rationalRadialHilbert (negLe hα) s}
    (hu : u ∈ rationalRadialThetaClosure (negLe hα) s) :
    rationalRadialHilbertTranslate hα hs y u ∈ rationalRadialThetaClosure (negLe hα) s := by
  let T := rationalRadialHilbertTranslate hα hs y
  let R := rationalRadialThetaHilbertRange (negLe hα) s
  change T u ∈ closure (R : Set _)
  refine closure_minimal ?_ (isClosed_closure.preimage T.continuous) hu
  intro v hv
  rw [rationalRadialThetaHilbertRange_eq_range] at hv
  obtain ⟨f, rfl⟩ := hv
  change rationalRadialHilbertTranslate hα hs y
    (rationalRadialHilbertInclusion (negLe hα) s (rationalRadialThetaProfiles f)) ∈ closure (R : Set _)
  rw [rationalRadialHilbertTranslate_inclusion, rationalRadialProfileTranslate_theta]
  apply subset_closure
  change _ ∈ rationalRadialThetaHilbertRange (negLe hα) s
  rw [rationalRadialThetaHilbertRange_eq_range]
  exact ⟨_, rfl⟩

/-- Bounded left translation on the actual separated theta quotient. -/
@[expose] public def rationalRadialQuotientTranslate {α s : ℝ} (hα : 0 ≤ α) (hs : 0 ≤ s) (y : ℝ) :
    rationalRadialHilbertQuotient (negLe hα) s →L[ℂ] rationalRadialHilbertQuotient (negLe hα) s :=
  (rationalRadialQuotientProjection (negLe hα) s).comp
    ((rationalRadialHilbertTranslate hα hs y).comp (rationalRadialHilbertQuotient (negLe hα) s).subtypeL)

set_option synthInstance.maxHeartbeats 150000 in
/-- The operator is genuinely induced: projection intertwines on every lift. -/
public theorem rationalRadialQuotientTranslate_projection {α s : ℝ}
    (hα : 0 ≤ α) (hs : 0 ≤ s) (y : ℝ) (u : rationalRadialHilbert (negLe hα) s) :
    rationalRadialQuotientTranslate hα hs y (rationalRadialQuotientProjection (negLe hα) s u) =
      rationalRadialQuotientProjection (negLe hα) s (rationalRadialHilbertTranslate hα hs y u) := by
  let P := rationalRadialQuotientProjection (negLe hα) s
  let T := rationalRadialHilbertTranslate hα hs y
  let K := rationalRadialHilbertQuotient (negLe hα) s
  have hP (q : K) : P q.val = q :=
    ((rationalRadialThetaHilbertRange (negLe hα) s)ᗮ).orthogonalProjectionOnto_mem_subspace_eq_self q
  have hu : u - (P u).val ∈ rationalRadialThetaClosure (negLe hα) s := by
    rw [← (rationalRadialQuotientProjection_exact (negLe hα) s).1]
    exact LinearMap.mem_ker.mpr (by change P (u - (P u).val) = 0; rw [map_sub, hP, sub_self])
  have ht := rationalRadialHilbertTranslate_mem_thetaClosure hα hs y hu
  rw [← (rationalRadialQuotientProjection_exact (negLe hα) s).1] at ht
  have hz := LinearMap.mem_ker.mp ht
  change P (T (u - (P u).val)) = 0 at hz
  rw [map_sub, map_sub, sub_eq_zero] at hz
  exact hz.symm

end
end Masullo
