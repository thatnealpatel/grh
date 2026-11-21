module

public import Lemmas.RealLogCutoff
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! # Both signs and both log rays of the real cutoff -/

open Filter MeasureTheory Set
open scoped ENNReal Topology

namespace Masullo.RealLogHaarFold

private def tails (ε : ℝ) : Set ℝ := {x | ε ≤ |x|}

private theorem logValueSet_split (ε : ℝ) :
    RealLogCutoff.logValueSet ε =
      (Real.exp '' tails ε ∪ (fun x ↦ -Real.exp x) '' tails ε) ∪ {0} := by
  ext y
  have hpos (t : ℝ) (ht : 0 < t) :
      t ∈ Real.exp '' tails ε ↔ t ≤ Real.exp (-ε) ∨ Real.exp ε ≤ t := by
    rw [← Real.log_le_iff_le_exp ht, ← Real.le_log_iff_exp_le ht]
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [Real.log_exp]
      rcases le_abs.mp (show ε ≤ |x| from hx) with h | h
      · exact Or.inr h
      · exact Or.inl (by linarith)
    · intro h
      refine ⟨Real.log t, ?_, Real.exp_log ht⟩
      change ε ≤ |Real.log t|
      apply le_abs.mpr
      rcases h with h | h
      · exact Or.inr (by linarith)
      · exact Or.inl h
  by_cases h : y = 0
  · subst y
    simp [RealLogCutoff.logValueSet, (Real.exp_pos (-ε)).le]
  rcases lt_or_gt_of_ne h with hy | hy
  · have hn : y ∈ (fun x ↦ -Real.exp x) '' tails ε ↔ -y ∈ Real.exp '' tails ε := by
      constructor <;> rintro ⟨x, hx, hh⟩ <;> exact ⟨x, hx, by linarith⟩
    have hp : y ∉ Real.exp '' tails ε := by
      rintro ⟨x, _, rfl⟩
      exact (Real.exp_pos x).not_gt hy
    simpa [RealLogCutoff.logValueSet, abs_of_neg hy, hp, hn, h] using (hpos (-y) (neg_pos.mpr hy)).symm
  · have hn : y ∉ (fun x ↦ -Real.exp x) '' tails ε := by
      rintro ⟨x, _, rfl⟩
      linarith [Real.exp_pos x]
    simpa [RealLogCutoff.logValueSet, abs_of_pos hy, hn, h] using (hpos y hy).symm

private noncomputable def weight (x : ℝ) : ℝ :=
    Real.exp (x / 2) * (|1 - Real.exp x|⁻¹ + (1 + Real.exp x)⁻¹)

private theorem weight_neg {x : ℝ} (hx : 0 < x) : weight (-x) = weight x := by
  have h : 1 < Real.exp x := Real.one_lt_exp_iff.mpr hx
  have hn : Real.exp (-x) < 1 := Real.exp_lt_one_iff.mpr (neg_neg_of_pos hx)
  have hb := Real.exp_pos (x / 2)
  have hab : Real.exp x = Real.exp (x / 2) ^ 2 := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  unfold weight
  rw [abs_of_pos (sub_pos.mpr hn), abs_of_neg (sub_neg.mpr h), neg_sub]
  simp only [neg_div, Real.exp_neg]
  rw [hab] at h ⊢
  generalize Real.exp (x / 2) = b at h hb ⊢
  have hb2 : 0 < b ^ 2 := sq_pos_of_pos hb
  have hz : b ^ 2 - 1 ≠ 0 := (sub_pos.mpr h).ne'
  have hp : 1 + b ^ 2 ≠ 0 := by positivity
  field_simp [hb.ne', hb2.ne', hz, hp]
  ring

private theorem half_weight {x : ℝ} (hx : 0 < x) :
    weight x / 2 = Real.exp (-x / 2) / (1 - Real.exp (-2 * x)) := by
  have h : 1 < Real.exp x := Real.one_lt_exp_iff.mpr hx
  have hb := Real.exp_pos (x / 2)
  have hab : Real.exp x = Real.exp (x / 2) ^ 2 := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hab' : Real.exp (-2 * x) = (Real.exp (x / 2) ^ 4)⁻¹ := by
    rw [show -2 * x = -(4 * (x / 2)) by ring, Real.exp_neg]
    congr 1
    exact mod_cast (Real.exp_nat_mul (x / 2) 4)
  unfold weight
  rw [abs_of_neg (sub_neg.mpr h), neg_sub, neg_div, Real.exp_neg]
  rw [hab, hab']
  rw [hab] at h
  generalize Real.exp (x / 2) = b at h hb ⊢
  have hz : b ^ 2 - 1 ≠ 0 := (sub_pos.mpr h).ne'
  have hp : 1 + b ^ 2 ≠ 0 := by positivity
  have h4 : b ^ 4 - 1 ≠ 0 := by
    rw [show b ^ 4 - 1 = (b ^ 2 - 1) * (1 + b ^ 2) by ring]
    exact mul_ne_zero hz hp
  field_simp [hb.ne', hz, hp, h4]
  ring

/-- In the signed exponential coordinates the log cutoff on half of full
Haar folds to a single positive ray. The kernel is absolutely integrable
on that ray at each positive cutoff. -/
public theorem fold {F : ℝ → ℂ} (hu : Integrable (realLogProfileAdditive F))
    {ε : ℝ} (hε : 0 < ε) :
    let μ := (1 / 2 : ℝ≥0∞) • realMultiplicativeHaar
    let w (x : ℝ) := (F x + F (-x)) * Complex.exp (-(x : ℂ) / 2) /
      (1 - Complex.exp (-2 * (x : ℂ)))
    IntegrableOn w (Ioi ε) ∧
      (∫ y in {y : ℝˣ | ε ≤ |Real.log (|(y : ℝ)|)|}, realLogProfileHaarKernel F y ∂μ) =
        ∫ x in Ioi ε, w x := by
  intro μ w
  let d (y : ℝ) : ℂ := realLogProfileAdditive F (y - 1) / (|1 - y| : ℝ)
  let N (x : ℝ) := -Real.exp x
  let S := tails ε
  have hS : MeasurableSet S := measurableSet_le measurable_const continuous_abs.measurable
  have hN : MeasurableEmbedding N :=
    (Homeomorph.neg ℝ).isClosedEmbedding.measurableEmbedding.comp
      Real.isOpenEmbedding_exp.measurableEmbedding
  have hD : Disjoint (Real.exp '' S) (N '' S) := by
    rw [Set.disjoint_left]
    rintro _ ⟨x, _, rfl⟩ ⟨y, _, hy⟩
    dsimp [N] at hy
    linarith [Real.exp_pos x, Real.exp_pos y]
  have hunion : Real.exp '' S ∪ N '' S ⊆ RealLogCutoff.logValueSet ε := by
    rw [logValueSet_split]
    exact subset_union_left
  have hdi : IntegrableOn d (RealLogCutoff.logValueSet ε) :=
    (RealLogProfileHaar.translate_set _ _).1.mp (RealLogCutoff.integrableOn_logAddSet hu hε)
  have hP : ∀ x ∈ S, HasDerivWithinAt Real.exp (Real.exp x) S x :=
    fun x _ ↦ (Real.hasDerivAt_exp x).hasDerivWithinAt
  have hM : ∀ x ∈ S, HasDerivWithinAt N (-Real.exp x) S x :=
    fun x _ ↦ (Real.hasDerivAt_exp x).neg.hasDerivWithinAt
  have hp := integrableOn_image_iff_integrableOn_abs_deriv_smul hS hP
    Real.exp_injective.injOn d
  have hn := integrableOn_image_iff_integrableOn_abs_deriv_smul hS hM hN.injective.injOn d
  have hpi := hp.mp (hdi.mono_set (subset_union_left.trans hunion))
  have hni := hn.mp (hdi.mono_set (subset_union_right.trans hunion))
  let J (x : ℝ) := (weight x : ℂ) * F x
  have hj (x : ℝ) : |Real.exp x| • d (Real.exp x) + |-Real.exp x| • d (N x) = J x := by
    have hp' := Real.exp_pos x
    have hy (y : ℝ) : 1 + (y - 1) = y := by ring
    have hh : Real.exp x * (Real.exp x) ^ (-(1 / 2) : ℝ) = Real.exp (x / 2) := by
      rw [Real.rpow_def_of_pos hp', Real.log_exp, ← Real.exp_add]
      congr 1
      ring
    simp only [J, d, N, realLogProfileAdditive, hy, abs_neg, abs_of_pos hp', hp'.ne',
      neg_ne_zero.mpr hp'.ne', ite_false, Real.log_exp, sub_neg_eq_add, abs_of_pos (by positivity : 0 < 1 + Real.exp x),
      Complex.real_smul, weight]
    push_cast [← hh]
    ring
  have hJi : IntegrableOn J S := (hpi.add hni).congr (Filter.Eventually.of_forall hj)
  have hsum : (∫ y in RealLogCutoff.logValueSet ε, d y) = ∫ x in S, J x := by
    rw [logValueSet_split, integral_union_eq_left_of_forall (measurableSet_singleton 0)
      (by simp [d, realLogProfileAdditive] : ∀ x ∈ ({0} : Set ℝ), d x = 0),
      setIntegral_union hD (hN.measurableSet_image' hS)
        (hdi.mono_set (subset_union_left.trans hunion)) (hdi.mono_set (subset_union_right.trans hunion)),
      integral_image_eq_integral_abs_deriv_smul hS hP Real.exp_injective.injOn d,
      integral_image_eq_integral_abs_deriv_smul hS hM hN.injective.injOn d, ← integral_add hpi hni]
    exact integral_congr_ae (Filter.Eventually.of_forall hj)
  have hs : S = Ici ε ∪ Iic (-ε) := by
    ext x
    simp only [S, tails, mem_ofPred_eq, mem_union, mem_Ici, mem_Iic, le_abs]
    constructor <;> rintro (h | h) <;> [exact Or.inl h; exact Or.inr (by linarith); exact Or.inl h; exact Or.inr (by linarith)]
  have hdis : Disjoint (Ici ε) (Iic (-ε)) := by
    rw [Set.disjoint_left]
    intro x hx hx'
    exact (not_le_of_gt (by linarith : -ε < ε)) ((mem_Ici.mp hx).trans (mem_Iic.mp hx'))
  rw [hs] at hJi
  have hJp := (hJi.mono_set subset_union_left).mono_set Ioi_subset_Ici_self
  have hJn := hJi.mono_set subset_union_right
  have hJR : IntegrableOn (fun x ↦ J (-x)) (Ioi ε) := by
    have he : MeasurableEmbedding (fun x : ℝ ↦ -x) :=
      (Homeomorph.neg ℝ).isClosedEmbedding.measurableEmbedding
    have hh := he.integrableOn_map_iff (μ := volume) (f := J) (s := Iic (-ε))
    change IntegrableOn J (Iic (-ε)) (volume.map Neg.neg) ↔
      IntegrableOn (fun x ↦ J (-x)) ((fun x : ℝ ↦ -x) ⁻¹' Iic (-ε)) at hh
    rw [Measure.map_neg_eq_self (volume : Measure ℝ)] at hh
    have hp : (fun x : ℝ ↦ -x) ⁻¹' Iic (-ε) = Ici ε := by ext x; simp
    exact ((hh.mp hJn).mono_set (hp ▸ Ioi_subset_Ici_self))
  have hw (x : ℝ) (hx : x ∈ Ioi ε) : (1 / 2 : ℂ) * (J x + J (-x)) = w x := by
    have hx' := hε.trans hx
    have hk := congrArg Complex.ofReal (half_weight hx')
    push_cast [Complex.ofReal_exp] at hk
    simp only [J, w, weight_neg hx']
    linear_combination (F x + F (-x)) * hk
  have hwAE : (fun x ↦ (1 / 2 : ℂ) * (J x + J (-x))) =ᵐ[volume.restrict (Ioi ε)] w :=
    (ae_restrict_mem measurableSet_Ioi).mono hw
  refine ⟨((hJp.add hJR).const_mul _).congr hwAE, ?_⟩
  have hreflect : (∫ x in Iic (-ε), J x) = ∫ x in Ioi ε, J (-x) := by
    simpa only [neg_neg] using integral_comp_neg_Iic (-ε) (fun x ↦ J (-x))
  rw [(RealLogCutoff.haar_logCutoff_eq hu hε).2]
  change (1 / 2 : ℂ) * (∫ z in (fun z ↦ 1 + z) ⁻¹' RealLogCutoff.logValueSet ε,
    realLogProfileAdditive F z / (|z| : ℝ)) = _
  rw [(RealLogProfileHaar.translate_set (realLogProfileAdditive F) (RealLogCutoff.logValueSet ε)).2]
  change (1 / 2 : ℂ) * (∫ y in RealLogCutoff.logValueSet ε, d y) = _
  rw [hsum, hs, setIntegral_union hdis measurableSet_Iic (hJi.mono_set subset_union_left) hJn,
    integral_Ici_eq_integral_Ioi, hreflect]
  rw [← integral_add hJp hJR, ← integral_const_mul]
  exact integral_congr_ae hwAE

private noncomputable def gap (x : ℝ) : ℝ := 1 - Real.exp (-2 * x)

private theorem gap_pos {x : ℝ} (hx : 0 < x) : 0 < gap x :=
  sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith))

private theorem hasDerivAt_gap (x : ℝ) : HasDerivAt gap (2 * Real.exp (-2 * x)) x := by
  convert (((Real.hasDerivAt_exp (-2 * x)).comp x
    ((hasDerivAt_id x).const_mul (-2))).const_sub 1) using 1
  · rfl
  · ring

private theorem integral_gap_deriv {ε : ℝ} (hε : 0 < ε) :
    let f (x : ℝ) := 2 * Real.exp (-2 * x) / gap x
    IntegrableOn f (Ioi ε) ∧ (∫ x in Ioi ε, f x) = -Real.log (gap ε) := by
  intro f
  have hder : ∀ x ∈ Ici ε, HasDerivAt (fun x ↦ Real.log (gap x)) (f x) x := by
    intro x hx
    have hg := gap_pos (hε.trans_le (mem_Ici.mp hx))
    simpa only [f, Function.comp_def, div_eq_mul_inv, mul_comm] using
      (Real.hasDerivAt_log hg.ne').comp x (hasDerivAt_gap x)
  have hpos : ∀ x ∈ Ioi ε, 0 ≤ f x := fun x hx ↦
    div_nonneg (by positivity) (gap_pos (hε.trans hx)).le
  have he : Tendsto (fun x : ℝ ↦ Real.exp (-2 * x)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, id_eq, neg_mul] using Real.tendsto_exp_atBot.comp
      (tendsto_neg_atTop_atBot.comp ((tendsto_const_mul_atTop_of_pos (by norm_num : (0 : ℝ) < 2)).mpr tendsto_id))
  have ht : Tendsto (fun x ↦ Real.log (gap x)) atTop (𝓝 0) := by
    have hg : Tendsto gap atTop (𝓝 1) := by
      unfold gap
      simpa only [sub_zero] using he.const_sub 1
    simpa only [Real.log_one, Function.comp_def] using (Real.continuousAt_log one_ne_zero).tendsto.comp hg
  exact ⟨integrableOn_Ioi_deriv_of_nonneg' hder hpos ht,
    by rw [integral_Ioi_of_hasDerivAt_of_nonneg' hder hpos ht, zero_sub]⟩

/-- The identity subtraction has an elementary primitive on each positive ray. -/
public theorem integral_subtraction (c : ℂ) {ε : ℝ} (hε : 0 < ε) :
    let f (x : ℝ) := 2 * c * Complex.exp (-2 * (x : ℂ)) / (1 - Complex.exp (-2 * (x : ℂ)))
    IntegrableOn f (Ioi ε) ∧ (∫ x in Ioi ε, f x) = -(Real.log (1 - Real.exp (-2 * ε)) : ℂ) * c := by
  intro f
  obtain ⟨hi, he⟩ := integral_gap_deriv hε
  have hf : f = fun x ↦ c * ((2 * Real.exp (-2 * x) / gap x : ℝ) : ℂ) := by
    funext x
    push_cast [gap, Complex.ofReal_exp]
    simp only [f]
    ring
  rw [hf]
  refine ⟨hi.ofReal.const_mul _, ?_⟩
  rw [integral_const_mul, integral_complex_ofReal, he, Complex.ofReal_neg, mul_comm, gap]

/-- At zero the primitive's logarithm differs from the cutoff logarithm by `log 2`. -/
public theorem tendsto_subtraction_correction (c : ℂ) :
    Tendsto (fun ε : ℝ ↦ (∫ x in Ioi ε,
        2 * c * Complex.exp (-2 * (x : ℂ)) / (1 - Complex.exp (-2 * (x : ℂ)))) +
      (Real.log ε : ℂ) * c) (𝓝[Ioi 0] 0) (𝓝 (-(Real.log 2 : ℂ) * c)) := by
  have hr : Tendsto (fun ε : ℝ ↦ gap ε / ε) (𝓝[Ioi 0] 0) (𝓝 2) := by
    simpa [gap, smul_eq_mul, div_eq_mul_inv, mul_comm] using
      (hasDerivAt_gap 0).tendsto_slope_zero_right
  have ht := ((Real.continuousAt_log (by norm_num : (2 : ℝ) ≠ 0)).tendsto.comp hr).neg
  have hc := (Complex.continuous_ofReal.continuousAt.tendsto.comp ht).mul_const c
  rw [Complex.ofReal_neg] at hc
  refine hc.congr' ?_
  filter_upwards [eventually_mem_nhdsWithin (a := (0 : ℝ)) (s := Ioi 0)] with ε hε
  rw [(integral_subtraction c hε).2]
  change (↑(-Real.log (gap ε / ε)) : ℂ) * c = -(Real.log (gap ε) : ℂ) * c + _
  rw [Real.log_div (gap_pos hε).ne' (ne_of_gt hε)]
  push_cast
  ring

/-- Drop the cutoff only for the integrable, combined density. -/
public theorem tendsto_setIntegral_Ioi_zero {f : ℝ → ℂ} (hf : IntegrableOn f (Ioi 0)) :
    Tendsto (fun ε : ℝ ↦ ∫ x in Ioi ε, f x) (𝓝[Ioi 0] 0) (𝓝 (∫ x in Ioi 0, f x)) := by
  have h : Tendsto (fun ε : ℝ ↦ ∫ x, (Ioi ε).indicator f x ∂volume.restrict (Ioi 0))
      (𝓝[Ioi 0] 0) (𝓝 (∫ x in Ioi 0, f x)) := by
    apply tendsto_integral_filter_of_dominated_convergence (fun x ↦ ‖f x‖)
    · exact .of_forall fun ε ↦ hf.aestronglyMeasurable.indicator measurableSet_Ioi
    · exact .of_forall fun ε ↦ .of_forall fun x ↦ by by_cases hx : x ∈ Ioi ε <;> simp [hx]
    · exact hf.norm
    · filter_upwards [ae_restrict_mem (μ := (volume : Measure ℝ)) measurableSet_Ioi] with x hx
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [nhdsWithin_le_nhds (eventually_lt_nhds (mem_Ioi.mp hx))] with ε hε
      exact (indicator_of_mem hε f).symm
  refine h.congr' ?_
  filter_upwards [eventually_mem_nhdsWithin (a := (0 : ℝ)) (s := Ioi 0)] with ε hε
  rw [integral_indicator measurableSet_Ioi,
    Measure.restrict_restrict_of_subset (Ioi_subset_Ioi (le_of_lt hε))]

end Masullo.RealLogHaarFold
