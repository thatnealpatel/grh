module

public import Lemmas.PadicLogMoment
public import Theorems.PadicIntegralBallFourier

import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.NumberTheory.Padics.ProperSpace

/-! # The first outer additive shell and its character integral -/

open scoped Padic ENNReal
open MeasureTheory Set

namespace Masullo

variable (p : ℕ) [Fact p.Prime]

local notation "B" => Set.ofPred (fun x : ℚ_[p] ↦ ‖x‖ ≤ 1)
local notation "T" => Set.ofPred (fun x : ℚ_[p] ↦ ‖(p : ℚ_[p]) * x‖ ≤ 1)
local notation "U" => Set.ofPred (fun x : ℚ_[p] ↦ ‖1 + x‖ = 1)
local notation "C" => Set.ofPred (fun x : ℚ_[p] ↦ ‖(p : ℚ_[p])⁻¹ * (x - (-1))‖ ≤ 1)
local notation "J" => (fun x : ℚ_[p] ↦ ((Real.log ‖x‖ / Real.log (p : ℝ) : ℝ) : ℂ))
local notation "χ" => (fun x : ℚ_[p] ↦ star (padicStdAddChar p (-x)))

private lemma prime_gt_one : (1 : ℝ) < p := by
  exact_mod_cast (Fact.out : p.Prime).one_lt

private lemma largeBall_eq : T = Metric.closedBall 0 (p : ℝ) := by
  ext x
  simp only [mem_ofPred_eq, Metric.mem_closedBall, dist_zero_right,
    norm_mul, Padic.norm_p, ← div_eq_inv_mul]
  rw [div_le_one₀ (lt_trans zero_lt_one (prime_gt_one p))]

private lemma integralBall_subset : B ⊆ T := by
  rw [largeBall_eq]
  intro x hx
  exact Metric.mem_closedBall.mpr (by rw [dist_zero_right]; exact hx.trans (prime_gt_one p).le)

private lemma log_outer : EqOn J (fun _ ↦ (1 : ℂ)) (T \ B) := by
  intro x hx
  have hle : ‖x‖ ≤ p := by
    have ht := hx.1
    rw [largeBall_eq, Metric.mem_closedBall, dist_zero_right] at ht
    exact ht
  have hge : (p : ℝ) ≤ ‖x‖ := by
    apply le_of_not_gt
    intro h
    apply hx.2
    change ‖x‖ ≤ 1
    have hd := (Padic.norm_le_pow_iff_norm_lt_pow_add_one x 0).mpr
    apply (by simpa only [zpow_zero] using hd : ‖x‖ < (p : ℝ) ^ ((0 : ℤ) + 1) → ‖x‖ ≤ 1)
    simpa using h
  change ((Real.log ‖x‖ / Real.log (p : ℝ) : ℝ) : ℂ) = 1
  rw [le_antisymm hle hge, div_self (Real.log_pos (prime_gt_one p)).ne', Complex.ofReal_one]

/-- The translated unit indicator is the difference of the integral ball and
its residue class of `-1`. The weight `|1+x|ₚ^(-1/2)` is one on its support. -/
public lemma padicTranslatedUnits_eq_sdiff : U = B \ C ∧ C ⊆ B := by
  have hp := lt_trans zero_lt_one (prime_gt_one p)
  have hc (x : ℚ_[p]) : x ∈ C ↔ ‖1 + x‖ < 1 := by
    change ‖(p : ℚ_[p])⁻¹ * (x - (-1))‖ ≤ 1 ↔ _
    have hd := Padic.norm_lt_pow_iff_norm_le_pow_sub_one (1 + x) 0
    simp only [zpow_zero, zero_sub, zpow_neg_one] at hd
    rw [norm_mul, norm_inv, Padic.norm_p, inv_inv, ← le_div_iff₀' hp, one_div,
      sub_neg_eq_add, add_comm x, ← hd]
  have hxB (x : ℚ_[p]) (h : ‖1 + x‖ ≤ 1) : x ∈ B := by
    change ‖x‖ ≤ 1
    have hdiff := IsUltrametricDist.norm_add_le_max (1 + x) (-1 : ℚ_[p])
    have he : 1 + x + (-1 : ℚ_[p]) = x := by abel
    rw [he] at hdiff
    exact hdiff.trans (max_le h (by simp))
  refine ⟨?_, fun x hx ↦ hxB x ((hc x).mp hx).le⟩
  ext x
  change ‖1 + x‖ = 1 ↔ x ∈ B ∧ x ∉ C
  rw [hc]
  constructor
  · intro h
    exact ⟨hxB x h.le, not_lt.mpr h.ge⟩
  · rintro ⟨hx, hn⟩
    change ‖x‖ ≤ 1 at hx
    have hadd := IsUltrametricDist.norm_add_le_max (1 : ℚ_[p]) x
    exact le_antisymm (hadd.trans (max_le (by simp) hx)) (not_lt.mp hn)

private lemma phase_on_B : EqOn χ (fun _ ↦ (1 : ℂ)) B := by
  intro x hx
  change ‖x‖ ≤ 1 at hx
  change star (padicStdAddChar p (-x)) = 1
  rw [(padicStdAddChar_eq_one_iff p (-x)).mpr (by simpa only [norm_neg] using hx), star_one]

private lemma phase_integral_T : (∫ x in T, χ x ∂padicAddHaar p) = 0 := by
  let d : ℚ_[p] := p
  have hd : d ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne p)
  let e := (ContinuousAddEquiv.mulLeft (Units.mk0 d⁻¹ (inv_ne_zero hd))).toHomeomorph.toMeasurableEquiv
  have he : e ⁻¹' T = B := by
    ext x
    change ‖d * (d⁻¹ * x)‖ ≤ 1 ↔ ‖x‖ ≤ 1
    rw [← mul_assoc, mul_inv_cancel₀ hd, one_mul]
  have hmap : Measure.map e (padicAddHaar p) = (p : ℝ≥0∞)⁻¹ • padicAddHaar p := by
    change Measure.map (fun x : ℚ_[p] ↦ (p : ℚ_[p])⁻¹ * x) (padicAddHaar p) = _
    simpa only [pow_one] using padicAddHaar_map_inv_pow p 1
  have h := setIntegral_map_equiv (μ := padicAddHaar p) e χ T
  rw [hmap, he, Measure.restrict_smul, integral_smul_measure] at h
  have hf : (∫ x in B, χ (e x) ∂padicAddHaar p) = 0 := by
    have hnot : -d⁻¹ ∉ B := by
      change ¬ ‖(-(p : ℚ_[p])⁻¹)‖ ≤ 1
      rw [norm_neg, norm_inv, Padic.norm_p, inv_inv]
      exact not_le.mpr (prime_gt_one p)
    convert (padicIntegralBall_fourier p (-d⁻¹)).trans (indicator_of_notMem hnot _) using 2
    ext x
    change star (padicStdAddChar p (-(d⁻¹ * x))) = star (padicStdAddChar p (x * -d⁻¹))
    rw [mul_neg, mul_comm d⁻¹ x]
  rw [hf, smul_eq_zero] at h
  refine h.resolve_left ?_
  simp [NeZero.ne p]

/-- Integrating the phase-weighted logarithm on `p⁻¹ ℤ_[p]` adds `-1` to the
inner-ball logarithmic moment: The outer shell has logarithm one, and its
character integral is minus the mass of the inner ball. -/
public lemma padicOuterBall_log_phase :
    IntegrableOn (fun x ↦ J x * χ x) T (padicAddHaar p) ∧
      (∫ x in T, J x * χ x ∂padicAddHaar p) = (-1 / ((p : ℝ) - 1) : ℝ) - 1 := by
  have hB : MeasurableSet B := (isClosed_le continuous_norm continuous_const).measurableSet
  have hT : MeasurableSet T := by rw [largeBall_eq]; exact Metric.isClosed_closedBall.measurableSet
  have hBT := integralBall_subset p
  have heB : EqOn (fun x ↦ J x * χ x) J B := fun x hx ↦ by
    change J x * χ x = J x
    rw [show χ x = 1 from phase_on_B p hx, mul_one]
  have heO : EqOn (fun x ↦ J x * χ x) χ (T \ B) := fun x hx ↦ by
    change J x * χ x = χ x
    rw [show J x = 1 from log_outer p hx, one_mul]
  have hχ : IntegrableOn χ T (padicAddHaar p) := by
    have hc : Continuous χ := (continuous_padicStdAddChar p).comp continuous_neg |>.star
    rw [largeBall_eq]
    exact hc.continuousOn.integrableOn_compact (isCompact_closedBall _ _)
  have hm := padicIntegralBall_log_moment p
  have hiB : IntegrableOn (fun x ↦ J x * χ x) B (padicAddHaar p) :=
    (hm.1.ofReal).congr_fun heB.symm hB
  have hiO := (hχ.mono_set (sdiff_subset : T \ B ⊆ T)).congr_fun heO.symm (hT.diff hB)
  have hs : T \ B ∪ B = T := sdiff_union_of_subset hBT
  refine ⟨hs ▸ hiO.union hiB, ?_⟩
  rw [← hs, setIntegral_union disjoint_sdiff_left hB hiO hiB,
    setIntegral_congr_fun (hT.diff hB) heO, setIntegral_congr_fun hB heB,
    setIntegral_sdiff hB hχ hBT, phase_integral_T,
    setIntegral_congr_fun hB (phase_on_B p), setIntegral_const,
    integral_complex_ofReal, hm.2, measureReal_def, padicAddHaar_integralBall]
  simp [sub_eq_add_neg, add_comm]

private lemma radial_tail_integral (R : ℝ) (w : ℝ → ℂ) :
    (∫ x in Metric.closedBall (0 : ℚ_[p]) R \ T, w ‖x‖ * χ x ∂padicAddHaar p) = 0 := by
  let D := Metric.closedBall (0 : ℚ_[p]) R \ T
  let f := D.indicator (fun x ↦ w ‖x‖ * χ x)
  -- Translation by `p⁻¹` preserves the tail radius, but multiplies the phase by `χ b`.
  let b : ℚ_[p] := (p : ℚ_[p])⁻¹
  have hb : ‖b‖ = (p : ℝ) := by simp [b, Padic.norm_p]
  have hχb : χ b ≠ 1 := by
    intro h
    have hh : padicStdAddChar p (-b) = 1 := by simpa using congrArg star h
    have hn := (padicStdAddChar_eq_one_iff p _).mp hh
    rw [norm_neg, hb] at hn
    exact (not_le.mpr (prime_gt_one p)) hn
  have hmem (x : ℚ_[p]) : x ∈ D ↔ (p : ℝ) < ‖x‖ ∧ ‖x‖ ≤ R := by
    simp only [D, mem_sdiff, largeBall_eq, Metric.mem_closedBall, dist_zero_right, not_le, and_comm]
  have hnorm (x : ℚ_[p]) (hx : (p : ℝ) < ‖x‖) : ‖x + b‖ = ‖x‖ := by
    have hb' : ‖b‖ < ‖x‖ := hb ▸ hx
    rw [Padic.add_eq_max_of_ne hb'.ne', max_eq_left hb'.le]
  have htrans (x : ℚ_[p]) : f (x + b) = χ b * f x := by
    by_cases hx : (p : ℝ) < ‖x‖
    · have hm : x + b ∈ D ↔ x ∈ D := by rw [hmem, hmem, hnorm x hx]
      by_cases h : x ∈ D
      · rw [show f (x + b) = _ from indicator_of_mem (hm.mpr h) _,
          show f x = _ from indicator_of_mem h _, hnorm x hx]
        simp only [neg_add, AddChar.map_add_eq_mul, star_mul']
        ring
      · rw [show f (x + b) = 0 from indicator_of_notMem (mt hm.mp h) _,
          show f x = 0 from indicator_of_notMem h _, mul_zero]
    · have hxb : ‖x + b‖ ≤ (p : ℝ) :=
        (IsUltrametricDist.norm_add_le_max x b).trans (max_le (not_lt.mp hx) hb.le)
      rw [show f (x + b) = 0 from indicator_of_notMem (fun h ↦ (not_lt.mpr hxb) ((hmem _).mp h).1) _,
        show f x = 0 from indicator_of_notMem (fun h ↦ hx ((hmem _).mp h).1) _, mul_zero]
  have h := integral_add_right_eq_self (μ := padicAddHaar p) f b
  simp_rw [htrans] at h
  rw [integral_const_mul] at h
  have hz : (∫ x, f x ∂padicAddHaar p) = 0 := by
    by_contra hn
    exact hχb ((mul_eq_right₀ hn).mp h)
  have hD : MeasurableSet D := Metric.isClosed_closedBall.measurableSet.diff
    (largeBall_eq p ▸ Metric.isClosed_closedBall.measurableSet)
  rwa [show (∫ x, f x ∂padicAddHaar p) = _ from integral_indicator hD] at hz

private lemma shiftedLog_moment (R : ℝ) (hR : (p : ℝ) ≤ R) (c : ℂ) :
    let D := Metric.closedBall (0 : ℚ_[p]) R
    IntegrableOn (fun x ↦ (J x + c) * χ x) D (padicAddHaar p) ∧
      (∫ x in D, (J x + c) * χ x ∂padicAddHaar p) = (-1 / ((p : ℝ) - 1) : ℝ) - 1 := by
  dsimp only
  let D := Metric.closedBall (0 : ℚ_[p]) R
  have hT : MeasurableSet T := by rw [largeBall_eq]; exact Metric.isClosed_closedBall.measurableSet
  have hTD : T ⊆ D := by rw [largeBall_eq]; exact Metric.closedBall_subset_closedBall hR
  have hiχ : IntegrableOn χ T (padicAddHaar p) := by
    rw [largeBall_eq]
    exact ((continuous_padicStdAddChar p).comp continuous_neg).star.continuousOn.integrableOn_compact
      (isCompact_closedBall _ _)
  have hiT : IntegrableOn (fun x ↦ (J x + c) * χ x) T (padicAddHaar p) := by
    convert (padicOuterBall_log_phase p).1.add (hiχ.const_mul c) using 1
    ext x
    exact add_mul _ _ _
  have hiD : IntegrableOn (fun x ↦ (J x + c) * χ x) (D \ T) (padicAddHaar p) := by
    classical
    let w : ℝ → ℝ := fun r ↦ Real.log (max r (p : ℝ)) / Real.log (p : ℝ)
    have hw : Continuous w := (continuous_id.max continuous_const).log
      (fun r ↦ ne_of_gt ((lt_trans zero_lt_one (prime_gt_one p)).trans_le (le_max_right r _))) |>.div_const _
    have hc : Continuous (fun x : ℚ_[p] ↦ ((w ‖x‖ : ℂ) + c) * χ x) :=
      (((Complex.continuous_ofReal.comp (hw.comp continuous_norm)).add continuous_const).mul
        ((continuous_padicStdAddChar p).comp continuous_neg).star)
    refine ((hc.continuousOn.integrableOn_compact (isCompact_closedBall (0 : ℚ_[p]) R)).mono_set
      (sdiff_subset : D \ T ⊆ D)).congr_fun ?_ (Metric.isClosed_closedBall.measurableSet.diff hT)
    intro x hx
    have hx' : ¬ ‖x‖ ≤ (p : ℝ) := by
      have h := hx.2
      change x ∉ T at h
      rwa [largeBall_eq, Metric.mem_closedBall, dist_zero_right] at h
    change ((w ‖x‖ : ℂ) + c) * χ x = _
    simp only [w, max_eq_left (not_le.mp hx').le]
  change IntegrableOn _ D _ ∧ (∫ x in D, _ ∂padicAddHaar p) = _
  rw [← sdiff_union_of_subset hTD]
  refine ⟨hiD.union hiT, ?_⟩
  rw [setIntegral_union disjoint_sdiff_left hT hiD hiT,
    radial_tail_integral p R (fun r ↦ ((Real.log r / Real.log (p : ℝ) : ℝ) : ℂ) + c), zero_add]
  simp_rw [add_mul]
  rw [integral_add (padicOuterBall_log_phase p).1 (hiχ.const_mul c), integral_const_mul,
    phase_integral_T p, mul_zero, add_zero, (padicOuterBall_log_phase p).2]

private lemma padicAddHaar_map_dilation (d : ℚ_[p]) (hd : d ≠ 0) :
    Measure.map (fun x : ℚ_[p] ↦ d * x) (padicAddHaar p) =
      ENNReal.ofReal ‖d‖⁻¹ • padicAddHaar p := by
  let e := ContinuousAddEquiv.mulLeft (Units.mk0 d hd)
  let μ := Measure.map e (padicAddHaar p)
  have : μ.IsAddHaarMeasure := ContinuousAddEquiv.isAddHaarMeasure_map _ e
  have h := Measure.isAddLeftInvariant_eq_smul μ (padicAddHaar p)
  have hmass : μ B = ENNReal.ofReal ‖d‖⁻¹ := by
    have hB : MeasurableSet B := (isClosed_le continuous_norm continuous_const).measurableSet
    have hem : Measurable (e : ℚ_[p] → ℚ_[p]) := e.continuous.measurable
    rw [show μ = Measure.map e (padicAddHaar p) from rfl, Measure.map_apply hem hB]
    have he : e ⁻¹' B = (fun x : ℚ_[p] ↦ d⁻¹ * x) '' B := by
      ext x
      change ‖d * x‖ ≤ 1 ↔ ∃ y : ℚ_[p], ‖y‖ ≤ 1 ∧ d⁻¹ * y = x
      constructor
      · intro hx
        exact ⟨d * x, hx, by rw [← mul_assoc, inv_mul_cancel₀ hd, one_mul]⟩
      · rintro ⟨y, hy, rfl⟩
        rwa [← mul_assoc, mul_inv_cancel₀ hd, one_mul]
    rw [he, padicAddHaar_dilate_integralBall p _ (inv_ne_zero hd), norm_inv]
  have hc := congrArg (fun m : Measure ℚ_[p] ↦ m B) h
  simp only [smul_apply, ENNReal.smul_def, smul_eq_mul, padicAddHaar_integralBall, mul_one] at hc
  change μ = _
  rw [h]
  change (↑(μ.addHaarScalarFactor (padicAddHaar p)) : ℝ≥0∞) • padicAddHaar p = _
  rw [← hc, hmass]

/-- The log-weighted phase has a stable integral once the frequency ball
includes the first shell on which the phase is nontrivial. -/
public lemma padic_log_phase_moment (a : ℚ_[p]) (ha : a ≠ 0) (R : ℝ)
    (hR : (p : ℝ) ≤ ‖a‖ * R) :
    let D := Metric.closedBall (0 : ℚ_[p]) R
    let f := fun ξ ↦ J ξ * star (padicStdAddChar p (a * ξ))
    IntegrableOn f D (padicAddHaar p) ∧
      (∫ ξ in D, f ξ ∂padicAddHaar p) =
        ((‖a‖⁻¹ : ℝ) : ℂ) * ((-1 / ((p : ℝ) - 1) : ℝ) - 1) := by
  dsimp only
  let D := Metric.closedBall (0 : ℚ_[p]) R
  let E := Metric.closedBall (0 : ℚ_[p]) (‖a‖ * R)
  let e := (ContinuousAddEquiv.mulLeft (Units.mk0 (-a) (neg_ne_zero.mpr ha))).toHomeomorph.toMeasurableEquiv
  let c : ℂ := -J a
  let g := fun x ↦ (J x + c) * χ x
  have he : e ⁻¹' E = D := by
    ext x
    simp only [mem_preimage, E, D, Metric.mem_closedBall, dist_zero_right]
    change ‖(-a) * x‖ ≤ ‖a‖ * R ↔ ‖x‖ ≤ R
    rw [norm_mul, norm_neg, mul_le_mul_iff_right₀ (norm_pos_iff.mpr ha)]
  have hmap : Measure.map e (padicAddHaar p) = ENNReal.ofReal ‖a‖⁻¹ • padicAddHaar p := by
    change Measure.map (fun x : ℚ_[p] ↦ (-a) * x) (padicAddHaar p) = _
    simpa only [norm_neg] using padicAddHaar_map_dilation p (-a) (neg_ne_zero.mpr ha)
  -- The logarithm picks up an additive constant under scaling, except at the null singleton.
  have hf : (fun ξ ↦ J ξ * star (padicStdAddChar p (a * ξ))) =ᵐ[(padicAddHaar p).restrict D] g ∘ e := by
    apply ae_restrict_of_ae
    have hzero : ∀ᵐ ξ ∂padicAddHaar p, ξ ≠ (0 : ℚ_[p]) := by
      simp [ae_iff]
    filter_upwards [hzero] with ξ hξ
    change J ξ * star (padicStdAddChar p (a * ξ)) =
      (J ((-a) * ξ) - J a) * star (padicStdAddChar p (-((-a) * ξ)))
    rw [neg_mul, neg_neg, show J (-(a * ξ)) = J a + J ξ by
      simp only [norm_neg, norm_mul,
        Real.log_mul (norm_ne_zero_iff.mpr ha) (norm_ne_zero_iff.mpr hξ), add_div, Complex.ofReal_add]]
    ring
  have hm := shiftedLog_moment p (‖a‖ * R) hR c
  refine ⟨?_, ?_⟩
  · apply (integrable_congr hf).mpr
    change IntegrableOn (g ∘ e) D (padicAddHaar p)
    rw [← he, ← integrableOn_map_equiv e, hmap, IntegrableOn, Measure.restrict_smul]
    exact hm.1.smul_measure ENNReal.ofReal_ne_top
  · rw [integral_congr_ae hf]
    have h := setIntegral_map_equiv (μ := padicAddHaar p) e g E
    rw [he, hmap, Measure.restrict_smul, integral_smul_measure,
      ENNReal.toReal_ofReal (by positivity), hm.2, Complex.real_smul] at h
    exact h.symm

end Masullo
