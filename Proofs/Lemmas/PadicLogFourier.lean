module

public import Lemmas.PadicLogMoment
public import Theorems.PadicIntegralBallFourier

import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.MeasureTheory.Function.LocallyIntegrable
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

end Masullo
