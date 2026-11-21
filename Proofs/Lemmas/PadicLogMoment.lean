module

public import Lemmas.PadicAddHaar
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

import Lemmas.PadicBallPartition
import Mathlib.Analysis.SpecificLimits.Normed

/-! # Logarithmic moment of normalized additive Haar on the integral ball -/

open scoped Padic ENNReal
open MeasureTheory Set Function

namespace Masullo

variable (p : ℕ) [Fact p.Prime]

local notation "B" => Set.ofPred (fun x : ℚ_[p] ↦ ‖x‖ ≤ 1)
local notation "J" => (fun x : ℚ_[p] ↦ Real.log ‖x‖ / Real.log (p : ℝ))

private def shell (n : ℕ) : Set ℚ_[p] := {x | ‖x‖ = (p : ℝ) ^ (-(n : ℤ))}

private lemma prime_gt_one : (1 : ℝ) < p := by
  exact_mod_cast (Fact.out : p.Prime).one_lt

private lemma shell_measurable (n : ℕ) : MeasurableSet (shell p n) :=
  (isClosed_eq continuous_norm continuous_const).measurableSet

private lemma log_on_shell (n : ℕ) : EqOn J (fun _ ↦ -(n : ℝ)) (shell p n) := by
  intro x hx
  change ‖x‖ = _ at hx
  change Real.log ‖x‖ / Real.log (p : ℝ) = _
  rw [hx, Real.log_zpow, mul_div_cancel_right₀ _ (Real.log_pos (prime_gt_one p)).ne']
  push_cast
  rfl

private lemma shell_lt_or_le {x : ℚ_[p]} (hx : x ≠ 0) (n : ℕ) :
    ‖x‖ ≤ (p : ℝ) ^ (-(n : ℤ)) ↔ (n : ℤ) ≤ x.valuation := by
  rw [Padic.norm_eq_zpow_neg_valuation hx, zpow_le_zpow_iff_right₀ (prime_gt_one p), neg_le_neg_iff]

private lemma integralBall_split : B = (⋃ n, shell p n) ∪ {0} := by
  have h1 : (p : ℝ) ^ (-(0 : ℕ) : ℤ) = 1 := by simp
  ext x
  change ‖x‖ ≤ 1 ↔ x ∈ _
  simp only [mem_union, mem_iUnion, mem_singleton_iff]
  by_cases hx : x = 0
  · simp [hx]
  simp only [hx, or_false]
  constructor
  · intro hb
    have hv : (0 : ℤ) ≤ x.valuation := (shell_lt_or_le p hx 0).mp (h1 ▸ hb)
    exact ⟨x.valuation.toNat, by
      change ‖x‖ = _
      rw [Int.toNat_of_nonneg hv, Padic.norm_eq_zpow_neg_valuation hx]⟩
  · rintro ⟨n, hn⟩
    change ‖x‖ = _ at hn
    rw [hn, ← h1, zpow_le_zpow_iff_right₀ (prime_gt_one p)]
    omega

private lemma shell_disjoint : Pairwise (Disjoint on shell p) := by
  intro i j hij
  refine Set.disjoint_left.mpr fun x hi hj ↦ hij ?_
  have h := (log_on_shell p i hi).symm.trans (log_on_shell p j hj)
  apply Nat.cast_injective (R := ℝ)
  exact neg_injective h

private def innerBall (n : ℕ) : Set ℚ_[p] := {x | ‖x‖ ≤ (p : ℝ) ^ (-(n : ℤ))}

private lemma innerBall_measurable (n : ℕ) : MeasurableSet (innerBall p n) :=
  (isClosed_le continuous_norm continuous_const).measurableSet

private lemma innerBall_succ_subset (n : ℕ) : innerBall p (n + 1) ⊆ innerBall p n := by
  intro x hx
  exact le_trans hx ((zpow_le_zpow_iff_right₀ (prime_gt_one p)).mpr (by omega))

private lemma shell_eq_diff (n : ℕ) : shell p n = innerBall p n \ innerBall p (n + 1) := by
  ext x
  change (‖x‖ = _) ↔ ‖x‖ ≤ _ ∧ ¬ ‖x‖ ≤ _
  by_cases hx : x = 0
  · rw [hx, norm_zero]
    have hpos (k : ℕ) : 0 < (p : ℝ) ^ (-(k : ℤ)) :=
      zpow_pos (lt_trans zero_lt_one (prime_gt_one p)) _
    exact iff_of_false (hpos n).ne (fun h ↦ h.2 (hpos (n + 1)).le)
  rw [shell_lt_or_le p hx, shell_lt_or_le p hx, Padic.norm_eq_zpow_neg_valuation hx]
  have heq : (p : ℝ) ^ (-x.valuation) = (p : ℝ) ^ (-(n : ℤ)) ↔ x.valuation = n := by
    rw [(zpow_right_injective₀ (lt_trans zero_lt_one (prime_gt_one p))
      (prime_gt_one p).ne').eq_iff, neg_inj]
  rw [heq]
  omega

private lemma innerBall_mass (n : ℕ) :
    padicAddHaar p (innerBall p n) = ((p : ℝ≥0∞) ^ n)⁻¹ := by
  have h := padic_measure_dilatedBall p (padicAddHaar p) (padicAddHaar_integralBall p) n
  convert h using 2
  ext x
  have hn : ‖(p : ℚ_[p]) ^ n‖ = (p : ℝ) ^ (-(n : ℤ)) := by
    rw [← zpow_natCast, Padic.norm_p_zpow]
  change ‖x‖ ≤ _ ↔ ‖((p : ℚ_[p]) ^ n)⁻¹ * x‖ ≤ 1
  rw [mul_comm, ← div_eq_mul_inv, norm_div, div_le_one₀, hn]
  rw [hn]
  exact zpow_pos (lt_trans zero_lt_one (prime_gt_one p)) _

private lemma shell_mass_real (n : ℕ) : (padicAddHaar p).real (shell p n) =
    (1 - (p : ℝ)⁻¹) * ((p : ℝ)⁻¹) ^ n := by
  rw [measureReal_def, shell_eq_diff, measure_sdiff (innerBall_succ_subset p n)
    (innerBall_measurable p (n + 1)).nullMeasurableSet]
  · rw [ENNReal.toReal_sub_of_le (measure_mono (innerBall_succ_subset p n)),
      innerBall_mass, innerBall_mass, ENNReal.toReal_inv, ENNReal.toReal_inv,
      ENNReal.toReal_pow, ENNReal.toReal_pow, ENNReal.toReal_natCast, ← inv_pow, ← inv_pow,
      pow_succ]
    · ring
    · rw [innerBall_mass]
      simp [NeZero.ne p]
  · rw [innerBall_mass]
    simp [NeZero.ne p]

private lemma shell_integrable (n : ℕ) : IntegrableOn J (shell p n) (padicAddHaar p) := by
  apply (integrableOn_congr_fun (log_on_shell p n) (shell_measurable p n)).mpr
  refine integrableOn_const ?_ (by simp)
  have hs : shell p n ⊆ innerBall p n := by rw [shell_eq_diff]; exact sdiff_subset
  apply ne_top_of_le_ne_top _ (measure_mono hs)
  rw [innerBall_mass]
  simp [NeZero.ne p]

/-- With integral-ball mass one, `log |x|ₚ / log p` is absolutely integrable on
`ℤ_[p]` and its mean is `-1/(p-1)`. -/
public theorem padicIntegralBall_log_moment :
    IntegrableOn J B (padicAddHaar p) ∧
      (∫ x in B, J x ∂padicAddHaar p) = -1 / ((p : ℝ) - 1) := by
  let r : ℝ := (p : ℝ)⁻¹
  have hp := prime_gt_one p
  have hp₀ : (p : ℝ) ≠ 0 := by positivity
  have hr : ‖r‖ < 1 := by
    rw [Real.norm_of_nonneg (by positivity)]
    exact inv_lt_one_of_one_lt₀ hp
  have hs : HasSum (fun n : ℕ ↦ (n : ℝ) * r ^ n) (r / (1 - r) ^ 2) :=
    hasSum_coe_mul_geometric_of_norm_lt_one hr
  have hU : IntegrableOn J (⋃ n, shell p n) (padicAddHaar p) := by
    refine integrableOn_iUnion_of_summable_integral_norm (shell_integrable p) ?_
    have hn (n : ℕ) : (∫ x in shell p n, ‖J x‖ ∂padicAddHaar p) =
        (1 - r) * ((n : ℝ) * r ^ n) := by
      rw [setIntegral_congr_fun (shell_measurable p n) (fun x hx ↦ congrArg norm (log_on_shell p n hx)),
        setIntegral_const, smul_eq_mul, shell_mass_real, norm_neg, Real.norm_of_nonneg (Nat.cast_nonneg n)]
      dsimp [r]
      ring
    simp_rw [hn]
    exact (hs.mul_left (1 - r)).summable
  have h0 : EqOn J (fun _ ↦ 0) ({0} : Set ℚ_[p]) := by
    intro x hx
    rw [mem_singleton_iff.mp hx]
    simp
  have hm0 : MeasurableSet ({0} : Set ℚ_[p]) := measurableSet_singleton _
  have hI0 := (integrableOn_congr_fun (μ := padicAddHaar p) h0 hm0).mpr (integrable_zero _ _ _)
  have hd : Disjoint (⋃ n, shell p n) ({0} : Set ℚ_[p]) := by
    refine Set.disjoint_left.mpr fun x hx hx₀ ↦ ?_
    obtain ⟨n, hn⟩ := mem_iUnion.mp hx
    change ‖x‖ = _ at hn
    rw [mem_singleton_iff.mp hx₀, norm_zero] at hn
    exact (ne_of_gt (zpow_pos (lt_trans zero_lt_one hp) (-(n : ℤ)))) hn.symm
  rw [integralBall_split p]
  refine ⟨hU.union hI0, ?_⟩
  rw [setIntegral_union hd hm0 hU hI0, setIntegral_congr_fun hm0 h0, integral_zero, add_zero,
    integral_iUnion (shell_measurable p) (shell_disjoint p) hU]
  have hn (n : ℕ) : (∫ x in shell p n, J x ∂padicAddHaar p) =
      (-(1 - r)) * ((n : ℝ) * r ^ n) := by
    rw [setIntegral_congr_fun (shell_measurable p n) (log_on_shell p n), setIntegral_const,
      smul_eq_mul, shell_mass_real]
    dsimp [r]
    ring
  simp_rw [hn]
  rw [(hs.mul_left (-(1 - r))).tsum_eq]
  have hr' : r < 1 := inv_lt_one_of_one_lt₀ hp
  dsimp [r] at *
  field_simp [hp₀, ne_of_gt (sub_pos.mpr hp), ne_of_gt (sub_pos.mpr hr')]

end Masullo
