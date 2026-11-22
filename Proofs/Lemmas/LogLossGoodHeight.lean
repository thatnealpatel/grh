module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! # Averaging logarithmic losses over a unit interval -/

open Filter MeasureTheory Set
open scoped BigOperators

namespace Masullo

private noncomputable def logLoss (x : ℝ) : ℝ := max 0 (-Real.log |x|)

private theorem logLoss_nonneg (x : ℝ) : 0 ≤ logLoss x := le_max_left _ _

private theorem logLoss_integrable_and_integral :
    Integrable logLoss ∧ (∫ x, logLoss x) = 2 := by
  -- `Real.log_abs` holds also at zero, where Lean sets `Real.log 0 = 0`.
  have hcut : logLoss = (Icc (-1 : ℝ) 1).indicator (fun x ↦ -Real.log x) := by
    funext x
    by_cases hx : x ∈ Icc (-1 : ℝ) 1
    · have hn := Real.log_nonpos (abs_nonneg x) (abs_le.mpr hx)
      rw [indicator_of_mem hx, logLoss, max_eq_right (neg_nonneg.mpr hn), Real.log_abs]
    · have hx' : 1 ≤ |x| := le_of_not_gt fun h ↦ hx ⟨(abs_lt.mp h).1.le, (abs_lt.mp h).2.le⟩
      rw [indicator_of_notMem hx, logLoss, max_eq_left (neg_nonpos.mpr (Real.log_nonneg hx'))]
  rw [hcut]
  have hab : (-1 : ℝ) ≤ 1 := by norm_num
  have hlog : IntervalIntegrable (fun x ↦ -Real.log x) volume (-1) 1 :=
    (intervalIntegral.intervalIntegrable_log' (a := -1) (b := 1)).neg
  refine ⟨((intervalIntegrable_iff_integrableOn_Icc_of_le hab).1 hlog).integrable_indicator
    measurableSet_Icc, ?_⟩
  rw [integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hab, intervalIntegral.integral_neg, integral_log]
  norm_num [Real.log_neg_eq_log]

private theorem logLoss_translate (a : ℝ) :
    Integrable (fun t ↦ logLoss (t - a)) ∧ (∫ t, logLoss (t - a)) = 2 := by
  have hp := measurePreserving_sub_right (volume : Measure ℝ) a
  have he : MeasurableEmbedding (fun t : ℝ ↦ t - a) :=
    (Homeomorph.subRight a).isClosedEmbedding.measurableEmbedding
  exact ⟨(hp.integrable_comp_emb he).2 logLoss_integrable_and_integral.1,
    (hp.integral_comp he logLoss).trans logLoss_integrable_and_integral.2⟩

/-- A unit interval contains a height that avoids all the ordinates and has total
multiplicity-weighted logarithmic loss at most twice the total multiplicity. -/
public theorem exists_goodHeight_sum_posLog {ι : Type*} (A : Finset ι) (ordinate : ι → ℝ)
    (n : ι → ℕ) (H : ℝ) :
    ∃ T ∈ Ioo H (H + 1), (∀ ρ ∈ A, T ≠ ordinate ρ) ∧
      (∑ ρ ∈ A, (n ρ : ℝ) * max 0 (-Real.log |T - ordinate ρ|)) ≤
        2 * (∑ ρ ∈ A, (n ρ : ℝ)) := by
  let I := Ioo H (H + 1)
  let F := fun t : ℝ ↦ ∑ ρ ∈ A, (n ρ : ℝ) * logLoss (t - ordinate ρ)
  let B := 2 * (∑ ρ ∈ A, (n ρ : ℝ))
  change ∃ T ∈ I, (∀ ρ ∈ A, T ≠ ordinate ρ) ∧ F T ≤ B
  have hterm (ρ : ι) :
      Integrable (fun t ↦ (n ρ : ℝ) * logLoss (t - ordinate ρ)) (volume.restrict I) :=
    ((logLoss_translate (ordinate ρ)).1.const_mul (n ρ : ℝ)).integrableOn
  have hF : IntegrableOn F I := integrable_finsetSum A fun ρ _ ↦ hterm ρ
  have hbound : (∫ t in I, F t) ≤ B := calc
    (∫ t in I, F t) = ∑ ρ ∈ A, ∫ t in I, (n ρ : ℝ) * logLoss (t - ordinate ρ) :=
      integral_finsetSum A fun ρ _ ↦ hterm ρ
    _ ≤ ∑ ρ ∈ A, (n ρ : ℝ) * 2 := by
      apply Finset.sum_le_sum
      intro ρ _
      rw [integral_const_mul, ← (logLoss_translate (ordinate ρ)).2]
      exact mul_le_mul_of_nonneg_left
        (integral_mono_measure Measure.restrict_le_self
          (Eventually.of_forall fun t ↦ logLoss_nonneg (t - ordinate ρ))
          (logLoss_translate (ordinate ρ)).1) (Nat.cast_nonneg _)
    _ = B := by simp only [B, mul_comm _ (2 : ℝ), Finset.mul_sum]
  have hlen : H + 1 - H = 1 := by ring
  have hvol : volume I = 1 := by simp [I, Real.volume_Ioo, hlen]
  have : (ae (volume.restrict I)).NeBot := ae_restrict_neBot.mpr (by simp [hvol])
  -- The excluded ordinates form a finite union of null singletons.
  have havoid : ∀ᵐ t ∂volume.restrict I, ∀ ρ ∈ A, t ≠ ordinate ρ :=
    A.eventually_all.mpr fun ρ _ ↦ ae_mono Measure.restrict_le_self (volume.ae_ne (ordinate ρ))
  by_contra hex
  have hpos : ∀ᵐ t ∂volume.restrict I, 0 < F t - B := by
    filter_upwards [ae_restrict_mem (μ := volume) (s := I) measurableSet_Ioo, havoid] with t ht htne
    exact sub_pos.mpr (lt_of_not_ge fun h ↦ hex ⟨t, ht, htne, h⟩)
  have hnonneg : 0 ≤ᵐ[volume.restrict I] (fun t ↦ F t - B) := hpos.mono fun _ ht ↦ ht.le
  have hconst : IntegrableOn (fun _ : ℝ ↦ B) I := integrableOn_const (by simp [hvol])
  have hzero : (∫ t in I, F t - B) = 0 := by
    refine le_antisymm ?_ (integral_nonneg_of_ae hnonneg)
    rw [integral_sub hF hconst, setIntegral_const]
    simpa [measureReal_def, hvol] using sub_nonpos.mpr hbound
  have heq := (integral_eq_zero_iff_of_nonneg_ae hnonneg (hF.sub hconst)).mp hzero
  obtain ⟨t, ht, ht'⟩ := (hpos.and heq).exists
  exact ht.ne' ht'

end Masullo
