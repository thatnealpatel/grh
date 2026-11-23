module

public import Props.RealSharpLowerEdges
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic

/-! # The pointwise real radial cutoff comparison

On the repaired positive radial domain for (12.4.1.22) and
(12.4.1.24), p. 518, bracket each upper cutoff profile by two sharp
indicators. Their products bracket the retained radial weight.
-/

open MeasureTheory Set

namespace Masullo

private noncomputable def radialBandDensity (B D r : ℝ) : ℝ → ℝ :=
  (Icc (r / D) B).indicator (fun s ↦ s⁻¹)

private theorem radialBandDensity_apply {B D r s : ℝ} (hD : 0 < D) (hs : 0 < s) :
    radialBandDensity B D r s =
      (Iic B).indicator (fun _ ↦ (1 : ℝ)) s *
        (Iic D).indicator (fun _ ↦ (1 : ℝ)) (r / s) * s⁻¹ := by
  have hd : r / s ≤ D ↔ r / D ≤ s := by
    rw [div_le_iff₀ hs, div_le_iff₀ hD, mul_comm D s]
  by_cases hb : s ≤ B <;> by_cases ha : r / D ≤ s <;>
    simp [radialBandDensity, hd, hb, ha]

private theorem integrable_radialBandDensity {B D r : ℝ} (hD : 0 < D) (hr : 0 < r) :
    Integrable (radialBandDensity B D r) := by
  apply (integrable_indicator_iff measurableSet_Icc).2
  refine (continuous_id.continuousOn.inv₀ ?_).integrableOn_Icc
  intro s hs
  exact ((div_pos hr hD).trans_le hs.1).ne'

private theorem integral_radialBandDensity {B D r : ℝ} (hB : 0 < B) (hD : 0 < D)
    (hr : 0 < r) :
    (∫ s in Ioi 0, radialBandDensity B D r s) = max 0 (Real.log (B * D / r)) := by
  have hsub : Icc (r / D) B ⊆ Ioi 0 := fun _ hs ↦ (div_pos hr hD).trans_le hs.1
  rw [radialBandDensity, setIntegral_indicator measurableSet_Icc, inter_eq_right.mpr hsub]
  by_cases h : r ≤ B * D
  · have hvol := real_position_band_radial_volume (div_pos hr hD) ((div_le_iff₀ hD).2 h) hD hr
    have he : r / D * D = r := div_mul_cancel₀ _ hD.ne'
    have hlog := Real.log_nonneg ((le_div_iff₀ hr).2 (by simpa using h))
    rw [max_eq_right hlog, Real.log_div (hr.trans_le h).ne' hr.ne']
    simpa [he, h] using hvol
  · have hlt := lt_of_not_ge h
    have hlog := Real.log_nonpos (div_nonneg (mul_nonneg hB.le hD.le) hr.le)
      ((div_le_iff₀ hr).2 (by simpa using hlt.le))
    rw [Icc_eq_empty_of_lt ((lt_div_iff₀ hD).2 hlt), setIntegral_empty, max_eq_left hlog]

/-- For bracketed real profiles, the retained product is absolutely integrable
against `ds/s` at every positive radius and lies between the sharp log weights.
Measurability is required only on the positive ray, via zero extension. -/
public theorem real_radial_weight_sandwich {p q : ℝ → ℝ}
    (hp : Measurable ((Ioi (0 : ℝ)).indicator p))
    (hq : Measurable ((Ioi (0 : ℝ)).indicator q))
    {Blo Bhi Dlo Dhi r : ℝ} (hBlo : 0 < Blo) (hB : Blo ≤ Bhi)
    (hDlo : 0 < Dlo) (hD : Dlo ≤ Dhi) (hr : 0 < r)
    (hpB : ∀ s > 0, (Iic Blo).indicator (fun _ ↦ (1 : ℝ)) s ≤ p s ∧
      p s ≤ (Iic Bhi).indicator (fun _ ↦ (1 : ℝ)) s)
    (hqD : ∀ s > 0, (Iic Dlo).indicator (fun _ ↦ (1 : ℝ)) s ≤ q s ∧
      q s ≤ (Iic Dhi).indicator (fun _ ↦ (1 : ℝ)) s) :
    IntegrableOn (fun s ↦ p s * q (r / s) * s⁻¹) (Ioi 0) ∧
      max 0 (Real.log (Blo * Dlo / r)) ≤ (∫ s in Ioi 0, p s * q (r / s) * s⁻¹) ∧
      (∫ s in Ioi 0, p s * q (r / s) * s⁻¹) ≤ max 0 (Real.log (Bhi * Dhi / r)) := by
  let g (s : ℝ) := p s * q (r / s) * s⁻¹
  have hDhi := hDlo.trans_le hD
  have hmeas : AEStronglyMeasurable g (volume.restrict (Ioi 0)) := by
    have hd : Measurable (fun s : ℝ ↦ r / s) := measurable_const.div measurable_id
    have hm := (hp.mul (hq.comp hd)).mul (measurable_id.inv : Measurable (fun s : ℝ ↦ s⁻¹))
    apply hm.aestronglyMeasurable.congr
    filter_upwards [ae_restrict_mem (μ := (volume : Measure ℝ)) measurableSet_Ioi] with s hs
    change 0 < s at hs
    simp [g, indicator_of_mem (mem_Ioi.mpr hs), indicator_of_mem (mem_Ioi.mpr (div_pos hr hs))]
  have hcmp (s : ℝ) (hs : 0 < s) :
      0 ≤ g s ∧ radialBandDensity Blo Dlo r s ≤ g s ∧ g s ≤ radialBandDensity Bhi Dhi r s := by
    have hn (b t : ℝ) : 0 ≤ (Iic b).indicator (fun _ ↦ (1 : ℝ)) t :=
      indicator_nonneg (fun _ _ ↦ zero_le_one) t
    obtain ⟨hpl, hpu⟩ := hpB s hs
    obtain ⟨hql, hqu⟩ := hqD (r / s) (div_pos hr hs)
    have hpn := (hn Blo s).trans hpl
    have hqn := (hn Dlo (r / s)).trans hql
    rw [radialBandDensity_apply hDlo hs, radialBandDensity_apply hDhi hs]
    exact ⟨mul_nonneg (mul_nonneg hpn hqn) (inv_nonneg.mpr hs.le),
      mul_le_mul_of_nonneg_right (mul_le_mul hpl hql (hn Dlo (r / s)) hpn)
        (inv_nonneg.mpr hs.le),
      mul_le_mul_of_nonneg_right (mul_le_mul hpu hqu hqn (hn Bhi s)) (inv_nonneg.mpr hs.le)⟩
  have hlow := (integrable_radialBandDensity (B := Blo) (r := r) hDlo hr).integrableOn (s := Ioi 0)
  have hupp := (integrable_radialBandDensity (B := Bhi) (r := r) hDhi hr).integrableOn (s := Ioi 0)
  have hint : IntegrableOn g (Ioi 0) := by
    refine hupp.mono' hmeas ?_
    filter_upwards [ae_restrict_mem (μ := (volume : Measure ℝ)) measurableSet_Ioi] with s hs
    obtain ⟨hn, _, hu⟩ := hcmp s (mem_Ioi.mp hs)
    simpa [Real.norm_eq_abs, abs_of_nonneg hn] using hu
  change IntegrableOn g (Ioi 0) ∧
    max 0 (Real.log (Blo * Dlo / r)) ≤ (∫ s in Ioi 0, g s) ∧
    (∫ s in Ioi 0, g s) ≤ max 0 (Real.log (Bhi * Dhi / r))
  rw [← integral_radialBandDensity hBlo hDlo hr,
    ← integral_radialBandDensity (hBlo.trans_le hB) hDhi hr]
  exact ⟨hint, setIntegral_mono_on hlow hint measurableSet_Ioi fun s hs ↦ (hcmp s hs).2.1,
    setIntegral_mono_on hint hupp measurableSet_Ioi fun s hs ↦ (hcmp s hs).2.2⟩

end Masullo
