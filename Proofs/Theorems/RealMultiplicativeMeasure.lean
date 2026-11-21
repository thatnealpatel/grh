module

public import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# The positive part of the real multiplicative measure

Definition A.3.1.2(1), p. 556, gives additive Lebesgue measure at the
real place. Definition A.3.2.2(1), p. 560, restricts it to the field
units and weights it by `|t|⁻¹`. The positive window in (A.2.3.14),
p. 549, selects only the positive component. We express its measure
on the ambient real line, not by folding the two components together.
-/

open MeasureTheory Set

namespace Masullo

/-- The positive restriction of `dt / |t|` on the real field units is the
pushforward of Lebesgue measure by the exponential. Both sides are measures on `ℝ`. -/
public theorem map_volume_exp_eq_restrict_realMultiplicative :
    (volume : Measure ℝ).map Real.exp =
      (((volume : Measure ℝ).restrict ({0}ᶜ)).withDensity
        (fun t ↦ ENNReal.ofReal |t|⁻¹)).restrict (Ioi 0) := by
  have hpos : Ioi (0 : ℝ) ⊆ ({0} : Set ℝ)ᶜ := by
    intro t ht
    simpa only [mem_compl_iff, mem_singleton_iff] using (ne_of_gt (mem_Ioi.mp ht))
  rw [restrict_withDensity measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi,
    inter_eq_left.mpr hpos]
  ext s hs
  rw [Measure.map_apply Real.continuous_exp.measurable hs, withDensity_apply _ hs,
    Measure.restrict_restrict hs]
  have himage : Real.log '' (s ∩ Ioi 0) = Real.exp ⁻¹' s := by
    ext x
    constructor
    · rintro ⟨t, ⟨ht, htpos⟩, rfl⟩
      simpa only [mem_preimage, Real.exp_log htpos] using ht
    · intro hx
      exact ⟨Real.exp x, ⟨hx, Real.exp_pos x⟩, Real.log_exp x⟩
  have hlog := lintegral_image_eq_lintegral_abs_deriv_mul (f := Real.log)
    (f' := fun t : ℝ ↦ t⁻¹) (hs.inter measurableSet_Ioi)
    (fun t ht ↦ (Real.hasDerivAt_log (ne_of_gt ht.2)).hasDerivWithinAt)
    (Real.strictMonoOn_log.injOn.mono inter_subset_right) (fun _ ↦ 1)
  rw [himage, lintegral_const, one_mul,
    Measure.restrict_apply MeasurableSet.univ, univ_inter] at hlog
  simp only [mul_one] at hlog
  rw [hlog]
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem (μ := (volume : Measure ℝ))
    (hs.inter measurableSet_Ioi)] with t ht
  rw [abs_of_pos ht.2, abs_of_pos (inv_pos.mpr ht.2)]

/-- The real factor gives a positive norm strip from `1` to `T` mass `log T`.
In particular the strip from `1` to `e` has mass one. -/
public theorem restrict_realMultiplicative_Icc_one (T : ℝ) (hT : 1 ≤ T) :
    ((((volume : Measure ℝ).restrict ({0}ᶜ)).withDensity
      (fun t ↦ ENNReal.ofReal |t|⁻¹)).restrict (Ioi 0)) (Icc 1 T) =
      ENNReal.ofReal (Real.log T) := by
  have hpreimage : Real.exp ⁻¹' Icc 1 T = Icc 0 (Real.log T) := by
    ext x
    change (1 ≤ Real.exp x ∧ Real.exp x ≤ T) ↔ (0 ≤ x ∧ x ≤ Real.log T)
    conv_lhs => rw [← Real.exp_zero, ← Real.exp_log (zero_lt_one.trans_le hT)]
    simp only [Real.exp_le_exp]
  rw [← map_volume_exp_eq_restrict_realMultiplicative,
    Measure.map_apply Real.continuous_exp.measurable measurableSet_Icc, hpreimage,
    Real.volume_Icc, sub_zero]

end Masullo
