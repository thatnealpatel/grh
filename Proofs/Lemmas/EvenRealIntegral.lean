module

public import Mathlib.MeasureTheory.Measure.Lebesgue.Integral

/-! # Reflection across the origin for real-line integrals -/

open MeasureTheory Set

namespace Masullo

/-- Reflect an even complex-valued density to the positive real half-line. -/
public theorem even_real_integral {f : ℝ → ℂ} (he : Function.Even f)
    (hf : IntegrableOn f (Ioi 0)) : Integrable f ∧
      (∫ x, f x) = (2 : ℂ) * ∫ x in Ioi (0 : ℝ), f x := by
  have hm : MeasurableEmbedding (fun x : ℝ ↦ -x) := (Homeomorph.neg ℝ).measurableEmbedding
  have hEven (x : ℝ) : f (-x) = f x := he x
  have hn : IntegrableOn f (Iic (0 : ℝ)) := by
    rw [← Measure.map_neg_eq_self (volume : Measure ℝ), hm.integrableOn_map_iff]
    simpa only [Function.comp_def, hEven, neg_preimage, neg_Iic, neg_zero] using
      ((integrableOn_Ici_iff_integrableOn_Ioi (f := f) (b := (0 : ℝ))).mpr hf)
  have hfull : Integrable f := by
    simpa [← compl_Ioi] using hf.union hn
  have hReflect : (∫ x in Iic (0 : ℝ), f x) = ∫ x in Ioi (0 : ℝ), f x := by
    simpa only [neg_zero, hEven] using (integral_comp_neg_Ioi 0 f).symm
  refine ⟨hfull, ?_⟩
  rw [← integral_add_compl (s := Ioi (0 : ℝ)) measurableSet_Ioi hfull,
    compl_Ioi, hReflect, two_mul]

end Masullo
