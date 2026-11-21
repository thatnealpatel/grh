module

public import Mathlib.MeasureTheory.Measure.Haar.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-! Lebesgue measure in multiplicatively tagged log coordinates. -/

open MeasureTheory

namespace Masullo

/-- Lebesgue measure on the real log line, with its group law written multiplicatively. -/
public noncomputable def logVolume : Measure (Multiplicative ℝ) :=
  Measure.map Multiplicative.ofAdd volume

@[simp] public theorem map_toAdd_logVolume :
    logVolume.map (Multiplicative.toAdd : Multiplicative ℝ → ℝ) = volume := by
  rw [logVolume, Measure.map_map measurable_toAdd measurable_ofAdd]
  exact Measure.map_id

private theorem logVolume_eq : logVolume = (volume : Measure ℝ) := by
  ext s hs
  exact Measure.map_apply measurable_ofAdd hs

private theorem isHaarMeasure_logVolume : logVolume.IsHaarMeasure := by
  rw [logVolume_eq]
  have h : (volume : Measure ℝ).IsAddHaarMeasure := inferInstance
  exact { toIsFiniteMeasureOnCompacts := h.toIsFiniteMeasureOnCompacts
          toIsOpenPosMeasure := h.toIsOpenPosMeasure
          map_mul_left_eq_self := fun x ↦ h.map_add_left_eq_self x.toAdd }

/-- The product is Haar using only measurability of fixed translations on `K`.
This avoids needing joint measurability of multiplication on the norm-one group. -/
public theorem isHaarMeasure_logVolume_prod {K : Type*} [Group K] [TopologicalSpace K]
    [MeasurableSpace K] [BorelSpace K] [ContinuousMul K] (μ : Measure K)
    [μ.IsHaarMeasure] [IsFiniteMeasure μ] : (logVolume.prod μ).IsHaarMeasure := by
  let := isHaarMeasure_logVolume
  refine { map_mul_left_eq_self := ?_ }
  rintro ⟨x, k⟩
  change Measure.map (Prod.map (x * ·) (k * ·)) _ = _
  rw [← Measure.map_prod_map _ _ (measurable_const_mul x) (measurable_const_mul k),
    MeasureTheory.map_mul_left_eq_self, MeasureTheory.map_mul_left_eq_self]

end Masullo
