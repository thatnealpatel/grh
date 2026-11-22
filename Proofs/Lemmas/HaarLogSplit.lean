module

public import Lemmas.LogVolume
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-! Haar measure in a topologically split log coordinate. -/

open MeasureTheory

namespace Masullo

/-- In split coordinates the second Haar factor absorbs all of the scalar
from Haar uniqueness, leaving Lebesgue measure in the log coordinate. -/
public theorem logVolume_prod_of_split_haar {G H : Type*}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [MeasurableSpace H] [BorelSpace H]
    (e : (Multiplicative ℝ × G) ≃ₜ* H) (μ : Measure H) [μ.IsHaarMeasure] :
    ∃ ν : Measure G, ν.IsHaarMeasure ∧ μ.map e.symm = logVolume.prod ν := by
  let η : Measure G := Measure.haar
  let : η.IsHaarMeasure := inferInstanceAs (Measure.haar : Measure G).IsHaarMeasure
  let : (logVolume.prod η).IsHaarMeasure := isHaarMeasure_logVolume_prod η
  let : (μ.map e.symm).IsHaarMeasure := e.symm.isHaarMeasure_map μ
  let c := Measure.haarScalarFactor (μ.map e.symm) (logVolume.prod η)
  have hc : 0 < c := Measure.haarScalarFactor_pos_of_isHaarMeasure _ _
  refine ⟨c • η, Measure.IsHaarMeasure.nnreal_smul η hc.ne', ?_⟩
  rw [Measure.prod_smul_right]
  exact Measure.isMulLeftInvariant_eq_smul _ _

end Masullo
