module

public import Lemmas.RationalIdeleFiniteStageMeasure
public import Theorems.RationalIdeleHaarComparison
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# The rational finite-stage product formula for Haar measure

This is the stage restriction in the restricted product (A.3.2.5), p. 560,
in the sense of the prescription on p. 556. The positive finite-unit strip
fixes the scale on the whole signed stage.
-/

open IsDedekindDomain NumberField MeasureTheory

namespace Masullo

local notation "Ideles" => IdeleGroup (𝓞 ℚ) ℚ

local instance : T2Space Ideles := t2Space_rationalIdeleGroup

set_option linter.concreteInstances false

variable [MeasurableSpace Ideles] [BorelSpace Ideles]

/-- The restriction of normalized rational idele Haar to any open finite stage,
expressed in stage coordinates, is exactly the product of the normalized local
measures. This includes the empty finite set and retains all real units. -/
public theorem comap_rationalIdeleHaar_finiteStage (S : Finset (HeightOneSpectrum (𝓞 ℚ))) :
    rationalIdeleHaar.comap (rationalIdeleFiniteStageEmbedding S) = rationalIdeleFiniteStageHaar S := by
  let j := rationalIdeleFiniteStageEmbedding S
  have hj := isOpenEmbedding_rationalIdeleFiniteStageEmbedding S
  let μ := rationalIdeleHaar.comap j
  have : μ.IsHaarMeasure := Measure.IsHaarMeasure.comap (mH := inferInstance) rationalIdeleHaar hj
  let K := rationalIdeleFiniteStageUnitStrip S
  let : LocallyCompactSpace (RationalIdeleFiniteStage S) := K.locallyCompactSpace_of_group
  have hμ : μ K = 1 := by
    rw [hj.measurableEmbedding.comap_apply, image_rationalIdeleFiniteStageUnitStrip]
    exact rationalIdeleHaar_unitStrip
  exact ((Measure.haarMeasure_eq_iff K μ).mpr hμ).symm.trans
    ((Measure.haarMeasure_eq_iff K _).mpr (rationalIdeleFiniteStageHaar_unitStrip S))

end Masullo
