module

public import Lemmas.RationalIdeleFiniteStageMeasure
public import Theorems.RationalIdeleHaarComparison
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.NumberTheory.Padics.HeightOneSpectrum

/-!
# Rational idele Haar as a restricted product

The stage restrictions from p. 556 determine the normalized Haar measure in
(A.3.2.5), p. 560. The positive finite-unit strip fixes the scale on each
whole signed stage.
-/

open IsDedekindDomain NumberField MeasureTheory Set

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

/-- The finite-stage product formulas characterize normalized rational idele
Haar among all Borel measures, not just among Haar measures. -/
public theorem rationalIdeleHaar_eq_iff_finiteStage (μ : Measure Ideles) :
    μ = rationalIdeleHaar ↔ ∀ S : Finset (HeightOneSpectrum (𝓞 ℚ)),
      μ.comap (rationalIdeleFiniteStageEmbedding S) = rationalIdeleFiniteStageHaar S := by
  constructor
  · rintro rfl S
    exact comap_rationalIdeleHaar_finiteStage S
  · intro h
    let : Countable (HeightOneSpectrum (𝓞 ℚ)) :=
      Function.Injective.countable Rat.HeightOneSpectrum.primesEquiv.injective
    apply Measure.ext_of_iUnion_eq_univ iUnion_range_rationalIdeleFiniteStageEmbedding
    intro S
    let j := rationalIdeleFiniteStageEmbedding S
    have hj := (isOpenEmbedding_rationalIdeleFiniteStageEmbedding S).measurableEmbedding
    rw [← hj.map_comap μ, ← hj.map_comap rationalIdeleHaar]
    change (μ.comap j).map j = (rationalIdeleHaar.comap j).map j
    rw [h S, comap_rationalIdeleHaar_finiteStage]

end Masullo
