module

public import Lemmas.RationalAdeleFiniteStageMeasure

import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.NumberTheory.Padics.HeightOneSpectrum

/-!
# Rational additive Haar as a restricted product

The stage formula on p. 556 and the global part of (A.3.1.3) over `ℚ`.
The real place is included at every stage. This does not treat the separate
measure on `A_{F,S}` with the `S`-integer lattice.
-/

open IsDedekindDomain NumberField MeasureTheory Set

namespace Masullo

local notation "A" => AdeleRing (𝓞 ℚ) ℚ
local notation "V" => HeightOneSpectrum (𝓞 ℚ)

set_option linter.concreteInstances false

variable [MeasurableSpace A] [BorelSpace A]

/-- On each open finite stage, the restriction of normalized rational additive
Haar in stage coordinates equals the product of the local measures. -/
public theorem comap_rationalAdeleAddHaar_finiteStage (S : Finset V) :
    rationalAdeleAddHaar.comap (rationalAdeleFiniteStageEmbedding S) =
      rationalAdeleFiniteStageHaar S := by
  let μ := rationalAdeleAddHaar.comap (rationalAdeleFiniteStageAddEmbedding S)
  have hj := isOpenEmbedding_rationalAdeleFiniteStageEmbedding S
  have : μ.IsAddHaarMeasure := Measure.IsAddHaarMeasure.comap (mH := inferInstance)
    rationalAdeleAddHaar (f := rationalAdeleFiniteStageAddEmbedding S) hj
  let K := rationalAdeleFiniteStageClosedUnitStrip S
  let : LocallyCompactSpace (RationalAdeleFiniteStage S) := K.locallyCompactSpace_of_addGroup
  have hμ : μ K = 1 := by
    change (rationalAdeleAddHaar.comap (rationalAdeleFiniteStageEmbedding S)) K = 1
    rw [hj.measurableEmbedding.comap_apply, image_rationalAdeleFiniteStageClosedUnitStrip]
    exact rationalAdeleAddHaar_closedUnitStrip
  exact ((Measure.addHaarMeasure_eq_iff K μ).mpr hμ).symm.trans
    ((Measure.addHaarMeasure_eq_iff K _).mpr (rationalAdeleFiniteStageHaar_closedUnitStrip S))

/-- These local product restrictions characterize rational additive Haar among
all Borel measures on the adeles, without assuming invariance in advance. -/
public theorem rationalAdeleAddHaar_eq_iff_finiteStage (μ : Measure A) :
    μ = rationalAdeleAddHaar ↔ ∀ S : Finset V,
      μ.comap (rationalAdeleFiniteStageEmbedding S) = rationalAdeleFiniteStageHaar S := by
  constructor
  · rintro rfl S
    exact comap_rationalAdeleAddHaar_finiteStage S
  · intro h
    let : Countable V := Function.Injective.countable Rat.HeightOneSpectrum.primesEquiv.injective
    apply Measure.ext_of_iUnion_eq_univ iUnion_range_rationalAdeleFiniteStageEmbedding
    intro S
    let j := rationalAdeleFiniteStageEmbedding S
    have hj := (isOpenEmbedding_rationalAdeleFiniteStageEmbedding S).measurableEmbedding
    rw [← hj.map_comap μ, ← hj.map_comap rationalAdeleAddHaar]
    change (μ.comap j).map j = (rationalAdeleAddHaar.comap j).map j
    rw [h S, comap_rationalAdeleAddHaar_finiteStage]

end Masullo
