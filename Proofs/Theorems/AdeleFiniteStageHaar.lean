module

public import Lemmas.AdeleFiniteStageMeasure

/-! # Explicit additive Haar on a finite stage of the adeles

Masullo, PDF p. 556, Definition A.3.1.2 and Lemma A.3.1.3, (A.3.1.3), give
local normalizations and a restricted product of measures. The prescription
before the definition supplies the stage shape: All Archimedean places and
all places in `S` have full coordinates, and the remaining coordinates are
integral. Here `S` indexes only the finite places. We prove the Borel stage
input to that prescription, constructing its compact tail by taking the
probability product of the actual local restrictions. We do not identify a
global measure, prove compatibility across stages, or normalize a quotient.
Source reading: Provisional, from the pinned Markdown and numbered PDF layout.
-/

open IsDedekindDomain MeasureTheory NumberField

namespace Masullo

open scoped AdeleStage

variable (K : Type*) [Field K] [NumberField K]

local notation "V" => HeightOneSpectrum (𝓞 K)
local notation "F" v => HeightOneSpectrum.adicCompletion K v
local notation "O" v => HeightOneSpectrum.adicCompletionIntegers K v

/-- The trace measure transported to the infinite adele ring, times the full
local measures in `S` and the integer-ring restrictions off `S`. The latter
factors must have mass one for the probability product. -/
@[expose] public noncomputable def adeleFiniteStageHaar (S : Finset V) :
    Measure (AdeleFiniteStage K S) :=
  ((archimedeanTraceMeasure K).map (archimedeanEuclideanToAdele K)).prod
    ((Measure.pi (fun v : {v // v ∈ S} ↦ finiteCompletionNormalizedHaar v.val)).prod
      (Measure.infinitePi (adeleFiniteStageOutsideFactor K S)))

/-- For any finite stage with unit integer-ring mass at each omitted place,
the displayed product is additive Haar on the actual stage. -/
public theorem adeleFiniteStageHaar_isAddHaarMeasure (S : Finset V)
    (hS : ∀ v ∉ S, finiteCompletionNormalizedHaar v (O v : Set (F v)) = 1) :
    (adeleFiniteStageHaar K S).IsAddHaarMeasure := by
  let := adeleFiniteStageOutside_isProbabilityMeasure K S hS
  let := adeleFiniteStageOutside_isAddHaarMeasure K S hS
  unfold adeleFiniteStageHaar
  apply Measure.prod.instIsAddHaarMeasure

end Masullo
