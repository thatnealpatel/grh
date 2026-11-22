module

public import Theorems.AdeleFiniteStageHaar

import Lemmas.FiniteCompletionCompact

/-! # The common integral-finite rectangle for additive Haar comparison -/

open IsDedekindDomain MeasureTheory NumberField Set Topology TopologicalSpace
open scoped ENNReal RestrictedProduct

namespace Masullo

noncomputable section

variable (K : Type*) [Field K] [NumberField K]

local notation "V" => HeightOneSpectrum (𝓞 K)
local notation "F" v => HeightOneSpectrum.adicCompletion K v
local notation "O" v => HeightOneSpectrum.adicCompletionIntegers K v
local notation "A∞" => InfiniteAdeleRing K
local notation "A" => AdeleRing (𝓞 K) K

open scoped AdeleStage

namespace AdeleStage

public scoped instance : MeasurableSpace A := borel _

public scoped instance : BorelSpace A := ⟨rfl⟩

public scoped instance : T2Space A := by
  let : T2Space (FiniteAdeleRing (𝓞 K) K) :=
    show T2Space (Πʳ v : V, [F v, O v]) from inferInstance
  let : T2Space A∞ := (archimedeanEuclideanToAdele K).symm.toHomeomorph.isEmbedding.t2Space
  change T2Space (A∞ × FiniteAdeleRing (𝓞 K) K)
  infer_instance

end AdeleStage

local instance (v : V) : CompactSpace (O v) := compactSpace_finiteCompletionIntegers K v

/-- The normalized additive mass of the integer ring at a finite place. -/
@[expose] public def finiteCompletionIntegerMass (v : V) : ℝ≥0∞ :=
  finiteCompletionNormalizedHaar v (O v : Set (F v))

/-- The adele set with Archimedean component in `B` and integral at every finite place. -/
@[expose] public def adeleIntegerRectangle (B : Set A∞) : Set A :=
  {a | a.1 ∈ B ∧ ∀ v : V, a.2 v ∈ O v}

/-- The same rectangle in the product coordinates of the stage `S`. -/
@[expose] public def adeleStageIntegerRectangle (B : Set A∞) (S : Finset V) :
    Set (AdeleFiniteStage K S) :=
  B ×ˢ (univ.pi (fun v : {v // v ∈ S} ↦ (O v.val : Set (F v.val))) ×ˢ univ)

private theorem preimage_adeleIntegerRectangle (B : Set A∞) (S : Finset V) :
    adeleFiniteStageEmbedding K S ⁻¹' adeleIntegerRectangle K B =
      adeleStageIntegerRectangle K B S := by
  ext x
  change ((adeleFiniteStageEmbedding K S x).1 ∈ B ∧
    ∀ v : V, (adeleFiniteStageEmbedding K S x).2 v ∈ O v) ↔ x ∈ adeleStageIntegerRectangle K B S
  rw [adeleFiniteStageEmbedding_infinite]
  simp only [adeleStageIntegerRectangle, mem_prod, mem_univ, and_true, mem_pi]
  refine and_congr_right fun _ ↦ ⟨fun h v _ ↦ ?_, fun h v ↦ ?_⟩
  · rw [← adeleFiniteStageEmbedding_finite_mem K S x v.val v.property]
    exact h v.val
  · classical
    by_cases hv : v ∈ S
    · rw [adeleFiniteStageEmbedding_finite_mem K S x v hv]
      exact h ⟨v, hv⟩ trivial
    · rw [adeleFiniteStageEmbedding_finite_notMem K S x v hv]
      exact (x.2.2 ⟨v, hv⟩).property

/-- The same upstairs rectangle is obtained from every stage. -/
public theorem image_adeleStageIntegerRectangle (B : Set A∞) (S : Finset V) :
    adeleFiniteStageEmbedding K S '' adeleStageIntegerRectangle K B S =
      adeleIntegerRectangle K B := by
  rw [← preimage_adeleIntegerRectangle]
  apply image_preimage_eq_of_subset
  intro a ha
  rw [range_adeleFiniteStageEmbedding]
  exact fun v _ ↦ ha.2 v

/-- An open stage is also a measurable embedding for the specified Borel structures. -/
public theorem measurableEmbedding_adeleFiniteStageEmbedding (S : Finset V) :
    MeasurableEmbedding (adeleFiniteStageEmbedding K S) :=
  (isOpenEmbedding_adeleFiniteStageEmbedding K S).measurableEmbedding

/-- Integral-finite rectangles with measurable infinite component are Borel. -/
public theorem measurableSet_adeleIntegerRectangle {B : Set A∞} (hB : MeasurableSet B) :
    MeasurableSet (adeleIntegerRectangle K B) := by
  rw [← image_adeleStageIntegerRectangle K B ∅]
  exact (measurableEmbedding_adeleFiniteStageEmbedding K ∅).measurableSet_image.mpr
    (hB.prod ((MeasurableSet.pi countable_univ fun v _ ↦
      (Valued.isOpen_valuationSubring (F v.val)).measurableSet).prod MeasurableSet.univ))

/-- A compact positive rectangle in stage coordinates. -/
public def adeleStageIntegerBox (B : PositiveCompacts A∞) (S : Finset V) :
    PositiveCompacts (AdeleFiniteStage K S) where
  carrier := adeleStageIntegerRectangle K B S
  isCompact' := B.isCompact.prod ((isCompact_univ_pi fun v ↦
    isCompact_iff_compactSpace.mpr (compactSpace_finiteCompletionIntegers K v.val)).prod
    isCompact_univ)
  interior_nonempty' := by
    have hO (v : V) : IsOpen (O v : Set (F v)) := Valued.isOpen_valuationSubring _
    have h := isOpen_set_pi finite_univ (fun (v : {v // v ∈ S}) _ ↦ hO v.val)
    rw [adeleStageIntegerRectangle, interior_prod_eq, interior_prod_eq, h.interior_eq, interior_univ]
    exact B.interior_nonempty.prod (Set.Nonempty.prod ⟨0, fun _ _ ↦ zero_mem _⟩ univ_nonempty)

public theorem coe_adeleStageIntegerBox (B : PositiveCompacts A∞) (S : Finset V) :
    (adeleStageIntegerBox K B S : Set (AdeleFiniteStage K S)) =
      adeleStageIntegerRectangle K B S := by
  rfl

/-- A compact positive rectangle in the actual adele ring. -/
public def adeleCalibrationBox (B : PositiveCompacts A∞) : PositiveCompacts A :=
  let j := isOpenEmbedding_adeleFiniteStageEmbedding K ∅
  (adeleStageIntegerBox K B ∅).map _ j.continuous j.isOpenMap

/-- The calibration box is the image of the positive rectangle in any stage. -/
public theorem image_adeleStageIntegerBox (B : PositiveCompacts A∞) (S : Finset V) :
    adeleFiniteStageEmbedding K S '' (adeleStageIntegerBox K B S : Set (AdeleFiniteStage K S)) =
      adeleCalibrationBox K B :=
  (image_adeleStageIntegerRectangle K B S).trans (image_adeleStageIntegerRectangle K B ∅).symm

/-- The stage rectangle mass keeps the integer-ring masses of the active places. -/
public theorem adeleFiniteStageHaar_integerRectangle (B : Set A∞) (S : Finset V)
    (hS : ∀ v ∉ S, finiteCompletionIntegerMass K v = 1) :
    adeleFiniteStageHaar K S (adeleStageIntegerRectangle K B S) =
      ((archimedeanTraceMeasure K).map (archimedeanEuclideanToAdele K)) B *
        ∏ v ∈ S, finiteCompletionIntegerMass K v := by
  let := adeleFiniteStageOutside_isProbabilityMeasure K S hS
  rw [adeleFiniteStageHaar, adeleStageIntegerRectangle, Measure.prod_prod, Measure.prod_prod,
    Measure.pi_pi, measure_univ, mul_one]
  exact congrArg (_ * ·) (Finset.prod_attach S (finiteCompletionIntegerMass K))

end

end Masullo
