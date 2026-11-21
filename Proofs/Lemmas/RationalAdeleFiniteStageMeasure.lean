module

public import Lemmas.RationalAdeleFiniteStage
public import Theorems.RationalAdeleIntegralStageHaar
public import Mathlib.MeasureTheory.Constructions.Pi

import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.NumberTheory.Padics.HeightOneSpectrum
import Mathlib.NumberTheory.Padics.ProperSpace

/-! # The product measure in rational additive finite-stage coordinates -/

open NumberField IsDedekindDomain HeightOneSpectrum MeasureTheory Set Topology TopologicalSpace

namespace Masullo

local notation "V" => HeightOneSpectrum (𝓞 ℚ)
local notation "A" => AdeleRing (𝓞 ℚ) ℚ
local notation "F" v => adicCompletion ℚ v
local notation "O" v => adicCompletionIntegers ℚ v

local instance : Countable V :=
  Function.Injective.countable Rat.HeightOneSpectrum.primesEquiv.injective

local instance (v : V) : SecondCountableTopology (F v) :=
  (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v).toHomeomorph.secondCountableTopology

local instance (v : V) : LocallyCompactSpace (F v) :=
  (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v).toHomeomorph.isClosedEmbedding.locallyCompactSpace

local instance (v : V) : SecondCountableTopology (O v) :=
  (Rat.HeightOneSpectrum.adicCompletionIntegers.padicIntEquiv v).toHomeomorph.secondCountableTopology

local instance (v : V) : CompactSpace (O v) :=
  (Rat.HeightOneSpectrum.adicCompletionIntegers.padicIntEquiv v).toHomeomorph.symm.compactSpace

/-- The stage's product measurable structure agrees with its Borel structure. -/
public scoped instance (S : Finset V) : BorelSpace (RationalAdeleFiniteStage S) := by
  change BorelSpace (ℝ × (((v : {v // v ∈ S}) → F v.val) × ((v : {v // v ∉ S}) → O v.val)))
  infer_instance

public scoped instance (S : Finset V) : SecondCountableTopology (RationalAdeleFiniteStage S) := by
  change SecondCountableTopology (ℝ × (((v : {v // v ∈ S}) → F v.val) × ((v : {v // v ∉ S}) → O v.val)))
  infer_instance

/-- The full finite-place Haar measures are sigma-finite. -/
public scoped instance (v : V) : SigmaFinite (rationalLocalFieldAddHaar v) := inferInstance

private noncomputable def outsideHaar (S : Finset V) : Measure ((v : {v // v ∉ S}) → O v.val) :=
  Measure.infinitePi (fun v ↦ rationalLocalIntegersAddHaar v.val)

private instance (S : Finset V) : IsProbabilityMeasure (outsideHaar S) := by
  unfold outsideHaar
  infer_instance

private instance (S : Finset V) : (outsideHaar S).IsAddLeftInvariant where
  map_add_left_eq_self u := by
    change (Measure.infinitePi _).map (fun w v ↦ u v + w v) = Measure.infinitePi _
    rw [Measure.infinitePi_map_pi _ (f := fun v w ↦ u v + w)
      (fun v ↦ (continuous_const_add (u v)).measurable)]
    congr 1
    funext v
    exact map_add_left_eq_self (rationalLocalIntegersAddHaar v.val) (u v)

private instance (S : Finset V) : (outsideHaar S).IsAddHaarMeasure := by
  have h := (Measure.addHaarMeasure_eq_iff
    (⊤ : PositiveCompacts ((v : {v // v ∉ S}) → O v.val)) (outsideHaar S)).mpr
    (by rw [PositiveCompacts.coe_top, measure_univ])
  rw [← h]
  infer_instance

/-- Lebesgue measure times the full local field measures in `S` and the local
integer-ring probabilities outside `S`. -/
@[expose]
public noncomputable def rationalAdeleFiniteStageHaar (S : Finset V) :
    Measure (RationalAdeleFiniteStage S) :=
  volume.prod
    ((Measure.pi (fun v : {v // v ∈ S} ↦ rationalLocalFieldAddHaar v.val)).prod
      (Measure.infinitePi (fun v : {v // v ∉ S} ↦ rationalLocalIntegersAddHaar v.val)))

public instance (S : Finset V) : (rationalAdeleFiniteStageHaar S).IsAddHaarMeasure := by
  unfold rationalAdeleFiniteStageHaar
  change (volume.prod ((Measure.pi _).prod (outsideHaar S))).IsAddHaarMeasure
  apply Measure.prod.instIsAddHaarMeasure

private theorem closedStrip_subset_stage (S : Finset V) :
    (rationalAdeleClosedUnitStrip : Set A) ⊆ range (rationalAdeleFiniteStageEmbedding S) := by
  rw [range_rationalAdeleFiniteStageEmbedding]
  exact fun _ ha v _ ↦ (mem_rationalAdeleClosedUnitStrip.mp ha).1 v

/-- The closed calibration strip in stage coordinates, with all finite coordinates integral. -/
public noncomputable def rationalAdeleFiniteStageClosedUnitStrip (S : Finset V) :
    PositiveCompacts (RationalAdeleFiniteStage S) where
  carrier := rationalAdeleFiniteStageEmbedding S ⁻¹' rationalAdeleClosedUnitStrip
  isCompact' := by
    apply (isOpenEmbedding_rationalAdeleFiniteStageEmbedding S).isCompact_iff.mpr
    rw [image_preimage_eq_of_subset (closedStrip_subset_stage S)]
    exact rationalAdeleClosedUnitStrip.isCompact
  interior_nonempty' := by
    let hj := isOpenEmbedding_rationalAdeleFiniteStageEmbedding S
    rw [← hj.isOpenMap.preimage_interior_eq_interior_preimage hj.continuous]
    obtain ⟨a, ha⟩ := rationalAdeleClosedUnitStrip.interior_nonempty
    obtain ⟨x, rfl⟩ := closedStrip_subset_stage S (interior_subset ha)
    exact ⟨x, ha⟩

/-- The calibration strip is a box in finite-stage coordinates. -/
public theorem rationalAdeleFiniteStageClosedUnitStrip_eq (S : Finset V) :
    (rationalAdeleFiniteStageClosedUnitStrip S : Set (RationalAdeleFiniteStage S)) =
      Icc 0 1 ×ˢ (univ.pi (fun v : {v // v ∈ S} ↦ (O v.val : Set (F v.val))) ×ˢ univ) := by
  ext x
  change rationalAdeleFiniteStageEmbedding S x ∈ (rationalAdeleClosedUnitStrip : Set A) ↔ _
  rw [mem_rationalAdeleClosedUnitStrip, rationalAdeleReal_apply,
    rationalAdeleFiniteStageEmbedding_real S x, and_comm]
  simp only [mem_prod, mem_univ, and_true, mem_pi]
  refine and_congr_right fun _ ↦ ⟨?_, ?_⟩
  · intro hx v _
    exact rationalAdeleFiniteStageEmbedding_finite_mem S x v.val v.property ▸ hx v.val
  · intro hx v
    by_cases hv : v ∈ S
    · rw [rationalAdeleFiniteStageEmbedding_finite_mem S x v hv]
      exact hx ⟨v, hv⟩ trivial
    · rw [rationalAdeleFiniteStageEmbedding_finite_notMem S x v hv]
      exact (x.2.2 ⟨v, hv⟩).property

/-- The product measure gives the closed unit strip mass one. -/
public theorem rationalAdeleFiniteStageHaar_closedUnitStrip (S : Finset V) :
    rationalAdeleFiniteStageHaar S (rationalAdeleFiniteStageClosedUnitStrip S) = 1 := by
  rw [rationalAdeleFiniteStageClosedUnitStrip_eq, rationalAdeleFiniteStageHaar]
  change volume.prod ((Measure.pi _).prod (outsideHaar S)) _ = 1
  rw [Measure.prod_prod, Measure.prod_prod, Measure.pi_pi]
  simp [Real.volume_Icc, rationalLocalFieldAddHaar_integers, measure_univ]

/-- The stage inclusion maps its calibration strip onto the upstairs strip. -/
public theorem image_rationalAdeleFiniteStageClosedUnitStrip (S : Finset V) :
    rationalAdeleFiniteStageEmbedding S '' (rationalAdeleFiniteStageClosedUnitStrip S :
      Set (RationalAdeleFiniteStage S)) = rationalAdeleClosedUnitStrip :=
  image_preimage_eq_of_subset (closedStrip_subset_stage S)

end Masullo
