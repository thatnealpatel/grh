module

public import Lemmas.RationalIdeleWindowMeasure
public import Theorems.RationalIdeleFiniteStage
public import Theorems.RationalLocalMultiplicativeHaar
public import Theorems.RealMultiplicativeHaar
public import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.NumberTheory.Padics.HeightOneSpectrum
import Mathlib.NumberTheory.Padics.ProperSpace

/-!
# Haar measure in rational finite-stage coordinates

The product on each stage is the one in the restricted-product prescription
on p. 556, applied to the multiplicative factors in (A.3.2.5), p. 560.
The same positive finite-unit strip calibrates both measures, but the
comparison is on the whole stage, including the negative real component.
-/

open NumberField IsDedekindDomain HeightOneSpectrum MeasureTheory Set Topology TopologicalSpace

namespace Masullo

local notation "V" => HeightOneSpectrum (𝓞 ℚ)
local notation "Ideles" => IdeleGroup (𝓞 ℚ) ℚ
local notation "F" v => adicCompletion ℚ v
local notation "G" v => (F v)ˣ
local notation "O" v => adicCompletionIntegers ℚ v
local notation "U" v => (O v)ˣ

/-- The full finite-place multiplicative groups carry their Borel sigma-algebras. -/
public noncomputable scoped instance rationalLocalFieldUnitsMeasurableSpace (v : V) :
    MeasurableSpace (G v) := borel _

public scoped instance rationalLocalFieldUnitsBorelSpace (v : V) : BorelSpace (G v) := ⟨rfl⟩

local instance : Countable V :=
  Function.Injective.countable Rat.HeightOneSpectrum.primesEquiv.injective

private theorem secondCountable_units (R : Type*) [Monoid R] [TopologicalSpace R]
    [SecondCountableTopology R] : SecondCountableTopology Rˣ := by
  let : SecondCountableTopology Rᵐᵒᵖ := MulOpposite.opHomeomorph.symm.secondCountableTopology
  exact Units.isInducing_embedProduct.secondCountableTopology

local instance : SecondCountableTopology ℝˣ := secondCountable_units _

local instance (v : V) : SecondCountableTopology (G v) := by
  let : SecondCountableTopology (F v) :=
    (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v).toHomeomorph.secondCountableTopology
  exact secondCountable_units _

local instance (v : V) : SecondCountableTopology (U v) := by
  let : SecondCountableTopology (O v) :=
    (Rat.HeightOneSpectrum.adicCompletionIntegers.padicIntEquiv v).toHomeomorph.secondCountableTopology
  exact secondCountable_units _

local instance (v : V) : LocallyCompactSpace (G v) := by
  let : LocallyCompactSpace (F v) :=
    (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v).toHomeomorph.isClosedEmbedding.locallyCompactSpace
  infer_instance

local instance (v : V) : CompactSpace (U v) := compactSpace_rationalLocalUnits v
local instance : T2Space Ideles := t2Space_rationalIdeleGroup

private noncomputable def outsideHaar (S : Finset V) : Measure ((v : {v // v ∉ S}) → U v.val) :=
  Measure.infinitePi (fun v ↦ rationalLocalUnitHaar v.val)

private instance (S : Finset V) : IsProbabilityMeasure (outsideHaar S) := by
  unfold outsideHaar
  infer_instance

private instance (S : Finset V) : (outsideHaar S).IsMulLeftInvariant where
  map_mul_left_eq_self u := by
    change (Measure.infinitePi _).map (fun w v ↦ u v * w v) = Measure.infinitePi _
    rw [Measure.infinitePi_map_pi _ (f := fun v w ↦ u v * w)
      (fun v ↦ (continuous_const_mul (u v)).measurable)]
    congr 1
    funext v
    exact map_mul_left_eq_self (rationalLocalUnitHaar v.val) (u v)

private instance (S : Finset V) : (outsideHaar S).IsHaarMeasure := by
  have h := (Measure.haarMeasure_eq_iff
    (⊤ : PositiveCompacts ((v : {v // v ∉ S}) → U v.val)) (outsideHaar S)).mpr
    (by rw [PositiveCompacts.coe_top, measure_univ])
  rw [← h]
  infer_instance

/-- The full real local measure times the local field-unit Haar measures in `S`
and the local integral-unit Haar probabilities outside `S`. -/
@[expose] public noncomputable def rationalIdeleFiniteStageHaar (S : Finset V) :
    Measure (RationalIdeleFiniteStage S) :=
  realMultiplicativeHaar.prod
    ((Measure.pi (fun v : {v // v ∈ S} ↦ rationalLocalMultiplicativeHaar v.val)).prod
      (Measure.infinitePi (fun v : {v // v ∉ S} ↦ rationalLocalUnitHaar v.val)))

public instance (S : Finset V) : (rationalIdeleFiniteStageHaar S).IsHaarMeasure := by
  unfold rationalIdeleFiniteStageHaar
  change (realMultiplicativeHaar.prod ((Measure.pi _).prod (outsideHaar S))).IsHaarMeasure
  apply Measure.prod.instIsHaarMeasure

private theorem mem_localUnitRange_iff {v : V} (x : G v) :
    x ∈ range (rationalLocalUnitInclusion v) ↔ (x : F v) ∈ (O v) ∧ (↑(x⁻¹) : F v) ∈ (O v) := by
  constructor
  · rintro ⟨u, rfl⟩
    exact ⟨u.val.property, u.inv.property⟩
  · intro hx
    let T := (O v).toSubring.toSubmonoid
    exact ⟨T.unitsEquivUnitsType ⟨x, hx⟩, Units.ext rfl⟩

private theorem strip_subset_stage (S : Finset V) :
    (rationalIdeleWindowUnitStrip : Set Ideles) ⊆ range (rationalIdeleFiniteStageEmbedding S) := by
  rw [range_rationalIdeleFiniteStageEmbedding]
  intro x hx v _
  exact ⟨hx.1.2.1 v, hx.1.2.2 v⟩

/-- The positive finite-unit calibration strip in the coordinates of stage `S`. -/
public noncomputable def rationalIdeleFiniteStageUnitStrip (S : Finset V) :
    PositiveCompacts (RationalIdeleFiniteStage S) where
  carrier := rationalIdeleFiniteStageEmbedding S ⁻¹' (rationalIdeleWindowUnitStrip : Set Ideles)
  isCompact' := by
    apply (isOpenEmbedding_rationalIdeleFiniteStageEmbedding S).isCompact_iff.mpr
    rw [image_preimage_eq_of_subset (strip_subset_stage S)]
    exact rationalIdeleWindowUnitStrip.isCompact
  interior_nonempty' := by
    let hj := isOpenEmbedding_rationalIdeleFiniteStageEmbedding S
    rw [← hj.isOpenMap.preimage_interior_eq_interior_preimage hj.continuous]
    obtain ⟨a, ha⟩ := rationalIdeleWindowUnitStrip.interior_nonempty
    obtain ⟨x, rfl⟩ := strip_subset_stage S (interior_subset ha)
    exact ⟨x, ha⟩

private theorem stageStrip_eq (S : Finset V) :
    (rationalIdeleFiniteStageUnitStrip S : Set (RationalIdeleFiniteStage S)) =
      (Units.val ⁻¹' Icc 1 (Real.exp 1)) ×ˢ
        (univ.pi (fun v : {v // v ∈ S} ↦ range (rationalLocalUnitInclusion v.val)) ×ˢ univ) := by
  ext x
  let j := rationalIdeleFiniteStageEmbedding S
  have hr : rationalIdeleReal (j x) = (x.1 : ℝ) := rationalIdeleReal_finiteStageEmbedding S x
  have hfin (hw : j x ∈ rationalIdeleUnitWindow) : ideleNorm (j x) = (x.1 : ℝ) := by
    rw [ideleNorm_eq_abs_rationalIdeleReal _ (finiteValuation_eq_one_of_mem_rationalIdeleUnitWindow hw),
      abs_of_pos hw.1, hr]
  change j x ∈ rationalIdeleUnitWindow ∩ {a | ideleNorm a ∈ Icc 1 (Real.exp 1)} ↔ _
  simp only [mem_inter_iff, mem_ofPred_eq, mem_prod, mem_preimage, mem_univ, and_true, mem_pi]
  constructor
  · rintro ⟨hw, hn⟩
    rw [hfin hw] at hn
    refine ⟨hn, fun v _ ↦ (mem_localUnitRange_iff _).mpr ⟨?_, ?_⟩⟩
    · rw [← rationalIdeleFiniteStageEmbedding_finite_mem S x v.val v.property]
      exact hw.2.1 v.val
    · change (↑(x⁻¹.2.1 v) : F v.val) ∈ (O v.val)
      rw [← rationalIdeleFiniteStageEmbedding_finite_mem S x⁻¹ v.val v.property, map_inv]
      exact hw.2.2 v.val
  · rintro ⟨hrange, hlocal⟩
    have hw : j x ∈ rationalIdeleUnitWindow := by
      have hpositive : 0 < rationalIdeleReal (j x) := hr ▸ (zero_lt_one.trans_le hrange.1)
      have hcoord (v : V) : (j x : AdeleRing (𝓞 ℚ) ℚ).2 v ∈ (O v) ∧
          (↑((j x)⁻¹) : AdeleRing (𝓞 ℚ) ℚ).2 v ∈ (O v) := by
        by_cases hv : v ∈ S
        · rw [← map_inv j, rationalIdeleFiniteStageEmbedding_finite_mem S x v hv,
            rationalIdeleFiniteStageEmbedding_finite_mem S x⁻¹ v hv]
          exact (mem_localUnitRange_iff _).mp (hlocal ⟨v, hv⟩ trivial)
        · exact (range_rationalIdeleFiniteStageEmbedding S ▸ mem_range_self x) v hv
      exact ⟨hpositive, fun v ↦ (hcoord v).1, fun v ↦ (hcoord v).2⟩
    exact ⟨hw, (hfin hw).symm ▸ hrange⟩

/-- All three local product factors give their part of the calibration strip mass one. -/
public theorem rationalIdeleFiniteStageHaar_unitStrip (S : Finset V) :
    rationalIdeleFiniteStageHaar S (rationalIdeleFiniteStageUnitStrip S) = 1 := by
  rw [stageStrip_eq, rationalIdeleFiniteStageHaar]
  change realMultiplicativeHaar.prod ((Measure.pi _).prod (outsideHaar S)) _ = 1
  rw [Measure.prod_prod, Measure.prod_prod, Measure.pi_pi]
  simp only [realMultiplicativeHaar_unitStrip, rationalLocalMultiplicativeHaar_unitMass,
    Finset.prod_const_one, measure_univ, mul_one]

/-- Inserting the stage coordinates maps its calibration strip onto the upstairs strip. -/
public theorem image_rationalIdeleFiniteStageUnitStrip (S : Finset V) :
    rationalIdeleFiniteStageEmbedding S '' (rationalIdeleFiniteStageUnitStrip S :
      Set (RationalIdeleFiniteStage S)) = rationalIdeleWindowUnitStrip :=
  image_preimage_eq_of_subset (strip_subset_stage S)

/-- With the product sigma-algebra, the stage has its Borel measurable structure. -/
public scoped instance (S : Finset V) : BorelSpace (RationalIdeleFiniteStage S) := by
  change BorelSpace (ℝˣ × (((v : {v // v ∈ S}) → G v.val) × ((v : {v // v ∉ S}) → U v.val)))
  infer_instance

public scoped instance (S : Finset V) : SecondCountableTopology (RationalIdeleFiniteStage S) := by
  change SecondCountableTopology
    (ℝˣ × (((v : {v // v ∈ S}) → G v.val) × ((v : {v // v ∉ S}) → U v.val)))
  infer_instance

end Masullo
