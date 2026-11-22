module

public import Lemmas.AdeleFiniteStage
public import Lemmas.FiniteCompletionNormalizedHaar
public import Theorems.ArchimedeanIdealDual
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.Probability.ProductMeasure

import Lemmas.IdeleFiniteStageMeasure
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-! # Haar factors in additive finite-stage coordinates

The factors are those in Masullo, PDF p. 556, Definition A.3.1.2 and the
restricted-product prescription immediately preceding it. The finite-place
scale is already proved in `finiteCompletionNormalizedHaar_real`, with the
different/discriminant comparison in `finiteCompletion_norm_discr_eq_inv_residueNorm_pow`.
Here the integer factor is the actual Borel comap, not a newly chosen Haar
measure with an unspecified constant. Source reading: Provisional, from the
pinned Markdown and numbered PDF layout.
-/

open IsDedekindDomain MeasureTheory NumberField Set Topology TopologicalSpace
open scoped Classical InnerProductSpace

namespace Masullo

noncomputable section

variable (K : Type*) [Field K] [NumberField K]

local notation "V" => HeightOneSpectrum (𝓞 K)
local notation "F" v => HeightOneSpectrum.adicCompletion K v
local notation "O" v => HeightOneSpectrum.adicCompletionIntegers K v
local notation "A∞" => InfiniteAdeleRing K
local notation "Eucl" => mixedEmbedding.euclidean.mixedSpace K

namespace AdeleStage

/-- The Borel σ-algebra of the actual finite completion. -/
public scoped instance (v : V) :
    MeasurableSpace (F v) := borel _

public scoped instance (v : V) : BorelSpace (F v) := ⟨rfl⟩

/-- The Borel σ-algebra of the actual completion integers. -/
public scoped instance (v : V) :
    MeasurableSpace (O v) := borel _

public scoped instance (v : V) : BorelSpace (O v) := ⟨rfl⟩

/-- The Borel σ-algebra of the infinite adele ring. -/
public scoped instance : MeasurableSpace A∞ := borel _

public scoped instance : BorelSpace A∞ := ⟨rfl⟩

end AdeleStage

open scoped AdeleStage

namespace AdeleStage

public scoped instance : Countable V := countable_ideleFinitePlaces K

public scoped instance (v : V) : SecondCountableTopology (F v) := by
  let : Countable K := Countable.of_moduleFinite (R := ℚ)
  let : SeparableSpace (F v) :=
    ⟨range (algebraMap K (F v)), countable_range _, v.denseRange_algebraMap K⟩
  infer_instance

public scoped instance (v : V) : SecondCountableTopology (O v) :=
  IsEmbedding.subtypeVal.secondCountableTopology

end AdeleStage

local instance (v : V) : CompactSpace (O v) := compactSpace_finiteCompletionIntegers K v

local instance (v : V) : LocallyCompactSpace (F v) := by
  have hO : IsOpen (O v : Set (F v)) := Valued.isOpen_valuationSubring _
  exact ({ carrier := (O v : Set (F v))
           isCompact' := isCompact_iff_compactSpace.mpr (compactSpace_finiteCompletionIntegers K v)
           interior_nonempty' := hO.interior_eq.symm ▸ ⟨0, zero_mem _⟩ } :
    PositiveCompacts (F v)).locallyCompactSpace_of_addGroup

private def infiniteAdeleMixedEquiv : A∞ ≃ₜ+ mixedEmbedding.mixedSpace K := by
  let e : A∞ ≃ₜ mixedEmbedding.mixedSpace K :=
    (Homeomorph.piEquivPiSubtypeProd (fun (v : InfinitePlace K) => v.IsReal)
      (fun v => v.Completion)).trans
      ((Homeomorph.piCongrRight (fun ⟨_, h⟩ =>
          (InfinitePlace.Completion.isometryEquivRealOfIsReal h).toHomeomorph)).prodCongr
        ((Homeomorph.piCongrRight (fun ⟨_, h⟩ =>
          (InfinitePlace.Completion.isometryEquivComplexOfIsComplex
            (InfinitePlace.not_isReal_iff_isComplex.mp h)).toHomeomorph)).trans
          (Homeomorph.piCongrLeft (Y := fun _ : {v : InfinitePlace K // v.IsComplex} => ℂ)
            (Equiv.subtypeEquivRight (fun _ => InfinitePlace.not_isReal_iff_isComplex)))))
  exact { e with map_add' := (InfiniteAdeleRing.ringEquiv_mixedSpace K).map_add }

/-- Euclidean mixed coordinates, carried to the actual infinite completions. -/
public def archimedeanEuclideanToAdele : Eucl ≃ₜ+ A∞ :=
  (mixedEmbedding.euclidean.toMixed K).toContinuousAddEquiv.trans
    (infiniteAdeleMixedEquiv K).symm

namespace AdeleStage

public scoped instance : SecondCountableTopology A∞ :=
  (archimedeanEuclideanToAdele K).symm.toHomeomorph.secondCountableTopology

public scoped instance (S : Finset V) : SecondCountableTopology (AdeleFiniteStage K S) := by
  change SecondCountableTopology
    (A∞ × (((v : {v // v ∈ S}) → F v.val) × ((v : {v // v ∉ S}) → O v.val)))
  infer_instance

/-- The product σ-algebra used for Haar on a stage is its Borel σ-algebra. -/
public scoped instance (S : Finset V) : BorelSpace (AdeleFiniteStage K S) := by
  change BorelSpace
    (A∞ × (((v : {v // v ∈ S}) → F v.val) × ((v : {v // v ∉ S}) → O v.val)))
  infer_instance

public scoped instance (v : V) : SigmaFinite (finiteCompletionNormalizedHaar v) := inferInstance

end AdeleStage

public instance : ((archimedeanTraceMeasure K).map (archimedeanEuclideanToAdele K)).IsAddHaarMeasure := by
  let : (archimedeanTraceMeasure K).IsAddHaarMeasure :=
    Measure.IsAddHaarMeasure.smul volume (by simp) (by finiteness)
  exact ContinuousAddEquiv.isAddHaarMeasure_map _ _

private abbrev integerInclusion (v : V) : (O v) →+ (F v) :=
  (ValuationSubring.subtype (O v)).toAddMonoidHom

private theorem isOpenEmbedding_integerInclusion (v : V) :
    IsOpenEmbedding (integerInclusion K v) := by
  refine ⟨IsEmbedding.subtypeVal, ?_⟩
  rw [show range (integerInclusion K v) = (O v : Set (F v)) from Subtype.range_coe]
  exact Valued.isOpen_valuationSubring _

/-- The restriction of calibrated local Haar to the integer ring is still additive Haar. -/
public theorem finiteCompletionNormalizedHaar_comap_isAddHaarMeasure (v : V) :
    ((finiteCompletionNormalizedHaar v).comap (fun x : O v ↦ (x : F v))).IsAddHaarMeasure :=
  Measure.IsAddHaarMeasure.comap (mH := inferInstance) _ (isOpenEmbedding_integerInclusion K v)

/-- If the integer ring has mass one, the comap is a probability measure. -/
public theorem finiteCompletionNormalizedHaar_comap_isProbabilityMeasure (v : V)
    (hv : finiteCompletionNormalizedHaar v (O v : Set (F v)) = 1) :
    IsProbabilityMeasure ((finiteCompletionNormalizedHaar v).comap (fun x : O v ↦ (x : F v))) := by
  constructor
  change (finiteCompletionNormalizedHaar v).comap (integerInclusion K v) univ = 1
  rwa [(isOpenEmbedding_integerInclusion K v).measurableEmbedding.comap_apply, image_univ,
    show range (integerInclusion K v) = (O v : Set (F v)) from Subtype.range_coe]

/-- The local measures in the compact tail, before taking their probability product. -/
@[expose] public def adeleFiniteStageOutsideFactor (S : Finset V) (v : {v // v ∉ S}) :
    Measure (O v.val) :=
  (finiteCompletionNormalizedHaar v.val).comap (fun x : O v.val ↦ (x : F v.val))

/-- The product of all omitted integer factors has mass one under the local mass hypothesis. -/
public theorem adeleFiniteStageOutside_isProbabilityMeasure (S : Finset V)
    (hS : ∀ v ∉ S, finiteCompletionNormalizedHaar v (O v : Set (F v)) = 1) :
    IsProbabilityMeasure (Measure.infinitePi (adeleFiniteStageOutsideFactor K S)) := by
  let (v : {v // v ∉ S}) : IsProbabilityMeasure (adeleFiniteStageOutsideFactor K S v) :=
    finiteCompletionNormalizedHaar_comap_isProbabilityMeasure K v.val (hS v.val v.property)
  infer_instance

/-- The omitted probability product is additive Haar on the compact product of integer rings. -/
public theorem adeleFiniteStageOutside_isAddHaarMeasure (S : Finset V)
    (hS : ∀ v ∉ S, finiteCompletionNormalizedHaar v (O v : Set (F v)) = 1) :
    (Measure.infinitePi (adeleFiniteStageOutsideFactor K S)).IsAddHaarMeasure := by
  let μv := adeleFiniteStageOutsideFactor K S
  let (v : {v // v ∉ S}) : IsProbabilityMeasure (μv v) :=
    finiteCompletionNormalizedHaar_comap_isProbabilityMeasure K v.val (hS v.val v.property)
  let (v : {v // v ∉ S}) : (μv v).IsAddHaarMeasure :=
    finiteCompletionNormalizedHaar_comap_isAddHaarMeasure K v.val
  let μ := Measure.infinitePi μv
  have : μ.IsAddLeftInvariant := ⟨fun u ↦ by
    change μ.map (fun w v ↦ u v + w v) = μ
    dsimp only [μ]
    rw [Measure.infinitePi_map_pi _ (f := fun v w ↦ u v + w)
      (fun v ↦ (continuous_const_add (u v)).measurable)]
    congr 1
    funext v
    exact map_add_left_eq_self (μv v) (u v)⟩
  have h := (Measure.addHaarMeasure_eq_iff (⊤ : PositiveCompacts ((v : {v // v ∉ S}) → O v.val))
    μ).mpr (by rw [PositiveCompacts.coe_top, measure_univ])
  change μ.IsAddHaarMeasure
  rw [← h]
  infer_instance

end

end Masullo
