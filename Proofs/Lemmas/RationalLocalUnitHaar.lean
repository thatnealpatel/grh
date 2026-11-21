module

public import Lemmas.RationalFiniteUnits
public import Mathlib.Probability.ProductMeasure
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.NumberTheory.Padics.HeightOneSpectrum
import Mathlib.NumberTheory.Padics.ProperSpace

/-!
# Haar probabilities on rational local integral units

The measure on the full product uses the product sigma-algebra. Countability
of the places and second countability of each unit group make this the Borel
sigma-algebra for the product topology.
-/

open NumberField IsDedekindDomain HeightOneSpectrum MeasureTheory Set TopologicalSpace

namespace Masullo

local notation "V" => HeightOneSpectrum (𝓞 ℚ)
local notation "U" v => (adicCompletionIntegers ℚ v)ˣ

/-- The local unit groups carry their Borel sigma-algebras. -/
public noncomputable scoped instance rationalLocalUnitsMeasurableSpace (v : V) : MeasurableSpace (U v) :=
  borel _

public scoped instance rationalLocalUnitsBorelSpace (v : V) : BorelSpace (U v) := ⟨rfl⟩

local instance : Countable V :=
  Function.Injective.countable Rat.HeightOneSpectrum.primesEquiv.injective

local instance (v : V) : SecondCountableTopology (U v) := by
  let : SecondCountableTopology (v.adicCompletionIntegers ℚ) :=
    (Rat.HeightOneSpectrum.adicCompletionIntegers.padicIntEquiv v).toHomeomorph.secondCountableTopology
  let : SecondCountableTopology (v.adicCompletionIntegers ℚ)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.secondCountableTopology
  exact Units.isInducing_embedProduct.secondCountableTopology

public theorem compactSpace_rationalLocalUnits (v : V) : CompactSpace (U v) := by
  let : CompactSpace (v.adicCompletionIntegers ℚ) :=
    (Rat.HeightOneSpectrum.adicCompletionIntegers.padicIntEquiv v).toHomeomorph.symm.compactSpace
  infer_instance

local instance (v : V) : CompactSpace (U v) := compactSpace_rationalLocalUnits v

/-- The inclusion of the integral units into the multiplicative group of the local field. -/
@[expose]
public noncomputable def rationalLocalUnitInclusion (v : V) : (U v) →* (v.adicCompletion ℚ)ˣ :=
  Units.map (v.adicCompletionIntegers ℚ).subtype.toMonoidHom

public theorem isOpenEmbedding_rationalLocalUnitInclusion (v : V) :
    Topology.IsOpenEmbedding (rationalLocalUnitInclusion v) := by
  have hc : Continuous (rationalLocalUnitInclusion v) := Units.continuous_map continuous_subtype_val
  have hi : Function.Injective (rationalLocalUnitInclusion v) := Units.map_injective Subtype.val_injective
  let S := (v.adicCompletionIntegers ℚ).toSubring.toSubmonoid
  have hr : Set.range (rationalLocalUnitInclusion v) = (S.units : Set (v.adicCompletion ℚ)ˣ) := by
    ext x
    constructor
    · rintro ⟨u, rfl⟩
      exact ⟨u.val.property, u.inv.property⟩
    · intro hx
      exact ⟨S.unitsEquivUnitsType ⟨x, hx⟩, Units.ext rfl⟩
  refine ⟨(hc.isClosedEmbedding hi).isEmbedding, ?_⟩
  rw [hr]
  exact S.isOpen_units (Valued.isOpen_valuationSubring (v.adicCompletion ℚ))

public theorem isCompact_range_rationalLocalUnitInclusion (v : V) :
    IsCompact (Set.range (rationalLocalUnitInclusion v)) :=
  isCompact_range (isOpenEmbedding_rationalLocalUnitInclusion v).continuous

local instance : CompactSpace RationalFiniteUnits := compactSpace_rationalFiniteUnits

public scoped instance rationalFiniteUnitsBorelSpace : BorelSpace RationalFiniteUnits :=
  Pi.borelSpace

/-- The Haar probability normalized by the whole integral unit group at `v`. -/
public noncomputable def rationalLocalUnitHaar (v : V) : Measure (U v) :=
  Measure.haarMeasure (⊤ : PositiveCompacts (U v))

public instance (v : V) : (rationalLocalUnitHaar v).IsHaarMeasure := by
  unfold rationalLocalUnitHaar
  infer_instance

public instance (v : V) : IsProbabilityMeasure (rationalLocalUnitHaar v) :=
  ⟨by simpa only [rationalLocalUnitHaar, PositiveCompacts.coe_top] using
    (Measure.haarMeasure_self (K₀ := (⊤ : PositiveCompacts (U v))))⟩

/-- The product of the local integral-unit Haar probabilities over all finite places. -/
public noncomputable def rationalFiniteUnitHaar : Measure RationalFiniteUnits :=
  Measure.infinitePi rationalLocalUnitHaar

public instance : IsProbabilityMeasure rationalFiniteUnitHaar := by
  unfold rationalFiniteUnitHaar
  infer_instance

/-- A finite measurable cylinder has the product of its local masses. -/
public theorem rationalFiniteUnitHaar_cylinder {s : Finset V} {t : (v : V) → Set (U v)}
    (ht : ∀ v ∈ s, MeasurableSet (t v)) :
    rationalFiniteUnitHaar ((s : Set V).pi t) = ∏ v ∈ s, rationalLocalUnitHaar v (t v) :=
  Measure.infinitePi_pi _ ht

private instance : rationalFiniteUnitHaar.IsMulLeftInvariant := by
  refine ⟨fun u ↦ ?_⟩
  change (Measure.infinitePi rationalLocalUnitHaar).map (fun w v ↦ u v * w v) = _
  rw [Measure.infinitePi_map_pi rationalLocalUnitHaar (f := fun v w ↦ u v * w)
    (fun v ↦ (continuous_const_mul (u v)).measurable)]
  congr 1
  funext v
  exact map_mul_left_eq_self (rationalLocalUnitHaar v) (u v)

public instance : rationalFiniteUnitHaar.IsHaarMeasure := by
  have h : Measure.haarMeasure (⊤ : PositiveCompacts RationalFiniteUnits) =
      rationalFiniteUnitHaar := (Measure.haarMeasure_eq_iff _ _).mpr
    (by rw [PositiveCompacts.coe_top, measure_univ])
  rw [← h]
  infer_instance

end Masullo
