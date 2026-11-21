module

public import Lemmas.RationalLocalUnitHaar
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.NumberTheory.Padics.HeightOneSpectrum
import Mathlib.NumberTheory.Padics.ProperSpace

/-!
# Local multiplicative Haar measures over the rationals

This is the rational finite-place case of Definition A.3.2.2 and
(A.3.2.2), p. 560. The local field at `p` is `ℚ_[p]`, so the local
extension over `ℚ_[p]` is trivial and the prescribed unit mass is one.
We use that normalization directly, without formalizing the discriminant
formula or identifying the additive density in (A.3.2.3).
-/

open NumberField IsDedekindDomain HeightOneSpectrum MeasureTheory Set TopologicalSpace

namespace Masullo

local notation "V" => HeightOneSpectrum (𝓞 ℚ)
local notation "G" v => (adicCompletion ℚ v)ˣ

private noncomputable def localIntegralUnitRange (v : V) : PositiveCompacts (G v) where
  carrier := range (rationalLocalUnitInclusion v)
  isCompact' := isCompact_range_rationalLocalUnitInclusion v
  interior_nonempty' := by
    rw [(isOpenEmbedding_rationalLocalUnitInclusion v).isOpen_range.interior_eq]
    exact range_nonempty _

variable (v : V) [MeasurableSpace (G v)] [BorelSpace (G v)]

/-- Local multiplicative Haar measure normalized on the integral unit subgroup. -/
public noncomputable def rationalLocalMultiplicativeHaar : Measure (G v) :=
  Measure.haarMeasure (localIntegralUnitRange v)

public instance : (rationalLocalMultiplicativeHaar v).IsHaarMeasure := by
  unfold rationalLocalMultiplicativeHaar
  infer_instance

/-- The rational finite-place normalization prescribed by (A.3.2.2). -/
public theorem rationalLocalMultiplicativeHaar_unitMass :
    rationalLocalMultiplicativeHaar v (range (rationalLocalUnitInclusion v)) = 1 :=
  Measure.haarMeasure_self (K₀ := localIntegralUnitRange v)

/-- The unit-mass normalization characterizes rational local multiplicative Haar measure. -/
public theorem rationalLocalMultiplicativeHaar_eq (ν : Measure (G v)) [ν.IsHaarMeasure]
    (hν : ν (range (rationalLocalUnitInclusion v)) = 1) :
    rationalLocalMultiplicativeHaar v = ν := by
  let : SecondCountableTopology (v.adicCompletion ℚ) :=
    (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v).toHomeomorph.secondCountableTopology
  let : SecondCountableTopology (v.adicCompletion ℚ)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.secondCountableTopology
  let : SecondCountableTopology (G v) := Units.isInducing_embedProduct.secondCountableTopology
  let : LocallyCompactSpace (G v) := (localIntegralUnitRange v).locallyCompactSpace_of_group
  exact (Measure.haarMeasure_eq_iff (localIntegralUnitRange v) ν).mpr hν

/-- Restricting the normalized ambient Haar to integral units, expressed in
integral-unit coordinates, gives the local factor used in the quotient product. -/
public theorem comap_rationalLocalMultiplicativeHaar :
    (rationalLocalMultiplicativeHaar v).comap (rationalLocalUnitInclusion v) =
      rationalLocalUnitHaar v := by
  let : CompactSpace (v.adicCompletionIntegers ℚ)ˣ := compactSpace_rationalLocalUnits v
  let ν := rationalLocalMultiplicativeHaar v
  let j := rationalLocalUnitInclusion v
  have hj := isOpenEmbedding_rationalLocalUnitInclusion v
  have : (ν.comap j).IsHaarMeasure := Measure.IsHaarMeasure.comap (mH := inferInstance) ν hj
  have : IsProbabilityMeasure (ν.comap j) := ⟨by
    rw [Measure.comap_apply j hj.injective (fun _ hs ↦ hj.measurableEmbedding.measurableSet_image' hs)
      ν MeasurableSet.univ, image_univ]
    exact rationalLocalMultiplicativeHaar_unitMass v⟩
  exact Measure.isHaarMeasure_eq_of_isProbabilityMeasure _ _

end Masullo
