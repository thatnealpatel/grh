module

public import Theorems.RationalAdeleAddHaar
public import Theorems.PadicIntegralBallFourier
public import Mathlib.Probability.ProductMeasure

import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.NumberTheory.Padics.HeightOneSpectrum
import Mathlib.NumberTheory.Padics.ProperSpace

/-!
# The local product formula on the integral-finite additive stage

In the rational case of (A.3.1.2), p. 556, the local integer ring has mass
one. On the stage with every finite coordinate integral, the measure in
(A.3.1.3) is therefore Lebesgue times a product of probabilities. We identify
that product with the compact factor of the normalized adelic measure.
-/

open IsDedekindDomain MeasureTheory NumberField Set TopologicalSpace
open scoped Padic

namespace Masullo

local notation "V" => HeightOneSpectrum (𝓞 ℚ)
local notation:max "O" v:max => HeightOneSpectrum.adicCompletionIntegers ℚ v
local notation "p[" v "]" => (Rat.HeightOneSpectrum.primesEquiv v : Nat.Primes)
local notation "K" => RationalFiniteIntegers

local instance (v : V) : Fact (p[v] : ℕ).Prime := ⟨(p[v]).property⟩

local instance : Countable V :=
  Function.Injective.countable Rat.HeightOneSpectrum.primesEquiv.injective

local instance (v : V) : SecondCountableTopology (O v) :=
  (Rat.HeightOneSpectrum.adicCompletionIntegers.padicIntEquiv v).toHomeomorph.secondCountableTopology

local instance : CompactSpace K := compactSpace_rationalFiniteIntegers

private noncomputable def localIntegerInclusion (v : V) : O v →+ ℚ_[p[v]] :=
  (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v).toRingEquiv.toAddMonoidHom.comp
    (O v).subtype.toAddMonoidHom

private theorem isOpenEmbedding_localIntegerInclusion (v : V) :
    Topology.IsOpenEmbedding (localIntegerInclusion v) := by
  change Topology.IsOpenEmbedding
    (((↑) : ℤ_[p[v]] → ℚ_[p[v]]) ∘
      (Rat.HeightOneSpectrum.adicCompletionIntegers.padicIntEquiv v).toHomeomorph)
  exact PadicInt.isOpenEmbedding_coe.comp
    (Rat.HeightOneSpectrum.adicCompletionIntegers.padicIntEquiv v).toHomeomorph.isOpenEmbedding

/-- The standard local additive Haar measure restricted to the integer ring,
expressed as a measure on that subtype via the local field identification. -/
@[expose]
public noncomputable def rationalLocalIntegersAddHaar (v : V) : Measure (O v) :=
  (@padicAddHaar p[v] ⟨(p[v]).property⟩).comap
    (fun x : O v ↦ Rat.HeightOneSpectrum.adicCompletion.padicEquiv v x)

public instance rationalLocalIntegersAddHaar_isAddHaarMeasure (v : V) :
    (rationalLocalIntegersAddHaar v).IsAddHaarMeasure :=
  Measure.IsAddHaarMeasure.comap (mH := inferInstance) (padicAddHaar p[v])
    (isOpenEmbedding_localIntegerInclusion v)

public instance rationalLocalIntegersAddHaar_isProbabilityMeasure (v : V) :
    IsProbabilityMeasure (rationalLocalIntegersAddHaar v) := by
  refine ⟨?_⟩
  change (padicAddHaar p[v]).comap (localIntegerInclusion v) univ = 1
  rw [(isOpenEmbedding_localIntegerInclusion v).measurableEmbedding.comap_apply, image_univ]
  have hrange : range (localIntegerInclusion v) = (PadicInt.subring p[v] : Set ℚ_[p[v]]) := by
    change range ((Rat.HeightOneSpectrum.adicCompletion.padicEquiv v) ∘
      ((↑) : O v → v.adicCompletion ℚ)) = _
    rw [range_comp, Subtype.range_coe]
    exact (Rat.HeightOneSpectrum.adicCompletion.padicEquiv_bijOn v).image_eq
  rw [hrange]
  exact padicAddHaar_integralBall p[v]

private instance : (Measure.infinitePi rationalLocalIntegersAddHaar).IsAddLeftInvariant := by
  refine ⟨fun u ↦ ?_⟩
  change (Measure.infinitePi rationalLocalIntegersAddHaar).map (fun w v ↦ u v + w v) = _
  rw [Measure.infinitePi_map_pi rationalLocalIntegersAddHaar (f := fun v w ↦ u v + w)
    (fun v ↦ (continuous_const_add (u v)).measurable)]
  congr 1
  funext v
  exact map_add_left_eq_self (rationalLocalIntegersAddHaar v) (u v)

/-- The normalized Haar measure on the compact product of the rational local
integer rings is the product of their additive Haar probabilities. -/
public theorem rationalFiniteIntegersHaar_eq_infinitePi :
    rationalFiniteIntegersHaar = Measure.infinitePi rationalLocalIntegersAddHaar := by
  let U := (⊤ : PositiveCompacts K)
  have normalized (μ : Measure K) [IsProbabilityMeasure μ] [μ.IsAddLeftInvariant] :
      Measure.addHaarMeasure U = μ :=
    (Measure.addHaarMeasure_eq_iff U μ).mpr (by rw [PositiveCompacts.coe_top, measure_univ])
  exact (normalized rationalFiniteIntegersHaar).symm.trans (normalized _)

set_option linter.concreteInstances false in
/-- On the open integral-finite stage of the rational adeles, normalized
additive Haar is Lebesgue times the product of local integer-ring measures. -/
public theorem comap_rationalAdeleAddHaar_integral_eq_prod
    [MeasurableSpace (AdeleRing (𝓞 ℚ) ℚ)] [BorelSpace (AdeleRing (𝓞 ℚ) ℚ)] :
    rationalAdeleAddHaar.comap rationalAdeleIntegralEmbedding =
      volume.prod (Measure.infinitePi rationalLocalIntegersAddHaar) := by
  rw [comap_rationalAdeleAddHaar_integral, rationalFiniteIntegersHaar_eq_infinitePi]

end Masullo
