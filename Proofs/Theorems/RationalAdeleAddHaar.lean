module

public import Theorems.RationalAdeleFundamentalDomain
public import Mathlib.MeasureTheory.Measure.Haar.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.NumberTheory.Padics.ProperSpace

/-!
# Additive Haar normalization on the rational adeles

In Example A.3.1.8, p. 558, the local product measure gives the fundamental
strip mass one. We construct additive Haar with that normalization and
identify its restriction to the open integral-finite stage. The restricted
product formula on all stages and the quotient integration formula are separate.
-/

open NumberField IsDedekindDomain MeasureTheory Set Topology TopologicalSpace
open scoped RestrictedProduct

namespace Masullo

local notation "V" => HeightOneSpectrum (𝓞 ℚ)
local notation "O" v => HeightOneSpectrum.adicCompletionIntegers ℚ v
local notation "A" => AdeleRing (𝓞 ℚ) ℚ
local notation "K" => RationalFiniteIntegers

local instance : T2Space A := by
  let : T2Space (FiniteAdeleRing (𝓞 ℚ) ℚ) :=
    show T2Space (Πʳ v : V, [v.adicCompletion ℚ, v.adicCompletionIntegers ℚ]) from inferInstance
  unfold AdeleRing InfiniteAdeleRing
  infer_instance

local instance : CompactSpace K := compactSpace_rationalFiniteIntegers

local instance : Countable V :=
  Function.Injective.countable Rat.HeightOneSpectrum.primesEquiv.injective

local instance (v : V) : SecondCountableTopology (O v) :=
  (Rat.HeightOneSpectrum.adicCompletionIntegers.padicIntEquiv v).toHomeomorph.secondCountableTopology

private noncomputable def closedWindow : PositiveCompacts (ℝ × K) where
  carrier := Icc 0 1 ×ˢ univ
  isCompact' := isCompact_Icc.prod isCompact_univ
  interior_nonempty' := by
    rw [interior_prod_eq, interior_Icc, interior_univ]
    exact (nonempty_Ioo.mpr zero_lt_one).prod univ_nonempty

private noncomputable def closedStrip : PositiveCompacts A :=
  closedWindow.map rationalAdeleIntegralEmbedding
    isOpenEmbedding_rationalAdeleIntegralEmbedding.continuous
    isOpenEmbedding_rationalAdeleIntegralEmbedding.isOpenMap

private theorem image_halfOpenWindow :
    rationalAdeleIntegralEmbedding '' (Ico 0 1 ×ˢ (univ : Set K)) = rationalAdeleUnitStrip := by
  ext a
  constructor
  · rintro ⟨x, hx, rfl⟩
    change (rationalIntegralAdelesHomeomorph x : A) ∈ rationalIntegralAdeles ∧
      rationalAdeleReal (rationalIntegralAdelesHomeomorph x : A) ∈ Ico 0 1
    exact ⟨(rationalIntegralAdelesHomeomorph x).property,
      (rationalIntegralAdelesHomeomorph_real x).symm ▸ hx.1⟩
  · rintro ⟨ha, hr⟩
    obtain ⟨x, hx⟩ := rationalIntegralAdelesHomeomorph.surjective ⟨a, ha⟩
    refine ⟨x, ⟨?_, mem_univ _⟩, congrArg Subtype.val hx⟩
    rwa [← rationalIntegralAdelesHomeomorph_real x, hx]

/-- The local integral rings carry their Borel sigma-algebras. -/
public noncomputable scoped instance rationalLocalIntegersMeasurableSpace (v : V) :
    MeasurableSpace (O v) := borel _

public scoped instance rationalLocalIntegersBorelSpace (v : V) : BorelSpace (O v) := ⟨rfl⟩

public scoped instance rationalFiniteIntegersBorelSpace : BorelSpace K := Pi.borelSpace

/-- The additive Haar probability on the compact product of local integral rings. -/
public noncomputable def rationalFiniteIntegersHaar : Measure K :=
  Measure.addHaarMeasure (⊤ : PositiveCompacts K)

public instance : rationalFiniteIntegersHaar.IsAddHaarMeasure := by
  unfold rationalFiniteIntegersHaar
  infer_instance

public instance : IsProbabilityMeasure rationalFiniteIntegersHaar :=
  ⟨by simpa only [rationalFiniteIntegersHaar, PositiveCompacts.coe_top] using
    (Measure.addHaarMeasure_self (K₀ := (⊤ : PositiveCompacts K)))⟩

set_option linter.concreteInstances false

variable [MeasurableSpace A] [BorelSpace A]

/-- Additive Haar measure on the rational adeles, normalized by the closed real
unit interval with integral finite coordinates. -/
public noncomputable def rationalAdeleAddHaar : Measure A := Measure.addHaarMeasure closedStrip

public instance : rationalAdeleAddHaar.IsAddHaarMeasure := by
  unfold rationalAdeleAddHaar
  infer_instance

public instance : rationalAdeleAddHaar.Regular := by
  unfold rationalAdeleAddHaar
  infer_instance

/-- On the open integral-finite stage, the upstairs measure is Lebesgue measure
in the real coordinate times additive Haar probability in the compact factor. -/
public theorem comap_rationalAdeleAddHaar_integral :
    rationalAdeleAddHaar.comap rationalAdeleIntegralEmbedding =
      volume.prod rationalFiniteIntegersHaar := by
  let j := rationalAdeleIntegralEmbedding
  let μ := rationalAdeleAddHaar.comap j
  have hj := isOpenEmbedding_rationalAdeleIntegralEmbedding
  have : μ.IsAddHaarMeasure := Measure.IsAddHaarMeasure.comap (mH := inferInstance) _ hj
  have hμ : μ closedWindow = 1 := by
    change (rationalAdeleAddHaar.comap j) closedWindow = 1
    rw [hj.measurableEmbedding.comap_apply]
    exact Measure.addHaarMeasure_self (K₀ := closedStrip)
  have hprod : (volume.prod rationalFiniteIntegersHaar) (closedWindow : Set (ℝ × K)) = 1 := by
    change (volume.prod rationalFiniteIntegersHaar) (Icc 0 1 ×ˢ univ) = 1
    rw [Measure.prod_prod, Real.volume_Icc, measure_univ]
    simp
  exact ((Measure.addHaarMeasure_eq_iff closedWindow μ).mpr hμ).symm.trans
    ((Measure.addHaarMeasure_eq_iff closedWindow _).mpr hprod)

/-- The half-open additive fundamental domain has volume one. -/
public theorem rationalAdeleAddHaar_unitStrip : rationalAdeleAddHaar rationalAdeleUnitStrip = 1 := by
  rw [← image_halfOpenWindow,
    ← isOpenEmbedding_rationalAdeleIntegralEmbedding.measurableEmbedding.comap_apply,
    comap_rationalAdeleAddHaar_integral, Measure.prod_prod, Real.volume_Ico, measure_univ]
  simp

end Masullo
