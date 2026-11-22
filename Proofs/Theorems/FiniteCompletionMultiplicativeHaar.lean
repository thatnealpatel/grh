module

public import Theorems.FiniteCompletionDifferentExtension
public import Theorems.DifferentUnitScales
public import Lemmas.IdeleFiniteStageMeasure
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.LinearAlgebra.Countable

/-! # Discriminant-normalized multiplicative Haar at a finite place

Definition A.3.2.2(2), (A.3.2.2), PDF p. 560, prescribes the unit mass as
the square root of the base p-adic discriminant norm. We construct the
measure by scaling Haar on the compact open group of integral units,
then use the extension-of-differents comparison to verify the mass for
every integral basis. This also supplies the finite support and product
of the unit scales used in Lemma A.3.2.4. Source reading: Provisional,
from the pinned Markdown and numbered PDF text, not the rendered page.
-/

open IsDedekindDomain MeasureTheory Module NumberField Set TopologicalSpace
open scoped ENNReal Masullo

namespace Masullo

variable {K : Type*} [Field K] [NumberField K]

local notation "V" => HeightOneSpectrum (𝓞 K)
local notation "D" => differentIdeal ℤ (𝓞 K)
local notation "weight" v =>
  (Real.sqrt ((Ideal.absNorm (HeightOneSpectrum.asIdeal v) ^ multiplicity (HeightOneSpectrum.asIdeal v) D : ℕ) : ℝ))⁻¹

private noncomputable def finiteCompletionUnitRange (v : V) : PositiveCompacts (v.adicCompletion K)ˣ where
  carrier := range (finiteCompletionUnitInclusion K v)
  isCompact' := by
    let : CompactSpace (v.adicCompletionIntegers K)ˣ := compactSpace_finiteCompletionIntegralUnits K v
    exact isCompact_range (isOpenEmbedding_finiteCompletionIntegralUnits K v).continuous
  interior_nonempty' := by
    rw [(isOpenEmbedding_finiteCompletionIntegralUnits K v).isOpen_range.interior_eq]
    exact range_nonempty _

section Local

variable (v : HeightOneSpectrum (𝓞 K)) [MeasurableSpace (v.adicCompletion K)ˣ] [BorelSpace (v.adicCompletion K)ˣ]

/-- Haar on the actual finite completion's multiplicative group, with integral
unit mass the inverse square root of the norm of the local different. -/
public noncomputable def finiteCompletionMultiplicativeHaar : Measure (v.adicCompletion K)ˣ :=
  ENNReal.ofReal (weight v) • Measure.haarMeasure (finiteCompletionUnitRange v)

public instance finiteCompletionMultiplicativeHaar_isHaarMeasure :
    (finiteCompletionMultiplicativeHaar v).IsHaarMeasure := by
  have hq : 0 < v.asIdeal.absNorm := Nat.pos_of_ne_zero fun h ↦
    v.ne_bot (Ideal.absNorm_eq_zero_iff.mp h)
  have hweight : 0 < weight v := inv_pos.mpr (Real.sqrt_pos.2 (by positivity))
  exact Measure.IsHaarMeasure.smul _ (ENNReal.ofReal_ne_zero_iff.mpr hweight) ENNReal.ofReal_ne_top

/-- The unit mass in terms of the global different at this place. -/
public theorem finiteCompletionMultiplicativeHaar_unitMass :
    finiteCompletionMultiplicativeHaar v (range (finiteCompletionUnitInclusion K v)) =
      ENNReal.ofReal (weight v) := by
  change (ENNReal.ofReal (weight v) • Measure.haarMeasure (finiteCompletionUnitRange v))
    (finiteCompletionUnitRange v) = _
  rw [smul_apply, Measure.haarMeasure_self, smul_eq_mul, mul_one]

/-- The mass is the square root of the p-adic discriminant norm for every
finite integral basis, as in (A.3.2.2). -/
public theorem finiteCompletionMultiplicativeHaar_unitMass_eq_sqrt_discr
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Basis ι ℤ_[finiteCompletionBasePrime v] (v.adicCompletionIntegers K)) :
    finiteCompletionMultiplicativeHaar v (range (finiteCompletionUnitInclusion K v)) =
      ENNReal.ofReal (Real.sqrt ‖Algebra.discr ℤ_[finiteCompletionBasePrime v] b‖) := by
  rw [finiteCompletionMultiplicativeHaar_unitMass,
    finiteCompletion_norm_discr_eq_inv_globalDifferent_residueNorm_pow v b, Real.sqrt_inv]

/-- The prescribed unit mass characterizes this Haar measure. -/
public theorem finiteCompletionMultiplicativeHaar_eq (ν : Measure (v.adicCompletion K)ˣ) [ν.IsHaarMeasure]
    (hν : ν (range (finiteCompletionUnitInclusion K v)) = ENNReal.ofReal (weight v)) :
    finiteCompletionMultiplicativeHaar v = ν := by
  let F := v.adicCompletion K
  let : Countable K := Countable.of_moduleFinite (R := ℚ)
  let : SeparableSpace F := ⟨range (algebraMap K F), countable_range _, v.denseRange_algebraMap K⟩
  let : SecondCountableTopology F := inferInstance
  let : SecondCountableTopology Fᵐᵒᵖ := MulOpposite.opHomeomorph.symm.secondCountableTopology
  let : SecondCountableTopology (v.adicCompletion K)ˣ := Units.isInducing_embedProduct.secondCountableTopology
  let : LocallyCompactSpace (v.adicCompletion K)ˣ := (finiteCompletionUnitRange v).locallyCompactSpace_of_group
  rw [Measure.haarMeasure_unique ν (finiteCompletionUnitRange v)]
  exact congrArg (· • Measure.haarMeasure (finiteCompletionUnitRange v)) hν.symm

end Local

section Product

variable [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)ˣ] [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)ˣ]

/-- Away from the support of the different, the local measure gives integral
units mass one, so the omitted factors in a restricted product are probabilities. -/
public theorem finiteCompletionMultiplicativeHaar_unitMass_eq_one (v : V)
    (hv : multiplicity v.asIdeal D = 0) :
    finiteCompletionUnitMass K (fun w ↦ finiteCompletionMultiplicativeHaar w) v = 1 := by
  rw [finiteCompletionUnitMass, finiteCompletionMultiplicativeHaar_unitMass, hv]
  simp

/-- Over any finite set containing the support of the different, the product
of the actual unit masses is the inverse square root of the absolute discriminant. -/
public theorem prod_finiteCompletionMultiplicativeHaar_unitMass
    (S : Finset V) (hS : ∀ v ∉ S, multiplicity v.asIdeal D = 0) :
    (∏ v ∈ S, (finiteCompletionUnitMass K (fun w ↦ finiteCompletionMultiplicativeHaar w) v).toReal) =
      (Real.sqrt ((discr K).natAbs : ℝ))⁻¹ := by
  rw [← prod_differentIdeal_unit_scales S hS]
  apply Finset.prod_congr rfl
  intro v _
  rw [finiteCompletionUnitMass, finiteCompletionMultiplicativeHaar_unitMass, ENNReal.toReal_ofReal]
  positivity

end Product

end Masullo
