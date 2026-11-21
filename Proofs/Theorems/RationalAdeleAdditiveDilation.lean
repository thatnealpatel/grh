module

public import Lemmas.RationalAdeleAdditiveModulus

import Mathlib.MeasureTheory.Measure.Haar.Unique

/-! # Additive Haar scaling by a rational idele

The rational case of Lemma A.3.1.4, p. 556. The factor for images, or
comap, is the norm of the idele, not its inverse.
-/

open NumberField MeasureTheory Set

namespace Masullo

local notation "A" => AdeleRing (𝓞 ℚ) ℚ

set_option linter.concreteInstances false

variable [MeasurableSpace A] [BorelSpace A]

/-- Pulling back normalized additive Haar by multiplication by `g` multiplies
it by the idelic norm of `g`. -/
public theorem comap_rationalAdeleAddHaar_dilate (g : IdeleGroup (𝓞 ℚ) ℚ) :
    rationalAdeleAddHaar.comap (fun x : A ↦ (g : A) * x) =
      ENNReal.ofReal (ideleNorm g) • rationalAdeleAddHaar := by
  let K := rationalAdeleClosedUnitStrip
  let : LocallyCompactSpace A := K.locallyCompactSpace_of_addGroup
  let : SecondCountableTopology A := secondCountableTopology_rationalAdeles
  let e := ContinuousAddEquiv.mulLeft g
  let μ := rationalAdeleAddHaar.comap e.toAddEquiv.toAddMonoidHom
  have : μ.IsAddHaarMeasure := Measure.IsAddHaarMeasure.comap (mH := inferInstance)
    rationalAdeleAddHaar (f := e.toAddEquiv.toAddMonoidHom) e.toHomeomorph.isOpenEmbedding
  have hμ : μ K = ENNReal.ofReal (ideleNorm g) := by
    change (rationalAdeleAddHaar.comap (fun x : A ↦ (g : A) * x)) K = _
    exact (e.toHomeomorph.measurableEmbedding.comap_apply _ _).trans
      (rationalAdeleAddHaar_dilate_closedUnitStrip g)
  change μ = _
  simpa only [hμ, rationalAdeleAddHaar_eq_addHaarMeasure, K] using Measure.addHaarMeasure_unique μ K

/-- For arbitrary additive Haar on the rational adeles, dilation by an idele
scales the measure of a Borel set by the idelic norm. -/
public theorem rationalAdeleHaar_image_idele_mul (μ : Measure A) [μ.IsAddHaarMeasure]
    (g : IdeleGroup (𝓞 ℚ) ℚ) (B : Set A) (hB : MeasurableSet B) :
    μ ((fun x : A ↦ (g : A) * x) '' B) = ENNReal.ofReal (ideleNorm g) * μ B := by
  let K := rationalAdeleClosedUnitStrip
  let : LocallyCompactSpace A := K.locallyCompactSpace_of_addGroup
  let : SecondCountableTopology A := secondCountableTopology_rationalAdeles
  have hμ : μ = μ K • rationalAdeleAddHaar := by
    rw [rationalAdeleAddHaar_eq_addHaarMeasure]
    exact Measure.addHaarMeasure_unique μ K
  have hd := congrArg (fun ν : Measure A ↦ ν B) (comap_rationalAdeleAddHaar_dilate g)
  change (rationalAdeleAddHaar.comap (fun x : A ↦ (g : A) * x)) B = _ at hd
  have e : MeasurableEmbedding (fun x : A ↦ (g : A) * x) :=
    (ContinuousAddEquiv.mulLeft g).toHomeomorph.measurableEmbedding
  rw [Measure.comap_apply (fun x : A ↦ (g : A) * x) e.injective
    (fun _ ↦ e.measurableSet_image.mpr) _ hB,
    smul_apply, smul_eq_mul] at hd
  calc
    _ = μ K * rationalAdeleAddHaar ((fun x : A ↦ (g : A) * x) '' B) := by
      rw [congrArg (fun ν : Measure A ↦ ν _) hμ, smul_apply, smul_eq_mul]
    _ = ENNReal.ofReal (ideleNorm g) * (μ K * rationalAdeleAddHaar B) := by
      rw [hd, mul_left_comm]
    _ = _ := by conv_rhs => arg 2; rw [hμ, smul_apply, smul_eq_mul]

end Masullo
