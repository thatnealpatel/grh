module

public import Theorems.ArchimedeanLogMeasure
public import Lemmas.ArchimedeanAngularChart
public import Mathlib.Topology.Algebra.Group.Units

import Lemmas.MeasurePreservingPiProd

/-!
# Archimedean multiplicative Haar in norm, regulator, and angular coordinates

Masullo gives the weighted logarithms in (A.2.3.3)–(5), PDF p. 548, and
prescribes the local measures in Definitions A.3.1.2(1)–(2), p. 556, and
A.3.2.2(1), p. 560. The Archimedean factor in (A.3.2.5), p. 560, is
the product of these local measures. We supply its coordinate formula:
Apply the local signed-real and complex log-polar identities, group the
logs and angles, and split the log norm off without rescaling the
retained coordinates. This does not yet compare the quotient mass with
(A.3.2.1), pp. 559–560. Source reading: Pinned Markdown and numbered PDF
text, not rendered pages.
-/

open MeasureTheory NumberField Set
open NumberField.Units.dirichletUnitTheorem (w₀ logSpace)
open scoped Classical

namespace Masullo

variable (K : Type*) [Field K] [NumberField K]
variable [∀ v : InfinitePlace K, MeasurableSpace v.Completionˣ]
  [∀ v : InfinitePlace K, BorelSpace v.Completionˣ]

/-- The product of the prescribed local Haar measures becomes Lebesgue in
log norm, product Lebesgue in the retained weighted logs, and the product
of the local sign and angle measures. No scalar enters this separation. -/
public theorem measurePreserving_archimedeanHaarCoordinates :
    MeasurePreserving (fun u : (v : InfinitePlace K) → v.Completionˣ ↦
      ((∑ v, (v.mult : ℝ) * Real.log ‖(u v).val‖),
        (fun v : {v : InfinitePlace K // v ≠ w₀} ↦ (v.val.mult : ℝ) * Real.log ‖(u v.val).val‖),
        fun v ↦ archimedeanAngle v (u v)))
      (Measure.pi fun v ↦ archimedeanCompletionHaar v)
      ((volume : Measure ℝ).prod ((volume : Measure (logSpace K)).prod
        (Measure.pi fun v : InfinitePlace K ↦ archimedeanAngularMeasure v))) := by
  -- The local laws retain both signs and the complex angular density.
  have hlocal := measurePreserving_pi (fun v : InfinitePlace K ↦ archimedeanCompletionHaar v)
    (fun v ↦ (volume : Measure ℝ).prod (archimedeanAngularMeasure v))
    (fun v ↦ measurePreserving_archimedeanLocalCoordinates v)
  -- Product rectangles separate the tuple of pairs into two tuples.
  have hgroup := measurePreserving_piProd (InfinitePlace K) (fun _ ↦ ℝ) ArchimedeanAngle
    (fun _ ↦ volume) archimedeanAngularMeasure
  let ω := Measure.pi fun v : InfinitePlace K ↦ archimedeanAngularMeasure v
  -- Separate log norm from the retained logs and leave the angular tuple fixed.
  have hsplit := (measurePreserving_archimedeanLogSplit K).prod (MeasurePreserving.id ω)
  exact (measurePreserving_prodAssoc volume (volume : Measure (logSpace K)) ω).comp
    (hsplit.comp (hgroup.comp hlocal))

/-- On units of the Archimedean adele ring, transport the same product measure
along the units-of-a-product equivalence. -/
public theorem measurePreserving_infiniteAdeleHaarCoordinates
    [MeasurableSpace (InfiniteAdeleRing K)ˣ] [BorelSpace (InfiniteAdeleRing K)ˣ] :
    let e : (InfiniteAdeleRing K)ˣ ≃ₜ* ((v : InfinitePlace K) → v.Completionˣ) :=
      ContinuousMulEquiv.piUnits
    MeasurePreserving (fun a : (InfiniteAdeleRing K)ˣ ↦
      let u := e a
      ((∑ v, (v.mult : ℝ) * Real.log ‖(u v).val‖),
        (fun v : {v : InfinitePlace K // v ≠ w₀} ↦ (v.val.mult : ℝ) * Real.log ‖(u v.val).val‖),
        fun v ↦ archimedeanAngle v (u v)))
      ((Measure.pi fun v ↦ archimedeanCompletionHaar v).comap e)
      ((volume : Measure ℝ).prod ((volume : Measure (logSpace K)).prod
        (Measure.pi fun v : InfinitePlace K ↦ archimedeanAngularMeasure v))) := by
  intro e
  let (v : InfinitePlace K) : SecondCountableTopology v.Completionˣ := by
    open InfinitePlace.Completion in
    rcases v.isReal_or_isComplex with hv | hv
    · exact ((isometryEquivRealOfIsReal hv).toHomeomorph.isOpenEmbedding.comp
        Units.isOpenEmbedding_val).isEmbedding.secondCountableTopology
    · exact ((isometryEquivComplexOfIsComplex hv).toHomeomorph.isOpenEmbedding.comp
        Units.isOpenEmbedding_val).isEmbedding.secondCountableTopology
  let μ := Measure.pi fun v : InfinitePlace K ↦ archimedeanCompletionHaar v
  have he : MeasurableEmbedding e := e.toHomeomorph.toMeasurableEquiv.measurableEmbedding
  have h : MeasurePreserving e (μ.comap e) μ := by
    refine ⟨he.measurable, ?_⟩
    rw [he.map_comap, range_eq_univ.mpr e.surjective, Measure.restrict_univ]
  exact (measurePreserving_archimedeanHaarCoordinates K).comp h

end Masullo
