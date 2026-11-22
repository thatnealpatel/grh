module

public import Theorems.AdeleRestrictedProductHaar
public import Lemmas.FinitePlaceSupport

import Lemmas.ArchimedeanAdeleAdditiveModulus
import Lemmas.AdeleStageAdditiveModulus
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-! # Additive Haar scaling under multiplication by an idele

Masullo states the image formula in Lemma A.3.1.4, PDF p. 556, and gives
an external reference for the proof. We compute the ratio on one compact
box in a stage containing the integer-mass exceptions and the nonintegral
coordinates of the idele and its inverse. `archimedeanAdeleTraceMeasure_image_mul`
and `adeleCalibrationBox_image_idele_stage` prove the local determinant and
stage-product calculations. Uniqueness of Haar then gives the ratio for
any additive Haar measure, without changing its normalization.

The inverse factor for pushforward is the change of variables needed in
Theorem 2.2.3.2, p. 82, with the counting normalization of Remark 2.2.3.3.
Source reading: Provisional, from the pinned Markdown and numbered PDF layout.
-/

open IsDedekindDomain MeasureTheory NumberField Set Topology TopologicalSpace
open scoped Masullo.AdeleStage

namespace Masullo

variable {K : Type*} [Field K] [NumberField K]

local notation "V" => HeightOneSpectrum (𝓞 K)
local notation "A" => AdeleRing (𝓞 K) K
local notation "A∞" => InfiniteAdeleRing K
local notation "I" => IdeleGroup (𝓞 K) K

private theorem exists_idele_stage_superset (E : Finset V) (h : I) :
    ∃ (S : Finset V) (u : IdeleFiniteStage K S), E ⊆ S ∧
      ideleFiniteStageEmbedding K S u = h := by
  classical
  have hh : h ∈ ⋃ S : Finset V, range (ideleFiniteStageEmbedding K S) := by
    rw [iUnion_range_ideleFiniteStageEmbedding]
    exact mem_univ _
  obtain ⟨S, hS⟩ := mem_iUnion.mp hh
  have ht : h ∈ range (ideleFiniteStageEmbedding K (E ∪ S)) := by
    rw [range_ideleFiniteStageEmbedding] at hS ⊢
    exact fun v hv ↦ hS v (fun hvS ↦ hv (Finset.mem_union_right _ hvS))
  obtain ⟨u, hu⟩ := ht
  exact ⟨E ∪ S, u, Finset.subset_union_left, hu⟩

private theorem secondCountableTopology_adeleRing : SecondCountableTopology A := by
  classical
  let E : Finset V := ∅
  let (S : Finset V) : SecondCountableTopology (range (adeleFiniteStageEmbedding K (E ∪ S))) :=
    (isEmbedding_adeleFiniteStageEmbedding K (E ∪ S)).toHomeomorph.symm.secondCountableTopology
  exact secondCountableTopology_of_countable_cover
    (fun S ↦ (isOpenEmbedding_adeleFiniteStageEmbedding K (E ∪ S)).isOpen_range)
    (iUnion_range_adeleFiniteStageEmbedding K E)

private theorem comap_adeleHaar_dilate_of_calibration
    (ν μ : Measure A) [ν.IsAddHaarMeasure] [μ.IsAddHaarMeasure] (h : I)
    (Q : PositiveCompacts A)
    (hmass : ν ((fun x : A ↦ (h : A) * x) '' (Q : Set A)) = ENNReal.ofReal (ideleNorm h) * ν Q) :
    μ.comap (fun x : A ↦ (h : A) * x) = ENNReal.ofReal (ideleNorm h) • μ := by
  let : LocallyCompactSpace A := Q.locallyCompactSpace_of_addGroup
  let : SecondCountableTopology A := secondCountableTopology_adeleRing
  let e := ContinuousAddEquiv.mulLeft h
  let H := Measure.addHaarMeasure Q
  let c := ENNReal.ofReal (ideleNorm h)
  let D := e '' (Q : Set A)
  have hν : ν = ν Q • H := Measure.addHaarMeasure_unique ν Q
  have hμ : μ = μ Q • H := Measure.addHaarMeasure_unique μ Q
  have hH : H D = c := by
    apply (ENNReal.mul_right_inj
      (Measure.measure_pos_of_nonempty_interior ν Q.interior_nonempty).ne'
      Q.isCompact.measure_ne_top).mp
    calc
      ν Q * H D = ν D := (congrArg (fun η : Measure A ↦ η D) hν).symm
      _ = c * ν Q := hmass
      _ = ν Q * c := mul_comm _ _
  have hcomap : (μ.comap e).IsAddHaarMeasure :=
    Measure.IsAddHaarMeasure.comap (mH := inferInstance) μ
      (f := e.toAddEquiv.toAddMonoidHom) e.toHomeomorph.isOpenEmbedding
  have hQ : (μ.comap e) Q = c * μ Q := by
    change (μ.comap e.toHomeomorph) Q = _
    rw [e.toHomeomorph.measurableEmbedding.comap_apply]
    change μ D = c * μ Q
    calc
      μ D = μ Q * H D := congrArg (fun η : Measure A ↦ η D) hμ
      _ = c * μ Q := hH ▸ mul_comm _ _
  change μ.comap e = c • μ
  calc
    μ.comap e = (μ.comap e) Q • H := Measure.addHaarMeasure_unique _ Q
    _ = c • (μ Q • H) := by rw [hQ, smul_smul]
    _ = c • μ := congrArg (c • ·) hμ.symm

/-- Pulling back any additive Haar measure by multiplication by an idele scales it by
that idele's norm. In particular, no new normalization of the box Fourier measure is needed. -/
public theorem comap_adeleAddHaar_dilate (μ : Measure A) [μ.IsAddHaarMeasure] (h : I) :
    μ.comap (fun x : A ↦ (h : A) * x) = ENNReal.ofReal (ideleNorm h) • μ := by
  obtain ⟨E, hE⟩ := exists_finiteCompletionIntegerMass_exceptions K
  have hE' (v : V) (hv : v ∉ E) : finiteCompletionIntegerMass K v = 1 := by
    by_contra hne
    exact hv ((hE v).2 hne)
  obtain ⟨ν, hν, _, hstage, _⟩ := exists_adeleRestrictedProductHaar K E hE'
  obtain ⟨S, u, hES, rfl⟩ := exists_idele_stage_superset E h
  let : LocallyCompactSpace A∞ := InfiniteAdeleRing.locallyCompactSpace K
  let : T2Space A∞ := (archimedeanEuclideanToAdele K).toHomeomorph.t2Space
  let B : PositiveCompacts A∞ := Classical.choice inferInstance
  -- Use the actual Archimedean projection of the embedded unit, not a new character or measure.
  let a : A∞ˣ := Units.map (RingHom.fst A∞ (FiniteAdeleRing (𝓞 K) K)).toMonoidHom
    (ideleFiniteStageEmbedding K S u)
  have hArch := archimedeanAdeleTraceMeasure_image_mul K a (B : Set A∞) B.isCompact.measurableSet
  have hS (v : V) (hv : v ∉ S) : finiteCompletionIntegerMass K v = 1 :=
    hE' v (fun hvE ↦ hv (hES hvE))
  exact comap_adeleHaar_dilate_of_calibration ν μ _ (adeleCalibrationBox K B)
    (adeleCalibrationBox_image_idele_stage K B u ν ((hstage ν).mp rfl S hES) hS hArch)

/-- The image formula of Masullo's Lemma A.3.1.4, for all sets and hence for Borel sets. -/
public theorem adeleAddHaar_image_idele_mul (μ : Measure A) [μ.IsAddHaarMeasure]
    (h : I) (B : Set A) :
    μ ((fun x : A ↦ (h : A) * x) '' B) = ENNReal.ofReal (ideleNorm h) * μ B := by
  let e := ContinuousAddEquiv.mulLeft h
  exact (e.toHomeomorph.measurableEmbedding.comap_apply μ B).symm.trans
    (congrArg (fun η : Measure A ↦ η B) (comap_adeleAddHaar_dilate μ h))

/-- Pushing forward additive Haar under multiplication by an idele scales it by
its inverse norm. -/
public theorem map_adeleAddHaar_dilate (μ : Measure A) [μ.IsAddHaarMeasure] (h : I) :
    μ.map (fun x : A ↦ (h : A) * x) = ENNReal.ofReal ((ideleNorm h)⁻¹) • μ := by
  let e := ContinuousAddEquiv.mulLeft h
  ext B hB
  change (μ.map e.toHomeomorph) B = _
  rw [Measure.map_apply e.continuous.measurable hB]
  change μ (e.toEquiv ⁻¹' B) = _
  rw [← e.toEquiv.image_symm_eq_preimage]
  change μ ((fun x : A ↦ (↑(h⁻¹) : A) * x) '' B) = ENNReal.ofReal ((ideleNorm h)⁻¹) * μ B
  rw [adeleAddHaar_image_idele_mul μ h⁻¹, map_inv]

end Masullo
