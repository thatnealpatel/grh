module

public import Lemmas.IdeleFiniteStageMeasure
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-! # The restricted product of local multiplicative Haar measures

Lemma A.3.2.4, (A.3.2.5), p. 560, invokes the restricted-product Haar
prescription (p. 556). We construct the product on the actual ideles and prove
its restrictions in stage coordinates. For a probability tail, the stage must
contain all exceptions to unit mass. We keep their masses, using one common
compact calibration box in every stage. This proves the measure construction
from given local measures, not the discriminant scaling in (A.3.2.2) or its
comparison with the separate quotient normalization in (A.3.2.1).
-/

open IsDedekindDomain MeasureTheory NumberField Set Topology TopologicalSpace
open scoped Masullo

namespace Masullo

variable (K : Type*) [Field K] [NumberField K]

local notation "V" => HeightOneSpectrum (𝓞 K)
local notation "I" => IdeleGroup (𝓞 K) K

variable [ma : ∀ v : InfinitePlace K, MeasurableSpace v.Completionˣ]
  [mf : ∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)ˣ]
  [mu : ∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletionIntegers K)ˣ]
  [ba : ∀ v : InfinitePlace K, BorelSpace v.Completionˣ]
  [bf : ∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)ˣ]
  [bu : ∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletionIntegers K)ˣ]
  [MeasurableSpace (IdeleGroup (𝓞 K) K)] [BorelSpace (IdeleGroup (𝓞 K) K)]
  (μa : (v : InfinitePlace K) → Measure v.Completionˣ)
  (μf : (v : HeightOneSpectrum (𝓞 K)) → Measure (v.adicCompletion K)ˣ)
  [ha : ∀ v, (μa v).IsHaarMeasure] [hf : ∀ v, (μf v).IsHaarMeasure]

/-- Given local Haar measures with unit mass one off `E`, there is a Haar
measure on the ideles whose pullback to every stage containing `E` is the
product of the given local factors. These pullbacks determine it among all
Borel measures. Its calibration box mass keeps the product of the masses in `E`. -/
public theorem exists_ideleRestrictedProductHaar (E : Finset V)
    (hE : ∀ v ∉ E, finiteCompletionUnitMass K μf v = 1) :
    ∃ μ : Measure I, μ.IsHaarMeasure ∧ μ.Regular ∧
      (∀ ν : Measure I, ν = μ ↔ ∀ S : Finset V, E ⊆ S →
        ν.comap (ideleFiniteStageEmbedding K S) = ideleFiniteStageProduct K μa μf S) ∧
      (∀ B : PositiveCompacts ((v : InfinitePlace K) → v.Completionˣ),
        μ (ideleCalibrationBox K B) = Measure.pi μa B * ∏ v ∈ E, finiteCompletionUnitMass K μf v) := by
  classical
  let : Countable V := countable_ideleFinitePlaces K
  let B := Classical.choice (nonempty_archimedeanUnitBoxes K)
  let Q := ideleCalibrationBox K B
  let : LocallyCompactSpace I := Q.locallyCompactSpace_of_group
  let c := ideleFiniteStageProduct K μa μf E (stageUnitBox K B E)
  let : (ideleFiniteStageProduct K μa μf E).IsHaarMeasure :=
    ideleFiniteStageProduct_isHaar K μa μf E hE
  have hc0 : c ≠ 0 := (Measure.measure_pos_of_nonempty_interior _ (stageUnitBox K B E).interior_nonempty).ne'
  have hcfin : c ≠ ⊤ := (stageUnitBox K B E).isCompact.measure_ne_top
  let μ := c • Measure.haarMeasure Q
  have hμ : μ.IsHaarMeasure := Measure.IsHaarMeasure.smul (Measure.haarMeasure Q) hc0 hcfin
  have hμQ : μ Q = c := by
    rw [smul_apply, Measure.haarMeasure_self, smul_eq_mul, mul_one]
  -- Every stage compares with the same upstairs box, at the same scale.
  have hstage (S : Finset V) (hES : E ⊆ S) :
      μ.comap (ideleFiniteStageEmbedding K S) = ideleFiniteStageProduct K μa μf S := by
    have hS : ∀ v ∉ S, finiteCompletionUnitMass K μf v = 1 := fun v hv ↦ hE v (fun hn ↦ hv (hES hn))
    let R := stageUnitBox K B S
    let j := isOpenEmbedding_ideleFiniteStageEmbedding K S
    let hleft : (μ.comap (ideleFiniteStageEmbedding K S)).IsHaarMeasure :=
      Measure.IsHaarMeasure.comap (mH := inferInstance) μ j
    let hright := ideleFiniteStageProduct_isHaar K μa μf S hS
    have h₁ : μ.comap (ideleFiniteStageEmbedding K S) R = c := by
      rw [j.measurableEmbedding.comap_apply, image_ideleStageUnitBox, hμQ]
    have h₂ : ideleFiniteStageProduct K μa μf S R = c := by
      change ideleFiniteStageProduct K μa μf S (stageUnitBox K B S) =
        ideleFiniteStageProduct K μa μf E (stageUnitBox K B E)
      rw [ideleFiniteStageProduct_unitBox K μa μf B S hS, ideleFiniteStageProduct_unitBox K μa μf B E hE,
        Finset.prod_subset hES (fun v _ hv ↦ hE v hv)]
    calc
      μ.comap (ideleFiniteStageEmbedding K S) = c • Measure.haarMeasure R :=
        (Measure.haarMeasure_unique (μ.comap (ideleFiniteStageEmbedding K S)) R).trans
          (congrArg (· • Measure.haarMeasure R) h₁)
      _ = ideleFiniteStageProduct K μa μf S :=
        ((Measure.haarMeasure_unique (ideleFiniteStageProduct K μa μf S) R).trans
          (congrArg (· • Measure.haarMeasure R) h₂)).symm
  have hreg : μ.Regular := Measure.Regular.smul (μ := Measure.haarMeasure Q) hcfin
  refine ⟨μ, hμ, hreg, ?_, ?_⟩
  · intro ν
    refine ⟨fun h ↦ h.symm ▸ hstage, fun h ↦ ?_⟩
    -- The cofinal stages still cover the group, and a comap specifies the restriction.
    have hcover : (⋃ S : Finset V, range (ideleFiniteStageEmbedding K (E ∪ S))) = univ := by
      apply eq_univ_of_forall fun x ↦ ?_
      have hx : x ∈ ⋃ S : Finset V, range (ideleFiniteStageEmbedding K S) := by
        rw [iUnion_range_ideleFiniteStageEmbedding K]; exact mem_univ _
      obtain ⟨S, hS⟩ := mem_iUnion.mp hx
      refine mem_iUnion.mpr ⟨S, ?_⟩
      rw [range_ideleFiniteStageEmbedding] at hS ⊢
      exact fun v hv ↦ hS v (fun hmem ↦ hv (Finset.mem_union_right _ hmem))
    apply Measure.ext_of_iUnion_eq_univ hcover
    intro S
    let j := (isOpenEmbedding_ideleFiniteStageEmbedding K (E ∪ S)).measurableEmbedding
    have hsub : E ⊆ E ∪ S := Finset.subset_union_left
    rw [← j.map_comap ν, ← j.map_comap μ, h _ hsub, hstage _ hsub]
  · intro D
    -- Evaluate a box of any Archimedean shape in the stage `E`.
    let j := (isOpenEmbedding_ideleFiniteStageEmbedding K E).measurableEmbedding
    rw [← image_ideleStageUnitBox K D E, ← j.comap_apply, hstage E subset_rfl,
      ideleFiniteStageProduct_unitBox K μa μf D E hE]

end Masullo
