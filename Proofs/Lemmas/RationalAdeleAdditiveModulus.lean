module

public import Theorems.RationalAdeleFiniteStageHaar
public import Theorems.RationalIdeleFiniteStage

import Lemmas.RationalLocalAdditiveModulus
import Mathlib.Algebra.Order.Group.Pointwise.Interval

/-! # Calibration of rational additive Haar under idele dilation -/

open NumberField IsDedekindDomain HeightOneSpectrum MeasureTheory Set Topology TopologicalSpace
open scoped BigOperators

namespace Masullo

local notation "V" => HeightOneSpectrum (𝓞 ℚ)
local notation "A" => AdeleRing (𝓞 ℚ) ℚ
local notation "F" v => adicCompletion ℚ v
local notation "O" v => adicCompletionIntegers ℚ v

/-- The rational adeles are second countable by their countable open stage cover. -/
public theorem secondCountableTopology_rationalAdeles : SecondCountableTopology A := by
  let : Countable V := Function.Injective.countable Rat.HeightOneSpectrum.primesEquiv.injective
  let (S : Finset V) : SecondCountableTopology (range (rationalAdeleFiniteStageEmbedding S)) :=
    (isEmbedding_rationalAdeleFiniteStageEmbedding S).toHomeomorph.symm.secondCountableTopology
  exact secondCountableTopology_of_countable_cover
    (fun S ↦ (isOpenEmbedding_rationalAdeleFiniteStageEmbedding S).isOpen_range)
    iUnion_range_rationalAdeleFiniteStageEmbedding

private theorem stage_norm {S : Finset V} (u : (RationalAdeleFiniteStage S)ˣ) :
    ideleNorm (Units.map (rationalAdeleFiniteStageEmbedding S) u) =
      |u.val.1| * ∏ v : {v // v ∈ S}, ‖u.val.2.1 v‖ := by
  let g := Units.map (rationalAdeleFiniteStageEmbedding S) u
  let f : V → ℝ := fun v ↦ ‖(g : A).2 v‖
  have hsupport : Function.mulSupport f ⊆ (S : Set V) := by
    intro v hv
    by_contra h
    have hmul : (u.val.2.2 ⟨v, h⟩ : F v) * (u.inv.2.2 ⟨v, h⟩ : F v) = 1 :=
      congrArg (fun y : RationalAdeleFiniteStage S ↦ (y.2.2 ⟨v, h⟩ : F v)) u.val_inv
    have hle (a : O v) : ‖(a : F v)‖ ≤ 1 := by
      rw [Valued.toNormedField.norm_le_one_iff, ← mem_adicCompletionIntegers]
      exact a.property
    have hnorm : ‖(u.val.2.2 ⟨v, h⟩ : F v)‖ = 1 := by
      refine le_antisymm (hle _) ?_
      calc
        1 = ‖(u.val.2.2 ⟨v, h⟩ : F v)‖ * ‖(u.inv.2.2 ⟨v, h⟩ : F v)‖ := by
          rw [← norm_mul, hmul, norm_one]
        _ ≤ _ := mul_le_of_le_one_right (norm_nonneg _) (hle _)
    apply hv
    change ‖(rationalAdeleFiniteStageEmbedding S u.val).2 v‖ = 1
    rwa [rationalAdeleFiniteStageEmbedding_finite_notMem S u.val v h]
  change ideleNorm g = _
  rw [ideleNorm_apply, AdeleRing.norm_apply_of_isUnit g.isUnit]
  change (∏ w : InfinitePlace ℚ, ‖(g : A).1 w‖ ^ w.mult) * (∏ᶠ v, f v) = _
  rw [Fintype.prod_subsingleton _ Rat.infinitePlace, Rat.isReal_infinitePlace.mult_eq_one, pow_one,
    finprod_eq_prod_of_mulSupport_subset f hsupport, ← Finset.prod_coe_sort]
  congr 1
  · rw [← rationalAdeleFiniteStageEmbedding_real S u.val, ← Real.norm_eq_abs]
    exact (Isometry.norm_map_of_map_zero
      (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal Rat.isReal_infinitePlace)
      (map_zero _) _).symm
  · apply Finset.prod_congr rfl
    intro v _
    simp only [f, g, Units.coe_map, rationalAdeleFiniteStageEmbedding_finite_mem S u.val v v.property]

private theorem measure_dilated_stage_strip {S : Finset V} (u : (RationalAdeleFiniteStage S)ˣ) :
    rationalAdeleFiniteStageHaar S ((fun x : RationalAdeleFiniteStage S ↦ u.val * x) ''
      (rationalAdeleFiniteStageClosedUnitStrip S : Set (RationalAdeleFiniteStage S))) =
      ENNReal.ofReal (|u.val.1| * ∏ v : {v // v ∈ S}, ‖u.val.2.1 v‖) := by
  let p : RationalAdeleFiniteStage S →* ((v : {v // v ∉ S}) → O v.val) :=
    (MonoidHom.snd _ _).comp (MonoidHom.snd _ _)
  let uOut := Units.map p u
  have hOut : (fun x ↦ u.val.2.2 * x) '' univ = univ := by
    rw [image_univ]
    exact uOut.mulLeft.surjective.range_eq
  rw [rationalAdeleFiniteStageClosedUnitStrip_eq]
  change rationalAdeleFiniteStageHaar S
    (Prod.map (u.val.1 * ·) (Prod.map (Pi.map (fun v a ↦ u.val.2.1 v * a))
      (u.val.2.2 * ·)) '' _) = _
  rw [prodMap_image_prod, prodMap_image_prod, piMap_image_univ_pi, hOut,
    ← uIcc_of_le (zero_le_one : (0 : ℝ) ≤ 1), image_const_mul_uIcc, mul_zero, mul_one]
  rw [rationalAdeleFiniteStageHaar, Measure.prod_prod, Measure.prod_prod, Measure.pi_pi,
    measure_univ, mul_one, uIcc, Real.volume_Icc, max_sub_min_eq_abs, sub_zero,
    ENNReal.ofReal_mul (abs_nonneg _), ENNReal.ofReal_prod_of_nonneg (fun _ _ ↦ norm_nonneg _)]
  congr 1
  apply Finset.prod_congr rfl
  intro v _
  apply rationalLocalFieldAddHaar_dilate_integers
  exact left_ne_zero_of_mul_eq_one
    (congrArg (fun y : RationalAdeleFiniteStage S ↦ y.2.1 v) u.val_inv)

set_option linter.concreteInstances false

variable [MeasurableSpace A] [BorelSpace A]

/-- The dilated closed unit strip has mass equal to the idelic norm. -/
public theorem rationalAdeleAddHaar_dilate_closedUnitStrip (g : IdeleGroup (𝓞 ℚ) ℚ) :
    rationalAdeleAddHaar ((fun x : A ↦ (g : A) * x) '' (rationalAdeleClosedUnitStrip : Set A)) =
      ENNReal.ofReal (ideleNorm g) := by
  obtain ⟨S, u, rfl⟩ := exists_rationalAdeleFiniteStage_unit g
  let j := rationalAdeleFiniteStageEmbedding S
  have h : ((fun x : A ↦ (Units.map j u : A) * x) ∘ j) =
      j ∘ (fun x ↦ u.val * x) := funext fun x ↦ (map_mul j u.val x).symm
  rw [← image_rationalAdeleFiniteStageClosedUnitStrip S, ← image_comp]
  change rationalAdeleAddHaar (((fun x : A ↦ (Units.map j u : A) * x) ∘ j) '' _) = _
  rw [h, image_comp,
    ← (isOpenEmbedding_rationalAdeleFiniteStageEmbedding S).measurableEmbedding.comap_apply,
    comap_rationalAdeleAddHaar_finiteStage, stage_norm]
  exact measure_dilated_stage_strip u

end Masullo
