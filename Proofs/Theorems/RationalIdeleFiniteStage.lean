module

public import Lemmas.RationalIdeleReal

import Lemmas.RationalAdeleFiniteStage
import Mathlib.Topology.Algebra.Group.Units

/-!
# Open finite stages of the rational ideles

The restricted product in (A.3.2.5), p. 560, uses the finite stages recalled
on p. 556. Over `ℚ` each stage includes all of `ℝˣ`, not just the positive ray.
-/

open Filter NumberField IsDedekindDomain Set Topology
open scoped RestrictedProduct

namespace Masullo

local notation "V" => HeightOneSpectrum (𝓞 ℚ)
local notation "F" v => HeightOneSpectrum.adicCompletion ℚ v
local notation "O" v => HeightOneSpectrum.adicCompletionIntegers ℚ v

/-- The real units, full local field units in `S`, and integral units outside `S`. -/
public abbrev RationalIdeleFiniteStage (S : Finset V) :=
  ℝˣ × (((v : {v // v ∈ S}) → (F v.val)ˣ) × ((v : {v // v ∉ S}) → (O v.val)ˣ))

private def prodCongr {A B C D : Type*} [Monoid A] [Monoid B] [Monoid C] [Monoid D]
    [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C] [TopologicalSpace D]
    (e : A ≃ₜ* B) (f : C ≃ₜ* D) : A × C ≃ₜ* B × D where
  __ := e.toMulEquiv.prodCongr f.toMulEquiv
  __ := e.toHomeomorph.prodCongr f.toHomeomorph

private noncomputable def stageUnits (S : Finset V) :
    (RationalAdeleFiniteStage S)ˣ ≃ₜ* RationalIdeleFiniteStage S :=
  (ContinuousMulEquiv.prodUnits _ _).trans <|
    prodCongr (ContinuousMulEquiv.refl ℝˣ) <|
      (ContinuousMulEquiv.prodUnits _ _).trans <|
        prodCongr ContinuousMulEquiv.piUnits ContinuousMulEquiv.piUnits

/-- The coordinatewise inclusion of a rational finite stage into the actual idele group. -/
public noncomputable def rationalIdeleFiniteStageEmbedding (S : Finset V) :
    RationalIdeleFiniteStage S →* IdeleGroup (𝓞 ℚ) ℚ :=
  (Units.map (rationalAdeleFiniteStageEmbedding S)).comp (stageUnits S).symm.toMonoidHom

public theorem rationalIdeleReal_finiteStageEmbedding (S : Finset V) (x : RationalIdeleFiniteStage S) :
    rationalIdeleReal (rationalIdeleFiniteStageEmbedding S x) = (x.1 : ℝ) :=
  rationalAdeleFiniteStageEmbedding_real S ((stageUnits S).symm x).val

public theorem rationalIdeleFiniteStageEmbedding_finite_mem (S : Finset V)
    (x : RationalIdeleFiniteStage S) (v : V) (hv : v ∈ S) :
    (rationalIdeleFiniteStageEmbedding S x : AdeleRing (𝓞 ℚ) ℚ).2 v = (x.2.1 ⟨v, hv⟩ : F v) :=
  rationalAdeleFiniteStageEmbedding_finite_mem S ((stageUnits S).symm x).val v hv

public theorem rationalIdeleFiniteStageEmbedding_finite_notMem (S : Finset V)
    (x : RationalIdeleFiniteStage S) (v : V) (hv : v ∉ S) :
    (rationalIdeleFiniteStageEmbedding S x : AdeleRing (𝓞 ℚ) ℚ).2 v = ((x.2.2 ⟨v, hv⟩).val : F v) :=
  rationalAdeleFiniteStageEmbedding_finite_notMem S ((stageUnits S).symm x).val v hv

private theorem mem_range_units_map_iff {M N : Type*} [Monoid M] [Monoid N]
    {f : M →* N} (hf : Function.Injective f) (a : Nˣ) :
    a ∈ range (Units.map f) ↔ (a : N) ∈ range f ∧ (↑(a⁻¹) : N) ∈ range f := by
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨⟨x.val, rfl⟩, ⟨x.inv, rfl⟩⟩
  · rintro ⟨⟨x, hx⟩, ⟨y, hy⟩⟩
    have hxy : x * y = 1 := hf (by rw [map_mul, hx, hy, Units.mul_inv, map_one])
    have hyx : y * x = 1 := hf (by rw [map_mul, hy, hx, Units.inv_mul, map_one])
    exact ⟨⟨x, y, hxy, hyx⟩, Units.ext hx⟩

/-- A rational idele is in the stage exactly when its value and its inverse are
integral outside `S`. There is no real sign restriction. -/
public theorem range_rationalIdeleFiniteStageEmbedding (S : Finset V) :
    range (rationalIdeleFiniteStageEmbedding S) =
      {a : IdeleGroup (𝓞 ℚ) ℚ | ∀ v ∉ S,
        (a : AdeleRing (𝓞 ℚ) ℚ).2 v ∈ (O v) ∧ (↑(a⁻¹) : AdeleRing (𝓞 ℚ) ℚ).2 v ∈ O v} := by
  change range (Units.map (rationalAdeleFiniteStageEmbedding S) ∘ (stageUnits S).symm) = _
  rw [range_comp, (stageUnits S).symm.surjective.range_eq, image_univ]
  ext a
  rw [mem_range_units_map_iff (isEmbedding_rationalAdeleFiniteStageEmbedding S).injective,
    range_rationalAdeleFiniteStageEmbedding]
  simp only [mem_ofPred_eq, imp_and, forall_and]

/-- Every rational finite stage carries the topology induced from the idele group
and has open image in that group. -/
public theorem isOpenEmbedding_rationalIdeleFiniteStageEmbedding (S : Finset V) :
    IsOpenEmbedding (rationalIdeleFiniteStageEmbedding S) := by
  refine ⟨(isEmbedding_rationalAdeleFiniteStageEmbedding S).units_map.comp
    (stageUnits S).symm.toHomeomorph.isEmbedding, ?_⟩
  have h : IsOpen {b : FiniteAdeleRing (𝓞 ℚ) ℚ | ∀ v ∉ S, b v ∈ O v} :=
    RestrictedProduct.isOpen_forall_imp_mem (fun v ↦ Valued.isOpen_valuationSubring (F v))
  rw [range_rationalIdeleFiniteStageEmbedding]
  have hfin : Continuous (fun a : IdeleGroup (𝓞 ℚ) ℚ ↦ (a : AdeleRing (𝓞 ℚ) ℚ).2) :=
    continuous_snd.comp Units.continuous_val
  simp only [imp_and, forall_and, ofPred_and]
  exact (h.preimage hfin).inter (h.preimage (hfin.comp continuous_inv))

/-- Every rational idele belongs to a finite stage: Enlarge the stage to include
all places at which its value or its inverse fails to be integral. -/
public theorem iUnion_range_rationalIdeleFiniteStageEmbedding :
    (⋃ S : Finset V, range (rationalIdeleFiniteStageEmbedding S)) = univ := by
  refine eq_univ_of_forall fun a ↦ ?_
  let b := (a : AdeleRing (𝓞 ℚ) ℚ).2
  let c := (↑(a⁻¹) : AdeleRing (𝓞 ℚ) ℚ).2
  have h : (∀ᶠ v in cofinite, b v ∈ (O v) ∧ c v ∈ O v) := b.property.and c.property
  let exceptions := {v : V | ¬(b v ∈ (O v) ∧ c v ∈ O v)}
  have hfinite : exceptions.Finite := eventually_cofinite.mp h
  refine mem_iUnion.mpr ⟨hfinite.toFinset, ?_⟩
  rw [range_rationalIdeleFiniteStageEmbedding]
  intro v hv
  by_contra hnot
  exact hv (hfinite.mem_toFinset.mpr hnot)

end Masullo
