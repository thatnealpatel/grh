module

public import Lemmas.AdeleFiniteStage
import Mathlib.Topology.Algebra.Group.Units

/-!
# Open finite stages of the ideles

Lemma A.1.3.3, p. 541, identifies the idelic topology of Definition A.1.3.1
with the restricted product topology. We verify the stage description used in
(A.3.2.5), p. 560, in the actual adele units. In particular, openness is for
the topology using both an adele value and its inverse.
-/

open Filter NumberField IsDedekindDomain Set Topology
open scoped RestrictedProduct

namespace Masullo

variable (K : Type*) [Field K] [NumberField K]

local notation "V" => HeightOneSpectrum (𝓞 K)
local notation "F" v => HeightOneSpectrum.adicCompletion K v
local notation "O" v => HeightOneSpectrum.adicCompletionIntegers K v

/-- All infinite-place units, full local field units in `S`, and integral units outside `S`. -/
public abbrev IdeleFiniteStage (S : Finset V) :=
  ((v : InfinitePlace K) → v.Completionˣ) ×
    (((v : {v // v ∈ S}) → (F v.val)ˣ) × ((v : {v // v ∉ S}) → (O v.val)ˣ))

private def prodCongr {A B C D : Type*} [Monoid A] [Monoid B] [Monoid C] [Monoid D]
    [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C] [TopologicalSpace D]
    (e : A ≃ₜ* B) (f : C ≃ₜ* D) : A × C ≃ₜ* B × D where
  __ := e.toMulEquiv.prodCongr f.toMulEquiv
  __ := e.toHomeomorph.prodCongr f.toHomeomorph

private noncomputable def stageUnits (S : Finset V) :
    (AdeleFiniteStage K S)ˣ ≃ₜ* IdeleFiniteStage K S :=
  (ContinuousMulEquiv.prodUnits _ _).trans <|
    prodCongr ContinuousMulEquiv.piUnits <|
      (ContinuousMulEquiv.prodUnits _ _).trans <|
        prodCongr ContinuousMulEquiv.piUnits ContinuousMulEquiv.piUnits

/-- The coordinatewise inclusion of a finite stage into the actual idele group. -/
public noncomputable def ideleFiniteStageEmbedding (S : Finset V) :
    IdeleFiniteStage K S →* IdeleGroup (𝓞 K) K :=
  (Units.map (adeleFiniteStageEmbedding K S)).comp (stageUnits K S).symm.toMonoidHom

public theorem ideleFiniteStageEmbedding_infinite (S : Finset V) (x : IdeleFiniteStage K S)
    (v : InfinitePlace K) :
    (ideleFiniteStageEmbedding K S x : AdeleRing (𝓞 K) K).1 v = (x.1 v : v.Completion) :=
  congrArg (fun a : InfiniteAdeleRing K ↦ a v)
    (adeleFiniteStageEmbedding_infinite K S ((stageUnits K S).symm x).val)

public theorem ideleFiniteStageEmbedding_finite_mem (S : Finset V)
    (x : IdeleFiniteStage K S) (v : V) (hv : v ∈ S) :
    (ideleFiniteStageEmbedding K S x : AdeleRing (𝓞 K) K).2 v = (x.2.1 ⟨v, hv⟩ : F v) :=
  adeleFiniteStageEmbedding_finite_mem K S ((stageUnits K S).symm x).val v hv

public theorem ideleFiniteStageEmbedding_finite_notMem (S : Finset V)
    (x : IdeleFiniteStage K S) (v : V) (hv : v ∉ S) :
    (ideleFiniteStageEmbedding K S x : AdeleRing (𝓞 K) K).2 v = ((x.2.2 ⟨v, hv⟩).val : F v) :=
  adeleFiniteStageEmbedding_finite_notMem K S ((stageUnits K S).symm x).val v hv

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

/-- An idele is in the stage exactly when its value and its inverse are
integral outside `S`. All infinite coordinates remain unrestricted. -/
public theorem range_ideleFiniteStageEmbedding (S : Finset V) :
    range (ideleFiniteStageEmbedding K S) =
      {a : IdeleGroup (𝓞 K) K | ∀ v ∉ S,
        (a : AdeleRing (𝓞 K) K).2 v ∈ (O v) ∧ (↑(a⁻¹) : AdeleRing (𝓞 K) K).2 v ∈ O v} := by
  change range (Units.map (adeleFiniteStageEmbedding K S) ∘ (stageUnits K S).symm) = _
  rw [range_comp, (stageUnits K S).symm.surjective.range_eq, image_univ]
  ext a
  rw [mem_range_units_map_iff (isEmbedding_adeleFiniteStageEmbedding K S).injective,
    range_adeleFiniteStageEmbedding]
  simp only [mem_ofPred_eq, imp_and, forall_and]

/-- Every finite stage carries the topology induced from the idele group
and has open image in that group. -/
public theorem isOpenEmbedding_ideleFiniteStageEmbedding (S : Finset V) :
    IsOpenEmbedding (ideleFiniteStageEmbedding K S) := by
  refine ⟨(isEmbedding_adeleFiniteStageEmbedding K S).units_map.comp
    (stageUnits K S).symm.toHomeomorph.isEmbedding, ?_⟩
  have h : IsOpen {b : FiniteAdeleRing (𝓞 K) K | ∀ v ∉ S, b v ∈ O v} :=
    RestrictedProduct.isOpen_forall_imp_mem (fun v ↦ Valued.isOpen_valuationSubring (F v))
  rw [range_ideleFiniteStageEmbedding K]
  have hfin : Continuous (fun a : IdeleGroup (𝓞 K) K ↦ (a : AdeleRing (𝓞 K) K).2) :=
    continuous_snd.comp Units.continuous_val
  simp only [imp_and, forall_and, ofPred_and]
  exact (h.preimage hfin).inter (h.preimage (hfin.comp continuous_inv))

/-- Every idele belongs to a finite stage: Enlarge the stage to include
all places at which its value or its inverse fails to be integral. -/
public theorem iUnion_range_ideleFiniteStageEmbedding :
    (⋃ S : Finset V, range (ideleFiniteStageEmbedding K S)) = univ := by
  refine eq_univ_of_forall fun a ↦ ?_
  let b := (a : AdeleRing (𝓞 K) K).2
  let c := (↑(a⁻¹) : AdeleRing (𝓞 K) K).2
  have h : (∀ᶠ v in cofinite, b v ∈ (O v) ∧ c v ∈ O v) := b.property.and c.property
  let exceptions := {v : V | ¬(b v ∈ (O v) ∧ c v ∈ O v)}
  have hfinite : exceptions.Finite := eventually_cofinite.mp h
  refine mem_iUnion.mpr ⟨hfinite.toFinset, ?_⟩
  rw [range_ideleFiniteStageEmbedding K]
  intro v hv
  by_contra hnot
  exact hv (hfinite.mem_toFinset.mpr hnot)

end Masullo
