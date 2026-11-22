module

public import Mathlib.NumberTheory.NumberField.AdeleRing

/-! # Finite stages of the adele ring

Coordinates outside the chosen finite set are integral. This is the underlying
adele-ring construction used to embed the corresponding stage of the ideles.
-/

open NumberField IsDedekindDomain Filter Set Topology
open scoped RestrictedProduct

namespace Masullo

variable (K : Type*) [Field K] [NumberField K]

local notation "V" => HeightOneSpectrum (𝓞 K)
local notation "F" v => HeightOneSpectrum.adicCompletion K v
local notation "O" v => HeightOneSpectrum.adicCompletionIntegers K v

private abbrev FinitePart (S : Finset V) :=
  ((v : {v // v ∈ S}) → F v.val) × ((v : {v // v ∉ S}) → O v.val)

/-- A stage with the whole infinite adele ring and with integrality imposed off `S`. -/
public abbrev AdeleFiniteStage (S : Finset V) :=
  InfiniteAdeleRing K × (((v : {v // v ∈ S}) → F v.val) × ((v : {v // v ∉ S}) → O v.val))

private noncomputable def glue (S : Finset V) : FinitePart K S → (v : V) → F v :=
  open Classical in
  fun x v ↦ if h : v ∈ S then x.1 ⟨v, h⟩ else (x.2 ⟨v, h⟩ : F v)

private theorem isEmbedding_glue (S : Finset V) : IsEmbedding (glue K S) := by
  classical
  let e := Homeomorph.piEquivPiSubtypeProd (· ∈ S) (fun v ↦ F v)
  have h : IsEmbedding (fun x : (v : {v // v ∉ S}) → O v.val ↦ fun v ↦ (x v : F v.val)) :=
    IsEmbedding.piMap fun _ ↦ IsEmbedding.subtypeVal
  convert e.symm.isEmbedding.comp (IsEmbedding.id.prodMap h) using 1
  funext x v
  by_cases hv : v ∈ S <;> simp [glue, e, hv, Homeomorph.piEquivPiSubtypeProd, Equiv.piEquivPiSubtypeProd]

omit [NumberField K] in
private theorem cofinite_le_stage (S : Finset V) : cofinite ≤ 𝓟 (↑S : Set V)ᶜ := by
  rw [le_principal_iff, mem_cofinite, compl_compl]
  exact S.finite_toSet

private noncomputable def finitePart (S : Finset V) (x : FinitePart K S) :
    FiniteAdeleRing (𝓞 K) K :=
  RestrictedProduct.inclusion _ _ (cofinite_le_stage K S)
    ⟨glue K S x, fun v hv ↦ by simp [glue, show v ∉ S from hv]⟩

/-- Assemble the infinite and finite coordinates into an adele. -/
public noncomputable def adeleFiniteStageEmbedding (S : Finset V) :
    AdeleFiniteStage K S →* AdeleRing (𝓞 K) K where
  toFun x := (x.1, finitePart K S x.2)
  map_one' := by
    refine Prod.ext rfl (FiniteAdeleRing.ext K fun v ↦ ?_)
    change glue K S (1, 1) v = 1
    by_cases hv : v ∈ S <;> simp [glue, hv]
  map_mul' x y := by
    refine Prod.ext rfl (FiniteAdeleRing.ext K fun v ↦ ?_)
    change glue K S (x.2 * y.2) v = glue K S x.2 v * glue K S y.2 v
    by_cases hv : v ∈ S <;> simp [glue, hv]

public theorem adeleFiniteStageEmbedding_infinite (S : Finset V) (x : AdeleFiniteStage K S) :
    (adeleFiniteStageEmbedding K S x).1 = x.1 := by
  rfl

public theorem adeleFiniteStageEmbedding_finite_mem (S : Finset V)
    (x : AdeleFiniteStage K S) (v : V) (hv : v ∈ S) :
    (adeleFiniteStageEmbedding K S x).2 v = x.2.1 ⟨v, hv⟩ := by
  change glue K S x.2 v = _
  simp [glue, hv]

public theorem adeleFiniteStageEmbedding_finite_notMem (S : Finset V)
    (x : AdeleFiniteStage K S) (v : V) (hv : v ∉ S) :
    (adeleFiniteStageEmbedding K S x).2 v = (x.2.2 ⟨v, hv⟩ : F v) := by
  change glue K S x.2 v = _
  simp [glue, hv]

public theorem isEmbedding_adeleFiniteStageEmbedding (S : Finset V) :
    IsEmbedding (adeleFiniteStageEmbedding K S) := by
  have hfin : IsEmbedding (finitePart K S) := by
    refine (RestrictedProduct.isEmbedding_inclusion_principal (cofinite_le_stage K S)).comp ?_
    exact .of_comp (RestrictedProduct.continuous_rng_of_principal.mpr (isEmbedding_glue K S).continuous)
      RestrictedProduct.continuous_coe (isEmbedding_glue K S)
  exact IsEmbedding.id.prodMap hfin

public theorem range_adeleFiniteStageEmbedding (S : Finset V) :
    range (adeleFiniteStageEmbedding K S) =
      {a | ∀ v ∉ S, a.2 v ∈ O v} := by
  ext a
  constructor
  · rintro ⟨x, rfl⟩ v hv
    rw [adeleFiniteStageEmbedding_finite_notMem K S x v hv]
    exact (x.2.2 ⟨v, hv⟩).property
  · intro ha
    let x : AdeleFiniteStage K S :=
      (a.1, (fun v ↦ a.2 v.val, fun v ↦ ⟨a.2 v.val, ha v.val v.property⟩))
    refine ⟨x, Prod.ext rfl (FiniteAdeleRing.ext K fun v ↦ ?_)⟩
    change glue K S x.2 v = a.2 v
    by_cases hv : v ∈ S <;> simp [glue, hv, x]

end Masullo
