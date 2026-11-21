module

public import Lemmas.RationalIdeleReal

/-! # Finite stages of the rational adele ring

Coordinates outside the chosen finite set are integral. This is the underlying
adele-ring construction used to embed the corresponding stage of the ideles.
-/

open NumberField IsDedekindDomain Filter Set Topology
open scoped RestrictedProduct

namespace Masullo

local notation "V" => HeightOneSpectrum (𝓞 ℚ)
local notation "F" v => HeightOneSpectrum.adicCompletion ℚ v
local notation "O" v => HeightOneSpectrum.adicCompletionIntegers ℚ v

private abbrev FinitePart (S : Finset V) :=
  ((v : {v // v ∈ S}) → F v.val) × ((v : {v // v ∉ S}) → O v.val)

/-- The finite adele stage with the real factor and with integrality imposed off `S`. -/
public abbrev RationalAdeleFiniteStage (S : Finset V) :=
  ℝ × (((v : {v // v ∈ S}) → F v.val) × ((v : {v // v ∉ S}) → O v.val))

private noncomputable def realEquiv : InfiniteAdeleRing ℚ ≃+* ℝ :=
  (RingEquiv.piUnique InfinitePlace.Completion).trans
    (InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace)

private noncomputable def realHomeomorph : InfiniteAdeleRing ℚ ≃ₜ ℝ :=
  (Homeomorph.piUnique InfinitePlace.Completion).trans
    (InfinitePlace.Completion.isometryEquivRealOfIsReal Rat.isReal_infinitePlace).toHomeomorph

private noncomputable def glue (S : Finset V) : FinitePart S → (v : V) → F v :=
  open Classical in
  fun x v ↦ if h : v ∈ S then x.1 ⟨v, h⟩ else (x.2 ⟨v, h⟩ : F v)

private theorem isEmbedding_glue (S : Finset V) : IsEmbedding (glue S) := by
  classical
  let e := Homeomorph.piEquivPiSubtypeProd (· ∈ S) (fun v ↦ F v)
  have h : IsEmbedding (fun x : (v : {v // v ∉ S}) → O v.val ↦ fun v ↦ (x v : F v.val)) :=
    IsEmbedding.piMap fun _ ↦ IsEmbedding.subtypeVal
  convert e.symm.isEmbedding.comp (IsEmbedding.id.prodMap h) using 1
  funext x v
  by_cases hv : v ∈ S <;> simp [glue, e, hv, Homeomorph.piEquivPiSubtypeProd, Equiv.piEquivPiSubtypeProd]

private theorem cofinite_le_stage (S : Finset V) : cofinite ≤ 𝓟 (↑S : Set V)ᶜ := by
  rw [le_principal_iff, mem_cofinite, compl_compl]
  exact S.finite_toSet

private noncomputable def finitePart (S : Finset V) (x : FinitePart S) :
    FiniteAdeleRing (𝓞 ℚ) ℚ :=
  RestrictedProduct.inclusion _ _ (cofinite_le_stage S)
    ⟨glue S x, fun v hv ↦ by simp [glue, show v ∉ S from hv]⟩

/-- Assemble the real and finite coordinates into an adele. -/
public noncomputable def rationalAdeleFiniteStageEmbedding (S : Finset V) :
    RationalAdeleFiniteStage S →* AdeleRing (𝓞 ℚ) ℚ where
  toFun x := (realEquiv.symm x.1, finitePart S x.2)
  map_one' := by
    refine Prod.ext (map_one _) (FiniteAdeleRing.ext ℚ fun v ↦ ?_)
    change glue S (1, 1) v = 1
    by_cases hv : v ∈ S <;> simp [glue, hv]
  map_mul' x y := by
    refine Prod.ext (map_mul _ _ _) (FiniteAdeleRing.ext ℚ fun v ↦ ?_)
    change glue S (x.2 * y.2) v = glue S x.2 v * glue S y.2 v
    by_cases hv : v ∈ S <;> simp [glue, hv]

public theorem rationalAdeleFiniteStageEmbedding_real (S : Finset V) (x : RationalAdeleFiniteStage S) :
    InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace
      ((rationalAdeleFiniteStageEmbedding S x).1 Rat.infinitePlace) = x.1 :=
  realEquiv.apply_symm_apply _

public theorem rationalAdeleFiniteStageEmbedding_finite_mem (S : Finset V)
    (x : RationalAdeleFiniteStage S) (v : V) (hv : v ∈ S) :
    (rationalAdeleFiniteStageEmbedding S x).2 v = x.2.1 ⟨v, hv⟩ := by
  change glue S x.2 v = _
  simp [glue, hv]

public theorem rationalAdeleFiniteStageEmbedding_finite_notMem (S : Finset V)
    (x : RationalAdeleFiniteStage S) (v : V) (hv : v ∉ S) :
    (rationalAdeleFiniteStageEmbedding S x).2 v = (x.2.2 ⟨v, hv⟩ : F v) := by
  change glue S x.2 v = _
  simp [glue, hv]

public theorem isEmbedding_rationalAdeleFiniteStageEmbedding (S : Finset V) :
    IsEmbedding (rationalAdeleFiniteStageEmbedding S) := by
  have hfin : IsEmbedding (finitePart S) := by
    refine (RestrictedProduct.isEmbedding_inclusion_principal (cofinite_le_stage S)).comp ?_
    exact .of_comp (RestrictedProduct.continuous_rng_of_principal.mpr (isEmbedding_glue S).continuous)
      RestrictedProduct.continuous_coe (isEmbedding_glue S)
  exact realHomeomorph.symm.isEmbedding.prodMap hfin

public theorem range_rationalAdeleFiniteStageEmbedding (S : Finset V) :
    range (rationalAdeleFiniteStageEmbedding S) =
      {a | ∀ v ∉ S, a.2 v ∈ O v} := by
  ext a
  constructor
  · rintro ⟨x, rfl⟩ v hv
    rw [rationalAdeleFiniteStageEmbedding_finite_notMem S x v hv]
    exact (x.2.2 ⟨v, hv⟩).property
  · intro ha
    let x : RationalAdeleFiniteStage S :=
      (realEquiv a.1, (fun v ↦ a.2 v.val, fun v ↦ ⟨a.2 v.val, ha v.val v.property⟩))
    refine ⟨x, Prod.ext (realEquiv.symm_apply_apply _) (FiniteAdeleRing.ext ℚ fun v ↦ ?_)⟩
    change glue S x.2 v = a.2 v
    by_cases hv : v ∈ S <;> simp [glue, hv, x]

end Masullo
