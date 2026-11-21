module

public import Theorems.RationalAdeleDenominators
public import Theorems.RationalAdeleCharacter

import Lemmas.RationalAdeleFiniteStage
import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.Algebra.Order.Floor.Semiring

/-! # The open integral-finite additive stage over ℚ -/

open NumberField IsDedekindDomain Set Topology
open scoped ComplexConjugate RestrictedProduct

namespace Masullo

local notation "V" => HeightOneSpectrum (𝓞 ℚ)
local notation "A" => AdeleRing (𝓞 ℚ) ℚ
local notation:max "O" v:max => HeightOneSpectrum.adicCompletionIntegers ℚ v
local notation "ι" => algebraMap ℚ A

/-- The open additive subgroup with arbitrary real coordinate and integral finite coordinates. -/
@[expose]
public def rationalIntegralAdeles : AddSubgroup A where
  carrier := {a | ∀ v : V, a.2 v ∈ O v}
  zero_mem' v := (O v).zero_mem
  add_mem' ha hb v := (O v).add_mem _ _ (ha v) (hb v)
  neg_mem' ha v := (O v).toSubring.neg_mem (ha v)

public theorem isOpen_rationalIntegralAdeles : IsOpen (rationalIntegralAdeles : Set A) :=
  (RestrictedProduct.isOpen_forall_mem
    (fun v : V ↦ Valued.isOpen_valuationSubring (v.adicCompletion ℚ))).preimage continuous_snd

/-- The diagonal image of ℚ in the additive adele group. -/
@[expose]
public noncomputable def rationalDiagonal : AddSubgroup A := (ι).toAddMonoidHom.range

/-- Integer casts lie in the integral-finite stage. -/
public theorem intCast_mem_rationalIntegralAdeles (z : ℤ) : (z : A) ∈ rationalIntegralAdeles :=
  fun v ↦ intCast_mem (O v) z

/-- The integer diagonal as a homomorphism into the integral-finite stage. -/
@[expose]
public noncomputable def rationalIntegralIntHom : ℤ →+ rationalIntegralAdeles :=
  (Int.castAddHom A).codRestrict rationalIntegralAdeles intCast_mem_rationalIntegralAdeles

/-- The diagonal integers inside the integral-finite stage. -/
@[expose]
public noncomputable def rationalIntegralDiagonal : AddSubgroup rationalIntegralAdeles := rationalIntegralIntHom.range

public theorem mem_rationalIntegralDiagonal_iff (w : rationalIntegralAdeles) :
    w ∈ rationalIntegralDiagonal ↔ ∃ z : ℤ, (w : A) = (z : A) := by
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨z, rfl⟩
  · rintro ⟨z, hz⟩
    exact ⟨z, Subtype.ext hz.symm⟩

/-- A rational diagonal adele has all finite coordinates integral exactly when it is an integer. -/
public theorem algebraMap_mem_rationalIntegralAdeles_iff (q : ℚ) :
    ι q ∈ rationalIntegralAdeles ↔ ∃ z : ℤ, q = z := by
  constructor
  · intro h
    apply exists_int_of_all_rationalPadicPhases_eq_one
    intro p
    let e := Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)
    let v := e.symm p
    have hv := (rationalLocalFiniteAddChar_eq_one_iff v _).2 (h v)
    change rationalLocalFiniteAddChar v (algebraMap ℚ (v.adicCompletion ℚ) q) = 1 at hv
    rw [rationalLocalFiniteAddChar_rat, show Rat.HeightOneSpectrum.primesEquiv v = p from
      e.apply_symm_apply p] at hv
    exact star_injective (hv.trans (map_one (starRingEnd ℂ)).symm)
  · rintro ⟨z, rfl⟩
    rw [map_intCast]
    exact intCast_mem_rationalIntegralAdeles z

/-- The compact product of the local integral rings over the finite places of ℚ. -/
public abbrev RationalFiniteIntegers := (v : V) → O v

private abbrev IntegralCoordinates := ℝ × RationalFiniteIntegers

private noncomputable def emptyStage (x : IntegralCoordinates) : RationalAdeleFiniteStage ∅ :=
  (x.1, (fun v ↦ False.elim (Finset.notMem_empty v.val v.property), fun v ↦ x.2 v.val))

private noncomputable def assemble (x : IntegralCoordinates) : rationalIntegralAdeles :=
  ⟨rationalAdeleFiniteStageEmbedding ∅ (emptyStage x), fun v ↦ by
    rw [rationalAdeleFiniteStageEmbedding_finite_notMem _ _ v (Finset.notMem_empty v)]
    exact (x.2 v).property⟩

private theorem isEmbedding_assemble : IsEmbedding assemble := by
  let g := rationalAdeleFiniteStageEmbedding (∅ : Finset V)
  let forget : RationalAdeleFiniteStage ∅ → IntegralCoordinates :=
    fun x ↦ (x.1, fun v ↦ x.2.2 ⟨v, Finset.notMem_empty v⟩)
  have hforget : Continuous forget := by fun_prop
  have hleft : Function.LeftInverse forget emptyStage := fun _ ↦ rfl
  have hstage : Continuous emptyStage := by
    refine continuous_fst.prodMk ((continuous_pi fun v ↦ ?_).prodMk
      (continuous_pi fun v ↦ (continuous_apply v.val).comp continuous_snd))
    exact False.elim (Finset.notMem_empty v.val v.property)
  have he : IsEmbedding emptyStage := hleft.isEmbedding hforget hstage
  exact .of_comp (f := assemble) ((isEmbedding_rationalAdeleFiniteStageEmbedding ∅).continuous.comp
    he.continuous |>.subtype_mk _) continuous_subtype_val
    ((isEmbedding_rationalAdeleFiniteStageEmbedding ∅).comp he : IsEmbedding (g ∘ emptyStage))

private theorem surjective_assemble : Function.Surjective assemble := by
  intro w
  have h : (w : A) ∈ range (rationalAdeleFiniteStageEmbedding ∅) := by
    rw [range_rationalAdeleFiniteStageEmbedding]
    exact fun v _ ↦ w.property v
  obtain ⟨x, hx⟩ := h
  refine ⟨(x.1, fun v ↦ x.2.2 ⟨v, Finset.notMem_empty v⟩), Subtype.ext ?_⟩
  refine (congrArg (rationalAdeleFiniteStageEmbedding ∅) ?_).trans hx
  exact Prod.ext rfl (Prod.ext (funext fun v ↦ False.elim (Finset.notMem_empty v.val v.property)) rfl)

/-- The integral-finite stage carries the product topology of the real line and the
local integral rings, not the full product topology on the ambient adele ring. -/
public noncomputable def rationalIntegralAdelesHomeomorph :
    (ℝ × ((v : V) → v.adicCompletionIntegers ℚ)) ≃ₜ rationalIntegralAdeles :=
  isEmbedding_assemble.toHomeomorphOfSurjective surjective_assemble

public theorem rationalIntegralAdelesHomeomorph_real (x : ℝ × ((v : V) → O v)) :
    rationalAdeleReal (rationalIntegralAdelesHomeomorph x : A) = x.1 := by
  rw [rationalAdeleReal_apply]
  exact rationalAdeleFiniteStageEmbedding_real ∅ (emptyStage x)

public theorem rationalIntegralAdelesHomeomorph_finite (x : ℝ × ((v : V) → O v)) (v : V) :
    ((rationalIntegralAdelesHomeomorph x : rationalIntegralAdeles) : A).2 v = (x.2 v : _) :=
  rationalAdeleFiniteStageEmbedding_finite_notMem ∅ (emptyStage x) v (Finset.notMem_empty v)

public theorem compactSpace_rationalFiniteIntegers : CompactSpace ((v : V) → O v) := by
  let (v : V) : CompactSpace (O v) :=
    (Rat.HeightOneSpectrum.adicCompletionIntegers.padicIntEquiv v).toHomeomorph.symm.compactSpace
  infer_instance

/-- The product coordinates of the integral-finite stage, embedded additively in the adeles. -/
@[expose]
public noncomputable def rationalAdeleIntegralEmbedding : (ℝ × RationalFiniteIntegers) →+ A :=
  AddMonoidHom.mk' (fun x ↦ (rationalIntegralAdelesHomeomorph x : A)) fun x y ↦ by
    refine Prod.ext ?_ (FiniteAdeleRing.ext ℚ fun v ↦ ?_)
    · funext v
      have hv : v = Rat.infinitePlace := Subsingleton.elim _ _
      subst v
      let e := InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace
      apply e.injective
      have h (a b : A) : rationalAdeleReal (a + b) = rationalAdeleReal a + rationalAdeleReal b := by
        simp only [rationalAdeleReal_apply]
        exact map_add e _ _
      simp only [e, ← rationalAdeleReal_apply, h, rationalIntegralAdelesHomeomorph_real]
      rfl
    · change ((rationalIntegralAdelesHomeomorph (x + y) : rationalIntegralAdeles) : A).2 v =
        ((rationalIntegralAdelesHomeomorph x : rationalIntegralAdeles) : A).2 v +
        ((rationalIntegralAdelesHomeomorph y : rationalIntegralAdeles) : A).2 v
      rw [rationalIntegralAdelesHomeomorph_finite, rationalIntegralAdelesHomeomorph_finite,
        rationalIntegralAdelesHomeomorph_finite]
      rfl

public theorem isOpenEmbedding_rationalAdeleIntegralEmbedding :
    IsOpenEmbedding rationalAdeleIntegralEmbedding :=
  isOpen_rationalIntegralAdeles.isOpenEmbedding_subtypeVal.comp
    rationalIntegralAdelesHomeomorph.isOpenEmbedding

public theorem range_rationalAdeleIntegralEmbedding :
    range rationalAdeleIntegralEmbedding = (rationalIntegralAdeles : Set A) := by
  ext a
  constructor
  · rintro ⟨x, rfl⟩
    exact (rationalIntegralAdelesHomeomorph x).property
  · intro ha
    obtain ⟨x, hx⟩ := rationalIntegralAdelesHomeomorph.surjective ⟨a, ha⟩
    exact ⟨x, congrArg Subtype.val hx⟩

/-- Subtracting a diagonal integer puts the real coordinate in the half-open unit interval. -/
public theorem exists_sub_intCast_real_mem_Ico (a : A) :
    ∃ z : ℤ, rationalAdeleReal (a - (z : A)) ∈ Ico (0 : ℝ) 1 := by
  refine ⟨⌊rationalAdeleReal a⌋, ?_⟩
  have hsub (b : A) : rationalAdeleReal (a - b) = rationalAdeleReal a - rationalAdeleReal b := by
    simp only [rationalAdeleReal_apply]
    exact map_sub (InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace) _ _
  rw [hsub, ← map_intCast (ι), rationalAdeleReal_algebraMap, Rat.cast_intCast]
  refine ⟨sub_nonneg.mpr (Int.floor_le _), sub_lt_iff_lt_add.mpr ?_⟩
  rw [add_comm 1]
  exact Int.lt_floor_add_one (rationalAdeleReal a)

end Masullo
