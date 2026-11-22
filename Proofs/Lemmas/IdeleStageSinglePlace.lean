module

public import Theorems.IdeleFiniteStage
import Mathlib.NumberTheory.NumberField.AdeleRing

/-! # Single-place coordinates in an idele stage

A stage tuple supported at one place gives the actual Mathlib insertion
at that place. For an inactive place, first include the integral unit
into the completion units.
-/

open IsDedekindDomain NumberField
open scoped Classical RestrictedProduct

namespace Masullo

variable (K : Type*) [Field K] [NumberField K]

local notation "V" => HeightOneSpectrum (𝓞 K)
local notation "I" => IdeleGroup (𝓞 K) K
local notation "F" v => HeightOneSpectrum.adicCompletion K v
local notation "O" v => HeightOneSpectrum.adicCompletionIntegers K v
local notation "J" S => {v : V // v ∈ S}
local notation "U" S => {v : V // v ∉ S}

private theorem idele_ext {a b : I}
    (hi : ∀ v : InfinitePlace K, (a : AdeleRing (𝓞 K) K).1 v = (b : AdeleRing (𝓞 K) K).1 v)
    (hf : ∀ v : V, (a : AdeleRing (𝓞 K) K).2 v = (b : AdeleRing (𝓞 K) K).2 v) : a = b :=
  Units.ext (Prod.ext (funext hi) (RestrictedProduct.ext _ _ hf))

public theorem ideleFiniteStageEmbedding_single_infinite (S : Finset V) (v : InfinitePlace K) (z : v.Completionˣ) :
    ideleFiniteStageEmbedding K S (Pi.mulSingle v z, 1, 1) = IdeleGroup.ofCompletion (𝓞 K) K v z := by
  apply idele_ext
  · intro w
    rw [ideleFiniteStageEmbedding_infinite]
    change ((Pi.mulSingle (M := fun t : InfinitePlace K ↦ t.Completionˣ) v z w) : w.Completion) =
      Pi.mulSingle (M := fun t : InfinitePlace K ↦ t.Completion) v (z : v.Completion) w
    by_cases h : w = v
    · subst w
      simp
    · simp [Pi.mulSingle_eq_of_ne h]
  · intro w
    by_cases h : w ∈ S
    · rw [ideleFiniteStageEmbedding_finite_mem K S _ w h]
      rfl
    · rw [ideleFiniteStageEmbedding_finite_notMem K S _ w h]
      rfl

public theorem ideleFiniteStageEmbedding_single_active (S : Finset V) (v : J S) (z : (F v.val)ˣ) :
    ideleFiniteStageEmbedding K S (1, Pi.mulSingle v z, 1) =
      IdeleGroup.ofAdicCompletion (𝓞 K) K v z := by
  apply idele_ext
  · intro w
    rw [ideleFiniteStageEmbedding_infinite]
    rfl
  · intro w
    by_cases h : w ∈ S
    · rw [ideleFiniteStageEmbedding_finite_mem K S _ w h]
      by_cases he : w = v.val
      · obtain ⟨v, hv⟩ := v
        subst w
        change _ = Pi.mulSingle (M := fun t : V ↦ F t) v _ v
        simp
      · have hne : (⟨w, h⟩ : J S) ≠ v := fun H ↦ he (congrArg Subtype.val H)
        change _ = Pi.mulSingle (M := fun t : V ↦ F t) v.val _ w
        simp [Pi.mulSingle_eq_of_ne he, Pi.mulSingle_eq_of_ne hne]
    · rw [ideleFiniteStageEmbedding_finite_notMem K S _ w h]
      have he : w ≠ v.val := fun H ↦ h (H ▸ v.property)
      change _ = Pi.mulSingle (M := fun t : V ↦ F t) v.val _ w
      simp [Pi.mulSingle_eq_of_ne he]

public theorem ideleFiniteStageEmbedding_single_inactive (S : Finset V) (v : U S) (z : (O v.val)ˣ) :
    ideleFiniteStageEmbedding K S (1, 1, Pi.mulSingle v z) =
      IdeleGroup.ofAdicCompletion (𝓞 K) K v (Units.map (O v.val).subtype.toMonoidHom z) := by
  apply idele_ext
  · intro w
    rw [ideleFiniteStageEmbedding_infinite]
    rfl
  · intro w
    by_cases h : w ∈ S
    · rw [ideleFiniteStageEmbedding_finite_mem K S _ w h]
      have he : w ≠ v.val := fun H ↦ v.property (H ▸ h)
      change _ = Pi.mulSingle (M := fun t : V ↦ F t) v.val _ w
      simp [Pi.mulSingle_eq_of_ne he]
    · rw [ideleFiniteStageEmbedding_finite_notMem K S _ w h]
      by_cases he : w = v.val
      · obtain ⟨v, hv⟩ := v
        subst w
        change _ = Pi.mulSingle (M := fun t : V ↦ F t) v _ v
        simp
      · have hne : (⟨w, h⟩ : U S) ≠ v := fun H ↦ he (congrArg Subtype.val H)
        change _ = Pi.mulSingle (M := fun t : V ↦ F t) v.val _ w
        simp [Pi.mulSingle_eq_of_ne he, Pi.mulSingle_eq_of_ne hne]

end Masullo
