module

public import Theorems.IdeleIdealClassStrict
public import Mathlib.NumberTheory.NumberField.HeckeLFunction
import Mathlib.Topology.Algebra.Group.Quotient

/-! # Finite Euler coefficients of ideal-class characters

For the factors in Masullo §3.2.1, (3.2.1.1), PDF p. 122, and Definition
3.2.1.4, (3.2.1.7), p. 124, pull a class-group character back to the
idele class group. The local integral units map to the identity ideal,
and a single-place uniformizer maps to the positive prime ideal.
-/

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField
open scoped Masullo nonZeroDivisors WithZero

namespace Masullo

variable {K : Type*} [Field K] [NumberField K]

local notation "V" => HeightOneSpectrum (𝓞 K)
local notation "A" => AdeleRing (𝓞 K) K
local notation "I" => IdeleGroup (𝓞 K) K
local notation "F" => FiniteAdeleRing (𝓞 K) K
local notation "J" => FractionalIdeal (𝓞 K)⁰ K
local notation "C" => IdeleClassGroup (𝓞 K) K
local notation "P" => ClassGroup (𝓞 K)

/-- The ideal class map is continuous on the actual quotient of the ideles. -/
public theorem continuous_ideleClassIdealClass : Continuous (ideleClassIdealClass (K := K)) := by
  apply (QuotientGroup.isOpenQuotientMap_mk
    (N := IdeleGroup.principalSubgroup (𝓞 K) K)).isQuotientMap.continuous_iff.mpr
  rw [show ((ideleClassIdealClass (K := K) : C → P) ∘ (QuotientGroup.mk : I → C)) =
    (ideleIdealClass (K := K) : I → P) from funext ideleClassIdealClass_mk]
  exact (ideleIdealClass_strictExact (K := K)).2.2.continuous

private theorem finitePart_insert (v w : V) (x : (v.adicCompletion K)ˣ) :
    letI := Classical.decEq V
    ((ideleFinitePart (IdeleGroup.ofAdicCompletion (𝓞 K) K v x) : Fˣ) : F) w =
      Pi.mulSingle (M := fun u : V ↦ u.adicCompletion K) v (x : v.adicCompletion K) w := by
  rw [ideleFinitePart_apply]
  rfl

private theorem idealClass_insert (v : V) (x : (v.adicCompletion K)ˣ) :
    ideleClassIdealClass (IdeleClassGroup.ofAdicCompletion (𝓞 K) K v x) =
      ClassGroup.mk K (finiteIdeleIdeal K (ideleFinitePart (IdeleGroup.ofAdicCompletion (𝓞 K) K v x))) := by
  rw [IdeleClassGroup.ofAdicCompletion, MonoidHom.comp_apply]
  exact (ideleClassIdealClass_mk _).trans (ideleIdealClass_apply _)

private theorem idealClass_insert_eq_one (v : V) (x : (v.adicCompletion K)ˣ)
    (hx : Valued.v (x : v.adicCompletion K) = 1) :
    ideleClassIdealClass (IdeleClassGroup.ofAdicCompletion (𝓞 K) K v x) = 1 := by
  classical
  rw [idealClass_insert, ← map_one (ClassGroup.mk K)]
  congr 1
  apply fractionalIdeal_units_ext_count
  intro w
  rw [count_finiteIdeleIdeal, finitePart_insert, Units.val_one, FractionalIdeal.count_one]
  by_cases hw : w = v
  · subst w
    simp [Pi.mulSingle_eq_same, hx]
  · simp [Pi.mulSingle_eq_of_ne hw]

/-- A uniformizer inserted at one place represents that prime ideal class, not its inverse. -/
public theorem ideleClassIdealClass_ofAdicCompletion_uniformizer (v : V)
    (π : (v.adicCompletion K)ˣ) (hπ : Valued.v.IsUniformizer (π : v.adicCompletion K)) :
    ideleClassIdealClass (IdeleClassGroup.ofAdicCompletion (𝓞 K) K v π) =
      ClassGroup.mk0 ⟨v.asIdeal, mem_nonZeroDivisors_iff_ne_zero.mpr v.ne_bot⟩ := by
  classical
  rw [idealClass_insert, ← ClassGroup.mk_mk0 K]
  congr 1
  apply fractionalIdeal_units_ext_count
  intro w
  rw [count_finiteIdeleIdeal, finitePart_insert, FractionalIdeal.coe_mk0]
  change -WithZero.log (Valued.v (Pi.mulSingle (M := fun u : V ↦ u.adicCompletion K)
      v (π : v.adicCompletion K) w)) = FractionalIdeal.count K w (v.asIdeal : J)
  by_cases hw : w = v
  · subst w
    rw [Pi.mulSingle_eq_same, hπ.val,
      Valuation.IsRankOneDiscrete.generator_eq_exp_neg_one_of_surjective
        (valuedAdicCompletion_surjective K v), Units.val_mk0, WithZero.log_exp, neg_neg,
      FractionalIdeal.count_self]
  · rw [Pi.mulSingle_eq_of_ne hw, map_one, WithZero.log_one, neg_zero,
      FractionalIdeal.count_maximal_coprime K w (Ne.symm hw)]

/-- Pull back a complex ideal-class character to the idele class group. -/
public noncomputable def idealClassHeckeCharacter (φ : P →* ℂ) : HeckeCharacter (𝓞 K) K where
  toMonoidHom := φ.comp ideleClassIdealClass
  continuous_toFun := (continuous_of_discreteTopology : Continuous φ).comp
    continuous_ideleClassIdealClass

/-- Evaluation of a pulled-back character uses the ideal class of the input. -/
public theorem idealClassHeckeCharacter_apply (φ : P →* ℂ) (x : C) :
    idealClassHeckeCharacter φ x = φ (ideleClassIdealClass x) := by
  unfold idealClassHeckeCharacter
  rfl

/-- Pullback preserves unitary values. -/
public theorem norm_idealClassHeckeCharacter (φ : P →* ℂ) (hφ : ∀ c : P, ‖φ c‖ = 1) (x : C) :
    ‖idealClassHeckeCharacter φ x‖ = 1 := by
  rw [idealClassHeckeCharacter_apply, hφ]

private theorem restrict_idealClassHeckeCharacter (φ : P →* ℂ) (v : V)
    (x : (v.adicCompletion K)ˣ) :
    (idealClassHeckeCharacter φ).restrict v (x : v.adicCompletion K) =
      φ (ideleClassIdealClass (IdeleClassGroup.ofAdicCompletion (𝓞 K) K v x)) := by
  rw [HeckeCharacter.restrict, MulChar.ofUnitHom_coe, MonoidHom.comp_apply,
    MonoidHom.coe_toHomUnits]
  exact idealClassHeckeCharacter_apply φ _

/-- Local integral units contribute trivially, even at places over field-ramified primes. -/
public theorem idealClassHeckeCharacter_isUnramifiedAt (φ : P →* ℂ) (v : V) :
    (idealClassHeckeCharacter φ).IsUnramifiedAt v := by
  refine HeckeCharacter.isUnramifiedAt_iff.mpr fun x ↦ ?_
  let y := Units.map (v.adicCompletionIntegers K).subtype.toMonoidHom x
  change (idealClassHeckeCharacter φ).restrict v (y : v.adicCompletion K) = 1
  rw [restrict_idealClassHeckeCharacter, idealClass_insert_eq_one, map_one]
  exact adicCompletionIntegers.isUnit_iff_valued_eq_one.mp x.isUnit

/-- The Euler coefficient at a finite place is the value at its positive prime ideal class. -/
public theorem idealClassHeckeCharacter_localValue (φ : P →* ℂ) (v : V) :
    (idealClassHeckeCharacter φ).localValue v =
      φ (ClassGroup.mk0 ⟨v.asIdeal, mem_nonZeroDivisors_iff_ne_zero.mpr v.ne_bot⟩) := by
  obtain ⟨π, hπ⟩ := (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰)
    |>.exists_isUniformizer_of_isCyclic_of_nontrivial
  let u : (v.adicCompletion K)ˣ := Units.mk0 (π : v.adicCompletion K) hπ.ne_zero
  have hu : Valued.v.IsUniformizer (u : v.adicCompletion K) := hπ
  rw [(idealClassHeckeCharacter_isUnramifiedAt φ v).localValue_eq (u : v.adicCompletion K) hu,
    restrict_idealClassHeckeCharacter, ideleClassIdealClass_ofAdicCompletion_uniformizer v u hu]

end Masullo
