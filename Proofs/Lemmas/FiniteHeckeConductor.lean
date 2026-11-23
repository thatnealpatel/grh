module

public import Lemmas.FiniteCompletionConductorChar
public import Lemmas.FiniteHeckePrincipalUnits

/-! # The conductor of a finite Hecke restriction -/

open IsDedekindDomain IsDiscreteValuationRing IsLocalRing NumberField

namespace Masullo

variable {K : Type*} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

local notation "F" => v.adicCompletion K
local notation "O" => v.adicCompletionIntegers K
local notation "m" => maximalIdeal O

/-- The finite Hecke restriction on the units of the completion integers. -/
@[expose] public noncomputable def finiteHeckeIntegralUnitChar (χ : HeckeCharacter (𝓞 K) K) :
    Oˣ →* ℂˣ :=
  (χ.restrict v).toUnitHom.comp (Units.map (O).subtype.toMonoidHom)

/-- The restriction to integral units has a least conductor, by triviality
on small principal units. -/
public theorem exists_finiteHeckeConductor (χ : HeckeCharacter (𝓞 K) K) :
    ∃ n, IsFiniteCompletionConductor v (finiteHeckeIntegralUnitChar v χ) n := by
  classical
  obtain ⟨ε, hε, _, heq⟩ := finiteHeckeRestriction_eq_one_near_one χ v
  obtain ⟨π, hπ⟩ := exists_irreducible O
  have hπm : π ∈ m := by
    rw [mem_maximalIdeal]
    exact hπ.not_isUnit
  have hπnorm : ‖(π : F)‖ < 1 := Valued.toNormedField.norm_lt_one_iff.mpr
    ((Valuation.mem_maximalIdeal_iff F _).mp hπm)
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hε hπnorm
  have hex : ∃ k, (finiteCompletionUnitReduction v k).ker ≤ (finiteHeckeIntegralUnitChar v χ).ker := by
    refine ⟨k, fun u hu ↦ ?_⟩
    have hm := (mem_finiteCompletionUnitReduction_ker v k u).mp hu
    rw [hπ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hm
    obtain ⟨a, ha⟩ := hm
    have hcast : ((u : O) : F) - 1 = (π : F) ^ k * (a : F) :=
      congrArg (fun x : O ↦ (x : F)) ha
    have hnorm : ‖(a : F)‖ ≤ 1 := Valued.toNormedField.norm_le_one_iff.mpr (by
      simpa only [HeightOneSpectrum.mem_adicCompletionIntegers] using a.property)
    have hsmall : ‖((u : O) : F) - 1‖ < ε := by
      rw [hcast, norm_mul, norm_pow]
      exact (mul_le_of_le_one_right (by positivity) hnorm).trans_lt hk
    apply Units.ext
    change χ.restrict v ((u : O) : F) = 1
    exact heq _ hsmall
  exact ⟨Nat.find hex, Nat.isLeast_find hex⟩

/-- At a ramified finite place the least conductor has positive level. -/
public theorem exists_pos_finiteHeckeConductor (χ : HeckeCharacter (𝓞 K) K)
    (hχ : ¬ χ.IsUnramifiedAt v) :
    ∃ n, 0 < n ∧ IsFiniteCompletionConductor v (finiteHeckeIntegralUnitChar v χ) n := by
  obtain ⟨n, hn⟩ := exists_finiteHeckeConductor v χ
  refine ⟨n, Nat.pos_of_ne_zero ?_, hn⟩
  rintro rfl
  exact hχ ((isFiniteCompletionConductor_zero_iff v _).mp hn)

end Masullo
