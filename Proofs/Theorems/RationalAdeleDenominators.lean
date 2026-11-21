module

public import Lemmas.RationalAdeleFiniteCharacter

/-!
# Clearing the finite coordinates of a rational adele

This gives surjectivity of the integral-finite window onto the additive
adele class group over ℚ, the algebraic surjectivity part of (A.1.2.2),
p. 541. It does not identify the quotient topology.
-/

open NumberField IsDedekindDomain Filter
open scoped BigOperators ComplexConjugate

namespace Masullo

local notation "V" => HeightOneSpectrum (𝓞 ℚ)
local notation "A" => AdeleRing (𝓞 ℚ) ℚ
local notation "pOf" => Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)

/-- One diagonal rational translate makes all finite coordinates integral. -/
public theorem exists_rational_sub_mem_integral (a : A) :
    ∃ q : ℚ, ∀ v : V, (a - algebraMap ℚ A q).2 v ∈ v.adicCompletionIntegers ℚ := by
  classical
  let S := (eventually_cofinite.mp a.2.cofinite_mem_adicCompletionIntegers).toFinset
  have hS (v : V) (hv : v ∉ S) : a.2 v ∈ v.adicCompletionIntegers ℚ := by
    simpa [S] using hv
  -- Choose turns for each finite coordinate, integral at every other place.
  have localTurns (v : V) : ∃ t : ℚ,
      conj (rationalPadicPhase (pOf v) t) = rationalLocalFiniteAddChar v (a.2 v) ∧
      ∀ w : V, w ≠ v → rationalPadicPhase (pOf w) t = 1 := by
    let : Fact (pOf v : ℕ).Prime := ⟨(pOf v).property⟩
    obtain ⟨t, ht, _, hoff⟩ := exists_padicPhase_turns (pOf v)
      (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v (a.2 v))
    refine ⟨t, ?_, fun w hw ↦ hoff (pOf w) (fun h ↦ hw ((pOf).injective h))⟩
    rw [rationalLocalFiniteAddChar_apply, ht]
  choose t hself hoff using localTurns
  let q := ∑ w ∈ S, t w
  refine ⟨q, fun v ↦ ?_⟩
  -- At v, only its own summand can contribute to the character of q.
  have hmatch : rationalLocalFiniteAddChar v (algebraMap ℚ (v.adicCompletion ℚ) q) =
      rationalLocalFiniteAddChar v (a.2 v) := by
    rw [rationalLocalFiniteAddChar_rat, rationalPadicPhase_sum]
    by_cases hv : v ∈ S
    · rw [Finset.prod_eq_single_of_mem v hv (fun w _ hw ↦ hoff w v (Ne.symm hw))]
      exact hself v
    · rw [Finset.prod_eq_one (fun w hw ↦ hoff w v (fun he ↦ hv (he ▸ hw))), map_one]
      exact ((rationalLocalFiniteAddChar_eq_one_iff v _).mpr (hS v hv)).symm
  -- Equal character values mean that the difference belongs to the local integer ring.
  change a.2 v - algebraMap ℚ (v.adicCompletion ℚ) q ∈ v.adicCompletionIntegers ℚ
  apply (rationalLocalFiniteAddChar_eq_one_iff v _).mp
  rw [sub_eq_add_neg, AddChar.map_add_eq_mul, ← hmatch, ← AddChar.map_add_eq_mul,
    add_neg_cancel, AddChar.map_zero_eq_one]

end Masullo
