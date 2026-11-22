module

public import Mathlib.NumberTheory.NumberField.Discriminant.Different
public import Mathlib.Analysis.Real.Sqrt

/-! # The finite arithmetic factor in the idelic Gaussian pairing

Masullo prescribes the square root of the local discriminant absolute
value as the integral-unit Haar mass in (A.3.2.2), p. 560, and takes the
restricted product in (A.3.2.5) on the same page. Here we supply the
arithmetic product for the candidate masses obtained from the global
different. The identification of each candidate with the corresponding
local discriminant is a separate step, not an input supplied by this
module. -/

open IsDedekindDomain NumberField

namespace Masullo

variable {K : Type*} [Field K] [NumberField K]

/-- The different contributes at only finitely many finite places. -/
public theorem finite_differentIdeal_multiplicity_support :
    {v : HeightOneSpectrum (𝓞 K) | multiplicity v.asIdeal (differentIdeal ℤ (𝓞 K)) ≠ 0}.Finite :=
  (Ideal.finite_factors (differentIdeal_ne_bot (A := ℤ) (B := 𝓞 K))).subset fun _ hv ↦
    Classical.not_not.mp fun h ↦ hv (multiplicity_eq_zero_of_not_dvd h)

/-- Taking absolute norms in the prime factorization of the different
recovers the absolute field discriminant on any finite set containing
its support. -/
public theorem prod_absNorm_pow_differentIdeal_multiplicity
    (T : Finset (HeightOneSpectrum (𝓞 K)))
    (hT : ∀ v ∉ T, multiplicity v.asIdeal (differentIdeal ℤ (𝓞 K)) = 0) :
    (∏ v ∈ T, v.asIdeal.absNorm ^ multiplicity v.asIdeal (differentIdeal ℤ (𝓞 K))) =
      (discr K).natAbs := by
  let D := differentIdeal ℤ (𝓞 K)
  have hD : D ≠ ⊥ := differentIdeal_ne_bot
  have hfactor : (∏ v ∈ T, v.asIdeal ^ multiplicity v.asIdeal D) = D := by
    calc
      _ = ∏ᶠ v : HeightOneSpectrum (𝓞 K), v.asIdeal ^ multiplicity v.asIdeal D :=
        (finprod_eq_prod_of_mulSupport_subset _ (s := T) fun v hv ↦ by
          by_contra h
          exact hv (by simp [D, hT v h])).symm
      _ = D := Ideal.finprod_heightOneSpectrum_pow_multiplicity hD
  simpa only [map_prod, map_pow, D, absNorm_differentIdeal K (𝓞 K)] using
    congrArg Ideal.absNorm hfactor

/-- The product of the proposed finite unit masses is the inverse square
root of the absolute field discriminant. No Haar measure is assumed to
have these individual masses here. -/
public theorem prod_differentIdeal_unit_scales
    (T : Finset (HeightOneSpectrum (𝓞 K)))
    (hT : ∀ v ∉ T, multiplicity v.asIdeal (differentIdeal ℤ (𝓞 K)) = 0) :
    (∏ v ∈ T, (Real.sqrt ((v.asIdeal.absNorm ^
      multiplicity v.asIdeal (differentIdeal ℤ (𝓞 K)) : ℕ) : ℝ))⁻¹) =
      (Real.sqrt ((discr K).natAbs : ℝ))⁻¹ := by
  rw [Finset.prod_inv_distrib, ← Real.sqrt_prod T (fun v _ ↦ Nat.cast_nonneg _), ← Nat.cast_prod,
    prod_absNorm_pow_differentIdeal_multiplicity T hT]

end Masullo
