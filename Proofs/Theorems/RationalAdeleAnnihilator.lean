module

public import Theorems.RationalAdeleCharacter

import Lemmas.RationalAdelePrimeTests
import Theorems.RationalAdeleDenominators

/-!
# The diagonal rational lattice is its own annihilator

This is a global rational calculation with our sign convention for the pairing
in Example A.3.1.8, p. 558. Example A.3.1.11 concerns S-local lattices instead.
-/

open NumberField IsDedekindDomain

namespace Masullo

local notation "V" => HeightOneSpectrum (𝓞 ℚ)
local notation "A" => AdeleRing (𝓞 ℚ) ℚ
local notation "ι" => algebraMap ℚ A

private theorem orthogonal_sub_rat (a : A)
    (h : ∀ r : ℚ, rationalAdeleAddChar (a * ι r) = 1) (q r : ℚ) :
    rationalAdeleAddChar ((a - ι q) * ι r) = 1 := by
  rw [sub_mul, ← map_mul, sub_eq_add_neg, AddChar.map_add_eq_mul,
    AddChar.map_neg_eq_inv, rationalAdeleAddChar_algebraMap, h r, inv_one, mul_one]

private theorem exists_int_real_of_integral (a : A)
    (hint : ∀ v : V, a.2 v ∈ v.adicCompletionIntegers ℚ)
    (h : rationalAdeleAddChar a = 1) : ∃ z : ℤ, rationalAdeleReal a = z := by
  rw [rationalAdeleAddChar_eq_prod a ∅ (fun v _ ↦ hint v), Finset.prod_empty, mul_one] at h
  obtain ⟨z, hz⟩ := Complex.exp_eq_one_iff.mp h
  refine ⟨z, ?_⟩
  have him := congrArg Complex.im hz
  simp [Complex.mul_im, Complex.mul_re] at him
  nlinarith [Real.pi_pos]

/-- Under the standard rational adelic pairing `(a,b) ↦ ψ (a*b)`, the elements
    trivial against every diagonal rational are precisely the diagonal rationals. -/
public theorem rationalAdele_orthogonal_iff (a : A) :
    (∀ r : ℚ, rationalAdeleAddChar (a * ι r) = 1) ↔ ∃ q : ℚ, a = ι q := by
  constructor
  · intro ha
    -- First normalize the finite part; testing at 1 then fixes the real part modulo ℤ.
    obtain ⟨q, hq⟩ := exists_rational_sub_mem_integral a
    let b := a - ι q
    have hb := orthogonal_sub_rat a ha q
    obtain ⟨z, hz⟩ := exists_int_real_of_integral b hq (by simpa using hb 1)
    let c := b - ι (z : ℚ)
    have hcReal : rationalAdeleReal c = 0 := by
      rw [rationalAdeleReal_apply]
      change InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace
        (b.1 Rat.infinitePlace - (ι (z : ℚ)).1 Rat.infinitePlace) = 0
      rw [map_sub, ← rationalAdeleReal_apply, ← rationalAdeleReal_apply,
        rationalAdeleReal_algebraMap, hz]
      simp
    have hcIntegral (v : V) : c.2 v ∈ v.adicCompletionIntegers ℚ := by
      change b.2 v - algebraMap ℚ (v.adicCompletion ℚ) (z : ℚ) ∈ v.adicCompletionIntegers ℚ
      rw [map_intCast]
      exact (v.adicCompletionIntegers ℚ).toSubring.sub_mem (hq v) (intCast_mem _ z)
    -- Inverse prime powers detect the remaining finite coordinates individually.
    have hc : c = 0 := rationalAdele_eq_zero_of_prime_tests c hcReal hcIntegral
      (fun _ _ ↦ orthogonal_sub_rat b hb z _)
    refine ⟨q + (z : ℚ), ?_⟩
    have heq : a - (ι q + ι (z : ℚ)) = 0 := by
      rw [← sub_sub]
      exact hc
    rw [map_add]
    exact sub_eq_zero.mp heq
  · rintro ⟨q, rfl⟩ r
    rw [← map_mul, rationalAdeleAddChar_algebraMap]

end Masullo
