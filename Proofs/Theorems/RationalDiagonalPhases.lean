module

public import Lemmas.RationalPadicPhase

/-!
# Rational diagonal phases

For the diagonal pairing over `ℚ`, the positive real exponential is paired
with the conjugates of the positive finite characters. This is a sign repair
for the rational lattice use of Example A.3.1.8, p. 558.
-/

open scoped BigOperators ComplexConjugate

namespace Masullo

/-- Positive finite phases multiply to the positive real exponential on the
    diagonal. Any finite set containing the denominator primes suffices. -/
public theorem prod_rationalPadicPhase (r : ℚ) (S : Finset Nat.Primes)
    (hS : ∀ p : Nat.Primes, (p : ℕ) ∣ r.den → p ∈ S) :
    (∏ p ∈ S, rationalPadicPhase p r) = Complex.exp (2 * Real.pi * Complex.I * (r : ℂ)) := by
  classical
  choose f hlocal hexp hcross using fun p ↦ exists_rationalPadicPhase_turns p r
  -- Each summand matches the local phase at its own prime and is integral at all others.
  have hsum (p : Nat.Primes) : rationalPadicPhase p (∑ q ∈ S, f q) = rationalPadicPhase p r := by
    rw [rationalPadicPhase_sum]
    by_cases hp : p ∈ S
    · rw [Finset.prod_eq_single_of_mem p hp (fun q _ hqp ↦ hcross q p hqp.symm)]
      exact hlocal p
    · rw [Finset.prod_eq_one (fun q hq ↦ hcross q p (ne_of_mem_of_not_mem hq hp).symm)]
      exact ((rationalPadicPhase_eq_one_iff p r).mpr (fun hd ↦ hp (hS p hd))).symm
  -- The difference is integral at every prime, so its real exponential is one.
  have hdiff (p : Nat.Primes) : rationalPadicPhase p (r - ∑ q ∈ S, f q) = 1 := by
    rw [sub_eq_add_neg, AddChar.map_add_eq_mul, ← hsum p, ← AddChar.map_add_eq_mul,
      add_neg_cancel, AddChar.map_zero_eq_one]
  obtain ⟨z, hz⟩ := exists_int_of_all_rationalPadicPhases_eq_one _ hdiff
  have hr : r = (z : ℚ) + ∑ q ∈ S, f q := by linarith
  calc
    _ = ∏ p ∈ S, Complex.exp (2 * Real.pi * Complex.I * (f p : ℂ)) :=
      Finset.prod_congr rfl fun p _ ↦ (hlocal p).symm.trans (hexp p)
    _ = _ := by
      rw [← Complex.exp_sum, hr]
      push_cast
      rw [mul_add, Finset.mul_sum, Complex.exp_add,
        mul_comm (2 * (Real.pi : ℂ) * Complex.I) (z : ℂ),
        Complex.exp_int_mul_two_pi_mul_I, one_mul]

/-- The positive real factor and the conjugated finite factors cancel on the
    rational diagonal. -/
public theorem rationalDiagonal_phase_eq_one (r : ℚ) (S : Finset Nat.Primes)
    (hS : ∀ p : Nat.Primes, (p : ℕ) ∣ r.den → p ∈ S) :
    Complex.exp (2 * Real.pi * Complex.I * (r : ℂ)) *
      (∏ p ∈ S, conj (rationalPadicPhase p r)) = 1 := by
  rw [← prod_rationalPadicPhase r S hS, ← map_prod, Complex.mul_conj,
    Complex.normSq_eq_norm_sq, norm_prod]
  simp only [norm_rationalPadicPhase, Finset.prod_const_one, one_pow, Complex.ofReal_one]

end Masullo
