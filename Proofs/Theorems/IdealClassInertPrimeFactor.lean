module

public import Theorems.IdealClassHeckeCharacter
public import Theorems.IdealClassSplitPrimeSign

/-!
# The grouped Hecke denominator at an inert rational prime

For (3.2.1.1), p. 122, and (3.2.1.7), p. 124, the class character retains
one place over a rational prime `p` for which `(p)` is prime. Its ideal is
principal and its absolute norm is `p ^ [K : ℚ]`.
-/

open IsDedekindDomain NumberField Polynomial
open scoped nonZeroDivisors

namespace Masullo

variable {K : Type*} [Field K] [NumberField K]

/-- If `(p)` is prime in the integer ring, it is the only finite place over `p`. -/
public theorem heckePrimeFiber_singleton_of_isPrime_span (p : Nat.Primes)
    (hp : (Ideal.span {(p.val : 𝓞 K)}).IsPrime) :
    ∃ v : heckePrimeFiber K p, v.1.asIdeal = Ideal.span {(p.val : 𝓞 K)} ∧
      ∀ w : heckePrimeFiber K p, w = v := by
  let P : Ideal (𝓞 K) := Ideal.span {(p.val : 𝓞 K)}
  have hP : P ≠ ⊥ := Ideal.span_singleton_eq_bot.not.mpr (Nat.cast_ne_zero.mpr p.2.ne_zero)
  have hpℤ : (p.val : ℤ) ≠ 0 := Nat.cast_ne_zero.mpr p.2.ne_zero
  have hmax : (Ideal.span {(p.val : ℤ)}).IsMaximal :=
    ((Ideal.span_singleton_prime hpℤ).mpr (Nat.prime_iff_prime_int.mp p.2)).isMaximal
      (Ideal.span_singleton_eq_bot.not.mpr hpℤ)
  have hPunder : P.under ℤ = Ideal.span {(p.val : ℤ)} := by
    symm
    apply hmax.eq_of_le (hp.comap (algebraMap ℤ (𝓞 K))).ne_top
    apply (Ideal.span_singleton_le_iff_mem _).mpr
    apply (Ideal.mem_under ℤ P).mpr
    rw [map_natCast]
    exact Ideal.subset_span (Set.mem_singleton _)
  let v : HeightOneSpectrum (𝓞 K) := ⟨P, hp, hP⟩
  have hv : heckeRationalPrime v = p := by
    apply Subtype.ext
    change (P.under ℤ).absNorm = p.val
    rw [hPunder]
    simp
  refine ⟨⟨v, hv⟩, rfl, fun w ↦ Subtype.ext (HeightOneSpectrum.ext_iff.mpr ?_)⟩
  change w.1.asIdeal = P
  symm
  apply (hp.isMaximal hP).eq_of_le w.1.isPrime.ne_top
  apply (Ideal.span_singleton_le_iff_mem _).mpr
  have hw : (p.val : ℤ) ∈ w.1.asIdeal.under ℤ := by
    rw [heckePrimeFiber_under_eq_span p w]
    exact Ideal.subset_span (Set.mem_singleton _)
  simpa using (Ideal.mem_under ℤ w.1.asIdeal).mp hw

/-- The norm of the principal ideal `(p)` forces the residue degree to be `[K : ℚ]`. -/
public theorem heckePrimeFiber_inertiaDeg_of_asIdeal_eq_span (p : Nat.Primes) (v : heckePrimeFiber K p)
    (hv : v.1.asIdeal = Ideal.span {(p.val : 𝓞 K)}) :
    v.1.asIdeal.inertiaDeg ℤ = Module.finrank ℚ K := by
  let _ : v.1.asIdeal.IsPrime := v.1.isPrime
  have hnorm := Ideal.absNorm_pow_inertiaDeg (v.1.asIdeal.under ℤ) v.1.asIdeal
  have hpℤ : (v.1.asIdeal.under ℤ).absNorm = p.val := by
    rw [heckePrimeFiber_under_eq_span p v]
    simp
  have hP : v.1.asIdeal.absNorm = p.val ^ Module.finrank ℚ K := by
    rw [hv, Ideal.absNorm_span_natCast, RingOfIntegers.rank]
  rw [hpℤ, hP] at hnorm
  exact Nat.pow_right_injective p.2.two_le hnorm

/-- In the inert case the single retained place has class coefficient one. -/
public theorem heckeRationalDenominator_idealClassHeckeCharacter_of_isPrime_span
    (φ : ClassGroup (𝓞 K) →* ℂ) (p : Nat.Primes)
    (hp : (Ideal.span {(p.val : 𝓞 K)}).IsPrime) :
    heckeRationalDenominator (idealClassHeckeCharacter φ) p = 1 - X ^ Module.finrank ℚ K := by
  classical
  obtain ⟨v, hv, hunique⟩ := heckePrimeFiber_singleton_of_isPrime_span p hp
  let _ : Subsingleton (heckePrimeFiber K p) := ⟨fun w z ↦ (hunique w).trans (hunique z).symm⟩
  have hprincipal : v.1.asIdeal.IsPrincipal := by
    rw [hv]
    infer_instance
  have hpoly : (idealClassHeckeCharacter φ).localPolynomial v.1 = 1 - X := by
    rw [HeckeCharacter.localPolynomial, ite_eq_left (idealClassHeckeCharacter_isUnramifiedAt φ v.1),
      idealClassHeckeCharacter_localValue, (ClassGroup.mk0_eq_one_iff _).mpr hprincipal,
      map_one, C_1, one_mul]
  rw [heckeRationalDenominator, Fintype.prod_subsingleton _ v,
    heckePrimeFiber_inertiaDeg_of_asIdeal_eq_span p v hv, hpoly, sub_comp, one_comp, X_comp]

/-- The inert row of the grouped Hecke denominator over `ℚ(√-5)`. -/
public theorem qSqrtNegFive_heckeRationalDenominator_of_isPrime_span
    (φ : ClassGroup (𝓞 QSqrtNegFive) →* ℂ) (p : Nat.Primes)
    (hp : (Ideal.span {(p.val : 𝓞 QSqrtNegFive)}).IsPrime) :
    heckeRationalDenominator (idealClassHeckeCharacter φ) p = 1 - X ^ 2 := by
  rw [heckeRationalDenominator_idealClassHeckeCharacter_of_isPrime_span φ p hp,
    show Module.finrank ℚ QSqrtNegFive = 2 from QuadraticAlgebra.finrank_eq_two _ _]

end Masullo
