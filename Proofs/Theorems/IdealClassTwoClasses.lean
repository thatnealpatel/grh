module

public import Theorems.IdealClassPrimeTwo
public import Theorems.IdealClassSmallRepresentative

/-!
# The two ideal classes of ℚ(√-5)

The small-norm bound and uniqueness of the prime over two discharge the
arithmetic inputs to the odd degree-one sign in the finite Euler product
(3.2.1.7), p. 124. This does not construct the idelic character.
-/

open NumberField IsDedekindDomain
open scoped nonZeroDivisors

namespace Masullo

local notation "O" => 𝓞 QSqrtNegFive

/-- Every ideal class is the identity or the class of the prime above two. -/
public theorem qSqrtNegFive_class_eq_one_or_primeTwo (c : ClassGroup O) :
    c = 1 ∨ c = qSqrtNegFivePlaceClass qSqrtNegFivePrimeTwo := by
  obtain ⟨I, rfl, hnorm | hnorm⟩ := qSqrtNegFive_exists_ideal_in_class_norm_one_or_two c
  · have htop : I = 1 :=
      Subtype.ext ((Ideal.absNorm_eq_one_iff.mp hnorm).trans Ideal.one_eq_top.symm)
    exact Or.inl (htop ▸ map_one ClassGroup.mk0)
  · have hprime : (I : Ideal O).IsPrime := Ideal.isPrime_of_irreducible_absNorm
      (hnorm.symm ▸ Nat.prime_two.prime.irreducible)
    have hmem : (2 : O) ∈ (I : Ideal O) := by
      simpa only [hnorm, Nat.cast_ofNat] using Ideal.absNorm_mem (I : Ideal O)
    have heq := qSqrtNegFivePrimeTwo_unique (I : Ideal O) hprime hmem
    exact Or.inr (congrArg ClassGroup.mk0 (Subtype.ext heq))

/-- At each odd degree-one place, a class character normalized at the prime
above two has the sign of the Dirichlet character modulo four. -/
public theorem qSqrtNegFive_split_classCharacter_primeTwo (v : HeightOneSpectrum O)
    (hdeg : v.asIdeal.inertiaDeg ℤ = 1) (hodd : Odd (heckeRationalPrime v).val)
    (χ : ClassGroup O →* ℂ) (hχ : χ (qSqrtNegFivePlaceClass qSqrtNegFivePrimeTwo) = -1) :
    χ (qSqrtNegFivePlaceClass v) = dirichletNegFour (heckeRationalPrime v).val :=
  qSqrtNegFive_split_classCharacter qSqrtNegFivePrimeTwo v qSqrtNegFivePrimeTwo_absNorm
    qSqrtNegFive_class_eq_one_or_primeTwo hdeg hodd χ hχ

end Masullo
