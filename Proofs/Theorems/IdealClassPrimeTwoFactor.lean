module

public import Theorems.IdealClassPrimeFiveFactor
public import Theorems.IdealClassSignCharacter

/-!
# The grouped Hecke denominator at two

The unique place over two has norm two and is retained in (3.2.1.7), p. 124.
Its class has sign `-1`, so the grouped denominator is `1 + X`, matching
both Dirichlet factors taken together.
-/

open Polynomial

namespace Masullo

/-- The normalized class character gives `1 + X` at the bundled prime two. -/
public theorem qSqrtNegFive_heckeRationalDenominator_at_two_eq_one_add_X :
    heckeRationalDenominator (idealClassHeckeCharacter qSqrtNegFiveClassCharacter)
      ⟨2, by decide⟩ = 1 + X := by
  rw [heckeRationalDenominator_idealClassHeckeCharacter_of_unique_prime_absNorm
    qSqrtNegFiveClassCharacter ⟨2, by decide⟩ qSqrtNegFivePrimeTwo qSqrtNegFivePrimeTwo_under
    qSqrtNegFivePrimeTwo_absNorm qSqrtNegFivePrimeTwo_unique,
    idealClassHeckeCharacter_localValue]
  change 1 - C (qSqrtNegFiveClassCharacter (qSqrtNegFivePlaceClass qSqrtNegFivePrimeTwo)) * X = _
  rw [qSqrtNegFiveClassCharacter_primeTwo]
  simp

/-- The grouped denominator at two matches the factors with coefficients `(0, -1)`. -/
public theorem qSqrtNegFive_heckeRationalDenominator_at_two :
    heckeRationalDenominator (idealClassHeckeCharacter qSqrtNegFiveClassCharacter) ⟨2, by decide⟩ =
      (1 - C (dirichletNegFour (2 : ℕ)) * X) * (1 - C (dirichletFive (2 : ℕ)) * X) := by
  have h₄ : dirichletNegFour (2 : ℕ) = 0 := by
    have h : ZMod.χ₄ (2 : ZMod 4) = 0 := by decide
    change dirichletNegFour (2 : ZMod 4) = 0
    norm_num [dirichletNegFour, MulChar.ringHomComp_apply, h]
  have h₅ : dirichletFive (2 : ℕ) = -1 := by
    let : Fact (Nat.Prime 5) := ⟨by decide⟩
    have hne : (2 : ZMod 5) ≠ 0 := by decide
    have hns : ¬ IsSquare (2 : ZMod 5) := by decide
    have h := (quadraticChar_eq_neg_one_iff_not_one hne).mpr
      (mt (quadraticChar_one_iff_isSquare hne).mp hns)
    change dirichletFive (2 : ZMod 5) = -1
    norm_num [dirichletFive, MulChar.ringHomComp_apply, h]
  rw [qSqrtNegFive_heckeRationalDenominator_at_two_eq_one_add_X, h₄, h₅]
  simp

end Masullo
