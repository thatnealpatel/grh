module

public import Theorems.IdealClassDirichletSigns
public import Theorems.IdealClassInertPrimeFactor
public import Theorems.IdealClassQuadraticReduction
public import Theorems.IdealClassSignCharacter

/-!
# The Dirichlet comparison at an inert rational prime

The retained Hecke denominator in (3.2.1.7), p. 124, is `1 - X ^ 2`.
The two Dirichlet coefficients are opposite signs, giving the same product.
-/

open Polynomial

namespace Masullo

/-- At an odd prime where `-5` is nonsquare, the retained Hecke factor matches the two
Dirichlet factors. -/
public theorem qSqrtNegFive_heckeRationalDenominator_of_not_isSquare (p : Nat.Primes)
    (hp₂ : p.val ≠ 2) (hs : ¬ IsSquare (-5 : ZMod p.val)) :
    heckeRationalDenominator (idealClassHeckeCharacter qSqrtNegFiveClassCharacter) p =
      (1 - C (dirichletNegFour p.val) * X) * (1 - C (dirichletFive p.val) * X) := by
  let _ : Fact p.val.Prime := ⟨p.2⟩
  have hsign := dirichletFive_eq_neg_dirichletNegFour_of_not_isSquare p.val hp₂ hs
  have hleg : legendreSym p.val (-5) = -1 :=
    (legendreSym.eq_neg_one_iff p.val).mpr (by simpa using hs)
  have hsq : dirichletNegFour p.val ^ 2 = 1 := by
    have hprod := dirichletNegFour_mul_dirichletFive_eq_legendreSym p.val hp₂
    rw [hsign, hleg, Int.cast_neg, Int.cast_one, mul_neg, ← pow_two] at hprod
    exact neg_injective hprod
  rw [qSqrtNegFive_heckeRationalDenominator_of_isPrime_span qSqrtNegFiveClassCharacter p
    ((qSqrtNegFive_isPrime_span_iff_not_isSquare p hp₂).mpr hs)]
  calc
    1 - X ^ 2 = 1 - (C (dirichletNegFour p.val) * X) ^ 2 := by
      rw [mul_pow, ← map_pow, hsq, map_one, one_mul]
    _ = _ := by
      rw [hsign, map_neg]
      ring

end Masullo
