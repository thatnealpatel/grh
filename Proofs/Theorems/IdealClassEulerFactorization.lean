module

public import Theorems.IdealClassInertPrimeComparison
public import Theorems.IdealClassPrimeTwoFactor
public import Theorems.IdealClassSplitPrimeFactor

/-!
# The finite Euler product of the quadratic class character of ℚ(√-5)

All finite places contribute to (3.2.1.7), p. 124, including the places above
`2` and `5`. Grouping by rational prime identifies the finite product with
that of the quadratic Dirichlet characters of discriminants `-4` and `5`.
-/

open Polynomial

namespace Masullo

/-- The grouped denominator of the normalized class character at every rational prime. -/
public theorem qSqrtNegFive_heckeRationalDenominator (p : Nat.Primes) :
    heckeRationalDenominator (idealClassHeckeCharacter qSqrtNegFiveClassCharacter) p =
      (1 - C (dirichletNegFour p.val) * X) * (1 - C (dirichletFive p.val) * X) := by
  by_cases hp₂ : p.val = 2
  · have h : p = ⟨2, by decide⟩ := Subtype.ext hp₂
    subst p
    exact qSqrtNegFive_heckeRationalDenominator_at_two
  by_cases hp₅ : p.val = 5
  · have h : p = ⟨5, by decide⟩ := Subtype.ext hp₅
    subst p
    exact qSqrtNegFive_heckeRationalDenominator_at_five qSqrtNegFiveClassCharacter
  by_cases hs : IsSquare (-5 : ZMod p.val)
  · obtain ⟨r, hr⟩ := (isSquare_iff_exists_sq _).mp hs
    exact qSqrtNegFive_heckeRationalDenominator_of_split_root p hp₂ hp₅ r hr.symm
  · exact qSqrtNegFive_heckeRationalDenominator_of_not_isSquare p hp₂ hs

/-- The explicit entire Dirichlet product agrees with the finite Hecke product for `1 < s.re`. -/
public theorem qSqrtNegFive_finiteHeckeCharacterEulerProduct_eq_dirichletProduct
    {s : ℂ} (hs : 1 < s.re) :
    finiteHeckeCharacterEulerProduct (idealClassHeckeCharacter qSqrtNegFiveClassCharacter) s =
      qSqrtNegFiveDirichletProduct s :=
  finiteHeckeCharacterEulerProduct_eq_qSqrtNegFiveDirichletProduct_of_local
    (idealClassHeckeCharacter qSqrtNegFiveClassCharacter)
    (norm_idealClassHeckeCharacter _ norm_qSqrtNegFiveClassCharacter)
    qSqrtNegFive_heckeRationalDenominator hs

end Masullo
