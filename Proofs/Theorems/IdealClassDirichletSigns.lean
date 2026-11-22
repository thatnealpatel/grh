module

public import Theorems.HeckeDirichletFactorization
public import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity

/-!
# Dirichlet signs for the finite Euler factors over ℚ(√-5)

Quadratic reciprocity compares the two rational Dirichlet coefficients
in the split and inert cases of the grouped product (3.2.1.7), p. 124.
-/

namespace Masullo

variable (p : ℕ) [Fact p.Prime]

private theorem dirichletNegFour_eq_legendreSym (hp₂ : p ≠ 2) :
    dirichletNegFour p = (legendreSym p (-1) : ℂ) := by
  rw [legendreSym.at_neg_one hp₂, dirichletNegFour, MulChar.ringHomComp_apply]
  rfl

private theorem dirichletFive_eq_legendreSym (hp₂ : p ≠ 2) :
    dirichletFive p = (legendreSym p 5 : ℂ) := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  have h : legendreSym p 5 = legendreSym 5 p := by
    simpa using (legendreSym.quadratic_reciprocity_one_mod_four (p := 5) (q := p) (by decide) hp₂)
  rw [h]
  change (((quadraticChar (ZMod 5)) (p : ZMod 5) : ℤ) : ℂ) = _
  rw [legendreSym, Int.cast_natCast]

/-- At every odd rational prime, the product of the Dirichlet coefficients
is the Legendre symbol of `-5`. At `5` both sides are zero. -/
public theorem dirichletNegFour_mul_dirichletFive_eq_legendreSym (hp₂ : p ≠ 2) :
    dirichletNegFour p * dirichletFive p = (legendreSym p (-5) : ℂ) := by
  rw [dirichletNegFour_eq_legendreSym p hp₂, dirichletFive_eq_legendreSym p hp₂,
    ← Int.cast_mul, ← legendreSym.mul]
  rfl

private theorem dirichletFive_eq_mul_legendreSym (hp₂ : p ≠ 2) :
    dirichletFive p = dirichletNegFour p * (legendreSym p (-5) : ℂ) := by
  have hs : dirichletNegFour p * dirichletNegFour p = 1 := by
    rw [← pow_two, dirichletNegFour_eq_legendreSym p hp₂,
      ← Int.cast_pow, legendreSym.sq_one p (a := -1) (by simp), Int.cast_one]
  rw [← dirichletNegFour_mul_dirichletFive_eq_legendreSym p hp₂, ← mul_assoc, hs, one_mul]

/-- For `p ≠ 2, 5`, a square root of `-5` forces the two Dirichlet signs to agree. -/
public theorem dirichletFive_eq_dirichletNegFour_of_isSquare (hp₂ : p ≠ 2) (hp₅ : p ≠ 5)
    (hs : IsSquare (-5 : ZMod p)) : dirichletFive p = dirichletNegFour p := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  have h₅ : (5 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 5 hp₅
  have h : ((-5 : ℤ) : ZMod p) ≠ 0 := by simpa using neg_ne_zero.mpr h₅
  have hsign : legendreSym p (-5) = 1 :=
    (legendreSym.eq_one_iff p h).mpr (by simpa using hs)
  rw [dirichletFive_eq_mul_legendreSym p hp₂, hsign, Int.cast_one, mul_one]

/-- At an odd prime where `-5` is nonsquare, the two Dirichlet signs are opposite. -/
public theorem dirichletFive_eq_neg_dirichletNegFour_of_not_isSquare (hp₂ : p ≠ 2)
    (hs : ¬ IsSquare (-5 : ZMod p)) : dirichletFive p = -dirichletNegFour p := by
  have hsign : legendreSym p (-5) = -1 :=
    (legendreSym.eq_neg_one_iff p).mpr (by simpa using hs)
  rw [dirichletFive_eq_mul_legendreSym p hp₂, hsign, Int.cast_neg, Int.cast_one, mul_neg, mul_one]

end Masullo
