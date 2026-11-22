module

public import Theorems.IdealClassDirichletSigns
public import Theorems.IdealClassHeckeCharacter
public import Theorems.IdealClassSignCharacter
public import Theorems.IdealClassSplitPrimeFiber

/-!
# The grouped Hecke denominator at an odd split rational prime

Both places in the rational-prime fiber contribute to (3.2.1.7), p. 124.
Their residue degrees are one, and the two Dirichlet signs agree.
-/

open NumberField Polynomial

namespace Masullo

/-- The two retained places above a split prime give the two Dirichlet factors. -/
public theorem qSqrtNegFive_heckeRationalDenominator_of_split_root (p : Nat.Primes)
    (hp₂ : p.val ≠ 2) (hp₅ : p.val ≠ 5) (r : ZMod p.val) (hr : r ^ 2 = -5) :
    heckeRationalDenominator (idealClassHeckeCharacter qSqrtNegFiveClassCharacter) p =
      (1 - C (dirichletNegFour p.val) * X) * (1 - C (dirichletFive p.val) * X) := by
  classical
  let _ : Fact p.val.Prime := ⟨p.2⟩
  have hsign := dirichletFive_eq_dirichletNegFour_of_isSquare p.val hp₂ hp₅
    ((isSquare_iff_exists_sq _).2 ⟨r, hr.symm⟩)
  obtain ⟨v₁, v₂, _, _, hne, hexhaust⟩ := qSqrtNegFive_heckePrimeFiber_of_split_root p hp₂ hp₅ r hr
  let f (v : heckePrimeFiber QSqrtNegFive p) : ℂ[X] :=
    ((idealClassHeckeCharacter qSqrtNegFiveClassCharacter).localPolynomial v.1).comp
      (X ^ v.1.asIdeal.inertiaDeg ℤ)
  have hprod : heckeRationalDenominator (idealClassHeckeCharacter qSqrtNegFiveClassCharacter) p =
      f v₁ * f v₂ :=
    Finset.prod_eq_mul_of_mem v₁ v₂ (Finset.mem_univ _) (Finset.mem_univ _) hne
      (fun v _ hv ↦ ((hexhaust v).elim hv.1 hv.2).elim)
  have hfactor (v : heckePrimeFiber QSqrtNegFive p) : f v = 1 - C (dirichletNegFour p.val) * X := by
    have hd := (qSqrtNegFive_heckePrimeFiber_residue_of_split_root p hp₂ hp₅ r hr v).2
    have hv : Odd (heckeRationalPrime v.1).val := by
      rw [v.2]
      exact p.2.odd_of_ne_two hp₂
    have hχ := qSqrtNegFive_split_classCharacter_primeTwo v.1 hd hv
      qSqrtNegFiveClassCharacter qSqrtNegFiveClassCharacter_primeTwo
    dsimp only [f]
    rw [hd, pow_one, comp_X, HeckeCharacter.localPolynomial,
      ite_eq_left (idealClassHeckeCharacter_isUnramifiedAt qSqrtNegFiveClassCharacter v.1),
      idealClassHeckeCharacter_localValue]
    change 1 - C (qSqrtNegFiveClassCharacter (qSqrtNegFivePlaceClass v.1)) * X = _
    rw [hχ, v.2]
  rw [hprod, hfactor v₁, hfactor v₂, hsign]

end Masullo
