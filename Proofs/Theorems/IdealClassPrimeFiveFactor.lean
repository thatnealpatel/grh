module

public import Theorems.IdealClassHeckeCharacter
public import Theorems.IdealClassPrimeFive

/-!
# The grouped Hecke denominator at five

A single place of norm `p` contributes its local polynomial unchanged
when the factors of (3.2.1.7), p. 124, are grouped over `p`. Above five in
`ℚ(√-5)` this retained place has principal ideal, so its denominator is
`1 - X`, matching the two Dirichlet factors.
-/

open IsDedekindDomain NumberField Polynomial

namespace Masullo

variable {K : Type*} [Field K] [NumberField K]

/-- A unique place of norm `p` over `p` contributes its degree-one local denominator. -/
public theorem heckeRationalDenominator_idealClassHeckeCharacter_of_unique_prime_absNorm
    (φ : ClassGroup (𝓞 K) →* ℂ) (p : Nat.Primes) (v : HeightOneSpectrum (𝓞 K))
    (hunder : v.asIdeal.under ℤ = Ideal.span {(p.val : ℤ)})
    (hnorm : v.asIdeal.absNorm = p.val)
    (hunique : ∀ P : Ideal (𝓞 K), P.IsPrime → (p.val : 𝓞 K) ∈ P → P = v.asIdeal) :
    heckeRationalDenominator (idealClassHeckeCharacter φ) p =
      1 - C ((idealClassHeckeCharacter φ).localValue v) * X := by
  classical
  have hp : (v.asIdeal.under ℤ).absNorm = p.val := by
    rw [hunder]
    simp
  let w : heckePrimeFiber K p := ⟨v, Subtype.ext hp⟩
  have hw (u : heckePrimeFiber K p) : u = w := by
    apply Subtype.ext (HeightOneSpectrum.ext_iff.mpr ?_)
    apply hunique _ u.1.isPrime
    have hmem : (p.val : ℤ) ∈ u.1.asIdeal.under ℤ := by
      rw [heckePrimeFiber_under_eq_span p u]
      exact Ideal.subset_span (Set.mem_singleton _)
    simpa using (Ideal.mem_under ℤ u.1.asIdeal).mp hmem
  let _ : Subsingleton (heckePrimeFiber K p) := ⟨fun u z ↦ (hw u).trans (hw z).symm⟩
  let _ : v.asIdeal.IsPrime := v.isPrime
  have hpow := Ideal.absNorm_pow_inertiaDeg (v.asIdeal.under ℤ) v.asIdeal
  rw [hp, hnorm] at hpow
  have hd : v.asIdeal.inertiaDeg ℤ = 1 :=
    Nat.pow_right_injective p.2.two_le (hpow.trans (pow_one _).symm)
  rw [heckeRationalDenominator, Fintype.prod_subsingleton _ w]
  change ((idealClassHeckeCharacter φ).localPolynomial v).comp (X ^ v.asIdeal.inertiaDeg ℤ) = _
  rw [hd, pow_one, comp_X, HeckeCharacter.localPolynomial,
    ite_eq_left (idealClassHeckeCharacter_isUnramifiedAt φ v)]

/-- The sole place above five is retained and has class coefficient one for every `φ`. -/
public theorem qSqrtNegFive_heckeRationalDenominator_at_five_eq_one_sub_X
    (φ : ClassGroup (𝓞 QSqrtNegFive) →* ℂ) :
    heckeRationalDenominator (idealClassHeckeCharacter φ) ⟨5, by decide⟩ = 1 - X := by
  rw [heckeRationalDenominator_idealClassHeckeCharacter_of_unique_prime_absNorm φ
    ⟨5, by decide⟩ qSqrtNegFivePrimeFive qSqrtNegFivePrimeFive_under
    qSqrtNegFivePrimeFive_absNorm qSqrtNegFivePrimeFive_unique,
    idealClassHeckeCharacter_localValue]
  change 1 - C (φ (qSqrtNegFivePlaceClass qSqrtNegFivePrimeFive)) * X = _
  rw [qSqrtNegFivePrimeFive_class_eq_one, map_one, C_1, one_mul]

/-- The grouped denominator at five matches the factors with coefficients `(1, 0)`. -/
public theorem qSqrtNegFive_heckeRationalDenominator_at_five
    (φ : ClassGroup (𝓞 QSqrtNegFive) →* ℂ) :
    heckeRationalDenominator (idealClassHeckeCharacter φ) ⟨5, by decide⟩ =
      (1 - C (dirichletNegFour (5 : ℕ)) * X) * (1 - C (dirichletFive (5 : ℕ)) * X) := by
  have h₄ : dirichletNegFour (5 : ZMod 4) = 1 := by
    rw [show (5 : ZMod 4) = 1 by decide, map_one]
  have h₅ : dirichletFive (5 : ZMod 5) = 0 := by
    let _ : Fact (Nat.Prime 5) := ⟨by decide⟩
    rw [show (5 : ZMod 5) = 0 by decide, MulChar.map_zero]
  simp [qSqrtNegFive_heckeRationalDenominator_at_five_eq_one_sub_X, h₄, h₅]

end Masullo
