module

public import Theorems.HeckeDirichletFactorization

/-!
# The Dirichlet characters of discriminants `-4` and `5`

Both characters are primitive and self-inverse, with opposite parities.
-/

namespace Masullo

public theorem dirichletNegFour_odd : dirichletNegFour.Odd := by
  have h : ZMod.χ₄ (-1 : ZMod 4) = -1 := by decide
  change (Int.castRingHom ℂ) (ZMod.χ₄ (-1 : ZMod 4)) = -1
  simp [h]

public theorem dirichletFive_even : dirichletFive.Even := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  have h := (quadraticChar_one_iff_isSquare (show (-1 : ZMod 5) ≠ 0 by decide)).2
    (show IsSquare (-1 : ZMod 5) from ⟨2, by decide⟩)
  change (Int.castRingHom ℂ) (quadraticChar (ZMod 5) (-1)) = 1
  simp [h]

public theorem dirichletNegFour_primitive : dirichletNegFour.IsPrimitive := by
  have hd := dirichletNegFour.conductor_dvd_level
  obtain ⟨k, hk, he⟩ := (Nat.dvd_prime_pow Nat.prime_two (m := 2)).1 hd
  interval_cases k
  · exact (dirichletNegFour_ne_one (DirichletCharacter.eq_one_iff_conductor_eq_one.2 he)).elim
  · have hf := dirichletNegFour.factorsThrough_conductor
    rw [show dirichletNegFour.conductor = 2 from he] at hf
    obtain ⟨hd₂, ψ, hψ⟩ := hf
    -- Reduction modulo 2 identifies -1 with 1, contrary to oddness.
    have h := DirichletCharacter.changeLevel_eq_cast_of_dvd' ψ hd₂ (a := -1)
      (show IsCoprime (-1 : ℤ) 4 from ⟨-1, 0, by decide⟩)
    rw [← hψ] at h
    have hodd : dirichletNegFour (-1) = -1 := dirichletNegFour_odd
    simp only [Int.cast_neg, Int.cast_one, hodd, show (-1 : ZMod 2) = 1 by decide, map_one] at h
    norm_num at h
  · exact he

public theorem dirichletFive_primitive : dirichletFive.IsPrimitive := by
  rcases (Nat.dvd_prime (by decide : Nat.Prime 5)).1 dirichletFive.conductor_dvd_level with h | h
  · exact (dirichletFive_ne_one (DirichletCharacter.eq_one_iff_conductor_eq_one.2 h)).elim
  · exact h

public theorem dirichletNegFour_inv : dirichletNegFour⁻¹ = dirichletNegFour :=
  (ZMod.isQuadratic_χ₄.comp (Int.castRingHom ℂ)).inv

public theorem dirichletFive_inv : dirichletFive⁻¹ = dirichletFive := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  exact ((quadraticChar_isQuadratic (ZMod 5)).comp (Int.castRingHom ℂ)).inv

end Masullo
