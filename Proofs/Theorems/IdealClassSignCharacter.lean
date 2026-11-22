module

public import Theorems.IdealClassTwoClasses

/-!
# The sign character of the ideal class group of ℚ(√-5)

The two ideal classes give a norm-one character with value `-1` on the
class of the prime above two.
-/

open NumberField

namespace Masullo

local notation "O" => 𝓞 QSqrtNegFive
local notation "c₂" => qSqrtNegFivePlaceClass qSqrtNegFivePrimeTwo

private theorem primeTwoClass_mul_self : c₂ * c₂ = 1 := by
  rcases qSqrtNegFive_class_eq_one_or_primeTwo (c₂ * c₂) with h | h
  · exact h
  · exact (qSqrtNegFivePrimeTwo_class_ne_one (mul_left_cancel (h.trans (mul_one c₂).symm))).elim

/-- The sign character, equal to `1` at the identity and `-1` at the other class. -/
public noncomputable def qSqrtNegFiveClassCharacter : ClassGroup O →* ℂ := by
  classical
  exact
    { toFun := fun c ↦ if c = 1 then 1 else -1
      map_one' := by simp
      map_mul' := fun c d ↦ by
        rcases qSqrtNegFive_class_eq_one_or_primeTwo c with rfl | rfl
        · simp
        · rcases qSqrtNegFive_class_eq_one_or_primeTwo d with rfl | rfl
          · simp
          · simp [primeTwoClass_mul_self, qSqrtNegFivePrimeTwo_class_ne_one] }

/-- Every value of the class character has norm one. -/
public theorem norm_qSqrtNegFiveClassCharacter (c : ClassGroup O) :
    ‖qSqrtNegFiveClassCharacter c‖ = 1 := by
  classical
  by_cases hc : c = 1 <;> simp [qSqrtNegFiveClassCharacter, hc]

/-- The class of the prime above two has the negative sign. -/
public theorem qSqrtNegFiveClassCharacter_primeTwo : qSqrtNegFiveClassCharacter c₂ = -1 := by
  classical
  simp [qSqrtNegFiveClassCharacter, qSqrtNegFivePrimeTwo_class_ne_one]

end Masullo
