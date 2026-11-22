module

public import Theorems.NegFiveDirichletReflection
import Lemmas.DirichletRightAnchor

/-! A uniform reciprocal estimate on the left line. -/

open Complex

namespace Masullo

/-- The reciprocal is `O(1 / (t² + 1/4))`, uniformly for all real heights. -/
public theorem exists_qSqrtNegFiveDirichletProduct_inv_norm_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ,
      ‖(qSqrtNegFiveDirichletProduct (-(1 / 2 : ℂ) + t * I))⁻¹‖ ≤ C / (t ^ 2 + 1 / 4) := by
  obtain ⟨b, hb, h⟩ := exists_qSqrtNegFiveDirichletProduct_threeHalves_anchor
  let a := 5 / Real.pi ^ 2
  have ha : 0 < a := by dsimp [a]; positivity
  refine ⟨1 / (a * b), by positivity, fun t ↦ ?_⟩
  have hright : b ≤ ‖qSqrtNegFiveDirichletProduct (3 / 2 - t * I)‖ := h (by simp)
  have ht : 0 < t ^ 2 + 1 / 4 := by positivity
  rw [norm_inv, qSqrtNegFiveDirichletProduct_norm_reflection, ← one_div]
  calc
    _ ≤ 1 / (a * (t ^ 2 + 1 / 4) * b) :=
      one_div_le_one_div_of_le (by positivity) (mul_le_mul_of_nonneg_left hright (by positivity))
    _ = _ := by rw [div_div, mul_right_comm]

end Masullo
