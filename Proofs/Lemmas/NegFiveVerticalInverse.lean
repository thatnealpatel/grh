module

public import Theorems.NegFiveDirichletReflection
import Lemmas.DirichletRightAnchor

/-! Uniform inverse bounds on the vertical edges of the quadratic class contour. -/

open Complex

namespace Masullo

/-- The class denominator is nonzero on both vertical edges, and its reciprocal is uniformly
bounded there. -/
public theorem qSqrtNegFiveDirichletProduct_vertical_inverse :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w : ℂ, w.re = -(1 / 2 : ℝ) ∨ w.re = 2 →
      qSqrtNegFiveDirichletProduct w ≠ 0 ∧ ‖(qSqrtNegFiveDirichletProduct w)⁻¹‖ ≤ C := by
  obtain ⟨b₃, hb₃, h₃⟩ := exists_qSqrtNegFiveDirichletProduct_threeHalves_anchor
  obtain ⟨b₂, hb₂, h₂⟩ := exists_qSqrtNegFiveDirichletProduct_right_anchor
  let a : ℝ := 5 / Real.pi ^ 2
  have ha : 0 < a := by dsimp [a]; positivity
  let d := min (a * (1 / 4) * b₃) b₂
  have hd : 0 < d := lt_min (by positivity) hb₂
  refine ⟨d⁻¹, inv_nonneg.mpr hd.le, fun w hw ↦ ?_⟩
  have hnorm : d ≤ ‖qSqrtNegFiveDirichletProduct w‖ := by
    rcases hw with hw | hw
    · have hw' : w = -(1 / 2 : ℂ) + (w.im : ℂ) * I := by
        simpa [hw] using (re_add_im w).symm
      have hright : b₃ ≤ ‖qSqrtNegFiveDirichletProduct (3 / 2 - (w.im : ℂ) * I)‖ :=
        h₃ (by simp)
      rw [hw', qSqrtNegFiveDirichletProduct_norm_reflection]
      calc
        d ≤ a * (1 / 4) * b₃ := min_le_left _ _
        _ ≤ a * (w.im ^ 2 + 1 / 4) * b₃ :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (sq_nonneg _)) ha.le) hb₃.le
        _ ≤ _ := mul_le_mul_of_nonneg_left hright (by positivity)
    · have hw' : w = 2 + (w.im : ℂ) * I := by
        simpa [hw] using (re_add_im w).symm
      exact (min_le_right _ _).trans (by simpa only [← hw'] using h₂ w.im)
  exact ⟨norm_pos_iff.mp (hd.trans_le hnorm), by rw [norm_inv]; exact inv_anti₀ hd hnorm⟩

end Masullo
