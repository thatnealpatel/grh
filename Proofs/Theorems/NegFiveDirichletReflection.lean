module

public import Lemmas.NegFiveCompletedReflection
import Lemmas.NegFiveGammaReflection

/-! Exact norm reflection for the explicit quadratic class denominator. -/

open Complex

namespace Masullo

/-- On `Re s = -1/2`, reflection multiplies the norm on `Re s = 3/2`
by the explicit quadratic factor below, with no nonvanishing hypothesis on the product. -/
public theorem qSqrtNegFiveDirichletProduct_norm_reflection (t : ℝ) :
    ‖qSqrtNegFiveDirichletProduct (-(1 / 2 : ℂ) + t * I)‖ =
      (5 / Real.pi ^ 2) * (t ^ 2 + 1 / 4) * ‖qSqrtNegFiveDirichletProduct (3 / 2 - t * I)‖ := by
  let s : ℂ := -(1 / 2 : ℂ) + t * I
  have hr : s.re = -(1 / 2 : ℝ) := by simp [s]
  have hg := negFive_gamma_norm t s rfl
  have hn := negFive_gamma_ne_zero t s rfl
  have hpos : 0 < ‖Gammaℂ (1 - s)‖ := by rw [hg]; have := norm_pos_iff.mpr hn; positivity
  have h := qSqrtNegFiveDirichletProduct_gamma_reflection hr hn (norm_pos_iff.mp hpos)
  rw [hg] at h
  rw [show (3 / 2 - t * I : ℂ) = 1 - s by dsimp [s]; ring]
  apply mul_right_cancel₀ (norm_ne_zero_iff.mpr hn)
  convert h using 1; ring

end Masullo
