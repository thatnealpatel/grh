module

public import Lemmas.NegFiveForwardRegularization
import Lemmas.NegFiveVerticalInverse
import Lemmas.NegFiveHorizontalInverse
import Lemmas.RegularizedStripBound

/-! The forward closed-strip estimate for the quadratic class denominator of `ℚ(√-5)`. -/

open Complex DirichletCharacter Set

namespace Masullo

/-- If `Φ = U H_D` has rapid value decay on the closed strip, then every polynomial
weight of the explicit regularization `B(s) = 2π U(s) Γℂ(s+1)` is bounded there.
The decay assumption concerns only `Φ`, including at the zeros of the denominator. -/
public theorem qSqrtNegFiveForwardB_closed_strip {U Φ : ℂ → ℂ} (hU : Differentiable ℂ U)
    (hΦ : ∀ s, Φ s = U s * (completedLFunction dirichletNegFour s * completedLFunction dirichletFive s))
    (hrapid : ∀ m : ℕ, ∃ M : ℝ, ∀ s : ℂ, -(1 / 2 : ℝ) ≤ s.re → s.re ≤ 2 →
      (1 + ‖s‖) ^ m * ‖Φ s‖ ≤ M) :
    ∀ N : ℕ, ∃ C : ℝ, ∀ s : ℂ, -(1 / 2 : ℝ) ≤ s.re → s.re ≤ 2 →
      ‖s ^ N * qSqrtNegFiveForwardB U s‖ ≤ C := by
  apply rapid_regularization_on_strip (D := qSqrtNegFiveDirichletProduct) (by norm_num) _ _ hrapid
    qSqrtNegFiveDirichletProduct_vertical_inverse qSqrtNegFiveDirichletProduct_horizontal_inverse
  · apply DifferentiableOn.diffContOnCl
    apply (qSqrtNegFiveForwardB_differentiableOn hU).mono
    rw [closure_preimage_re, closure_Ioo (by norm_num)]
    intro s hs
    exact lt_of_lt_of_le (by norm_num : (-1 : ℝ) < -(1 / 2)) hs.1
  · intro s ha hb hn
    rw [hΦ]
    exact qSqrtNegFiveForwardB_eq_div U hn

end Masullo
