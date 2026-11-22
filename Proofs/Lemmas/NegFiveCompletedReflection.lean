module

public import Lemmas.NegFiveDirichletCharacters
import Mathlib.NumberTheory.LSeries.Nonvanishing

/-! The primitive functional equations contribute `4 * 5` on the left line. The
odd and even Gamma factors together are exactly Deligne’s complex Gamma factor. -/

open Complex DirichletCharacter

namespace Masullo

private theorem completed_norm_reflection {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hprim : χ.IsPrimitive) (hinv : χ⁻¹ = χ) {s : ℂ} (hs : s.re = -(1 / 2 : ℝ)) :
    ‖completedLFunction χ s‖ = N * ‖completedLFunction χ (1 - s)‖ := by
  have h := hprim.completedLFunction_one_sub (1 - s)
  rw [sub_sub_cancel, hinv] at h
  have hre : (1 - s - 1 / 2).re = 1 := by simp [hs]
  simpa only [norm_mul, norm_natCast_cpow_of_pos (NeZero.pos N), hre, Real.rpow_one,
    norm_rootNumber hprim, mul_one] using congrArg norm h

private noncomputable abbrev completedProduct (s : ℂ) :=
  completedLFunction dirichletNegFour s * completedLFunction dirichletFive s

private theorem product_eq_completed_div (s : ℂ) :
    qSqrtNegFiveDirichletProduct s = completedProduct s / Gammaℂ s := by
  rw [qSqrtNegFiveDirichletProduct,
    dirichletNegFour.LFunction_eq_completed_div_gammaFactor s (.inr (by decide)),
    dirichletFive.LFunction_eq_completed_div_gammaFactor s (.inr (by decide)),
    dirichletNegFour_odd.gammaFactor_def, dirichletFive_even.gammaFactor_def, div_mul_div_comm,
    mul_comm (Gammaℝ (s + 1)), Gammaℝ_mul_Gammaℝ_add_one]

/-- Norm reflection before evaluating the quotient of archimedean factors. -/
public theorem qSqrtNegFiveDirichletProduct_gamma_reflection {s : ℂ} (hr : s.re = -(1 / 2 : ℝ))
    (h₁ : Gammaℂ s ≠ 0) (h₂ : Gammaℂ (1 - s) ≠ 0) :
    ‖qSqrtNegFiveDirichletProduct s‖ * ‖Gammaℂ s‖ =
      20 * ‖qSqrtNegFiveDirichletProduct (1 - s)‖ * ‖Gammaℂ (1 - s)‖ := by
  have hc : ‖completedProduct s‖ = 20 * ‖completedProduct (1 - s)‖ := by
    simp only [completedProduct, norm_mul,
      completed_norm_reflection dirichletNegFour_primitive dirichletNegFour_inv hr,
      completed_norm_reflection dirichletFive_primitive dirichletFive_inv hr]
    push_cast
    ring
  rw [product_eq_completed_div, product_eq_completed_div, norm_div, norm_div, hc]
  field_simp [norm_ne_zero_iff.mpr h₁, norm_ne_zero_iff.mpr h₂]

end Masullo
