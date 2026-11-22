module

public import Lemmas.NegFiveCompletedReflection

/-! The shifted complex Gamma factor regularizes the forward quotient. -/

open Complex DirichletCharacter

namespace Masullo

/-- The regularized forward factor for the quadratic class denominator. -/
@[expose] public noncomputable def qSqrtNegFiveForwardB (U : ℂ → ℂ) (s : ℂ) : ℂ :=
  (2 * Real.pi : ℂ) * U s * Gammaℂ (s + 1)

/-- The shifted Gamma argument has positive real part throughout this half-plane. -/
public theorem qSqrtNegFiveForwardB_differentiableOn {U : ℂ → ℂ}
    (hU : Differentiable ℂ U) :
    DifferentiableOn ℂ (qSqrtNegFiveForwardB U) {s : ℂ | -1 < s.re} := by
  intro s hs
  have hs' : 0 < (s + 1).re := by
    rw [add_re, one_re]
    exact neg_lt_iff_pos_add.mp hs
  have hπ : (2 * Real.pi : ℂ) ≠ 0 :=
    mul_ne_zero two_ne_zero (ofReal_ne_zero.mpr Real.pi_ne_zero)
  have hΓ : DifferentiableAt ℂ Gammaℂ (s + 1) := by
    unfold Gammaℂ
    have hpow : DifferentiableAt ℂ (fun z : ℂ ↦ (2 * Real.pi : ℂ) ^ (-z)) (s + 1) :=
      differentiableAt_id.neg.const_cpow (Or.inl hπ)
    exact (hpow.const_mul 2).mul (hasDerivAt_Gamma_of_re_pos hs').differentiableAt
  exact (((hU s).const_mul (2 * Real.pi : ℂ)).mul
    (hΓ.comp s (differentiableAt_id.add_const 1))).differentiableWithinAt

/-- The regularization agrees with the completed quotient wherever the denominator is nonzero. -/
public theorem qSqrtNegFiveForwardB_eq_div (U : ℂ → ℂ) {s : ℂ}
    (hD : qSqrtNegFiveDirichletProduct s ≠ 0) :
    qSqrtNegFiveForwardB U s =
      s * (U s * (completedLFunction dirichletNegFour s * completedLFunction dirichletFive s)) /
        qSqrtNegFiveDirichletProduct s := by
  have hprod := qSqrtNegFiveDirichletProduct_eq_completed_div s
  have hΓ : Gammaℂ s ≠ 0 := fun h ↦ hD (by rw [hprod, h, div_zero])
  have hs : s ≠ 0 := fun h ↦ hΓ (by simp [h, Gammaℂ_def, Complex.Gamma_zero])
  apply (eq_div_iff hD).2
  rw [qSqrtNegFiveForwardB, Gammaℂ_add_one hs, ← (eq_div_iff hΓ).1 hprod]
  field_simp [Real.pi_ne_zero]

end Masullo
