module

public import Theorems.HeckeDirichletFactorization
import Mathlib.NumberTheory.LSeries.Dirichlet

/-!
# Uniform right-hand anchor for the quadratic class denominator

On each half-plane `σ ≤ Re s` with `1 < σ`, the Möbius-twisted Dirichlet series is the reciprocal of the
Dirichlet L-function and has a height-independent absolute majorant.
-/

open scoped ArithmeticFunction.Moebius

namespace Masullo

/-- The Möbius series gives a height-independent positive lower bound for
Dirichlet L-functions on any fixed right half-plane strictly inside `Re s > 1`. -/
public theorem exists_dirichlet_anchor_at {σ : ℝ} (hσ : 1 < σ) :
    ∃ b : ℝ, 0 < b ∧ ∀ {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
      {s : ℂ}, σ ≤ s.re → b ≤ ‖χ.LFunction s‖ := by
  let F (n : ℕ) := ‖LSeries.term 1 (σ : ℂ) n‖
  have hF : Summable F := (LSeriesSummable_one_iff.mpr hσ).norm
  let B := 1 + ∑' n, F n
  have hB : 0 < B := by dsimp [B]; positivity
  refine ⟨1 / B, by positivity, fun {q} _ χ {s} hs ↦ ?_⟩
  let f (n : ℕ) : ℂ := χ n * (μ n : ℂ)
  have h₁ := hσ.trans_le hs
  have hf : LSeriesSummable f s := χ.LSeriesSummable_mul
    (ArithmeticFunction.LSeriesSummable_moebius_iff.mpr h₁)
  have hle (n : ℕ) : ‖LSeries.term f s n‖ ≤ F n := by
    apply le_trans (LSeries.norm_term_le (g := 1) s ?_) (LSeries.norm_term_le_of_re_le_re 1 hs n)
    simp only [f, norm_mul, Complex.norm_intCast, Pi.one_apply, norm_one]
    exact (mul_le_of_le_one_left (abs_nonneg _) (χ.norm_le_one _)).trans
      (by exact_mod_cast ArithmeticFunction.abs_moebius_le_one)
  have hbound : ‖LSeries f s‖ ≤ B := calc
    _ ≤ ∑' n, ‖LSeries.term f s n‖ := norm_tsum_le_tsum_norm hf.norm
    _ ≤ ∑' n, F n := hf.norm.tsum_le_tsum hle hF
    _ ≤ B := by dsimp [B]; linarith
  have hprod : χ.LFunction s * LSeries f s = 1 := by
    rw [χ.LFunction_eq_LSeries h₁]
    exact DirichletCharacter.LSeries.mul_mu_eq_one χ h₁
  apply (div_le_iff₀ hB).2
  calc
    1 = ‖χ.LFunction s‖ * ‖LSeries f s‖ := by rw [← norm_mul, hprod, norm_one]
    _ ≤ _ := mul_le_mul_of_nonneg_left hbound (norm_nonneg _)

/-- A single positive lower bound works for the whole right-hand half-plane. -/
public theorem exists_qSqrtNegFiveDirichletProduct_threeHalves_anchor :
    ∃ b : ℝ, 0 < b ∧ ∀ {s : ℂ}, 3 / 2 ≤ s.re → b ≤ ‖qSqrtNegFiveDirichletProduct s‖ := by
  obtain ⟨b, hb, h⟩ := exists_dirichlet_anchor_at (show (1 : ℝ) < 3 / 2 by norm_num)
  refine ⟨b * b, mul_pos hb hb, fun hs ↦ ?_⟩
  rw [qSqrtNegFiveDirichletProduct, norm_mul]
  exact mul_le_mul (h dirichletNegFour hs) (h dirichletFive hs) hb.le (norm_nonneg _)

/-- The explicit entire class denominator has a uniform positive lower
bound on the whole right-hand line, independently of any Hecke hypotheses. -/
public theorem exists_qSqrtNegFiveDirichletProduct_right_anchor :
    ∃ b : ℝ, 0 < b ∧ ∀ t : ℝ, b ≤ ‖qSqrtNegFiveDirichletProduct (2 + (t : ℂ) * Complex.I)‖ := by
  obtain ⟨b, hb, h⟩ := exists_qSqrtNegFiveDirichletProduct_threeHalves_anchor
  exact ⟨b, hb, fun t ↦ h (by norm_num)⟩

end Masullo
