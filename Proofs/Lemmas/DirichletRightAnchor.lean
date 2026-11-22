module

public import Theorems.HeckeDirichletFactorization
import Mathlib.NumberTheory.LSeries.Dirichlet

/-!
# Uniform right-hand anchor for the quadratic class denominator

On `Re s = 2`, the Möbius-twisted Dirichlet series is the reciprocal of the
Dirichlet L-function and has a height-independent absolute majorant.
-/

open scoped ArithmeticFunction.Moebius

namespace Masullo

private theorem exists_uniform_dirichlet_right_anchor :
    ∃ b : ℝ, 0 < b ∧ ∀ {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
      {s : ℂ}, s.re = 2 → b ≤ ‖χ.LFunction s‖ := by
  let F : ℕ → ℝ := fun n ↦ ‖LSeries.term 1 (2 : ℂ) n‖
  have hF : Summable F := (LSeriesSummable_one_iff.mpr (by norm_num)).norm
  let B := 1 + ∑' n, F n
  have hFsum : 0 ≤ ∑' n, F n := tsum_nonneg fun _ ↦ norm_nonneg _
  have hB : 0 < B := by dsimp [B]; linarith
  refine ⟨B⁻¹, inv_pos.mpr hB, fun {q} _ χ {s} hs ↦ ?_⟩
  have hs' : 1 < s.re := by rw [hs]; norm_num
  let f : ℕ → ℂ := fun n ↦ χ n * (μ n : ℂ)
  have hf : LSeriesSummable f s :=
    DirichletCharacter.LSeriesSummable_mul χ (ArithmeticFunction.LSeriesSummable_moebius_iff.mpr hs')
  have hle (n : ℕ) : ‖LSeries.term f s n‖ ≤ F n := by
    have hn : ‖f n‖ ≤ 1 := by
      have hμ : ‖(μ n : ℂ)‖ ≤ 1 := by
        rw [Complex.norm_intCast]
        exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := n))
      dsimp [f]
      rw [norm_mul]
      exact (mul_le_of_le_one_left (norm_nonneg _) (χ.norm_le_one _)).trans hμ
    have hs₂ : (2 : ℂ).re = 2 := by norm_num
    simpa only [F, LSeries.norm_term_eq, hs, hs₂, Pi.one_apply, norm_one] using
      (LSeries.norm_term_le (g := 1) s (n := n) (by simpa only [Pi.one_apply, norm_one] using hn))
  have hnorm : ‖LSeries f s‖ ≤ B := by
    calc
      _ ≤ ∑' n, ‖LSeries.term f s n‖ := norm_tsum_le_tsum_norm hf.norm
      _ ≤ ∑' n, F n := hf.norm.tsum_le_tsum hle hF
      _ ≤ B := by dsimp [B]; linarith
  have he : χ.LFunction s * LSeries f s = 1 := by
    rw [χ.LFunction_eq_LSeries hs']
    exact DirichletCharacter.LSeries.mul_mu_eq_one χ hs'
  have hnorme : ‖χ.LFunction s‖ * ‖LSeries f s‖ = 1 := by
    simpa only [norm_mul, norm_one] using congrArg norm he
  rw [← one_div]
  apply (div_le_iff₀ hB).2
  exact hnorme ▸ mul_le_mul_of_nonneg_left hnorm (norm_nonneg _)

/-- The explicit entire class denominator has a uniform positive lower
bound on the whole right-hand line, independently of any Hecke hypotheses. -/
public theorem exists_qSqrtNegFiveDirichletProduct_right_anchor :
    ∃ b : ℝ, 0 < b ∧ ∀ t : ℝ, b ≤ ‖qSqrtNegFiveDirichletProduct (2 + (t : ℂ) * Complex.I)‖ := by
  obtain ⟨b, hb, h⟩ := exists_uniform_dirichlet_right_anchor
  refine ⟨b * b, mul_pos hb hb, fun t ↦ ?_⟩
  have hs : (2 + (t : ℂ) * Complex.I).re = 2 := by simp
  rw [qSqrtNegFiveDirichletProduct, norm_mul]
  exact mul_le_mul (h dirichletNegFour hs) (h dirichletFive hs) hb.le (norm_nonneg _)

end Masullo
