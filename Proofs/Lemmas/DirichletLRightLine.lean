module

public import Lemmas.CompactLogMellinInversion
public import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.NumberTheory.LSeries.Dirichlet

/-! Integrability of the reflected Mellin test on an ordinary Dirichlet L-function's right line. -/

open Complex MeasureTheory
open scoped ContDiff LSeries.notation

namespace Masullo

/-- The twisted von Mangoldt series gives a height-independent bound on a
whole right half-plane strictly inside the half-plane of absolute convergence. -/
public theorem exists_norm_logDeriv_dirichletL_le {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) {a : ℝ} (ha : 1 < a) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ s : ℂ, a ≤ s.re → ‖logDeriv χ.LFunction s‖ ≤ B := by
  let b := ↗χ * ↗ArithmeticFunction.vonMangoldt
  let c (n : ℕ) := ‖LSeries.term b (a : ℂ) n‖
  have hsum : Summable c := (χ.LSeriesSummable_twist_vonMangoldt (s := (a : ℂ)) ha).norm
  refine ⟨∑' n, c n, tsum_nonneg (fun _ ↦ norm_nonneg _), fun s hs ↦ ?_⟩
  have h₁ := ha.trans_le hs
  have hlog : logDeriv χ.LFunction s = -LSeries b s := by
    rw [logDeriv_apply, χ.deriv_LFunction_eq_deriv_LSeries h₁, χ.LFunction_eq_LSeries h₁,
      χ.LSeries_twist_vonMangoldt_eq h₁, neg_div, neg_neg]
  rw [hlog, norm_neg]
  have hsum' := (χ.LSeriesSummable_twist_vonMangoldt h₁).norm
  exact (norm_tsum_le_tsum_norm hsum').trans (hsum'.tsum_le_tsum
    (LSeries.norm_term_le_of_re_le_re b (by simpa using hs)) hsum)

/-- On `Re s = a > 1`, the absolutely convergent twisted von Mangoldt series gives a
uniformly bounded multiplier for the reflected compact log Mellin test. -/
public theorem integrable_compactLogMellin_dirichletL_reflected {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) {g : ℝ → ℂ} (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g)
    {a : ℝ} (ha : 1 < a) : Integrable (fun t : ℝ ↦
      let s := (a : ℂ) + (t : ℂ) * I
      compactLogMellin g (1 - s) * logDeriv χ.LFunction s) := by
  let s (t : ℝ) : ℂ := a + (t : ℂ) * I
  let b := ↗χ * ↗ArithmeticFunction.vonMangoldt
  let F (n : ℕ) (t : ℝ) := LSeries.term b (s t) n
  let c (n : ℕ) := ‖LSeries.term b (a : ℂ) n‖
  have hsum : Summable c := (χ.LSeriesSummable_twist_vonMangoldt (s := (a : ℂ)) ha).norm
  have hre (t : ℝ) : (s t).re = a := by simp [s]
  have hnorm (n t) : ‖F n t‖ = c n := by
    simp only [F, c, LSeries.norm_term_eq, hre, ofReal_re]
  have hlog (t) : logDeriv χ.LFunction (s t) = -(∑' n, F n t) := by
    have ht : 1 < (s t).re := (hre t).symm ▸ ha
    change logDeriv χ.LFunction (s t) = -LSeries b (s t)
    rw [logDeriv_apply, χ.deriv_LFunction_eq_deriv_LSeries ht, χ.LFunction_eq_LSeries ht,
      χ.LSeries_twist_vonMangoldt_eq ht, neg_div, neg_neg]
  have hs : Continuous s := by dsimp [s]; fun_prop
  have hcont (n) : Continuous (F n) := by
    rcases eq_or_ne n 0 with rfl | hn
    · simp only [F, LSeries.term_zero]; exact continuous_const
    · simp only [F, LSeries.term_of_ne_zero hn]
      have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn
      exact continuous_const.div ((continuous_const_cpow' hn').comp hs) (fun t ↦ by simp [hn'])
  have hL : Continuous (fun t ↦ logDeriv χ.LFunction (s t)) := by
    simp only [hlog]
    exact (continuous_tsum hcont hsum fun n t ↦ (hnorm n t).le).neg
  have hW := integrable_compactLogMellin_reflected_vertical hg hc a
  refine (hW.norm.mul_const (∑' n, c n)).mono'
    (hW.aestronglyMeasurable.mul hL.aestronglyMeasurable)
    (Filter.Eventually.of_forall fun t ↦ ?_)
  change ‖compactLogMellin g (1 - s t) * logDeriv χ.LFunction (s t)‖ ≤ _
  rw [norm_mul, hlog, norm_neg]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  have hsum_t : Summable (fun n ↦ ‖F n t‖) := by simpa only [hnorm] using hsum
  simpa only [hnorm] using norm_tsum_le_tsum_norm hsum_t

end Masullo
