module

public import Lemmas.DirichletGammaRightLine
public import Lemmas.DirichletLRightLine
public import Mathlib.NumberTheory.LSeries.Nonvanishing

/-!
# The completed Dirichlet logarithmic derivative on the open right half-plane

Mathlib's completion is the ordinary L-function times the real Gamma factor
of the character's parity, without a conductor power.
-/

open Complex Filter MeasureTheory
open scoped ContDiff Topology

namespace Masullo

variable {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)

omit [NeZero N] in
private theorem dirichletGamma_regular {s : ℂ} (hs : 0 < s.re) :
    χ.gammaFactor s ≠ 0 ∧ DifferentiableAt ℂ χ.gammaFactor s := by
  obtain ⟨b, hb, heq⟩ := exists_dirichletGammaFactor_real_shift χ
  rw [heq]
  exact ⟨(logDeriv_archimedeanGammaFactor_eq_integral two_pos hb hs).1,
    (analyticOnNhd_archimedeanGammaFactor two_pos hb s hs).differentiableAt⟩

private theorem completedDirichlet_factorization {s : ℂ} (hs : 1 < s.re) :
    χ.completedLFunction s = χ.LFunction s * χ.gammaFactor s := by
  have h0 : s ≠ 0 := fun e ↦ by rw [e, zero_re] at hs; linarith
  have h := χ.LFunction_eq_completed_div_gammaFactor s (.inl h0)
  exact ((eq_div_iff (dirichletGamma_regular χ (zero_lt_one.trans hs)).1).mp h).symm

/-- The product rule applies in a neighborhood, not just along the vertical line. -/
public theorem completedDirichlet_logDeriv_right {s : ℂ} (hs : 1 < s.re) :
    logDeriv χ.completedLFunction s = logDeriv χ.LFunction s + logDeriv χ.gammaFactor s := by
  have heq : χ.completedLFunction =ᶠ[𝓝 s] χ.LFunction * χ.gammaFactor := by
    filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds hs] with z hz
    exact completedDirichlet_factorization χ hz
  have h1 : s ≠ 1 := fun e ↦ by simp [e] at hs
  obtain ⟨hG, hdG⟩ := dirichletGamma_regular χ (zero_lt_one.trans hs)
  exact (logDeriv_congr_nhds heq).eq_of_nhds.trans (logDeriv_mul s
    (χ.LFunction_ne_zero_of_one_le_re (.inr h1) hs.le) hG
    (χ.differentiableAt_LFunction s (.inl h1)) hdG)

/-- On every line `a > 1` the reflected test integrates the completed logarithmic
derivative, for an arbitrary Dirichlet character, including the principal one. -/
public theorem integrable_compactLogMellin_completedDirichlet_reflected {g : ℝ → ℂ}
    (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g) {a : ℝ} (ha : 1 < a) :
    Integrable (fun t : ℝ ↦
      let s := (a : ℂ) + (t : ℂ) * I
      compactLogMellin g (1 - s) * logDeriv χ.completedLFunction s) := by
  refine ((integrable_compactLogMellin_dirichletL_reflected χ hg hc ha).add
    (integrable_compactLogMellin_dirichletGamma_reflected χ hg hc ha)).congr ?_
  filter_upwards with t
  simp only [Pi.add_apply, completedDirichlet_logDeriv_right χ (s := (a : ℂ) + (t : ℂ) * I)
    (by simpa using ha), mul_add]

end Masullo
