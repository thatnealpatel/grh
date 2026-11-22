module

public import Props.ArchimedeanGammaRightLine
public import Mathlib.NumberTheory.LSeries.DirichletContinuation

/-! Absolute integrability of the reflected Mellin test against a Dirichlet Gamma factor. -/

open Complex MeasureTheory
open scoped ContDiff

namespace Masullo

/-- Both character parities give real archimedean factors with nonnegative shift. -/
public theorem exists_dirichletGammaFactor_real_shift {N : ℕ} (χ : DirichletCharacter ℂ N) :
    ∃ b : ℝ, 0 ≤ b ∧ χ.gammaFactor = archimedeanGammaFactor Real.pi 2 b 0 := by
  rcases χ.even_or_odd with he | ho
  · refine ⟨0, le_rfl, ?_⟩
    funext s
    simp [archimedeanGammaFactor_real, he.gammaFactor_def]
  · refine ⟨1, zero_le_one, ?_⟩
    funext s
    simp [archimedeanGammaFactor_real, ho.gammaFactor_def]

/-- On the right line only the Mellin argument is reflected. The Gamma factor
has real shift zero for even characters and one for odd characters. -/
public theorem integrable_compactLogMellin_dirichletGamma_reflected {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) {g : ℝ → ℂ} (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g)
    {a : ℝ} (ha : 1 < a) :
    Integrable (fun t : ℝ ↦
      let s := (a : ℂ) + (t : ℂ) * I
      compactLogMellin g (1 - s) * logDeriv χ.gammaFactor s) := by
  obtain ⟨b, hb, hχ⟩ := exists_dirichletGammaFactor_real_shift χ
  rw [hχ]
  simpa only [neg_zero] using (compactLogMellin_archimedeanGamma_reflected hg hc
    (zero_lt_one.trans ha) two_pos hb Real.pi 0).1

end Masullo
