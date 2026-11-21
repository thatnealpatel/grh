module

public import Lemmas.CompactLogMellin

/-!
# Mellin admissibility of compact log profiles

The smooth compact-log case of Masullo's Proposition B.2.1.9(1)–(2),
pp. 598–599, in the whole-line coordinates of (B.2.1.29). The contour
needs `N = 4` and may take `A = 2` on `-1 ≤ Re s ≤ 2`.
-/

open Filter MeasureTheory
open scoped ContDiff

namespace Masullo

/-- A continuous compact log profile has an entire Mellin transform. -/
public theorem analyticAt_compactLogMellin {g : ℝ → ℂ} (hg : Continuous g)
    (hc : HasCompactSupport g) (s : ℂ) : AnalyticAt ℂ (compactLogMellin g) s :=
  -- After (B.2.1.30) the text gives uniform absolute convergence.
  -- Dominated differentiation supplies complex differentiability explicitly.
  Complex.analyticAt_iff_eventually_differentiableAt.mpr
    (Eventually.of_forall (differentiable_compactLogMellin hg hc))

/-- The Mellin transform of a smooth compact log profile has arbitrarily
high polynomial decay, uniformly on each bounded closed vertical strip. -/
public theorem compactLogMellin_vertical_decay {g : ℝ → ℂ} (hg : ContDiff ℝ ∞ g)
    (hc : HasCompactSupport g) (A : ℝ) (N : ℕ) :
    ∃ B > (0 : ℝ), ∀ σ t : ℝ, |σ| ≤ A →
      ‖compactLogMellin g ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ B / (1 + |t|) ^ N := by
  let M₀ := ∫ x : ℝ, ‖g x‖ * Real.exp (A * |x|)
  let Mₙ := ∫ x : ℝ, ‖iteratedDeriv N g x‖ * Real.exp (A * |x|)
  have h₀ : 0 ≤ M₀ := integral_nonneg fun x ↦ mul_nonneg (norm_nonneg _) (Real.exp_pos _).le
  have hₙ : 0 ≤ Mₙ := integral_nonneg fun x ↦ mul_nonneg (norm_nonneg _) (Real.exp_pos _).le
  refine ⟨2 ^ N * (1 + M₀ + Mₙ), by positivity, fun σ t hσ ↦ ?_⟩
  let s : ℂ := (σ : ℂ) + (t : ℂ) * Complex.I
  have hre : s.re = σ := by simp [s, Complex.mul_re]
  have him : s.im = t := by simp [s, Complex.mul_im]
  have hs : |s.re| ≤ A := hre ▸ hσ
  have ht : |t| ≤ ‖s‖ := by simpa only [him] using Complex.abs_im_le_norm s
  change ‖compactLogMellin g s‖ ≤ _
  apply (le_div_iff₀ (by positivity)).mpr
  rw [mul_comm ‖compactLogMellin g s‖]
  by_cases h : |t| ≤ 1
  · -- Use the undifferentiated estimate at small heights, including zero.
    calc
      _ ≤ 2 ^ N * M₀ := by
        gcongr
        · linarith
        · exact norm_compactLogMellin_le hg.continuous hc hs
      _ ≤ _ := by gcongr; linarith
  · -- (B.2.1.31)–(35): Integrate by parts N times and use |t| ≤ ‖s‖.
    have hpow : ‖s‖ ^ N * ‖compactLogMellin g s‖ ≤ Mₙ := by
      rw [← norm_neg s, ← norm_pow, ← norm_mul, ← compactLogMellin_iteratedDeriv hg hc]
      exact norm_compactLogMellin_le (hg.continuous_iteratedDeriv N (WithTop.coe_le_coe.mpr le_top))
        (hasCompactSupport_iteratedDeriv_logProfile hc N) hs
    calc
      _ ≤ (2 * ‖s‖) ^ N * ‖compactLogMellin g s‖ := by
        gcongr
        linarith
      _ = 2 ^ N * (‖s‖ ^ N * ‖compactLogMellin g s‖) := by rw [mul_pow, mul_assoc]
      _ ≤ 2 ^ N * Mₙ := by gcongr
      _ ≤ _ := by gcongr; linarith

end Masullo
