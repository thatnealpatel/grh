module

public import Theorems.RationalExplicitFormulaRightLine
public import Props.CompactLogMellin
public import Mathlib.NumberTheory.LSeries.Dirichlet
import Lemmas.CompactLogMellinInversion
import Mathlib.Tactic.FieldSimp

/-!
# Finite-place evaluation of the rational explicit formula

We use the unshifted Mellin transform, as in (B.4.2.10)–(B.4.2.11),
p. 615. The Archimedean integral is left unevaluated.
-/

open Complex MeasureTheory Set
open scoped ContDiff

namespace Masullo

/-- Fourier inversion of the right and reflected Mellin test at `log n`.
Masullo invokes Dirac evaluation in (B.4.2.10)–(B.4.2.11). In ordinary
Lebesgue measure it requires `dt / (2π)`, with no relative minus sign:
`compactLogMellin_reflected_inversion` supplies this normalization. -/
public theorem compactLogMellin_prime_power_evaluation {g : ℝ → ℂ}
    (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g) {n : ℝ} (hn : 0 < n) :
    let s := fun t : ℝ ↦ (2 : ℂ) + (t : ℂ) * I
    let W := fun t ↦ compactLogMellin g (s t) + compactLogMellin g (1 - s t)
    (∫ t, W t / (n : ℂ) ^ s t) / (2 * (Real.pi : ℂ)) =
      g (Real.log n) + g (-Real.log n) / (n : ℂ) := by
  let s (t : ℝ) : ℂ := 2 + (t : ℂ) * I
  let W (t : ℝ) := compactLogMellin g (s t) + compactLogMellin g (1 - s t)
  change (∫ t, W t / (n : ℂ) ^ s t) / _ = _
  have hphase (t : ℝ) : W t / (n : ℂ) ^ s t =
      ((n : ℂ) ^ (2 : ℕ))⁻¹ * (W t * exp (-(t : ℂ) * Real.log n * I)) := by
    rw [div_eq_mul_inv, rightLine_cpow_inv hn t]
    ring
  simp_rw [hphase, integral_const_mul, mul_div_assoc]
  rw [compactLogMellin_reflected_inversion hg hc (Real.log n)]
  -- The unreflected weight is n², while the reflected weight is only n.
  have hn' := Complex.ofReal_ne_zero.mpr hn.ne'
  have he : exp (Real.log n : ℂ) = n := by rw [Complex.ofReal_log hn.le, Complex.exp_log hn']
  rw [two_mul, Complex.exp_add, he, pow_two]
  field_simp

/-- The rational split contour with its finite-place integrals evaluated.
Only prime powers contribute to the absolutely summable von Mangoldt
series. The real Gamma integral and the full zero multiplicities are retained. -/
public theorem completedZeta_contour_finite_places {g : ℝ → ℂ}
    (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g) :
    let Φ := compactLogMellin g
    let s := fun t : ℝ ↦ (2 : ℂ) + (t : ℂ) * I
    let W := fun t ↦ Φ (s t) + Φ (1 - s t)
    let prime := fun n : ℕ ↦ (ArithmeticFunction.vonMangoldt n : ℂ) *
      (g (Real.log n) + g (-Real.log n) / (n : ℂ))
    Integrable (fun t ↦ W t * logDeriv Gammaℝ (s t)) ∧
    Summable (fun n ↦ ‖prime n‖) ∧
    Summable (fun ρ : criticalStripZetaZeros ↦ ‖(zetaZeroOrder ρ : ℂ) * Φ (ρ : ℂ)‖) ∧
    (∫ t, W t * logDeriv Gammaℝ (s t)) / (2 * (Real.pi : ℂ)) - (∑' n, prime n) =
      -Φ 0 - Φ 1 + ∑' ρ : criticalStripZetaZeros, (zetaZeroOrder ρ : ℂ) * Φ (ρ : ℂ) := by
  let Φ := compactLogMellin g
  let s (t : ℝ) : ℂ := 2 + (t : ℂ) * I
  let W (t : ℝ) := Φ (s t) + Φ (1 - s t)
  let a (n : ℕ) : ℂ := ArithmeticFunction.vonMangoldt n
  let finite (n : ℕ) (t : ℝ) := W t * LSeries.term a (s t) n
  let prime (n : ℕ) := a n * (g (Real.log n) + g (-Real.log n) / (n : ℂ))
  let c : ℂ := 2 * (Real.pi : ℂ)
  have hdecay : ∃ B > (0 : ℝ), ∀ σ ∈ Icc (-1 : ℝ) 2, ∀ t : ℝ,
      ‖Φ ((σ : ℂ) + (t : ℂ) * I)‖ ≤ B / (1 + |t|) ^ 4 := by
    obtain ⟨B, hB, h⟩ := compactLogMellin_vertical_decay hg hc 2 4
    exact ⟨B, hB, fun σ hσ t ↦ h σ t (abs_le.mpr ⟨by linarith [hσ.1], hσ.2⟩)⟩
  obtain ⟨hΓ, _hfinite, hsum, hzeros, hcontour⟩ := completedZeta_contour_split
    (analyticAt_compactLogMellin hg.continuous hc) hdecay
  -- Evaluate term by term in the already justified, combined finite series.
  have hterm (n : ℕ) : (∫ t, finite n t) / c = prime n := by
    rcases eq_or_ne n 0 with rfl | hn
    · simp [finite, prime, a, LSeries.term_zero]
    have heq (t : ℝ) : finite n t = a n * (W t / (n : ℂ) ^ s t) := by
      dsimp only [finite]
      rw [LSeries.term_of_ne_zero hn, ← mul_div_assoc, ← mul_div_assoc, mul_comm (W t)]
    simp_rw [heq, integral_const_mul, mul_div_assoc]
    have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
    have heval := compactLogMellin_prime_power_evaluation hg hc hn'
    dsimp only at heval
    rw [Complex.ofReal_natCast] at heval
    exact congrArg (a n * ·) heval
  have hprime : Summable (fun n ↦ ‖prime n‖) := by
    refine (hsum.mul_right ‖c‖⁻¹).of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun n ↦ ?_)
    rw [← hterm, norm_div, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right (norm_integral_le_integral_norm _) (by positivity)
  refine ⟨hΓ, hprime, hzeros, ?_⟩
  change ((∫ t, W t * logDeriv Gammaℝ (s t)) - ∑' n, ∫ t, finite n t) / c = _ at hcontour
  rw [sub_div, ← tsum_div_const, tsum_congr hterm] at hcontour
  exact hcontour

end Masullo
