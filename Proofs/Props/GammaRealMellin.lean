module

public import Props.CompactLogMellin
public import Props.GammaRealLogDerivative
import Lemmas.GammaRealRightLine
import Theorems.RationalExplicitFormulaFinitePlaces
import Mathlib.Tactic.Ring

/-!
# The tested real Gamma factor

For the rational trivial character, this evaluates (B.4.2.13), p. 616,
on the right line. Barner supplies the subtracted digamma and Fourier
inversion route. We keep the subtraction inside the integral, including
the exponential factor on the identity sample missing from the extracted
(B.4.2.15). No contour shift or Stirling estimate is needed for this step.
-/

open Complex MeasureTheory Set
open scoped ContDiff

namespace Masullo

/-- The tested rational Archimedean term, with the full identity-supported
constant and absolute convergence of the combined kernel. Joint domination
justifies Fubini before the Mellin samples are evaluated. -/
public theorem compactLogMellin_GammaReal_evaluation {g : ℝ → ℂ}
    (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g) :
    let s := fun t : ℝ ↦ (2 : ℂ) + (t : ℂ) * I
    let W := fun t ↦ compactLogMellin g (s t) + compactLogMellin g (1 - s t)
    let F := fun x : ℝ ↦ (2 * g 0 * exp (-2 * (x : ℂ)) - g x - exp (-(x : ℂ)) * g (-x)) /
      (1 - exp (-2 * (x : ℂ)))
    IntegrableOn F (Ioi 0) ∧
    (∫ t, W t * logDeriv Gammaℝ (s t)) / (2 * (Real.pi : ℂ)) =
      -((Real.log Real.pi : ℂ) + (Real.eulerMascheroniConstant : ℂ)) * g 0 +
      ∫ x in Ioi (0 : ℝ), F x := by
  let s (t : ℝ) : ℂ := 2 + (t : ℂ) * I
  let W (t : ℝ) := compactLogMellin g (s t) + compactLogMellin g (1 - s t)
  let K (t x : ℝ) := (exp (-2 * (x : ℂ)) - exp (-s t * (x : ℂ))) /
    (1 - exp (-2 * (x : ℂ)))
  let F (x : ℝ) := (2 * g 0 * exp (-2 * (x : ℂ)) - g x - exp (-(x : ℂ)) * g (-x)) /
    (1 - exp (-2 * (x : ℂ)))
  let c : ℂ := 2 * (Real.pi : ℂ)
  let A : ℂ := (Real.log Real.pi : ℂ) + (Real.eulerMascheroniConstant : ℂ)
  obtain ⟨hW, hWi, hmom⟩ := compactLogMellin_reflected_integrable_moments hg hc
  change Continuous W at hW
  change Integrable W at hWi
  have hjoint : Integrable (fun p : ℝ × ℝ ↦ W p.1 * K p.1 p.2)
      ((volume : Measure ℝ).prod (volume.restrict (Ioi 0))) :=
    integrable_gammaReal_rightLine_product hW.measurable hmom
  -- Mellin inversion at `n = 1` and at `n = exp x`, on each fixed slice.
  have hzero : (∫ t, W t) / c = 2 * g 0 := by
    simpa [s, W, c, two_mul] using
      (compactLogMellin_prime_power_evaluation hg hc (n := 1) zero_lt_one)
  have hsample (x : ℝ) : (∫ t, W t * exp (-s t * (x : ℂ))) / c =
      g x + exp (-(x : ℂ)) * g (-x) := by
    obtain h := compactLogMellin_prime_power_evaluation hg hc (Real.exp_pos x)
    change (∫ t, W t / (Real.exp x : ℂ) ^ s t) / c = _ at h
    have hcast : (Real.exp x : ℂ) = exp (x : ℂ) := Complex.ofReal_exp x
    have hpow (t : ℝ) : ((Real.exp x : ℂ) ^ s t)⁻¹ = exp (-s t * (x : ℂ)) := by
      rw [cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (Real.exp_pos x).ne'),
        ← Complex.ofReal_log (Real.exp_pos x).le, Real.log_exp, ← Complex.exp_neg]
      congr 1
      ring
    simp only [div_eq_mul_inv, hpow, Real.log_exp] at h
    rw [hcast, ← Complex.exp_neg, mul_comm (g (-x))] at h
    simpa only [div_eq_mul_inv] using h
  have hslice (x : ℝ) : (∫ t, W t * K t x) / c = F x := by
    let D := 1 - exp (-2 * (x : ℂ))
    let E := exp (-2 * (x : ℂ))
    have hpoint (t : ℝ) : W t * K t x = (W t * E - W t * exp (-s t * (x : ℂ))) / D := by
      simp only [K, E, D, div_eq_mul_inv]
      ring
    simp_rw [hpoint]
    rw [integral_div, integral_sub (hWi.mul_const E) (integrable_gammaReal_rightLine_exp_sample hW hWi x),
      integral_mul_const]
    rw [show (((∫ t, W t) * E - ∫ t, W t * exp (-s t * (x : ℂ))) / D) / c =
      (((∫ t, W t) / c) * E - (∫ t, W t * exp (-s t * (x : ℂ))) / c) / D by
        simp only [div_eq_mul_inv]; ring, hzero, hsample]
    simp only [F, E, D, sub_sub]
  have hFi : IntegrableOn F (Ioi 0) :=
    (hjoint.integral_prod_right.div_const c).congr (Filter.Eventually.of_forall hslice)
  -- Substitute the scalar digamma identity and exchange only the combined kernel.
  have hΓ (t : ℝ) : logDeriv Gammaℝ (s t) = -A / 2 + ∫ x in Ioi (0 : ℝ), K t x :=
    (logDeriv_GammaReal_eq_integral (s := s t) (by simp [s])).2
  refine ⟨hFi, ?_⟩
  change (∫ t, W t * logDeriv Gammaℝ (s t)) / c = -A * g 0 + ∫ x in Ioi (0 : ℝ), F x
  simp_rw [hΓ, mul_add, ← integral_const_mul (W _)]
  rw [integral_add (hWi.mul_const (-A / 2)) hjoint.integral_prod_left, integral_mul_const,
    add_div, mul_div_right_comm, hzero, integral_integral_swap hjoint, ← integral_div]
  simp_rw [hslice]
  ring

end Masullo
