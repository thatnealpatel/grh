module

public import Lemmas.PadicLogFourier

/-!
# The rational finite logarithmic Fourier pairing off zero

Proposition B.4.3.1(2), (B.4.3.5), pp. 617–618, identifies the
logarithmic Fourier pairing on tests supported off zero with negative
unit-normalized multiplicative Haar. Lemma B.4.4.3, (B.4.4.8),
p. 621, applies this to the shifted test (B.4.4.7) when `f(1) = 0`.

Masullo determines the coefficient through covariance, uniqueness of
an invariant functional, and a unit test. Here we prove the rational
ball instance by a direct calculation instead of assuming that
distribution identity. Example A.3.1.6, (A.3.1.5), p. 557, gives the
centered cutoff and phase in its last expression, but the extracted
intermediate transform shifts the cutoff instead. We use the checked
`padicTranslatedBall_fourier` for the translation step. The off-zero
condition makes the cutoff include the first nontrivial phase shell;
`padic_log_phase_moment` then evaluates the stabilized moment.
This is a ball calculation, not yet the assembly for all translated
tests. The locators follow the pinned text extraction.
-/

open scoped Padic
open MeasureTheory Set

namespace Masullo

variable (p : ℕ) [Fact p.Prime]

/-- On the indicator of `a + p^n ℤₚ` avoiding zero, the pairing with
`log |ξ|ₚ / log p` is absolutely integrable and equals
`-p⁻ⁿ / ((1 - p⁻¹) * |a|ₚ)`. The denominator uses the unit-mass
multiplicative Haar normalization in (B.4.3.5). -/
public theorem padicTranslatedBall_log_fourier (n : ℕ) (a : ℚ_[p])
    (ha : ((p : ℝ)⁻¹) ^ n < ‖a‖) :
    let S := {x : ℚ_[p] | ‖((p : ℚ_[p]) ^ n)⁻¹ * (x - a)‖ ≤ 1}
    let g := fun ξ : ℚ_[p] ↦ (↑(Real.log ‖ξ‖ / Real.log (p : ℝ)) : ℂ) *
      (∫ x in S, star (padicStdAddChar p (x * ξ)) ∂padicAddHaar p)
    Integrable g (padicAddHaar p) ∧
      (∫ ξ, g ξ ∂padicAddHaar p) =
        -((p : ℂ) ^ n)⁻¹ * (↑((1 - (p : ℝ)⁻¹) * ‖a‖) : ℂ)⁻¹ := by
  classical
  dsimp only
  let R := (p : ℝ) ^ n
  let D := Metric.closedBall (0 : ℚ_[p]) R
  let f := fun ξ : ℚ_[p] ↦ (↑(Real.log ‖ξ‖ / Real.log (p : ℝ)) : ℂ) *
    star (padicStdAddChar p (a * ξ))
  have hp : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hp₀ : (0 : ℝ) < p := (lt_trans zero_lt_one hp)
  have hR : 0 < R := pow_pos hp₀ _
  have ha₀ : a ≠ 0 := norm_pos_iff.mp ((by positivity : 0 ≤ ((p : ℝ)⁻¹) ^ n).trans_lt ha)
  -- The discrete norm promotes strict separation to a full shell of room in frequency.
  have hcut : (p : ℝ) ≤ ‖a‖ * R := by
    have h := Padic.norm_le_pow_iff_norm_lt_pow_add_one a (-(n : ℤ))
    rw [zpow_neg, zpow_natCast, ← inv_pow, zpow_add₀ hp₀.ne', zpow_neg,
      zpow_natCast, zpow_one] at h
    have hh := not_lt.mp (mt h.mpr (not_le.mpr ha))
    exact (div_le_iff₀ hR).mp (by simpa [R, div_eq_inv_mul] using hh)
  -- The frequency cutoff from the ball transform is the centered ball of radius p^n.
  have hm (ξ : ℚ_[p]) : ‖(p : ℚ_[p]) ^ n * ξ‖ ≤ 1 ↔ ξ ∈ D := by
    rw [norm_mul, norm_pow, Padic.norm_p, inv_pow, ← le_div_iff₀' (inv_pos.mpr hR),
      div_inv_eq_mul, one_mul]
    simp [D, R, Metric.mem_closedBall, dist_zero_right]
  simp_rw [padicTranslatedBall_fourier p]
  have he (ξ : ℚ_[p]) :
      (↑(Real.log ‖ξ‖ / Real.log (p : ℝ)) : ℂ) *
        (((p : ℂ) ^ n)⁻¹ * star (padicStdAddChar p (a * ξ)) *
          (Set.ofPred (fun x : ℚ_[p] ↦ ‖x‖ ≤ 1)).indicator (fun _ ↦ (1 : ℂ))
            ((p : ℚ_[p]) ^ n * ξ)) = ((p : ℂ) ^ n)⁻¹ * D.indicator f ξ := by
    by_cases h : ξ ∈ D
    · rw [indicator_of_mem h, indicator_of_mem (show (p : ℚ_[p]) ^ n * ξ ∈
        Set.ofPred (fun x : ℚ_[p] ↦ ‖x‖ ≤ 1) from (hm ξ).mpr h) _, mul_one]
      dsimp [f]
      ring
    · have hn : (p : ℚ_[p]) ^ n * ξ ∉ Set.ofPred (fun x : ℚ_[p] ↦ ‖x‖ ≤ 1) :=
        mt (hm ξ).mp h
      simp [indicator_of_notMem h, indicator_of_notMem hn]
  simp_rw [he]
  -- Frequency radii past the first nontrivial shell contribute zero.
  have hv := padic_log_phase_moment p a ha₀ R hcut
  have hD : MeasurableSet D := Metric.isClosed_closedBall.measurableSet
  refine ⟨((integrable_indicator_iff hD).mpr hv.1).const_mul _, ?_⟩
  rw [integral_const_mul, integral_indicator hD, hv.2]
  push_cast
  have hpn : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne p)
  have hp₁ : (p : ℂ) - 1 ≠ 0 := by exact_mod_cast (sub_pos.mpr hp).ne'
  have han : (↑‖a‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr ha₀
  have hh : 1 - (p : ℂ)⁻¹ ≠ 0 := by
    have h := sub_pos.mpr (inv_lt_one_of_one_lt₀ hp)
    simpa only [Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_inv, Complex.ofReal_natCast]
      using (Complex.ofReal_ne_zero.mpr h.ne')
  field_simp [hpn, hp₁, han, hh]
  ring

end Masullo
