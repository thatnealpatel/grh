module

public import Mathlib.Analysis.SpecialFunctions.Exp

/-! # A two-tail bound for an exponentially weighted log-Mellin profile -/

namespace Masullo

/-- Arbitrary exponential decay on each log half-line absorbs the weight at any
fixed complex parameter, leaving a two-sided exponential majorant. -/
public theorem norm_logMellin_mul_exp_le_of_two_tails {p : ℝ → ℂ} {M : ℝ}
    (hM : 0 ≤ M)
    (hlarge : ∀ N : ℕ, ∃ A : ℝ, 0 < A ∧ ∀ x : ℝ, 0 ≤ x → ‖p x‖ ≤ A * Real.exp (-(N : ℝ) * x) * M)
    (hsmall : ∀ N : ℕ, ∃ B : ℝ, 0 < B ∧ ∀ x : ℝ, x < 0 → ‖p x‖ ≤ B * Real.exp ((N : ℝ) * x) * M)
    (s : ℂ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, ‖p x * Complex.exp (s * x)‖ ≤ C * Real.exp (-3 * |x|) := by
  obtain ⟨N, hN⟩ := exists_nat_ge (|s.re| + 3)
  obtain ⟨A, hA, hpos⟩ := hlarge N
  obtain ⟨B, _, hneg⟩ := hsmall N
  have hC : 0 ≤ max A B * M := mul_nonneg (hA.le.trans (le_max_left A B)) hM
  have hrate : -(N : ℝ) + |s.re| ≤ -3 := by linarith
  refine ⟨max A B * M, hC, fun x ↦ ?_⟩
  have hp : ‖p x‖ ≤ max A B * Real.exp (-(N : ℝ) * |x|) * M := by
    have hcoeff {K : ℝ} (hK : K ≤ max A B) :
        K * Real.exp (-(N : ℝ) * |x|) * M ≤ max A B * Real.exp (-(N : ℝ) * |x|) * M :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hK (Real.exp_pos _).le) hM
    rcases lt_or_ge x 0 with hx | hx
    · refine le_trans ?_ (hcoeff (le_max_right A B))
      simpa only [abs_of_neg hx, neg_mul_neg] using hneg x hx
    · refine le_trans ?_ (hcoeff (le_max_left A B))
      simpa only [abs_of_nonneg hx] using hpos x hx
  have hs : s.re * x ≤ |s.re| * |x| := by
    rw [← abs_mul]
    exact le_abs_self _
  rw [norm_mul, Complex.norm_exp, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, sub_zero]
  calc
    ‖p x‖ * Real.exp (s.re * x) ≤
        (max A B * Real.exp (-(N : ℝ) * |x|) * M) * Real.exp (s.re * x) :=
      mul_le_mul_of_nonneg_right hp (Real.exp_pos _).le
    _ = (max A B * M) * Real.exp (-(N : ℝ) * |x| + s.re * x) := by
      rw [Real.exp_add]
      ring
    _ ≤ (max A B * M) * Real.exp (-3 * |x|) := by
      apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hC
      calc
        _ ≤ -(N : ℝ) * |x| + |s.re| * |x| := add_le_add_right hs _
        _ = (-(N : ℝ) + |s.re|) * |x| := (add_mul _ _ _).symm
        _ ≤ -3 * |x| := mul_le_mul_of_nonneg_right hrate (abs_nonneg x)

end Masullo
