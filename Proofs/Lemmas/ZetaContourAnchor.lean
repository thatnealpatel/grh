module

public import Lemmas.CompletedZetaOrders
import Mathlib.NumberTheory.LSeries.HurwitzZetaValues
import Mathlib.Analysis.PSeriesComplex
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Tactic.Linarith

/-!
# A lower bound at the right-hand anchor for the rational explicit formula

Masullo invokes Lang for the contour growth in (B.4.2.1), p. 614. Lang compares
logarithmic derivatives using a right-hand anchor. For the project’s local disk
comparison instead, we bound the modulus of the pole-cleared completion at
`2 + it` from below. The Dirichlet series and Gamma reflection suffice there;
this is not by itself a bound on a logarithmic derivative.
-/

open Complex
open scoped ComplexConjugate

namespace Masullo

private theorem one_third_le_norm_zeta_of_re_two {s : ℂ} (hs : s.re = 2) :
    1 / 3 ≤ ‖riemannZeta s‖ := by
  let f (w : ℂ) (n : ℕ) : ℂ := 1 / (n + 1 : ℂ) ^ w
  let g (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1) ^ 2
  have hseries {w : ℂ} (hw : 1 < w.re) :
      riemannZeta w = 1 + ∑' n : ℕ, f w (n + 1) := by
    have hf : Summable (f w) := by
      simpa only [f, Nat.cast_add, Nat.cast_one] using (summable_nat_add_iff 1).2
        (Complex.summable_one_div_nat_cpow.mpr hw)
    rw [zeta_eq_tsum_one_div_nat_add_one_cpow hw]
    simpa [f] using hf.tsum_eq_zero_add
  have hnorm (n : ℕ) : ‖f s n‖ = g n := by
    have hp : 0 < (n : ℝ) + 1 := by positivity
    change ‖1 / (n + 1 : ℂ) ^ s‖ = 1 / ((n : ℝ) + 1) ^ 2
    rw [norm_div, norm_one,
      show (n + 1 : ℂ) = (((n : ℝ) + 1 : ℝ) : ℂ) by push_cast; rfl,
      norm_cpow_eq_rpow_re_of_pos hp, hs, ← Real.rpow_natCast]
    norm_num
  have hg : Summable fun n : ℕ ↦ g (n + 1) := by
    simpa only [g, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat, add_assoc, one_add_one_eq_two,
      one_div] using (summable_nat_add_iff 2).2
        (Real.summable_nat_pow_inv.mpr (by decide : 1 < (2 : ℕ)))
  have hgcast : (↑(∑' n : ℕ, g (n + 1)) : ℂ) = riemannZeta 2 - 1 := by
    rw [ofReal_tsum, hseries (w := 2) (by norm_num : 1 < (2 : ℂ).re), add_sub_cancel_left]
    congr 1
    funext n
    simp only [g, f, ofReal_div, ofReal_one, ofReal_pow, ofReal_add, ofReal_natCast, cpow_two]
  have hsum : (∑' n : ℕ, g (n + 1)) = Real.pi ^ 2 / 6 - 1 := by
    rw [riemannZeta_two] at hgcast
    rw [← ofReal_pow, ← ofReal_ofNat, ← ofReal_div, ← ofReal_one, ← ofReal_sub] at hgcast
    exact ofReal_injective hgcast
  have htail : ‖riemannZeta s - 1‖ ≤ Real.pi ^ 2 / 6 - 1 := by
    rw [hseries (by linarith), add_sub_cancel_left, ← hsum]
    simpa only [hnorm] using norm_tsum_le_tsum_norm
      (f := fun n : ℕ ↦ f s (n + 1)) (by simpa only [hnorm] using hg)
  have htri := norm_add_le (1 - riemannZeta s) (riemannZeta s)
  rw [sub_add_cancel, norm_one, norm_sub_rev] at htri
  nlinarith [Real.pi_lt_d2, Real.pi_pos]

private theorem exp_le_norm_Gamma_right_anchor (t : ℝ) (ht : 1 ≤ |t|) :
    Real.exp (-(Real.pi * |t| / 4)) ≤ ‖Gamma (1 + (t : ℂ) * I / 2)‖ := by
  let z : ℂ := ((t / 2 : ℝ) : ℂ) * I
  let u : ℝ := Real.pi * (t / 2)
  have ht0 : t ≠ 0 := by rintro rfl; norm_num at ht
  have hz : z ≠ 0 := mul_ne_zero (ofReal_ne_zero.mpr (div_ne_zero ht0 two_ne_zero)) I_ne_zero
  have hsin : sin ((Real.pi : ℂ) * z) = (Real.sinh u : ℂ) * I := by
    rw [ofReal_sinh, ← sin_mul_I]
    simp [z, u, mul_assoc]
  have hsin0 : sin ((Real.pi : ℂ) * z) ≠ 0 := by
    rw [hsin]
    exact mul_ne_zero (ofReal_ne_zero.mpr (Real.sinh_ne_zero.mpr
      (mul_ne_zero Real.pi_ne_zero (div_ne_zero ht0 two_ne_zero)))) I_ne_zero
  have hconj : conj (z + 1) = 1 - z := by
    simp [z, sub_eq_add_neg, add_comm, -ofReal_div]
  have hprod : Gamma (z + 1) * Gamma (1 - z) * sin ((Real.pi : ℂ) * z) = z * Real.pi := by
    rw [Gamma_add_one z hz, mul_assoc z, Gamma_mul_Gamma_one_sub, mul_assoc z,
      div_mul_cancel₀ _ hsin0]
  have habs : ‖Gamma (z + 1)‖ ^ 2 * ‖sin ((Real.pi : ℂ) * z)‖ = ‖z‖ * Real.pi := by
    simpa only [norm_mul, ← hconj, Gamma_conj, norm_conj, pow_two,
      norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos] using congrArg norm hprod
  have h1 : 1 ≤ ‖z‖ * Real.pi := by
    have hz' : ‖z‖ = |t| / 2 := by simp [z]
    rw [hz']
    calc
      (1 : ℝ) = (1 / 2) * 2 := by norm_num
      _ ≤ _ := mul_le_mul (by linarith) (by linarith [Real.pi_gt_three]) (by norm_num)
        (div_nonneg (abs_nonneg _) (by norm_num))
  have hsbound : ‖sin ((Real.pi : ℂ) * z)‖ ≤ Real.exp |u| := by
    rw [hsin, norm_mul, norm_I, mul_one, norm_real, Real.norm_eq_abs, Real.abs_sinh, Real.sinh_eq]
    linarith [Real.exp_pos (-|u|), Real.exp_pos |u|]
  have hsq : Real.exp (-|u|) ≤ ‖Gamma (z + 1)‖ ^ 2 := by
    apply le_of_mul_le_mul_right _ (Real.exp_pos |u|)
    calc
      Real.exp (-|u|) * Real.exp |u| = 1 := by rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
      _ ≤ ‖Gamma (z + 1)‖ ^ 2 * ‖sin ((Real.pi : ℂ) * z)‖ := habs.symm ▸ h1
      _ ≤ _ := mul_le_mul_of_nonneg_left hsbound (sq_nonneg _)
  have hu : |u| = Real.pi * |t| / 2 := by
    rw [show u = Real.pi * t / 2 by dsimp [u]; ring, abs_div, abs_mul,
      abs_of_pos Real.pi_pos, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  have harg : 1 + (t : ℂ) * I / 2 = z + 1 := by push_cast [z]; ring
  rw [harg]
  apply le_of_pow_le_pow_left₀ (by decide : (2 : ℕ) ≠ 0) (norm_nonneg _)
  rw [pow_two, ← Real.exp_add, show -(Real.pi * |t| / 4) + -(Real.pi * |t| / 4) = -|u| by
    rw [hu]; ring]
  exact hsq

/-- The pole-cleared completed zeta has a uniform exponential lower bound on
`Re s = 2` at heights of absolute value at least one. -/
public theorem entireZeta_right_anchor_lower_bound (t : ℝ) (ht : 1 ≤ |t|) :
    (3 * Real.pi)⁻¹ * Real.exp (-(Real.pi * |t| / 4)) ≤
      ‖entireZeta (2 + (t : ℂ) * I)‖ := by
  let s : ℂ := 2 + (t : ℂ) * I
  have hs : s.re = 2 := by simp [s]
  have hs' : 1 < s.re := by rw [hs]; norm_num
  have hs0 := ne_zero_of_one_lt_re hs'
  have hs1 : s ≠ 1 := by intro h; rw [h] at hs; norm_num at hs
  have hpi : ‖(↑Real.pi : ℂ) ^ (-s / 2)‖ = Real.pi⁻¹ := by
    rw [norm_cpow_eq_rpow_re_of_pos Real.pi_pos, div_ofNat_re, neg_re, hs,
      show -(2 : ℝ) / 2 = -1 by norm_num, Real.rpow_neg_one]
  have hΓ : Real.exp (-(Real.pi * |t| / 4)) ≤ ‖Gamma (s / 2)‖ := by
    rw [show s / 2 = 1 + (t : ℂ) * I / 2 by dsimp [s]; ring]
    exact exp_le_norm_Gamma_right_anchor t ht
  have hΛ : ‖completedRiemannZeta s‖ =
      Real.pi⁻¹ * ‖Gamma (s / 2)‖ * ‖riemannZeta s‖ := by
    rw [completedZeta_eq_tsum_of_one_lt_re hs', ← zeta_eq_tsum_one_div_nat_cpow hs',
      norm_mul, norm_mul, hpi]
  have hfac : 1 ≤ ‖s * (s - 1)‖ := by
    have h₀ : 1 ≤ ‖s‖ := by linarith [re_le_norm s]
    have h₁ : 1 ≤ ‖s - 1‖ := by
      have h := re_le_norm (s - 1)
      rw [sub_re, hs, one_re] at h
      linarith
    rw [norm_mul]
    simpa using mul_le_mul h₀ h₁ zero_le_one (norm_nonneg s)
  have hclear : entireZeta s = completedRiemannZeta s * (s * (s - 1)) :=
    (div_eq_iff (mul_ne_zero hs0 (sub_ne_zero.mpr hs1))).mp (completedZeta_eq_quotient hs0 hs1).symm
  change _ ≤ ‖entireZeta s‖
  rw [hclear, norm_mul, hΛ]
  calc
    _ = Real.pi⁻¹ * Real.exp (-(Real.pi * |t| / 4)) * (1 / 3) * 1 := by
      rw [mul_inv, mul_one, one_div]; ring
    _ ≤ _ := by
      gcongr
      exact one_third_le_norm_zeta_of_re_two hs

end Masullo
