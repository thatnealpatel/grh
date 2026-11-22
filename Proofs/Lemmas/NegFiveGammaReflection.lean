module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import Mathlib.Tactic

/-! Deligne's complex Gamma factor on the line `Re s = -1 / 2`. -/

open Complex
open scoped ComplexConjugate

namespace Masullo

private theorem negFive_re (t : ℝ) : (-(1 / 2 : ℂ) + t * I).re = -(1 / 2 : ℝ) := by
  norm_num [add_re, mul_re]

public theorem negFive_gamma_norm (t : ℝ) (s : ℂ) (hs : s = -(1 / 2 : ℂ) + t * Complex.I) :
    ‖Complex.Gammaℂ (1 - s)‖ = ((t ^ 2 + 1 / 4) / (4 * Real.pi ^ 2)) * ‖Complex.Gammaℂ s‖ := by
  have hr : s.re = -(1 / 2 : ℝ) := hs ▸ negFive_re t
  have hi : s.im = t := by rw [hs]; norm_num [add_im, mul_im]
  have hshift : conj s + 1 = -s := by
    apply Complex.ext <;> simp [add_re, add_im, hr]
    norm_num
  have hs0 : s ≠ 0 := by intro h; rw [h, zero_re] at hr; norm_num at hr
  have hc0 : conj s ≠ 0 := by simpa using hs0
  have h1 : conj s + 1 ≠ 0 := by simpa [hshift] using hs0
  have hsq : ‖s‖ ^ 2 = t ^ 2 + 1 / 4 := by
    rw [Complex.sq_norm, normSq_apply, hr, hi]; ring
  rw [show 1 - s = (conj s + 1) + 1 by rw [hshift]; ring, Gammaℂ_add_one h1,
    Gammaℂ_add_one hc0, Gammaℂ_conj]
  simp only [norm_div, norm_mul, norm_conj, hshift, norm_neg, Complex.norm_ofNat,
    norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  rw [← hsq]
  ring

public theorem negFive_gamma_ne_zero (t : ℝ) (s : ℂ) (hs : s = -(1 / 2 : ℂ) + t * Complex.I) :
    Complex.Gammaℂ s ≠ 0 := by
  have hr : s.re = -(1 / 2 : ℝ) := hs ▸ negFive_re t
  rw [Gammaℂ_def]
  apply mul_ne_zero
  · simp [Real.pi_ne_zero]
  · apply Complex.Gamma_ne_zero
    intro n h
    rw [h, neg_re, natCast_re] at hr
    cases n with
    | zero => norm_num at hr
    | succ n => push_cast at hr; linarith [Nat.cast_nonneg (α := ℝ) n]

end Masullo
