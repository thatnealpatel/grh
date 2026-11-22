module

public import Mathlib.Analysis.Complex.Norm
import Mathlib.Algebra.Order.Archimedean.Basic

/-! # A small identity neighborhood in the complex multiplicative group -/

namespace Masullo

/-- The ball of radius `1/2` around `1` in `ℂ` contains the powers of no
nontrivial element: Squaring expands the distance from `1` by at least `3/2`
while the element stays in that ball. -/
public theorem complex_eq_one_of_norm_pow_sub_one_lt (z : ℂ)
    (h : ∀ n : ℕ, ‖z ^ n - 1‖ < 1 / 2) : z = 1 := by
  have hgrow (w : ℂ) (hw : ‖w - 1‖ < 1 / 2) :
      (3 / 2 : ℝ) * ‖w - 1‖ ≤ ‖w ^ 2 - 1‖ := by
    have hsum : ‖(2 : ℂ)‖ ≤ ‖w + 1‖ + ‖w - 1‖ := by
      calc
        ‖(2 : ℂ)‖ = ‖(w + 1) - (w - 1)‖ := by ring_nf
        _ ≤ ‖w + 1‖ + ‖w - 1‖ := norm_sub_le _ _
    have htwo : ‖(2 : ℂ)‖ = 2 := by norm_num
    have hw' : (3 / 2 : ℝ) ≤ ‖w + 1‖ := by linarith
    rw [show w ^ 2 - 1 = (w + 1) * (w - 1) by ring, Complex.norm_mul]
    exact mul_le_mul_of_nonneg_right hw' (norm_nonneg _)
  have hiter (n : ℕ) : (3 / 2 : ℝ) ^ n * ‖z - 1‖ ≤ ‖z ^ (2 ^ n : ℕ) - 1‖ := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ (2 : ℕ), pow_mul, pow_succ (3 / 2 : ℝ), mul_comm (_ ^ n), mul_assoc]
      exact (mul_le_mul_of_nonneg_left ih (by norm_num)).trans (hgrow _ (h _))
  by_contra hz
  have hd : 0 < ‖z - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hz)
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt ((1 / 2 : ℝ) / ‖z - 1‖)
    (show (1 : ℝ) < 3 / 2 by norm_num)
  exact (not_lt_of_ge ((hiter n).trans (h (2 ^ n)).le)) ((div_lt_iff₀ hd).mp hn)

end Masullo
