module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! # The Vinogradov–Korobov scale on a power interval -/

namespace TerminalTriangle

/-- The Vinogradov–Korobov scale at `x` is at most twice its value at any `u`
from `x ^ (1 / 2 : ℝ)` to `x`, provided `exp 4 ≤ x`. -/
public theorem terminalVKScale_le_two_mul {x u : ℝ} (hx : Real.exp 4 ≤ x)
    (hxu : x ^ (1 / 2 : ℝ) ≤ u) (hux : u ≤ x) :
    (Real.log x) ^ (3 / 5 : ℝ) / (Real.log (Real.log x)) ^ (1 / 5 : ℝ) ≤
      2 * ((Real.log u) ^ (3 / 5 : ℝ) / (Real.log (Real.log u)) ^ (1 / 5 : ℝ)) := by
  have hx_pos : 0 < x := (Real.exp_pos 4).trans_le hx
  have hu_pos : 0 < u := (Real.rpow_pos_of_pos hx_pos _).trans_le hxu
  have hlog_x : 4 ≤ Real.log x := (Real.le_log_iff_exp_le hx_pos).2 hx
  have hhalf : (1 / 2 : ℝ) * Real.log x ≤ Real.log u := Real.le_log_of_rpow_le hx_pos hxu
  have hlog_u : 2 ≤ Real.log u := by linarith
  have hlog_le : Real.log u ≤ Real.log x := Real.log_le_log hu_pos hux
  have hloglog_u : 0 < Real.log (Real.log u) := Real.log_pos (by linarith)
  have hnum : (Real.log x) ^ (3 / 5 : ℝ) ≤ 2 * (Real.log u) ^ (3 / 5 : ℝ) := calc
    _ ≤ (2 * Real.log u) ^ (3 / 5 : ℝ) :=
      Real.rpow_le_rpow (by linarith) (by linarith) (by norm_num)
    _ = (2 : ℝ) ^ (3 / 5 : ℝ) * (Real.log u) ^ (3 / 5 : ℝ) :=
      Real.mul_rpow (by norm_num) (by linarith)
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (by linarith) _)
      simpa only [Real.rpow_one] using
        (Real.rpow_le_rpow_of_exponent_le (x := 2) (y := 3 / 5) (z := 1)
          (by norm_num) (by norm_num))
  have hden : (Real.log (Real.log u)) ^ (1 / 5 : ℝ) ≤
      (Real.log (Real.log x)) ^ (1 / 5 : ℝ) :=
    Real.rpow_le_rpow hloglog_u.le (Real.log_le_log (by linarith) hlog_le) (by norm_num)
  have hden_pos : 0 < (Real.log (Real.log u)) ^ (1 / 5 : ℝ) :=
    Real.rpow_pos_of_pos hloglog_u _
  calc
    _ ≤ (Real.log x) ^ (3 / 5 : ℝ) / (Real.log (Real.log u)) ^ (1 / 5 : ℝ) :=
      div_le_div_of_nonneg_left (Real.rpow_nonneg (by linarith) _) hden_pos hden
    _ ≤ (2 * (Real.log u) ^ (3 / 5 : ℝ)) / (Real.log (Real.log u)) ^ (1 / 5 : ℝ) :=
      div_le_div_of_nonneg_right hnum hden_pos.le
    _ = _ := mul_div_assoc _ _ _

end TerminalTriangle
