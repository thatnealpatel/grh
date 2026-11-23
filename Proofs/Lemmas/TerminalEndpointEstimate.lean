module

public import Lemmas.TerminalTriangle
public import Lemmas.TerminalVKScale

/-! # The long-endpoint estimate for the full terminal triangle

The short quotient intervals are not estimated independently. After finite
reversal all endpoints lie between `sqrt x` and `x`, and each is at most
`x / q`. The cost of summing their absolute errors is absorbed by `q*(x/q)`.
-/

namespace TerminalTriangle
open Filter Real

/-- The terminal Vaughan cutoff, the floor of the fourth root. -/
public noncomputable def cutoff (x : ℝ) := ⌊√(√x)⌋₊

/-- Transfer an eventual pointwise prime-prefix bound to the signed triangle.
The absolute-value argument loses a factor two in the exponential constant. -/
public theorem endpoint_estimate {C c : ℝ} (hC : 0 ≤ C) (hc : 0 ≤ c)
    (hD : ∀ᶠ u in atTop, |D u| ≤ C*u*exp (-c*((log u)^(3/5:ℝ)/(log (log u))^(1/5:ℝ)))) :
    ∀ᶠ x in atTop, |signedTriangle x (cutoff x)| ≤
      2*C*x*exp (-(c/2)*((log x)^(3/5:ℝ)/(log (log x))^(1/5:ℝ))) := by
  obtain ⟨U, hU⟩ := eventually_atTop.mp hD
  filter_upwards [eventually_ge_atTop (exp 4), eventually_ge_atTop (16:ℝ),
    eventually_ge_atTop (U^2)] with x h4 h16 hU2
  let q := cutoff x
  have hx : 0 ≤ x := by linarith
  have hs := Real.sq_sqrt hx
  have ht := Real.sq_sqrt (Real.sqrt_nonneg x)
  have ht2 : 2 ≤ √(√x) := by
    apply (Real.le_sqrt (by norm_num) (sqrt_nonneg x)).2
    apply (Real.le_sqrt (by norm_num) hx).2
    norm_num; exact h16
  have hq : 1 ≤ q := Nat.le_floor (by norm_num; linarith)
  have hqr : (0:ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hqle : (q:ℝ) ≤ √(√x) := Nat.floor_le (Real.sqrt_nonneg _)
  have h2q : 2*(q:ℝ) ≤ √x := by nlinarith [mul_nonneg (by linarith : 0 ≤ √(√x)-2) (Real.sqrt_nonneg (√x))]
  have hsU : U ≤ √x := by nlinarith [Real.sqrt_nonneg x, sq_abs U, le_abs_self U]
  let V := fun u : ℝ => (log u)^(3/5:ℝ)/(log (log u))^(1/5:ℝ)
  have bound := abs_triangle_le q (fun n => D (x/n)) coeff
    (K := C*(x/q)*exp (-(c/2)*V x)) (by positivity) (by
      intro n hn
      obtain ⟨hl,hr⟩ := Finset.mem_Icc.mp hn
      have hnq : (q:ℝ) ≤ n := by exact_mod_cast (show q ≤ n by omega)
      have hn : (0:ℝ) < n := hqr.trans_le hnq
      have hnr : (n:ℝ) ≤ 2*(q:ℝ) := by exact_mod_cast hr
      have hlow : √x ≤ x/n := (le_div_iff₀ hn).mpr (by
        calc √x * n ≤ √x * √x := mul_le_mul_of_nonneg_left (hnr.trans h2q) (sqrt_nonneg _)
             _ = x := mul_self_sqrt hx)
      have hhigh : x/n ≤ x := div_le_self hx (by exact_mod_cast (show 1 ≤ n by omega))
      have hv : V x ≤ 2*V (x/n) := terminalVKScale_le_two_mul h4 (by
        rwa [← Real.sqrt_eq_rpow]) hhigh
      calc |D (x/n)| ≤ C*(x/n)*exp (-c*V (x/n)) := hU _ (hsU.trans hlow)
           _ ≤ C*(x/q)*exp (-(c/2)*V x) := by
             apply mul_le_mul (mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_left hx hqr hnq) hC) _ (exp_pos _).le (by positivity)
             apply Real.exp_le_exp.mpr
             nlinarith [mul_nonneg hc (sub_nonneg.mpr hv)]) coeff_bound
  change |triangle q _ coeff| ≤ 2*C*x*exp (-(c/2)*V x)
  convert bound using 1
  field_simp [ne_of_gt hqr]

end TerminalTriangle
