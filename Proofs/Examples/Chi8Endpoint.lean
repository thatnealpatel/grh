module

public import Examples.Chi8Completion
public import Examples.Chi8Finite
public import Examples.Chi8Origin
public import Examples.Chi8Series
public import Examples.Chi8Tails
public import Lemmas.RampOrigin
import Mathlib.Tactic

/-! # The endpoint budget for the even primitive character modulo eight

These inequalities concern the actual continued Dirichlet L-function and its
completion. They do not identify a logarithmic derivative with a zero sum.
-/

open Filter DirichletCharacter
open scoped Topology

namespace Chi8Budget

local notation "χ" => Chi8Origin.χ
local notation "L" => LFunction χ

private theorem nonprincipal : χ ≠ 1 := by
  intro h
  have hc := Chi8Origin.conductor_eq
  rw [h, conductor_one] at hc
  contradiction

private theorem cast_weight (n : ℕ) : (w n : ℂ) = Masullo.chi8Complex (n : ZMod 8) := by
  simp [w, Masullo.chi8Complex, MulChar.ringHomComp_apply]

/-- Both error bars apply to the continued function, not just formal series. -/
public theorem endpoint_errors :
    ∃ l d : ℝ, L 1 = (l : ℂ) ∧ deriv L 1 = (d : ℂ) ∧
      |l - S 32| ≤ 1/32 ∧ |d - D 32| ≤ Real.log 32 / 32 := by
  obtain ⟨l, hl, hSl⟩ := Chi8Tails.exists_tendsto_S
  obtain ⟨d, hd, hDd⟩ := Chi8Tails.exists_tendsto_D
  change Tendsto S atTop (𝓝 l) at hl
  change Tendsto D atTop (𝓝 d) at hd
  have hs (N : ℕ) : (S N : ℂ) = ∑ n ∈ Finset.Icc 1 N, Masullo.chi8Complex (n : ZMod 8) / n := by
    simp only [S, Complex.ofReal_sum, Complex.ofReal_div, cast_weight, Complex.ofReal_natCast]
  have he (N : ℕ) : (D N : ℂ) = ∑ n ∈ Finset.Icc 1 N,
      -Masullo.chi8Complex (n : ZMod 8) * (Real.log n : ℂ) / n := by
    simp only [D, Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_neg, Complex.ofReal_div,
      cast_weight, Complex.ofReal_natCast, mul_div_assoc]
  refine ⟨l, d, ?_, ?_, hSl, hDd⟩
  · exact tendsto_nhds_unique Masullo.tendsto_chi8_series_one
      ((Complex.continuous_ofReal.continuousAt.tendsto.comp hl).congr hs)
  · exact tendsto_nhds_unique Masullo.tendsto_chi8_deriv_series_one
      ((Complex.continuous_ofReal.continuousAt.tendsto.comp hd).congr he)

/-- The strict endpoint budget with the even gamma factor. -/
public theorem completed_budget :
    2 * (deriv (Chi8Completion.completion L) 1 / Chi8Completion.completion L 1).re < 3/2 := by
  obtain ⟨l, d, hl, hd, hs, he⟩ := endpoint_errors
  rw [Chi8Completion.two_re_logDeriv_completion_one L (differentiable_LFunction nonprincipal 1)
    (LFunction_apply_one_ne_zero nonprincipal), hl, hd, ← Complex.ofReal_div, Complex.ofReal_re]
  rw [← mul_div_assoc]
  linarith [endpoint_bound_of_abs l d hs he, Real.one_half_lt_eulerMascheroniConstant]

/-- The origin correction for the actual mod-eight ramp integrand. -/
public theorem origin_principal_part :
    ∃ a b : ℂ, ∀ ℓ : ℂ, ∃ R : ℂ → ℂ, AnalyticAt ℂ R 0 ∧
      ∀ᶠ z in 𝓝[≠] (0 : ℂ),
        -Complex.exp (ℓ*z) * (deriv L z / L z) / z^2 =
          -1/z^3 - (ℓ+a)/z^2 - (ℓ^2/2 + a*ℓ + b)/z + R z :=
  RampOrigin.simple_zero_principal_part ((differentiable_LFunction nonprincipal).analyticAt 0)
    Chi8Origin.LFunction_zero Chi8Origin.deriv_LFunction_zero_ne_zero

end Chi8Budget
