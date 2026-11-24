module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# The logarithmic derivative of the even mod-eight completion

The archimedean contribution at `s = 1` depends only on the completion
factor, not on any arithmetic properties of `L`.
-/

namespace Chi8Completion

/-- Classical even mod-eight completion of a complex-valued function `L`. -/
@[expose] public noncomputable def completion (L : ℂ → ℂ) (s : ℂ) : ℂ :=
  ((8 : ℂ) / (Real.pi : ℂ)) ^ (s / 2) * Complex.Gamma (s / 2) * L s

/-- Twice the real part of the logarithmic derivative at `1`. -/
public theorem two_re_logDeriv_completion_one (L : ℂ → ℂ)
    (hL : DifferentiableAt ℂ L 1) (hL₀ : L 1 ≠ 0) :
    2 * (deriv (completion L) 1 / completion L 1).re =
      Real.log (8 / Real.pi) - Real.eulerMascheroniConstant - 2 * Real.log 2 +
        2 * (deriv L 1 / L 1).re := by
  let c : ℂ := (8 : ℂ) / (Real.pi : ℂ)
  let half : ℂ → ℂ := fun s => s / 2
  let P : ℂ → ℂ := fun s => c ^ half s
  let G : ℂ → ℂ := Complex.Gamma ∘ half
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_pos.ne'
  have hc : c ≠ 0 := div_ne_zero (by norm_num) hpi
  have hhalf : HasDerivAt half (1 / 2) 1 := (hasDerivAt_id (1 : ℂ)).div_const 2
  have hP := hhalf.const_cpow (Or.inl hc)
  have hP₀ : P 1 ≠ 0 := fun h => hc ((Complex.cpow_eq_zero_iff _ _).mp h).1
  have hGamma : DifferentiableAt ℂ Complex.Gamma (half 1) :=
    Complex.hasDerivAt_Gamma_one_half.differentiableAt
  have hG : DifferentiableAt ℂ G 1 := hGamma.comp 1 hhalf.differentiableAt
  have hG₀ : G 1 ≠ 0 := by
    change Complex.Gamma (1 / 2) ≠ 0
    rw [Complex.Gamma_one_half_eq]
    exact fun h => hpi ((Complex.cpow_eq_zero_iff _ _).mp h).1
  have hlogP : logDeriv P 1 = Complex.log c * (1 / 2) := by
    rw [logDeriv_apply, hP.deriv]
    change P 1 * Complex.log c * (1 / 2) / P 1 = _
    rw [mul_assoc, mul_comm (P 1), mul_div_cancel_right₀ _ hP₀]
  have hlogG : logDeriv G 1 = Complex.digamma (1 / 2) * (1 / 2) := by
    rw [logDeriv_comp hGamma hhalf.differentiableAt, hhalf.deriv, ← Complex.digamma_def]
  have hcast : c = ((8 / Real.pi : ℝ) : ℂ) := by
    simp [c]
  have hcastHalf : (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) := by norm_num
  change 2 * (logDeriv (P * G * L) 1).re = _
  rw [logDeriv_mul (f := P * G) (g := L) 1 (mul_ne_zero hP₀ hG₀) hL₀
      (hP.differentiableAt.mul hG) hL,
    logDeriv_mul 1 hP₀ hG₀ hP.differentiableAt hG,
    hlogP, hlogG, Complex.digamma_one_half, hcast, hcastHalf, ← Complex.ofNat_log (n := 2)]
  simp only [Complex.add_re, Complex.mul_re, Complex.log_ofReal_re, Complex.ofReal_im,
    Complex.sub_re, Complex.ofReal_re, mul_zero, sub_zero, logDeriv_apply]
  norm_num
  ring

end Chi8Completion
