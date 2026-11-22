module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Lemmas.DigammaExponential
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Tactic.Ring

/-!
# Shifted Archimedean Gamma factors on the right half-plane

The local factors (3.2.1.3)–(5), p. 123, give the real parity and the
absolute complex angular weight. In (B.4.2.12)–(16), pp. 615–616,
Masullo uses a digamma calculation, but the extracted purely imaginary
shift cannot encode those weights. Retain both the nonnegative shift
and the imaginary radial shift, differentiate the actual prefactor, and
use an absolutely integrable Gauss difference before testing the line.
The readings here are based on extraction, not the rendered equations.
-/

open Complex MeasureTheory Set

namespace Masullo

/-- The Gamma factor with base `B`, scale `d`, nonnegative parameter `b`,
and radial parameter `τ` in the normalized local norm. The real place
uses `B = π, d = 2, b = 0 or 1`; the complex place uses
`B = 2π, d = 1, b = |n|/2`. Complex conjugation changes `τ` to `-τ`
and leaves `b` unchanged. These parameters do not classify local characters. -/
public noncomputable def archimedeanGammaFactor (B d b τ : ℝ) (s : ℂ) : ℂ :=
  let z := (s + (b : ℂ) + (τ : ℂ) * I) / (d : ℂ)
  exp (-(Real.log B : ℂ) * z) * Gamma z

/-- At a positive base the exponential is the usual positive-base power
in (3.2.1.4)–(5). -/
private theorem archimedeanGammaFactor_eq_cpow {B : ℝ} (hB : 0 < B) (d b τ : ℝ) (s : ℂ) :
    let z := (s + (b : ℂ) + (τ : ℂ) * I) / (d : ℂ)
    archimedeanGammaFactor B d b τ s = (B : ℂ) ^ (-z) * Gamma z := by
  dsimp only [archimedeanGammaFactor]
  rw [cpow_def_of_ne_zero (ofReal_ne_zero.mpr hB.ne'), ← ofReal_log hB.le, neg_mul, mul_neg]

/-- The real factor in (3.2.1.4), with `b = 0` or `1` for its parity. -/
public theorem archimedeanGammaFactor_real (b τ : ℝ) :
    archimedeanGammaFactor Real.pi 2 b τ = fun s ↦ Gammaℝ (s + (b : ℂ) + (τ : ℂ) * I) := by
  funext s
  rw [archimedeanGammaFactor_eq_cpow Real.pi_pos, Gammaℝ_def, ofReal_ofNat, neg_div]

/-- The complex factor in (3.2.1.5), with `b = |n|/2` for its angular
weight. Deligne's `Gammaℂ` includes an extra factor of `2`. -/
public theorem archimedeanGammaFactor_complex (b τ : ℝ) :
    archimedeanGammaFactor (2 * Real.pi) 1 b τ =
      fun s ↦ Gammaℂ (s + (b : ℂ) + (τ : ℂ) * I) / 2 := by
  funext s
  rw [archimedeanGammaFactor_eq_cpow (by positivity), Gammaℂ_def]
  simp only [ofReal_mul, ofReal_ofNat, ofReal_one, div_one]
  ring

private theorem archimedeanGamma_argument_re_pos {d b τ : ℝ} (hd : 0 < d) (hb : 0 ≤ b)
    {s : ℂ} (hs : 0 < s.re) : 0 < ((s + (b : ℂ) + (τ : ℂ) * I) / (d : ℂ)).re := by
  have hre : (s + (b : ℂ) + (τ : ℂ) * I).re = s.re + b := by simp [mul_re]
  simpa only [div_eq_mul_inv, ← ofReal_inv, mul_re, ofReal_re, ofReal_im, mul_zero, sub_zero, hre]
    using (div_pos (add_pos_of_pos_of_nonneg hs hb) hd : 0 < (s.re + b) / d)

private theorem archimedeanGamma_argument_hasDerivAt (d b τ : ℝ) (s : ℂ) :
    HasDerivAt (fun w : ℂ ↦ (w + (b : ℂ) + (τ : ℂ) * I) / (d : ℂ)) (1 / (d : ℂ)) s :=
  ((((hasDerivAt_id s).add_const (b : ℂ)).add_const ((τ : ℂ) * I)).div_const (d : ℂ))

/-- The parameterized factor is holomorphic on the open right half-plane. -/
public theorem analyticOnNhd_archimedeanGammaFactor {B d b τ : ℝ} (hd : 0 < d) (hb : 0 ≤ b) :
    AnalyticOnNhd ℂ (archimedeanGammaFactor B d b τ) {s : ℂ | 0 < s.re} := by
  refine DifferentiableOn.analyticOnNhd (fun s hs ↦ ?_) (isOpen_lt continuous_const continuous_re)
  have hz := archimedeanGamma_argument_re_pos (τ := τ) hd hb hs
  have harg := archimedeanGamma_argument_hasDerivAt d b τ s
  exact ((harg.const_mul (-(Real.log B : ℂ))).cexp.differentiableAt.mul
    ((hasDerivAt_Gamma_of_re_pos hz).differentiableAt.comp s harg.differentiableAt)).differentiableWithinAt

/-- The corrected scalar (B.4.2.12), with the Gauss subtraction kept
inside the absolutely integrable kernel. The prefactor contributes
`-log B / d`; `t = exp (-d * x)` cancels the chain-rule `1 / d` in the
integral part of the digamma term. -/
public theorem logDeriv_archimedeanGammaFactor_eq_integral {B d b τ : ℝ}
    (hd : 0 < d) (hb : 0 ≤ b) {s : ℂ} (hs : 0 < s.re) :
    let w := s + (b : ℂ) + (τ : ℂ) * I
    let K := fun x : ℝ ↦ (exp (-(d : ℂ) * (x : ℂ)) - exp (-w * (x : ℂ))) /
      (1 - exp (-(d : ℂ) * (x : ℂ)))
    archimedeanGammaFactor B d b τ s ≠ 0 ∧ IntegrableOn K (Ioi 0) ∧
      logDeriv (archimedeanGammaFactor B d b τ) s =
        -((Real.log B : ℂ) + (Real.eulerMascheroniConstant : ℂ)) / (d : ℂ) +
          ∫ x in Ioi (0 : ℝ), K x := by
  let z (w : ℂ) := (w + (b : ℂ) + (τ : ℂ) * I) / (d : ℂ)
  let E (w : ℂ) := exp (-(Real.log B : ℂ) * z w)
  have hz : 0 < (z s).re := archimedeanGamma_argument_re_pos hd hb hs
  have hg₀ := Gamma_ne_zero_of_re_pos hz
  obtain ⟨hK, hval⟩ := digamma_sub_one_eq_exponential_integral hd hz
  refine ⟨mul_ne_zero (exp_ne_zero _) hg₀, hK, ?_⟩
  have harg := archimedeanGamma_argument_hasDerivAt d b τ s
  have hE := (harg.const_mul (-(Real.log B : ℂ))).cexp
  have hG := (hasDerivAt_Gamma_of_re_pos hz).differentiableAt
  -- First take the logarithmic derivatives of the two factors.
  change logDeriv (fun w ↦ E w * Gamma (z w)) s = _
  rw [logDeriv_fun_mul (f := E) (g := fun w ↦ Gamma (z w)) s (exp_ne_zero _) hg₀
    hE.differentiableAt (hG.comp s harg.differentiableAt),
    logDeriv_fun_comp (f := Gamma) (g := z) hG harg.differentiableAt,
    ← digamma_def]
  have hArgVal : deriv z s = 1 / (d : ℂ) := harg.deriv
  have hEVal : deriv E s = E s * (-(Real.log B : ℂ) * (1 / (d : ℂ))) := hE.deriv
  -- Then insert the absolutely integrable Gauss difference.
  rw [hArgVal, logDeriv_apply, hEVal, mul_div_cancel_left₀ _ (show E s ≠ 0 from exp_ne_zero _),
    hval, digamma_one]
  simp only [z, div_eq_mul_inv]
  ring

end Masullo
