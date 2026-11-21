module

public import Theorems.RationalThetaMellinOrder
import Lemmas.RationalThetaMellinDerivative

/-!
# Log moments and zeta jets of rational theta inputs

In the rational trivial compact isotype, the log moment computes the
unshifted Mellin derivative. Splitting the exponent at the twist `a`
gives the bilinear pairing of the once-twisted theta input from (10.1.1.3),
p. 434, with the jet (10.2.2.4), p. 446. This is a statement on theta
inputs, not on their weighted closure.
-/

open MeasureTheory
open scoped FourierTransform SchwartzMap

namespace Masullo

/-- The `m`-th complex derivative of the two-moment theta transform is its
absolutely convergent `m`-th log moment. -/
public theorem iteratedDeriv_rationalTheta_mellin_eq_logMoment (b : 𝓢(ℝ, ℂ))
    (hb : b 0 = 0) (hFourier : (𝓕 b) 0 = 0) (m : ℕ) (z : ℂ) :
    Integrable (fun x : ℝ ↦ (x : ℂ) ^ m * rationalTheta b (Real.exp x) *
      Complex.exp (z * x)) ∧
    iteratedDeriv m (fun w : ℂ ↦ ∫ x : ℝ, rationalTheta b (Real.exp x) *
      Complex.exp (w * x)) z =
      ∫ x : ℝ, (x : ℂ) ^ m * rationalTheta b (Real.exp x) * Complex.exp (z * x) := by
  refine ⟨(hasDerivAt_rationalTheta_mellin_logMoment b hb hFourier m z).1, ?_⟩
  induction m generalizing z with
  | zero => simp only [iteratedDeriv_zero, pow_zero, one_mul]
  | succ m ih =>
    rw [iteratedDeriv_succ, funext ih]
    exact (hasDerivAt_rationalTheta_mellin_logMoment b hb hFourier m z).2.deriv

/-- Pairing a rational theta input already twisted by `exp (a * x)` with
the jet at `ρ - a` is absolutely convergent and vanishes below the zeta
order. In particular one can use `a = 1/2` without inserting a second
half twist. -/
public theorem rationalTheta_twisted_logMoment_eq_zero (b : 𝓢(ℝ, ℂ))
    (hb : b 0 = 0) (hFourier : (𝓕 b) 0 = 0) (a : ℝ) {ρ : ℂ}
    (hpos : 0 < ρ.re) (hlt : ρ.re < 1) {m : ℕ}
    (hm : (m : ℕ∞) < analyticOrderAt riemannZeta ρ) :
    Integrable (fun x : ℝ ↦ (Complex.exp ((a : ℂ) * x) * rationalTheta b (Real.exp x)) *
      ((x : ℂ) ^ m * Complex.exp ((ρ - a) * x))) ∧
    (∫ x : ℝ, (Complex.exp ((a : ℂ) * x) * rationalTheta b (Real.exp x)) *
      ((x : ℂ) ^ m * Complex.exp ((ρ - a) * x))) = 0 := by
  have hsplit (x : ℝ) :
      (Complex.exp ((a : ℂ) * x) * rationalTheta b (Real.exp x)) *
        ((x : ℂ) ^ m * Complex.exp ((ρ - a) * x)) =
      (x : ℂ) ^ m * rationalTheta b (Real.exp x) * Complex.exp (ρ * x) := by
    rw [show ρ * (x : ℂ) = (a : ℂ) * x + (ρ - a) * x by ring, Complex.exp_add]
    ring
  rw [funext hsplit]
  obtain ⟨hint, hmoment⟩ := iteratedDeriv_rationalTheta_mellin_eq_logMoment b hb hFourier m ρ
  exact ⟨hint, hmoment.symm.trans
    (iteratedDeriv_rationalTheta_mellin_eq_zero b hb hFourier hpos hlt hm)⟩

end Masullo
