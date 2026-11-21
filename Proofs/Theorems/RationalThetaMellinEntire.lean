module

public import Theorems.RationalThetaMellin
import Lemmas.RationalThetaMellinDerivative

/-!
# Entire rational theta Mellin transform with both zero modes removed

This is the rational unramified lattice model of Masullo's Theorem
3.2.2.1(2)(a) and (3)(a), pp. 124–125, for the trivial compact isotype.
Here we differentiate the log-norm integral directly using the two-tail
bound, rather than proving holomorphy by locally uniform truncation.
-/

open MeasureTheory
open scoped FourierTransform SchwartzMap

namespace Masullo

/-- Both zero modes vanish, so the theta Mellin integrand and its parameter
derivative are absolutely integrable at every complex parameter. The derivative
of the integral inserts the factor `x`, the logarithm of the norm. -/
public theorem hasDerivAt_rationalTheta_mellin (b : 𝓢(ℝ, ℂ))
    (hb : b 0 = 0) (hFourier : (𝓕 b) 0 = 0) (z : ℂ) :
    Integrable (fun x : ℝ ↦ rationalTheta b (Real.exp x) * Complex.exp (z * x)) ∧
    Integrable (fun x : ℝ ↦ (x : ℂ) * (rationalTheta b (Real.exp x) * Complex.exp (z * x))) ∧
    HasDerivAt (fun w : ℂ ↦ ∫ x : ℝ, rationalTheta b (Real.exp x) * Complex.exp (w * x))
      (∫ x : ℝ, (x : ℂ) * (rationalTheta b (Real.exp x) * Complex.exp (z * x))) z := by
  have hzero := hasDerivAt_rationalTheta_mellin_logMoment b hb hFourier 0 z
  have hone := hasDerivAt_rationalTheta_mellin_logMoment b hb hFourier 1 z
  simpa only [pow_zero, pow_one, Nat.zero_add, one_mul, mul_assoc] using
    And.intro hzero.1 (And.intro hone.1 hzero.2)

/-- The two-moment rational theta Mellin transform is entire. -/
public theorem differentiable_rationalTheta_mellin (b : 𝓢(ℝ, ℂ))
    (hb : b 0 = 0) (hFourier : (𝓕 b) 0 = 0) :
    Differentiable ℂ (fun z : ℂ ↦ ∫ x : ℝ,
      rationalTheta b (Real.exp x) * Complex.exp (z * x)) :=
  fun z ↦ (hasDerivAt_rationalTheta_mellin b hb hFourier z).2.2.differentiableAt

end Masullo
