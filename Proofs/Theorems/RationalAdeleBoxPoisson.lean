module

public import Theorems.RationalAdeleBoxFourier
import Lemmas.RationalAdeleBoxPeriodization
import Theorems.RationalAdelePoisson

/-!
# Pointwise Poisson summation for rational adelic boxes

The rational counting-series form of Masullo's Theorem D.1.2.7(3), p. 749,
applies to every translated, idele-dilated unramified Schwartz tensor.
-/

open NumberField MeasureTheory
open scoped ComplexConjugate FourierTransform SchwartzMap

namespace Masullo

local notation "A" => AdeleRing (𝓞 ℚ) ℚ
local notation "J" => IdeleGroup (𝓞 ℚ) ℚ
local notation "Cq" => A ⧸ rationalDiagonal
local notation "ι" => algebraMap ℚ A
local notation "χ" => rationalAdeleAddChar
local notation "μA" => rationalAdeleAddHaar

set_option linter.concreteInstances false

variable [MeasurableSpace A] [BorelSpace A]

/-- The Fourier coefficients of a box on the rational diagonal are absolutely summable. -/
public theorem summable_norm_rationalAdeleBox_fourier (b : 𝓢(ℝ, ℂ)) (a : A) (g : J) :
    Summable (fun r : ℚ ↦ ‖∫ z, rationalAdeleBox b a g z * conj (χ (z * ι r)) ∂μA‖) := by
  simpa only [integral_rationalAdeleBox_mul_conj_char, norm_smul, norm_mul, Complex.norm_conj,
    norm_rationalAdeleAddChar, one_mul] using
    (summable_norm_rationalAdeleUnramified_mul_diagonal (𝓕 b) g).mul_left ‖ideleNorm g‖

variable [MeasurableSpace Cq] [BorelSpace Cq]

/-- At every adele, the sum of the box over rational diagonal translates equals
its Fourier series over all rational frequencies. Both series converge
absolutely and include the zero index. -/
public theorem hasSum_rationalAdeleBox_poisson (b : 𝓢(ℝ, ℂ)) (a : A) (g : J) (x : A) :
    HasSum (fun d : rationalDiagonal ↦ rationalAdeleBox b a g (x + (d : A)))
      (∑' r : ℚ, (ideleNorm g • (conj (χ (a * ι r)) *
        rationalAdeleUnramified (𝓕 b) ((g : A) * ι r))) * χ (x * ι r)) := by
  simpa only [integral_rationalAdeleBox_mul_conj_char] using
    hasSum_rationalAdele_poisson (continuous_rationalAdeleBox b a g).measurable
      (integrable_rationalAdeleBox b a g) (summable_norm_rationalAdeleBox_add b a g)
      (continuous_rationalAdeleComplexPeriodization_box b a g)
      (summable_norm_rationalAdeleBox_fourier b a g) x

end Masullo
