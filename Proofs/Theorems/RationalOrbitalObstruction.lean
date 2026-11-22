module

public import Theorems.RationalOrbitalPrimeTwo
public import Theorems.RationalOrbitalSectionWeight

/-!
# The two sides of the literal rational orbital identity disagree

On the Haar interpretation of (11.3.2.2), p. 495, the weight is zero even
before imposing the shell cutoff. For the unshifted right side of (11.3.2.1)
with the prime-two class test, the inverse uniformizer alone contributes.
The arbitrary kernel below can absorb the divisorial indicator difference;
there is no hypothesis about existence of a spectral tensor.
-/

open NumberField MeasureTheory

namespace Masullo

local notation "I" => IdeleGroup (𝓞 ℚ) ℚ
local notation "N" => ideleNormOne (K := ℚ)

set_option linter.concreteInstances false

/-- No kernel can realize the printed equality at the prime-two witness with
this literal section weight, even with freedom to choose the outer measure. -/
public theorem rationalOrbitalPrimeTwo_skewIntegral_ne_rhs [MeasurableSpace N] [BorelSpace N]
    (μ : Measure N) [μ.IsHaarMeasure] (E : Set N) (ν : Measure (Multiplicative ℝ))
    (K : I × I → ℂ) :
    (∑' ξ : ℚˣ, ∫ t, ∫ g in E,
      let xy := (rationalIdeleLogSection t,
        IdeleGroup.unitEmbedding (𝓞 ℚ) ℚ ξ * g.val * rationalIdeleLogSection t)
      (rationalOrbitalSectionWeight μ E xy : ℂ) * K xy ∂μ ∂ν) ≠ rationalOrbitalPrimeTwoRHS := by
  rw [rationalOrbitalSectionWeight_skewIntegral_eq_zero]
  exact rationalOrbitalPrimeTwo_rhs_ne_zero.symm

end Masullo
