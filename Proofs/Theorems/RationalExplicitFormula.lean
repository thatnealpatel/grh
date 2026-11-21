module

public import Theorems.RationalExplicitFormulaFinitePlaces
public import Props.GammaRealMellin

/-!
# The rational explicit formula with both local terms evaluated

This is Appendix B's explicit formula for the trivial rational character
and smooth compact log profiles, in the unshifted Mellin convention.
The zero sum uses full analytic orders, not a Sobolev cap. The equation
is not an identification with the global trace or the idelic principal value.
-/

open Complex MeasureTheory Set
open scoped ContDiff

namespace Masullo

/-- Rational compact-log case of Theorem B.4.2.2, with the real factor
from `compactLogMellin_GammaReal_evaluation` and the finite terms from
`completedZeta_contour_finite_places`. Both pole terms are retained. -/
public theorem completedZeta_explicit_formula {g : ℝ → ℂ}
    (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g) :
    let Φ := compactLogMellin g
    let prime := fun n : ℕ ↦ (ArithmeticFunction.vonMangoldt n : ℂ) *
      (g (Real.log n) + g (-Real.log n) / (n : ℂ))
    let real := fun x : ℝ ↦ (2 * g 0 * exp (-2 * (x : ℂ)) - g x - exp (-(x : ℂ)) * g (-x)) /
      (1 - exp (-2 * (x : ℂ)))
    IntegrableOn real (Ioi 0) ∧
    Summable (fun n ↦ ‖prime n‖) ∧
    Summable (fun ρ : criticalStripZetaZeros ↦ ‖(zetaZeroOrder ρ : ℂ) * Φ (ρ : ℂ)‖) ∧
    (-((Real.log Real.pi : ℂ) + (Real.eulerMascheroniConstant : ℂ)) * g 0 +
      ∫ x in Ioi (0 : ℝ), real x) - (∑' n, prime n) =
      -Φ 0 - Φ 1 + ∑' ρ : criticalStripZetaZeros, (zetaZeroOrder ρ : ℂ) * Φ (ρ : ℂ) := by
  obtain ⟨_, hprimes, hzeros, hcontour⟩ := completedZeta_contour_finite_places hg hc
  obtain ⟨hreal, hΓ⟩ := compactLogMellin_GammaReal_evaluation hg hc
  rw [hΓ] at hcontour
  exact ⟨hreal, hprimes, hzeros, hcontour⟩

end Masullo
