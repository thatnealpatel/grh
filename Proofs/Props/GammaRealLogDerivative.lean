module

public import Props.ArchimedeanGammaLogDerivative
public import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma

/-!
# The real Gamma factor on the right half-plane

The rational trivial character uses `Gammaℝ(s) = π^(-s/2) Γ(s/2)`,
the even real factor in (3.2.1.4), p. 123. Its scalar log derivative
in (B.4.2.12)–(16), pp. 615–616, is the unshifted case of the
subtracted Archimedean Gauss integral.
-/

open Complex MeasureTheory Set

namespace Masullo

/-- The real factor in the rational contour, before integration against a
Mellin test. The `π^(-s/2)` prefactor contributes `-log π / 2`. -/
public theorem logDeriv_GammaReal_eq_integral {s : ℂ} (hs : 0 < s.re) :
    let K := fun x : ℝ ↦ (exp (-2 * (x : ℂ)) - exp (-s * (x : ℂ))) /
      (1 - exp (-2 * (x : ℂ)))
    IntegrableOn K (Ioi 0) ∧
    logDeriv Gammaℝ s = -((Real.log Real.pi : ℂ) + (Real.eulerMascheroniConstant : ℂ)) / 2 +
      ∫ x in Ioi (0 : ℝ), K x := by
  have hfactor : archimedeanGammaFactor Real.pi 2 0 0 = Gammaℝ := by
    simpa only [ofReal_zero, zero_mul, add_zero] using archimedeanGammaFactor_real 0 0
  have h := (logDeriv_archimedeanGammaFactor_eq_integral (B := Real.pi) (d := 2) (b := 0) (τ := 0)
    two_pos le_rfl hs).2
  simpa only [hfactor, ofReal_zero, add_zero, zero_mul, ofReal_ofNat] using h

end Masullo
