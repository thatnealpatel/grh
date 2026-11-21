module

public import Theorems.RationalLocalPrincipalValue
public import Props.RationalFiniteHaar
import Lemmas.RationalLocalRadialTest

/-!
# The rational radial finite-place term in prime-power samples

For a compact log profile, this identifies the primed local integral
(B.4.4.21), p. 625, with the paired samples from the rational contour
evaluation of (B.4.2.10)–(11), p. 615, using the shell expansion
(B.4.4.22). This per-place calculation does not evaluate the Chapter 12
global trace. Locators follow the pinned text extraction.
-/

open NumberField IsDedekindDomain HeightOneSpectrum MeasureTheory

namespace Masullo

local notation "V" => HeightOneSpectrum (𝓞 ℚ)
local notation "K[" v "]" => adicCompletion ℚ v
local notation "P[" v "]" => (((Rat.HeightOneSpectrum.primesEquiv v : Nat.Primes) : ℕ) : ℝ)

/-- The negative logarithmic Fourier pairing of the actual shifted radial test
is its canonically normalized prime-power sum. The Fourier integrand is
absolutely integrable, and the samples vanish past a finite exponent.
The radial profile need not vanish at the identity. -/
public theorem rationalLocalRadialFourier_eq_primeSamples (v : V) [MeasurableSpace (K[v]ˣ)]
    [BorelSpace (K[v]ˣ)] {F : ℝ → ℂ} (hF : HasCompactSupport F) :
    let ν := rationalLocalFieldAddHaar v
    let f := fun y : K[v]ˣ ↦ F (Real.log ‖(y : K[v])‖)
    let g := fun x : ℝ ↦ Complex.exp (-(x : ℂ) / 2) * F x
    let l := Real.log P[v]
    let B := fun ξ ↦ (l : ℂ) * rationalLocalLogFourierIntegrand v (rationalLocalShiftedTest v f) ξ
    let C := fun m : ℕ ↦
      let n := P[v] ^ (m + 1)
      (l : ℂ) * (g (Real.log n) + g (-Real.log n) / (n : ℂ))
    Integrable B ν ∧ (∃ M : ℕ, ∀ m ≥ M, C m = 0) ∧ -(∫ ξ, B ξ ∂ν) = ∑' m : ℕ, C m := by
  intro ν f g l B C
  -- Compact log support meets the test hypotheses of (B.4.4.21) because
  -- the norm is locally constant and only finitely many compact shells meet the support.
  obtain ⟨hf, hfc⟩ := rationalLocalRadialTest_properties v hF
  obtain ⟨hB, _, hpair⟩ := rationalLocalShifted_principal_value v f hf hfc
  -- (B.4.4.22): Evaluate the subtracted Haar side by opposite valuation shells.
  obtain ⟨_, hfinite, hsum⟩ := rationalLocalRadialHaar_eq_primeSamples v hF
  refine ⟨hB, hfinite, hpair.trans ?_⟩
  calc
    _ = ∫ y, (l : ℂ) * rationalLocalRadialSubtracted v F y ∂rationalLocalMultiplicativeHaar v := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun y ↦ ?_)
      exact congrArg ((l : ℂ) * ·) (rationalLocalRadial_subtraction v F y)
    _ = _ := by
      rw [integral_const_mul]
      exact hsum

end Masullo
