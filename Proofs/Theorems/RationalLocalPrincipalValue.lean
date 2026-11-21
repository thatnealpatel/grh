module

public import Lemmas.RationalLocalPrincipalValue

/-!
# The rational finite-place principal value

Lemma B.4.4.5, (B.4.4.14), pp. 622–623, subtracts the identity value on
integral units. Over `ℚ` the local different is trivial, so there is no
additional contact term. The norm-one indicator is an admissible test;
`rationalLocalUnitIndicator_log_fourier` supplies its zero pairing using
the checked two-ball calibration, not the frequency display questioned
in footnote 24. Locators follow the pinned text extraction.
-/

open NumberField IsDedekindDomain HeightOneSpectrum MeasureTheory

namespace Masullo

local notation "V" => HeightOneSpectrum (𝓞 ℚ)
local notation "K[" v "]" => adicCompletion ℚ v
local notation "P[" v "]" => (((Rat.HeightOneSpectrum.primesEquiv v : Nat.Primes) : ℕ) : ℝ)
local notation "ν[" v "]" => rationalLocalFieldAddHaar v

/-- (B.4.4.14) at every rational finite place. The canonical factor `log p`
is included in both integrands. The additive Fourier input is the original
shifted test, while the multiplicative integral subtracts only on integral
units. Both integrands are absolutely integrable. -/
public theorem rationalLocalShifted_principal_value (v : V) [MeasurableSpace (K[v]ˣ)]
    [BorelSpace (K[v]ˣ)] (f : K[v]ˣ → ℂ) (hf : IsLocallyConstant f) (hc : HasCompactSupport f) :
    let L : ℂ := ↑(Real.log P[v])
    let F := fun ξ ↦ L * rationalLocalLogFourierIntegrand v (rationalLocalShiftedTest v f) ξ
    let H := fun y : K[v]ˣ ↦ L * ((f y - f 1 * rationalLocalUnitIndicator v y) *
      (↑(Real.sqrt ‖(y : K[v])‖) : ℂ) / (↑‖1 - (y : K[v])‖ : ℂ))
    Integrable F ν[v] ∧ Integrable H (rationalLocalMultiplicativeHaar v) ∧
      -(∫ ξ, F ξ ∂ν[v]) = ∫ y, H y ∂rationalLocalMultiplicativeHaar v := by
  let U := rationalLocalUnitIndicator v
  let g := fun y ↦ f y - f 1 * U y
  obtain ⟨hU, hUc, hU₁⟩ := rationalLocalUnitIndicator_properties v
  have hconst : IsLocallyConstant (fun _ : K[v]ˣ ↦ f 1) := IsLocallyConstant.const _
  have hg : IsLocallyConstant g := hf.sub (hconst.mul hU)
  have hgc : HasCompactSupport g := hc.sub (hUc.mul_left (f := fun _ ↦ f 1))
  have hg₁ : g 1 = 0 := by simp [g, U, hU₁]
  -- (B.4.4.5): Only the subtracted test goes into the zero-value comparison.
  obtain ⟨hFg, hH, hpair⟩ := rationalLocalShifted_log_fourier v g hg hgc hg₁
  -- (B.4.4.14), p. 623: The discarded unit term contributes zero on the Fourier side.
  obtain ⟨hFU, hzero⟩ := rationalLocalUnitIndicator_log_fourier v
  have hf' : f = fun y ↦ g y + f 1 * U y := by funext y; simp [g]
  have hlin := rationalLocalShiftedFourier_add_mul v (f 1) hg hgc hU hUc
  rw [← hf'] at hlin
  dsimp only
  simp_rw [hlin]
  refine ⟨(hFg.add (hFU.const_mul _)).const_mul _, hH.const_mul _, ?_⟩
  rw [integral_const_mul, integral_const_mul, integral_add hFg (hFU.const_mul _),
    integral_const_mul, hzero, mul_zero, add_zero, ← mul_neg, hpair]

end Masullo
