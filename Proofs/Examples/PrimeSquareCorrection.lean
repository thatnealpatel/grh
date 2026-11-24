module

public import Lemmas.LogRampAbel
public import Lemmas.IntegralRampAverage
public import Lemmas.OddPrimeTheta
import all Lemmas.LogRampAbel
import all Lemmas.OddPrimeTheta
import Mathlib.Tactic

/-!
# Removing prime squares from the mod-four logarithmic race

In the prime-power sum, every odd prime square has character `+1`, even
when its base prime has character `-1`. Removing these squares therefore
subtracts the entire sum below. The von Mangoldt coefficient is `log p`,
not `log (p^2)`; the factor of two comes from the *ramp*, not the weight.
Higher powers and the zero sum are separate parts of the race certificate.
See `.godel/conjectures/closed/mod-four-prime-ramp-eventual-sign.md`, square correction.
-/

open Filter MeasureTheory Finset Real
open scoped Topology

namespace PrimeSquareRamp

/-- The square term at the original cutoff `X`. Index by the base `p`,
so the endpoint is `√X`. A square exactly at the cutoff has zero ramp. -/
@[expose] public noncomputable def squareCorrection (X : ℝ) : ℝ :=
  ∑ p ∈ Ioc 1 ⌊√X⌋₊, log (X / (p : ℝ)^2) * oddWeight p

/-- Abel summation makes the sign and the normalization of the square term explicit. -/
public theorem squareCorrection_eq_integral {X : ℝ} (hX : 1 ≤ X) :
    squareCorrection X = 2 * ∫ t in (1 : ℝ)..√X, oddTheta t / t := by
  have hs : 1 ≤ √X := by simpa using Real.sqrt_le_sqrt hX
  unfold oddTheta
  rw [← logRamp_eq_integral oddWeight (by simp [oddWeight]) (by simp [oddWeight]) hs]
  unfold squareCorrection logRamp
  rw [Finset.mul_sum]
  apply sum_congr rfl
  intro p hp
  have hx : X = (√X)^2 := (Real.sq_sqrt (by linarith)).symm
  conv_lhs => rw [hx, ← div_pow, Real.log_pow]
  norm_num1
  ring

/-- The square contribution is `(2 + o(1)) * √X`, from the ordinary PNT.
No progression estimate, critical-line hypothesis, or zero sum enters. -/
public theorem tendsto_squareCorrection_div_sqrt :
    Tendsto (fun X : ℝ => squareCorrection X / √X) atTop (𝓝 2) := by
  have hav := tendsto_integral_average (f := fun t => oddTheta t / t)
    (fun _ h => partialSum_div_intervalIntegrable oddWeight h) tendsto_oddTheta_div
  have h := (hav.comp Real.tendsto_sqrt_atTop).const_mul (2 : ℝ)
  simp only [mul_one] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with X hX
  simp [Function.comp_apply, squareCorrection_eq_integral hX, mul_div_assoc]

end PrimeSquareRamp
