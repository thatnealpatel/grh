module

public import Theorems.PadicStandardCharacter
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Haar.Basic

import Mathlib.MeasureTheory.Group.Integral
import Mathlib.NumberTheory.Padics.ProperSpace

/-!
# Fourier transform of the integral ball of `ℚ_[p]`

We normalize additive Haar measure as in Definition A.3.1.2(3) and Example
A.3.1.7, pp. 556–558. The centered indicator calculation in Examples A.3.1.6–7
is unchanged when we conjugate the positive standard character to use the
negative-exponent Fourier convention.
-/

open scoped Padic
open MeasureTheory Set

namespace Masullo

variable (p : ℕ) [Fact p.Prime]

/-- The measurable sets of `ℚ_[p]` are its Borel sets. -/
public noncomputable scoped instance padicBorelMeasurableSpace : MeasurableSpace ℚ_[p] := borel _

public scoped instance padicBorelSpace : BorelSpace ℚ_[p] := ⟨rfl⟩

local notation "B[" q "]" => Set.ofPred (fun x : ℚ_[q] ↦ ‖x‖ ≤ 1)

private theorem padicIntegralBall_eq_closedBall : B[p] = Metric.closedBall 0 1 := by
  ext x
  simp [Metric.mem_closedBall, dist_eq_norm]

private def padicIntegralCompact : TopologicalSpace.PositiveCompacts ℚ_[p] where
  carrier := B[p]
  isCompact' := by
    rw [padicIntegralBall_eq_closedBall p]
    exact isCompact_closedBall _ _
  interior_nonempty' := by
    rw [padicIntegralBall_eq_closedBall p,
      (IsUltrametricDist.isOpen_closedBall (0 : ℚ_[p]) one_ne_zero).interior_eq]
    exact ⟨0, Metric.mem_closedBall_self zero_le_one⟩

/-- Additive Haar measure on `ℚ_[p]`, normalized by the integral ball. -/
public noncomputable def padicAddHaar : Measure ℚ_[p] :=
  Measure.addHaarMeasure (padicIntegralCompact p)

public instance : (padicAddHaar p).IsAddHaarMeasure := by
  unfold padicAddHaar
  infer_instance

/-- The `p`-adic integers have mass one for the normalized additive Haar measure. -/
public theorem padicAddHaar_integralBall : padicAddHaar p B[p] = 1 :=
  Measure.addHaarMeasure_self (K₀ := padicIntegralCompact p)

/-- The Fourier transform of the integral-ball indicator is itself. The
integral uses the conjugate of the positive standard character. -/
public theorem padicIntegralBall_fourier (y : ℚ_[p]) :
    (∫ x in B[p], star (padicStdAddChar p (x * y)) ∂padicAddHaar p) =
      (B[p]).indicator (fun _ ↦ (1 : ℂ)) y := by
  classical
  have hB : MeasurableSet B[p] := by
    rw [padicIntegralBall_eq_closedBall p]
    exact Metric.isClosed_closedBall.measurableSet
  by_cases hy : y ∈ B[p]
  · -- The character is trivial on all products of integral elements.
    rw [indicator_of_mem hy]
    calc
      _ = ∫ x in B[p], (1 : ℂ) ∂padicAddHaar p := by
        apply setIntegral_congr_fun hB
        intro x hx
        change star (padicStdAddChar p (x * y)) = 1
        rw [(padicStdAddChar_eq_one_iff p _).mpr, star_one]
        calc
          ‖x * y‖ = ‖x‖ * ‖y‖ := norm_mul x y
          _ ≤ 1 * ‖y‖ := mul_le_mul_of_nonneg_right hx (norm_nonneg y)
          _ ≤ 1 := by rwa [one_mul]
      _ = 1 := by simp [Measure.real, padicAddHaar_integralBall]
  · -- Translation by the integral element `1` preserves the ball and changes the phase.
    let f : ℚ_[p] → ℂ := (B[p]).indicator (fun x ↦ star (padicStdAddChar p (x * y)))
    have h₁ : padicStdAddChar p 1 = 1 := (padicStdAddChar_eq_one_iff p _).mpr (by simp)
    have htranslate (x : ℚ_[p]) : f (1 + x) = star (padicStdAddChar p y) * f x := by
      have hmem : 1 + x ∈ B[p] ↔ x ∈ B[p] := by
        change ‖1 + x‖ ≤ 1 ↔ ‖x‖ ≤ 1
        rw [← padicStdAddChar_eq_one_iff p (1 + x), ← padicStdAddChar_eq_one_iff p x,
          AddChar.map_add_eq_mul, h₁, one_mul]
      by_cases hx : x ∈ B[p]
      · simp only [f, indicator_of_mem hx, indicator_of_mem (hmem.mpr hx), add_mul, one_mul,
          AddChar.map_add_eq_mul, star_mul']
      · simp [f, indicator_of_notMem hx, indicator_of_notMem (mt hmem.mp hx)]
    have hinvariance :
        star (padicStdAddChar p y) * (∫ x, f x ∂padicAddHaar p) =
          ∫ x, f x ∂padicAddHaar p := by
      rw [← integral_const_mul]
      simpa only [htranslate] using
        (integral_add_left_eq_self (μ := padicAddHaar p) f 1)
    have hphase : star (padicStdAddChar p y) ≠ 1 := by
      intro h
      apply hy
      apply (padicStdAddChar_eq_one_iff p _).mp
      simpa using congrArg star h
    have hzero : (∫ x, f x ∂padicAddHaar p) = 0 := by
      by_contra h
      exact hphase ((mul_eq_right₀ h).mp hinvariance)
    rw [indicator_of_notMem hy]
    simpa only [f, integral_indicator hB] using hzero

end Masullo
