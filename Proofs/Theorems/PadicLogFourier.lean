module

public import Lemmas.PadicLogFourier

import Mathlib.Algebra.GroupWithZero.Indicator
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.NumberTheory.Padics.ProperSpace

/-!
# The translated rational unit-indicator test

In (B.4.4.2) and (B.4.4.7), pp. 620–621, the additive Fourier input is
`f(1+x) / |1+x|ₚ^(1/2)`, extended by zero at `-1`. For the unit indicator
this is the indicator of `|1+x|ₚ = 1`. Lemma B.4.4.5 reduces the general
principal-value formula to the zero-identity-value case and this test.
Masullo states a two-ball transform after (B.4.4.15), p. 623; footnote
24 asks to check the right-hand side. The transform is not yet an
evaluation of the logarithm-weighted pairing, and vanishing of the
logarithm on the original unit group does not give that evaluation.
We derive the signed transform from the checked ball formulas, then
compute both weighted frequency integrals. Locators are from the
pinned PDF text extraction.
-/

open scoped Padic
open MeasureTheory Set

namespace Masullo

variable (p : ℕ) [Fact p.Prime]

local notation "B" => Set.ofPred (fun x : ℚ_[p] ↦ ‖x‖ ≤ 1)
local notation "T" => Set.ofPred (fun x : ℚ_[p] ↦ ‖(p : ℚ_[p]) * x‖ ≤ 1)
local notation "U" => Set.ofPred (fun x : ℚ_[p] ↦ ‖1 + x‖ = 1)
local notation "C" => Set.ofPred (fun x : ℚ_[p] ↦ ‖(p : ℚ_[p])⁻¹ * (x - (-1))‖ ≤ 1)
local notation "J" => (fun x : ℚ_[p] ↦ ((Real.log ‖x‖ / Real.log (p : ℝ) : ℝ) : ℂ))
local notation "χ" => (fun x : ℚ_[p] ↦ star (padicStdAddChar p (-x)))

/-- The translated unit indicator in (B.4.4.14) has zero rational finite
principal-value pairing. The normalized logarithm times the additive
Fourier transform of the translated test is absolutely integrable. -/
public theorem padicTranslatedUnits_log_fourier :
    let g := fun ξ : ℚ_[p] ↦ J ξ *
      (∫ x in U, star (padicStdAddChar p (x * ξ)) ∂padicAddHaar p)
    Integrable g (padicAddHaar p) ∧ (∫ ξ, g ξ ∂padicAddHaar p) = 0 := by
  classical
  let f := (B).indicator J
  let h := (T).indicator (fun ξ ↦ J ξ * χ ξ)
  have hB : MeasurableSet B := (isClosed_le continuous_norm continuous_const).measurableSet
  have hT : MeasurableSet T := (isClosed_le (by fun_prop) continuous_const).measurableSet
  have hC : MeasurableSet C := (isClosed_le (by fun_prop) continuous_const).measurableSet
  -- The translated unit indicator removes exactly the `-1` residue coset.
  have hball := padicTranslatedUnits_eq_sdiff p
  have hFourier (ξ : ℚ_[p]) :
      (∫ x in U, star (padicStdAddChar p (x * ξ)) ∂padicAddHaar p) =
        (B).indicator (fun _ ↦ (1 : ℂ)) ξ - (p : ℂ)⁻¹ * χ ξ *
          (T).indicator (fun _ ↦ (1 : ℂ)) ξ := by
    have hi : IntegrableOn (fun x : ℚ_[p] ↦ star (padicStdAddChar p (x * ξ))) B
        (padicAddHaar p) := by
      have hBc : B = Metric.closedBall 0 1 := by
        ext x
        simp only [mem_ofPred_eq, Metric.mem_closedBall, dist_zero_right]
      rw [hBc]
      have hc : Continuous (fun x : ℚ_[p] ↦ star (padicStdAddChar p (x * ξ))) :=
        ((continuous_padicStdAddChar p).comp (continuous_id.mul continuous_const)).star
      exact hc.continuousOn.integrableOn_compact (isCompact_closedBall _ _)
    rw [hball.1, setIntegral_sdiff hC hi hball.2, padicIntegralBall_fourier]
    have hind : (T).indicator (fun _ ↦ (1 : ℂ)) ξ =
        (B).indicator (fun _ ↦ (1 : ℂ)) ((p : ℚ_[p]) * ξ) := by
      change ((fun z : ℚ_[p] ↦ (p : ℚ_[p]) * z) ⁻¹' B).indicator
        (fun _ ↦ (1 : ℂ)) ξ = _
      exact indicator_comp_right (fun z : ℚ_[p] ↦ (p : ℚ_[p]) * z)
        (g := fun _ ↦ (1 : ℂ))
    rw [hind]
    simpa only [pow_one, neg_one_mul] using
      congrArg (fun z : ℂ ↦ (B).indicator (fun _ ↦ (1 : ℂ)) ξ - z)
        (padicTranslatedBall_fourier p 1 (-1) ξ)
  have he : (fun ξ ↦ J ξ * (∫ x in U, star (padicStdAddChar p (x * ξ)) ∂padicAddHaar p)) =
      (fun ξ ↦ f ξ - (p : ℂ)⁻¹ * h ξ) := by
    funext ξ
    have hfξ : f ξ = J ξ * (B).indicator (fun _ ↦ 1) ξ := by
      simpa only [mul_one] using indicator_mul_right B J (fun _ ↦ (1 : ℂ)) (i := ξ)
    have hhξ : h ξ = J ξ * ((T).indicator (fun _ ↦ 1) ξ * χ ξ) := by
      rw [show h ξ = _ from indicator_mul_left T J χ,
        show (T).indicator J ξ = _ from by
          simpa only [mul_one] using indicator_mul_right T J (fun _ ↦ (1 : ℂ)) (i := ξ),
        mul_assoc]
    rw [hFourier, hfξ, hhξ]
    ring
  dsimp only
  rw [he]
  -- Integrate the logarithm on the inner ball and the weighted phase on the larger ball.
  have hinner := padicIntegralBall_log_moment p
  have houter := padicOuterBall_log_phase p
  have hfi : Integrable f (padicAddHaar p) := (integrable_indicator_iff hB).mpr hinner.1.ofReal
  have hhi : Integrable h (padicAddHaar p) := (integrable_indicator_iff hT).mpr houter.1
  refine ⟨hfi.sub (hhi.const_mul _), ?_⟩
  rw [integral_sub hfi (hhi.const_mul _), integral_const_mul,
    show (∫ ξ, f ξ ∂padicAddHaar p) = _ from integral_indicator hB,
    show (∫ ξ, h ξ ∂padicAddHaar p) = _ from integral_indicator hT,
    integral_complex_ofReal, hinner.2, houter.2]
  have hp : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hp₀ : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne p)
  have hp₁ : (p : ℂ) - 1 ≠ 0 := by
    exact_mod_cast (sub_pos.mpr hp).ne'
  push_cast
  field_simp [hp₀, hp₁]
  ring

end Masullo
