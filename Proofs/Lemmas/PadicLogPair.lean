module

public import Theorems.PadicLogBallFourier

import Lemmas.PadicBallPartition
import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-! # Integral forms of the off-zero ball calculation -/

open scoped Padic ENNReal
open Set Metric MeasureTheory

namespace Masullo

variable (p : ℕ) [Fact p.Prime]

private theorem padicClosedBall_eq (n : ℕ) (a : ℚ_[p]) :
    closedBall a (((p : ℝ)⁻¹) ^ n) = {x | ‖((p : ℚ_[p]) ^ n)⁻¹ * (x - a)‖ ≤ 1} := by
  have hp : 0 < (p : ℝ) := Nat.cast_pos.mpr (Fact.out : p.Prime).pos
  ext x
  rw [mem_closedBall, dist_eq_norm]
  change _ ↔ ‖((p : ℚ_[p]) ^ n)⁻¹ * (x - a)‖ ≤ 1
  rw [norm_mul, norm_inv, norm_pow, Padic.norm_p, ← le_div_iff₀' (inv_pos.mpr (pow_pos
    (inv_pos.mpr hp) n)), div_inv_eq_mul, one_mul]

private theorem padicClosedBall_measure (n : ℕ) (a : ℚ_[p]) :
    padicAddHaar p (closedBall a (((p : ℝ)⁻¹) ^ n)) = ((p : ℝ≥0∞) ^ n)⁻¹ := by
  rw [padicClosedBall_eq]
  calc
    _ = padicAddHaar p {x | ‖((p : ℚ_[p]) ^ n)⁻¹ * x‖ ≤ 1} := by
      change padicAddHaar p ((fun x : ℚ_[p] ↦ x - a) ⁻¹' {x | ‖((p : ℚ_[p]) ^ n)⁻¹ * x‖ ≤ 1}) = _
      simpa only [sub_eq_add_neg] using
        (measure_preimage_add_right (padicAddHaar p) (-a)
          {x | ‖((p : ℚ_[p]) ^ n)⁻¹ * x‖ ≤ 1})
    _ = _ := padic_measure_dilatedBall p _ (padicAddHaar_integralBall p) n

/-- Absolute integrability and the two equivalent pairings on a closed ball avoiding zero. -/
public theorem padicClosedBall_log_pair (n : ℕ) (a : ℚ_[p]) (ha : ((p : ℝ)⁻¹) ^ n < ‖a‖) :
    let S := closedBall a (((p : ℝ)⁻¹) ^ n)
    let F := fun ξ : ℚ_[p] ↦ (↑(Real.log ‖ξ‖ / Real.log (p : ℝ)) : ℂ) *
      (∫ x in S, star (padicStdAddChar p (x * ξ)) ∂padicAddHaar p)
    let G := S.indicator (fun x ↦ (↑‖x‖ : ℂ)⁻¹)
    Integrable F (padicAddHaar p) ∧ Integrable G (padicAddHaar p) ∧
      (∫ ξ, F ξ ∂padicAddHaar p) = -((↑(1 - (p : ℝ)⁻¹) : ℂ)⁻¹) *
        ∫ x, G x ∂padicAddHaar p := by
  dsimp only
  let S := closedBall a (((p : ℝ)⁻¹) ^ n)
  have hS : MeasurableSet S := isClosed_closedBall.measurableSet
  have hK : IsCompact S := isCompact_closedBall _ _
  have hnorm {x : ℚ_[p]} (hx : x ∈ S) : ‖x‖ = ‖a‖ := by
    have hlt : dist x a < dist a 0 := (mem_closedBall.mp hx).trans_lt (by simpa using ha)
    have h := IsUltrametricDist.dist_eq_max_of_dist_ne_dist x a 0 hlt.ne
    rw [max_eq_right hlt.le] at h
    simpa only [dist_zero_right] using h
  have he : S.indicator (fun x ↦ (↑‖x‖ : ℂ)⁻¹) = S.indicator (fun _ ↦ (↑‖a‖ : ℂ)⁻¹) :=
    indicator_congr (fun _ hx ↦ by rw [hnorm hx])
  have hf := padicTranslatedBall_log_fourier p n a ha
  rw [← padicClosedBall_eq p n a] at hf
  refine ⟨hf.1, ?_, ?_⟩
  · rw [he]
    exact (integrable_indicator_iff hS).mpr (integrableOn_const (hs := hK.measure_lt_top.ne))
  · rw [hf.2, he, integral_indicator hS, setIntegral_const, Measure.real,
      padicClosedBall_measure, ENNReal.toReal_inv, ENNReal.toReal_pow, ENNReal.toReal_natCast,
      Complex.real_smul, Complex.ofReal_inv, Complex.ofReal_pow, Complex.ofReal_natCast,
      Complex.ofReal_mul, mul_inv_rev]
    ring

/-- The Fourier kernel in the spatial variable is integrable on each closed ball. -/
public theorem integrableOn_padicClosedBall_char (r : ℝ) (a ξ : ℚ_[p]) :
    IntegrableOn (fun x : ℚ_[p] ↦ star (padicStdAddChar p (x * ξ)))
      (closedBall a r) (padicAddHaar p) := by
  have h : Continuous (fun x : ℚ_[p] ↦ star (padicStdAddChar p (x * ξ))) :=
    ((continuous_padicStdAddChar p).comp (continuous_id.mul continuous_const)).star
  exact h.continuousOn.integrableOn_compact (isCompact_closedBall _ _)

end Masullo
