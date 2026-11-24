module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Tactic.Ring

open Filter MeasureTheory Set

namespace PrimeSquareRamp

/-- The integral average of a function converging at infinity tends to the same limit. -/
public theorem tendsto_integral_average {f : ℝ → ℝ} {c : ℝ}
    (hi : ∀ Y : ℝ, 1 ≤ Y → IntervalIntegrable f MeasureTheory.volume 1 Y)
    (hf : Filter.Tendsto f Filter.atTop (nhds c)) :
    Filter.Tendsto (fun Y : ℝ => (∫ t in (1 : ℝ)..Y, f t) / Y) Filter.atTop (nhds c) := by
  let g : ℝ → ℝ := fun t => f t - c
  have hgi (Y : ℝ) (hY : 1 ≤ Y) : IntervalIntegrable g volume 1 Y :=
    (hi Y hY).sub intervalIntegrable_const
  refine Metric.tendsto_nhds.mpr fun ε hε => ?_
  have hε₂ : 0 < ε / 2 := half_pos hε
  obtain ⟨B, hB⟩ := eventually_atTop.mp (Metric.tendsto_nhds.mp hf (ε / 2) hε₂)
  let A := max 1 B
  have hA : 1 ≤ A := le_max_left _ _
  -- The fixed initial integral and the lower endpoint correction both vanish after division.
  let K := (∫ t in (1 : ℝ)..A, g t) - c
  have hK : Tendsto (fun Y : ℝ => K / Y) atTop (nhds 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using
      (tendsto_inv_atTop_zero : Tendsto (fun Y : ℝ => Y⁻¹) atTop (nhds 0)).const_mul K
  filter_upwards [eventually_ge_atTop A, Metric.tendsto_nhds.mp hK (ε / 2) hε₂] with Y hY hsmall
  have hY₁ := hA.trans hY
  have hY₀ : 0 < Y := zero_lt_one.trans_le hY₁
  have htail : IntervalIntegrable g volume A Y := by
    apply (hgi Y hY₁).mono_set
    rw [uIcc_of_le hY, uIcc_of_le hY₁]
    exact Icc_subset_Icc_left hA
  have hbound : ‖∫ t in A..Y, g t‖ ≤ (ε / 2) * (Y - A) := by
    rw [← abs_of_nonneg (sub_nonneg.mpr hY)]
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro t ht
    rw [uIoc_of_le hY] at ht
    exact (hB t ((le_max_right 1 B).trans ht.1.le)).le
  have htail' : ‖(∫ t in A..Y, g t) / Y‖ ≤ ε / 2 := by
    rw [norm_div, Real.norm_of_nonneg hY₀.le, div_le_iff₀ hY₀]
    exact hbound.trans (mul_le_mul_of_nonneg_left
      (sub_le_self _ (zero_le_one.trans hA)) hε₂.le)
  have hsplit := intervalIntegral.integral_add_adjacent_intervals (hgi A hA) htail
  have hcenter : (∫ t in (1 : ℝ)..Y, g t) = (∫ t in (1 : ℝ)..Y, f t) - (Y - 1) * c := by
    rw [show g = fun t => f t - c from rfl,
      intervalIntegral.integral_sub (hi Y hY₁) intervalIntegrable_const,
      intervalIntegral.integral_const, smul_eq_mul]
  have hdecomp : (∫ t in (1 : ℝ)..Y, f t) / Y - c = K / Y + (∫ t in A..Y, g t) / Y := by
    -- Recombine the centered integrals before simplifying the constant part.
    unfold K
    rw [← add_div, sub_add_eq_add_sub, hsplit, hcenter]
    apply (eq_div_iff hY₀.ne').2
    rw [sub_mul, div_mul_cancel₀ _ hY₀.ne']
    ring
  rw [Real.dist_eq, hdecomp, ← Real.norm_eq_abs]
  rw [dist_zero_right] at hsmall
  calc
    _ ≤ ‖K / Y‖ + ‖(∫ t in A..Y, g t) / Y‖ := norm_add_le _ _
    _ < ε / 2 + ε / 2 := add_lt_add_of_lt_of_le hsmall htail'
    _ = ε := add_halves ε

end PrimeSquareRamp
