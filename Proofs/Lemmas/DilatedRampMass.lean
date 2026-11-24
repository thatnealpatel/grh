module

public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Dilated ramp tail mass

Source: `45f0afd:.godel/bob/dilated-harmonic-ceiling.md:28–36`.
This is the normalized ramp mass used in the bounds for large harmonics and
exterior dilation parameters. We evaluate the tail and prove its global maximum
in the dilation parameter; we do not prove the numerical ceiling or prime realization.

Owning check session: `01a20c03-fe6f-73b3-a1bb-bf0df5b6ef1a`.
-/

open Filter MeasureTheory Set
open scoped Topology

namespace Masullo.DilatedRampMass

/-- The normalized ramp integrated against Lebesgue measure on `[v, ∞)`. -/
@[expose] public noncomputable def mass (v l : ℝ) : ℝ :=
  ∫ z in Ici v, Real.exp (-l / 2) * max (z + l) 0 * Real.exp (-z)

private theorem affine_tail_integral (l b : ℝ) (hb : -l ≤ b) :
    (∫ z in Ici b, (z + l) * Real.exp (-z)) = Real.exp (-b) * (1 + l + b) := by
  let F : ℝ → ℝ := fun z ↦ -(z + (l + 1)) * Real.exp (-z)
  have hderiv (z : ℝ) : HasDerivAt F ((z + l) * Real.exp (-z)) z := by
    have hd : HasDerivAt F (-1 * Real.exp (-z) + (-(z + (l + 1))) *
        (Real.exp (-z) * -1)) z :=
      (((hasDerivAt_id z).add_const (l + 1)).neg).mul ((hasDerivAt_id z).neg.exp)
    convert hd using 1
    ring
  have hlinear : Tendsto (fun z : ℝ ↦ z * Real.exp (-z)) atTop (𝓝 0) := by
    simpa only [pow_one] using Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1
  have hlim : Tendsto F atTop (𝓝 0) := by
    have h : Tendsto (fun z : ℝ ↦ -(z * Real.exp (-z) + (l + 1) * Real.exp (-z)))
        atTop (𝓝 0) := by
      simpa only [mul_zero, add_zero, neg_zero] using
        (hlinear.add (Real.tendsto_exp_neg_atTop_nhds_zero.const_mul (l + 1))).neg
    exact h.congr fun z ↦ by dsimp [F]; ring
  have hnonneg (z : ℝ) (hz : z ∈ Ioi b) : 0 ≤ (z + l) * Real.exp (-z) :=
    mul_nonneg (by linarith [mem_Ioi.mp hz]) (Real.exp_pos _).le
  rw [integral_Ici_eq_integral_Ioi, integral_Ioi_of_hasDerivAt_of_nonneg
    (hderiv b).continuousAt.continuousWithinAt (fun z _ ↦ hderiv z) hnonneg hlim]
  dsimp [F]
  ring

/-- The ramp vanishes below `−l`, so the effective lower endpoint is `max v (−l)`. -/
public theorem mass_eq (v l : ℝ) :
    let b := max v (-l)
    mass v l = Real.exp (-l / 2 - b) * (1 + l + b) := by
  let f : ℝ → ℝ := fun z ↦ Real.exp (-l / 2) * ((z + l) * Real.exp (-z))
  have hcut (z : ℝ) : Real.exp (-l / 2) * max (z + l) 0 * Real.exp (-z) =
      (Ici (-l)).indicator f z := by
    by_cases hz : z ∈ Ici (-l)
    · rw [indicator_of_mem hz, max_eq_left (by linarith [mem_Ici.mp hz]), mul_assoc]
    · rw [indicator_of_notMem hz,
        max_eq_right (by have h : z < -l := lt_of_not_ge hz; linarith), mul_zero, zero_mul]
  unfold mass
  simp_rw [hcut]
  rw [setIntegral_indicator measurableSet_Ici, Ici_inter_Ici]
  change (∫ z in Ici (max v (-l)), Real.exp (-l / 2) * ((z + l) * Real.exp (-z))) = _
  rw [integral_const_mul, affine_tail_integral l _ (le_max_right v (-l)),
    ← mul_assoc, ← Real.exp_add, ← sub_eq_add_neg]

private theorem affine_tail_le_peak (v l : ℝ) :
    Real.exp (-l / 2 - v) * (1 + l + v) ≤ 2 * Real.exp (-(1 + v) / 2) := by
  calc
    _ = (2 * Real.exp (-l / 2 - v)) * ((l + v - 1) / 2 + 1) := by ring
    _ ≤ (2 * Real.exp (-l / 2 - v)) * Real.exp ((l + v - 1) / 2) :=
      mul_le_mul_of_nonneg_left (Real.add_one_le_exp _) (by positivity)
    _ = _ := by
      rw [mul_assoc, ← Real.exp_add,
        show -l / 2 - v + (l + v - 1) / 2 = -(1 + v) / 2 by ring]

/-- The tail mass never exceeds its value at `l = 1 − v`. -/
public theorem mass_le_peak (v l : ℝ) : mass v l ≤ 2 * Real.exp (-(1 + v) / 2) := by
  rw [mass_eq]
  rcases le_total (-l) v with h | h
  · rw [max_eq_left h]
    exact affine_tail_le_peak v l
  · rw [max_eq_right h, show -l / 2 - -l = l / 2 by ring,
      show 1 + l + -l = 1 by ring, mul_one]
    calc
      _ ≤ Real.exp (-(-v) / 2 - v) := Real.exp_le_exp.mpr (by linarith)
      _ = Real.exp (-(-v) / 2 - v) * (1 + -v + v) := by
        rw [show 1 + -v + v = 1 by ring, mul_one]
      _ ≤ _ := affine_tail_le_peak v (-v)

/-- The global bound is attained at `l = 1 − v`. -/
public theorem mass_at_peak (v : ℝ) : mass v (1 - v) = 2 * Real.exp (-(1 + v) / 2) := by
  rw [mass_eq]
  rw [max_eq_left (show -(1 - v) ≤ v by linarith),
    show -(1 - v) / 2 - v = -(1 + v) / 2 by ring,
    show 1 + (1 - v) + v = 2 by ring, mul_comm]

end Masullo.DilatedRampMass
