module

public import Examples.Chi8Completion
public import Examples.Chi8Origin
public import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# The entire completion for the quadratic character modulo eight

The conductor factor converts mathlib's completed L-function to the classical
normalization. This defines the completion also at the poles of the Gamma factor.
-/

open DirichletCharacter Filter
open scoped Topology

namespace Chi8Entire

local notation "χ" => Chi8Origin.χ

/-- The entire completion in the conductor-eight normalization. -/
@[expose] public noncomputable def Λ (s : ℂ) :=
  (8 : ℂ) ^ (s / 2) * DirichletCharacter.completedLFunction Chi8Origin.χ s

private theorem eight_cpow_ne_zero (z : ℂ) : (8 : ℂ) ^ z ≠ 0 :=
  Complex.cpow_ne_zero_iff.mpr (Or.inl (by norm_num))

private theorem differentiable_eight_cpow : Differentiable ℂ (fun s : ℂ ↦ (8 : ℂ) ^ (s / 2)) :=
  (differentiable_id.div_const 2).const_cpow (Or.inl (by norm_num))

private theorem completion_factor (s : ℂ) :
    ((8 : ℂ) / Real.pi) ^ (s / 2) * Complex.Gamma (s / 2) =
      (8 : ℂ) ^ (s / 2) * Complex.Gammaℝ s := by
  rw [show (8 : ℂ) = ((8 : ℝ) : ℂ) by norm_num,
    Complex.div_cpow_ofReal_nonneg (by norm_num) Real.pi_pos.le,
    div_eq_mul_inv, ← Complex.cpow_neg, ← neg_div, mul_assoc, ← Complex.Gammaℝ_def]

/-- The classical product agrees with `Λ` wherever the Gamma factor is nonzero. -/
public theorem eq_completion (s : ℂ) (hΓ : Complex.Gammaℝ s ≠ 0) :
    Λ s = Chi8Completion.completion (LFunction χ) s := by
  rw [Λ, Chi8Completion.completion, completion_factor, mul_assoc,
    LFunction_eq_completed_div_gammaFactor χ s (Or.inr (by decide)),
    Chi8Origin.χ_even.gammaFactor_def, ← mul_div_assoc, mul_div_cancel_left₀ _ hΓ]

private theorem eq_near_of_re_pos {s : ℂ} (hs : 0 < s.re) :
    Λ =ᶠ[𝓝 s] Chi8Completion.completion (LFunction χ) := by
  have h : ∀ᶠ z : ℂ in 𝓝 s, 0 < z.re :=
    Complex.continuous_re.continuousAt.tendsto.eventually (lt_mem_nhds hs)
  exact h.mono fun z hz ↦ eq_completion z (Complex.Gammaℝ_ne_zero_of_re_pos hz)

/-- Near `1`, the classical product represents `Λ`. -/
public theorem eq_near_one :
    Λ =ᶠ[𝓝 (1 : ℂ)] Chi8Completion.completion (LFunction χ) :=
  eq_near_of_re_pos (by norm_num)

/-- The completed value at the origin is nonzero. -/
public theorem zero_ne_zero : Λ 0 ≠ 0 :=
  mul_ne_zero (eight_cpow_ne_zero _) Chi8Origin.completedLFunction_zero_ne_zero

private theorem ne_zero_of_one_le_re {s : ℂ} (hs : 1 ≤ s.re) : Λ s ≠ 0 :=
  mul_ne_zero (eight_cpow_ne_zero _)
    (completedLFunction_ne_zero_of_one_le_re χ (Or.inl Chi8Origin.χ_ne_one) hs)

/-- The completed value at `1` is nonzero. -/
public theorem one_ne_zero : Λ 1 ≠ 0 := ne_zero_of_one_le_re (by simp)

/-- The conductor-normalized completed L-function is entire. -/
public theorem differentiable : Differentiable ℂ Λ :=
  differentiable_eight_cpow.mul (differentiable_completedLFunction Chi8Origin.χ_ne_one)

/-- Completion preserves the analytic order at each point in the open right half-plane. -/
public theorem analyticOrderAt_eq {s : ℂ} (hs : 0 < s.re) :
    analyticOrderAt Λ s = analyticOrderAt (LFunction χ) s := by
  have hΓ := Complex.Gammaℝ_ne_zero_of_re_pos hs
  have haΓ : AnalyticAt ℂ Complex.Gammaℝ s := by
    have h := (Complex.differentiable_Gammaℝ_inv.analyticAt s).inv (inv_ne_zero hΓ)
    change AnalyticAt ℂ (fun z ↦ ((Complex.Gammaℝ z)⁻¹)⁻¹) s at h
    simpa only [inv_inv] using h
  let P : ℂ → ℂ := (fun z : ℂ ↦ (8 : ℂ) ^ (z / 2)) * Complex.Gammaℝ
  have haP : AnalyticAt ℂ P s := (differentiable_eight_cpow.analyticAt s).mul haΓ
  have hnP : P s ≠ 0 := mul_ne_zero (eight_cpow_ne_zero _) hΓ
  have hEq : Λ =ᶠ[𝓝 s] P * LFunction χ := (eq_near_of_re_pos hs).mono fun z hz ↦ by
    simpa only [P, Pi.mul_apply, Chi8Completion.completion, completion_factor] using hz
  rw [analyticOrderAt_congr hEq,
    analyticOrderAt_mul haP ((differentiable_LFunction Chi8Origin.χ_ne_one).analyticAt s),
    haP.analyticOrderAt_eq_zero.mpr hnP, zero_add]

private theorem ne_zero_of_re_nonpos {s : ℂ} (hs : s.re ≤ 0) : Λ s ≠ 0 := by
  have hprim : IsPrimitive χ := Chi8Origin.conductor_eq
  have hre : 1 ≤ (1 - s).re := by simpa using hs
  have h : completedLFunction χ⁻¹ (1 - s) ≠ 0 :=
    completedLFunction_ne_zero_of_one_le_re χ⁻¹
      (Or.inl (inv_ne_one.mpr Chi8Origin.χ_ne_one)) hre
  have hfe := hprim.completedLFunction_one_sub (1 - s)
  rw [sub_sub_cancel] at hfe
  rw [Λ, hfe]
  exact mul_ne_zero (eight_cpow_ne_zero _)
    (mul_ne_zero (mul_ne_zero (eight_cpow_ne_zero _) (rootNumber_ne_zero hprim)) h)

/-- The zeros of `Λ` are exactly the zeros of `LFunction χ` in the open critical strip. -/
public theorem zero_iff (s : ℂ) :
    Λ s = 0 ↔ 0 < s.re ∧ s.re < 1 ∧ LFunction χ s = 0 := by
  have hL (hs : 0 < s.re) : Λ s = 0 ↔ LFunction χ s = 0 := by
    have hΓ := Complex.Gammaℝ_ne_zero_of_re_pos hs
    rw [eq_completion s hΓ, Chi8Completion.completion, completion_factor]
    exact mul_eq_zero_iff_left (mul_ne_zero (eight_cpow_ne_zero _) hΓ)
  constructor
  · intro hz
    have hpos : 0 < s.re := lt_of_not_ge fun hs ↦ ne_zero_of_re_nonpos hs hz
    have hlt : s.re < 1 := lt_of_not_ge fun hs ↦ ne_zero_of_one_le_re hs hz
    exact ⟨hpos, hlt, (hL hpos).mp hz⟩
  · exact fun ⟨hpos, _, hz⟩ ↦ (hL hpos).mpr hz

end Chi8Entire
