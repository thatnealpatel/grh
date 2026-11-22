module

public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.Taylor

/-! # Flat real Schwartz tests in the negative log tail -/

open Set
open scoped SchwartzMap

namespace Masullo

private theorem exists_ray_pow_bound_of_vanishing_jets {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {f : ℝ → E} (n : ℕ)
    (hf : ContDiff ℝ (n + 1) f) (hflat : ∀ j ≤ n, iteratedDeriv j f 0 = 0) :
    ∃ C : ℝ, ∀ x ∈ Icc (0 : ℝ) 1, ‖f x‖ ≤ C * x ^ (n + 1) := by
  obtain ⟨C, hC⟩ := exists_taylor_mean_remainder_bound (a := 0) (b := 1) hf.contDiffOn
  refine ⟨C, fun x hx ↦ ?_⟩
  have hTaylor : taylorWithinEval f n (Icc 0 1) 0 x = 0 := by
    rw [taylor_within_apply]
    apply Finset.sum_eq_zero
    intro j hj
    have hjn : j ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
    have hjdiff : ContDiff ℝ j f := hf.of_le (by exact_mod_cast hjn.trans n.le_succ)
    rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc zero_lt_one)
      hjdiff.contDiffAt (left_mem_Icc.mpr zero_le_one), hflat j hjn, smul_zero]
  simpa only [hTaylor, sub_zero] using hC x hx

/-- Vanishing jets through order `n` give a common order-`n + 1` bound on both rays near zero. -/
public theorem exists_twoRay_pow_bound_of_vanishing_jets {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {f : ℝ → E} (n : ℕ)
    (hf : ContDiff ℝ (n + 1) f) (hflat : ∀ j ≤ n, iteratedDeriv j f 0 = 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ Icc (0 : ℝ) 1,
      ‖f x‖ ≤ C * x ^ (n + 1) ∧ ‖f (-x)‖ ≤ C * x ^ (n + 1) := by
  obtain ⟨Cp, hp⟩ := exists_ray_pow_bound_of_vanishing_jets n hf hflat
  have hneg : ∀ j ≤ n, iteratedDeriv j (fun x ↦ f (-x)) 0 = 0 := by
    intro j hj
    rw [iteratedDeriv_comp_neg, neg_zero, hflat j hj, smul_zero]
  have hsmoothNeg : ContDiff ℝ (n + 1) (fun x : ℝ ↦ -x) :=
    (contDiff_id : ContDiff ℝ (n + 1) (id : ℝ → ℝ)).neg
  obtain ⟨Cm, hm⟩ := exists_ray_pow_bound_of_vanishing_jets n (hf.comp hsmoothNeg) hneg
  refine ⟨max 0 (max Cp Cm), le_max_left .., fun x hx ↦ ⟨?_, ?_⟩⟩
  · exact (hp x hx).trans (mul_le_mul_of_nonneg_right
      ((le_max_left Cp Cm).trans (le_max_right _ _)) (pow_nonneg hx.1 _))
  · exact (hm x hx).trans (mul_le_mul_of_nonneg_right
      ((le_max_right Cp Cm).trans (le_max_right _ _)) (pow_nonneg hx.1 _))

/-- On both signed exponential rays a flat real Schwartz test decays at every positive
integer exponential rate as the log coordinate tends to minus infinity. -/
public theorem exists_realSchwartz_negLog_tail_bound (b : 𝓢(ℝ, ℂ))
    (hflat : ∀ j : ℕ, iteratedDeriv j (b : ℝ → ℂ) 0 = 0) (N : ℕ) (hN : 1 ≤ N) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, t ≤ 0 →
      ‖b (Real.exp t)‖ ≤ C * Real.exp ((N : ℝ) * t) ∧
        ‖b (-Real.exp t)‖ ≤ C * Real.exp ((N : ℝ) * t) := by
  cases N with
  | zero => omega
  | succ n =>
    obtain ⟨C, hC, h⟩ := exists_twoRay_pow_bound_of_vanishing_jets n (b.smooth _)
      (fun j _ ↦ hflat j)
    refine ⟨C, hC, fun t ht ↦ ?_⟩
    have hx : Real.exp t ∈ Icc (0 : ℝ) 1 := ⟨(Real.exp_pos t).le, Real.exp_le_one_iff.mpr ht⟩
    simpa only [Real.exp_nat_mul] using h (Real.exp t) hx

end Masullo
