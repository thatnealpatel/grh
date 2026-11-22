module

public import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.Ring

/-!
# Continuous unitary one-parameter characters

A project lemma for recognizing the characters used in Masullo's
(3.2.1.3)–(5), p. 123. The manuscript's Archimedean factor formulas
use parity or integer angular weight; they do not prove the common
one-parameter classification here.
-/

open Complex MeasureTheory Set

namespace Masullo

private theorem character_shortIntegral_ne_zero {h : ℝ → ℂ}
    (hcont : Continuous h) (hzero : h 0 = 1) :
    ∃ r : ℝ, (∫ u in (0 : ℝ)..r, h u) ≠ 0 := by
  have hopen : IsOpen {u : ℝ | 0 < (h u).re} :=
    isOpen_lt continuous_const (continuous_re.comp hcont)
  have hmem : (0 : ℝ) ∈ {u : ℝ | 0 < (h u).re} := by simp [hzero]
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hopen 0 hmem
  refine ⟨ε / 2, ?_⟩
  have hpos : 0 < ∫ u in (0 : ℝ)..(ε / 2), (h u).re := by
    refine intervalIntegral.integral_pos (half_pos hε)
      (continuous_re.comp hcont).continuousOn ?_ ⟨0, ⟨le_rfl, (half_pos hε).le⟩, hmem⟩
    intro u hu
    have hu' : u ∈ Metric.ball (0 : ℝ) ε := by
      rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_nonneg hu.1.le]
      exact hu.2.trans_lt (half_lt_self hε)
    exact (hball hu').le
  have hre : (∫ u in (0 : ℝ)..(ε / 2), (h u).re) =
      (∫ u in (0 : ℝ)..(ε / 2), h u).re :=
    intervalIntegral.intervalIntegral_re (hcont.intervalIntegrable _ _)
  rw [hre] at hpos
  intro heq
  simp [heq] at hpos

private theorem character_exp_hasDerivAt (k : ℂ) (t : ℝ) :
    HasDerivAt (fun u : ℝ ↦ exp (k * (u : ℂ))) (exp (k * (t : ℂ)) * k) t := by
  simpa only [id_eq, ofReal_one, mul_one] using
    (((hasDerivAt_id t).ofReal_comp).const_mul k).cexp

/-- Every continuous unitary character of the additive real group is
`exp (i * τ * t)` for a unique real `τ`. Integrating over a short interval
first supplies differentiability without choosing a branch of argument. -/
public theorem existsUnique_unitary_oneParameterCharacter (h : ℝ → ℂ)
    (hcont : Continuous h) (hzero : h 0 = 1)
    (hadd : ∀ x y : ℝ, h (x + y) = h x * h y) (hnorm : ∀ x : ℝ, ‖h x‖ = 1) :
    ∃! τ : ℝ, ∀ t : ℝ, h t = exp (((τ * t : ℝ) : ℂ) * I) := by
  obtain ⟨r, hr⟩ := character_shortIntegral_ne_zero hcont hzero
  let J : ℂ := ∫ u in (0 : ℝ)..r, h u
  let F (t : ℝ) : ℂ := ∫ u in (0 : ℝ)..t, h u
  have hFTC (t : ℝ) : HasDerivAt F (h t) t :=
    intervalIntegral.integral_hasDerivAt_right (hcont.intervalIntegrable _ _)
      hcont.aestronglyMeasurable.stronglyMeasurableAtFilter hcont.continuousAt
  have htranslate (t : ℝ) : h t = (F (t + r) - F t) / J := by
    apply (eq_div_iff hr).mpr
    calc
      h t * J = ∫ u in (0 : ℝ)..r, h (u + t) := by
        simp only [J, add_comm _ t, hadd, intervalIntegral.integral_const_mul]
      _ = ∫ u in t..(t + r), h u := by
        rw [intervalIntegral.integral_comp_add_right, zero_add, add_comm r t]
      _ = F (t + r) - F t := by
        have hsplit := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
          (hcont.intervalIntegrable 0 t) (hcont.intervalIntegrable t (t + r))
        apply eq_sub_iff_add_eq.mpr
        rw [add_comm]
        exact hsplit
  let k := (h r - 1) / J
  have hderiv (t : ℝ) : HasDerivAt h (k * h t) t := by
    have hshift : HasDerivAt (fun u : ℝ ↦ u + r) 1 t := (hasDerivAt_id t).add_const r
    have hFshift : HasDerivAt (fun u : ℝ ↦ F (u + r)) (h (t + r)) t := by
      change HasDerivAt (F ∘ fun u : ℝ ↦ u + r) (h (t + r)) t
      simpa only [one_smul] using (hFTC (t + r)).scomp t hshift
    convert (hFshift.sub (hFTC t)).div_const J using 1
    · exact funext htranslate
    · rw [hadd]
      dsimp [k]
      ring
  have hcancel (t : ℝ) : HasDerivAt (fun u : ℝ ↦ exp (-k * (u : ℂ)) * h u) 0 t := by
    convert (character_exp_hasDerivAt (-k) t).mul (hderiv t) using 1
    ring
  have hsol (t : ℝ) : h t = exp (k * (t : ℂ)) := by
    have hconst : exp (-k * (t : ℂ)) * h t = 1 := by
      simpa [hzero] using is_const_of_deriv_eq_zero (fun u ↦ (hcancel u).differentiableAt)
        (fun u ↦ (hcancel u).deriv) t 0
    calc
      h t = exp (k * (t : ℂ)) * (exp (-k * (t : ℂ)) * h t) := by
        rw [← mul_assoc, ← exp_add, neg_mul, add_neg_cancel, exp_zero, one_mul]
      _ = exp (k * (t : ℂ)) := by rw [hconst, mul_one]
  have hk : k.re = 0 := by
    apply Real.exp_injective
    have h := hnorm 1
    rw [hsol, ofReal_one, mul_one, norm_exp] at h
    simpa using h
  have him : k = (k.im : ℂ) * I := by
    apply Complex.ext <;> simp [hk, mul_re, mul_im]
  refine ⟨k.im, fun t ↦ ?_, fun τ hτ ↦ ?_⟩
  · rw [hsol, ofReal_mul]
    congr 1
    calc
      k * (t : ℂ) = ((k.im : ℂ) * I) * (t : ℂ) := congrArg (· * (t : ℂ)) him
      _ = (k.im : ℂ) * (t : ℂ) * I := by ring
  · have hτfun : h = fun t : ℝ ↦ exp (((τ : ℂ) * I) * (t : ℂ)) := by
      funext t
      rw [hτ, ofReal_mul]
      ring_nf
    have hτderiv : HasDerivAt h ((τ : ℂ) * I) 0 := by
      rw [hτfun]
      simpa using character_exp_hasDerivAt ((τ : ℂ) * I) 0
    have hcoef : (τ : ℂ) * I = k :=
      hτderiv.unique (by simpa [hzero] using hderiv 0)
    simpa [mul_im] using congrArg Complex.im hcoef

end Masullo
