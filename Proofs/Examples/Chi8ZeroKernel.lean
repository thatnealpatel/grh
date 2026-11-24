module

public import Examples.Chi8Origin
public import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Subtracting the two endpoint zero kernels for χ₈

The index type consists of actual zeros in the open critical strip, each weighted by its
analytic multiplicity. The subtraction is conditional on the critical-line hypothesis and
on convergence of the two endpoint expansions. No zero expansion is proved here.
-/

open DirichletCharacter Filter
open scoped ComplexConjugate Topology

namespace Chi8ZeroKernel

local notation "L" => LFunction Chi8Origin.χ

/-- An actual zero of the χ₈ L-function in the open critical strip. -/
public abbrev Zero := {ρ : ℂ // 0 < ρ.re ∧ ρ.re < 1 ∧ L ρ = 0}

/-- The order of vanishing of the χ₈ L-function at a strip zero. -/
@[expose] public noncomputable def multiplicity (ρ : Zero) : ℕ :=
  analyticOrderNatAt L (ρ : ℂ)

private theorem nonprincipal : Chi8Origin.χ ≠ 1 := by
  intro h
  have hc := Chi8Origin.conductor_eq
  rw [h, conductor_one] at hc
  exact (by decide : (1 : ℕ) ≠ 8) hc

/-- Each strip zero has positive multiplicity: infinite order is ruled out by the identity
principle and nonvanishing at `1`. -/
public theorem multiplicity_pos (ρ : Zero) : 0 < multiplicity ρ := by
  have ha (z : ℂ) : AnalyticAt ℂ L z := (differentiable_LFunction nonprincipal).analyticAt z
  have hfinite : analyticOrderAt L (ρ : ℂ) ≠ ⊤ := by
    intro htop
    have hzero : L =ᶠ[𝓝 (ρ : ℂ)] 0 := analyticOrderAt_eq_top.mp htop
    have hAll : AnalyticOnNhd ℂ L Set.univ := fun z _ ↦ ha z
    have hEq := hAll.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      isPreconnected_univ (Set.mem_univ (ρ : ℂ)) hzero (Set.mem_univ (1 : ℂ))
    exact LFunction_apply_one_ne_zero nonprincipal hEq
  exact ENat.toNat_pos (fun h ↦ (ha ρ).analyticOrderAt_eq_zero.mp h ρ.property.2.2) hfinite

/-- A genus-one zero term with reference point `a`. At `a = 0` the compensation is
`1 / ρ`; it cancels in the difference for every `a`. -/
@[expose] public noncomputable def regularizedTerm (a s : ℂ) (ρ : Zero) : ℂ :=
  (multiplicity ρ : ℂ) * (1 / (s - (ρ : ℂ)) + 1 / ((ρ : ℂ) - a))

/-- The real norm-square weight of a strip zero, counted with multiplicity. -/
@[expose] public noncomputable def weight (ρ : Zero) : ℝ :=
  (multiplicity ρ : ℝ) / ‖(ρ : ℂ)‖ ^ 2

/-- On the critical line, subtracting the regularized term at `0` from the term at `1`
gives the real weight, viewed in `ℂ`. This is a pointwise identity, independent of convergence. -/
public theorem regularizedTerm_one_sub_zero (a : ℂ) (ρ : Zero) (hline : (ρ : ℂ).re = 1 / 2) :
    regularizedTerm a 1 ρ - regularizedTerm a 0 ρ = (weight ρ : ℂ) := by
  have hρ : (ρ : ℂ) ≠ 0 := fun h ↦ (ne_of_gt ρ.property.1) (congrArg Complex.re h)
  have h1 : 1 - (ρ : ℂ) ≠ 0 := fun h ↦
    (ne_of_lt ρ.property.2.1) (congrArg Complex.re (sub_eq_zero.mp h)).symm
  have hconj : 1 - (ρ : ℂ) = conj (ρ : ℂ) := by
    apply Complex.ext
    · norm_num [Complex.sub_re, hline]
    · simp [Complex.sub_im]
  calc
    regularizedTerm a 1 ρ - regularizedTerm a 0 ρ =
        (multiplicity ρ : ℂ) * (1 / ((ρ : ℂ) * (1 - (ρ : ℂ)))) := by
      rw [regularizedTerm, regularizedTerm, ← mul_sub, add_sub_add_right_eq_sub, zero_sub]
      congr 1
      field_simp [hρ, h1]
      ring
    _ = (weight ρ : ℂ) := by
      rw [hconj, Complex.mul_conj, mul_one_div, weight, Complex.sq_norm,
        Complex.ofReal_div, Complex.ofReal_natCast]

/-- For a common finite set, subtract first and then take real parts. Only zeros in that
set need to lie on the critical line. -/
public theorem sum_weight_eq_re_sub (a : ℂ) (S : Finset Zero)
    (hline : ∀ ρ ∈ S, (ρ : ℂ).re = 1 / 2) :
    ∑ ρ ∈ S, weight ρ =
      ((∑ ρ ∈ S, regularizedTerm a 1 ρ) - ∑ ρ ∈ S, regularizedTerm a 0 ρ).re := by
  rw [← Finset.sum_sub_distrib, Complex.re_sum]
  exact Finset.sum_congr rfl fun ρ hρ ↦ by
    rw [regularizedTerm_one_sub_zero a ρ (hline ρ hρ), Complex.ofReal_re]

/-- Paired finite sums along a common filter have the indicated real limit if both complex
endpoint sums converge with the same additive constant `c`. No unordered summability is
needed, and the family of finite sets need not be monotone. -/
public theorem tendsto_weight {ι : Type*} {F : Filter ι} {S : ι → Finset Zero}
    {a A₁ A₀ c : ℂ} (hline : ∀ ρ : Zero, (ρ : ℂ).re = 1 / 2)
    (h₁ : Tendsto (fun i ↦ ∑ ρ ∈ S i, regularizedTerm a 1 ρ) F (𝓝 (A₁ - c)))
    (h₀ : Tendsto (fun i ↦ ∑ ρ ∈ S i, regularizedTerm a 0 ρ) F (𝓝 (A₀ - c))) :
    Tendsto (fun i ↦ ∑ ρ ∈ S i, weight ρ) F (𝓝 (A₁ - A₀).re) := by
  have h : Tendsto (fun i ↦ (∑ ρ ∈ S i, regularizedTerm a 1 ρ) -
      ∑ ρ ∈ S i, regularizedTerm a 0 ρ) F (𝓝 (A₁ - A₀)) := by
    simpa only [sub_sub_sub_cancel_right] using h₁.sub h₀
  exact (Complex.continuous_re.continuousAt.tendsto.comp h).congr fun i ↦
    (sum_weight_eq_re_sub a (S i) fun ρ _ ↦ hline ρ).symm

/-- If the two regularized endpoint sums exist as unordered sums, their shared additive
constant cancels, leaving the real sum of the norm-square weights. -/
public theorem hasSum_weight {a A₁ A₀ c : ℂ} (hline : ∀ ρ : Zero, (ρ : ℂ).re = 1 / 2)
    (h₁ : HasSum (regularizedTerm a 1) (A₁ - c))
    (h₀ : HasSum (regularizedTerm a 0) (A₀ - c)) : HasSum weight (A₁ - A₀).re :=
  tendsto_weight (F := atTop) (S := id) hline h₁ h₀

/-- The subtraction rule for the genus-one compensation `1 / ρ`. -/
public theorem hasSum_weight_at_origin {A₁ A₀ c : ℂ} (hline : ∀ ρ : Zero, (ρ : ℂ).re = 1 / 2)
    (h₁ : HasSum (fun ρ : Zero ↦ (multiplicity ρ : ℂ) *
      (1 / (1 - (ρ : ℂ)) + 1 / (ρ : ℂ))) (A₁ - c))
    (h₀ : HasSum (fun ρ : Zero ↦ (multiplicity ρ : ℂ) *
      (1 / (0 - (ρ : ℂ)) + 1 / (ρ : ℂ))) (A₀ - c)) : HasSum weight (A₁ - A₀).re := by
  apply hasSum_weight (a := 0) (A₁ := A₁) (A₀ := A₀) (c := c) hline
  · change HasSum (fun ρ ↦ regularizedTerm 0 1 ρ) (A₁ - c)
    simpa only [regularizedTerm, sub_zero] using h₁
  · change HasSum (fun ρ ↦ regularizedTerm 0 0 ρ) (A₀ - c)
    simpa only [regularizedTerm, sub_zero] using h₀

end Chi8ZeroKernel
