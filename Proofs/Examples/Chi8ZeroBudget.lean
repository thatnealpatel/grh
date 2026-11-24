module

public import Examples.Chi8Endpoint
public import Examples.Chi8Entire
public import Examples.Chi8ZeroKernel
public import Examples.Chi8ZeroSummability
public import Mathlib.Analysis.Complex.LocallyUniformLimit
import Theorems.DirichletContourReflection

/-! # The reflected endpoint budget for the even character modulo eight

Mathlib's functional equation has a conductor term. Multiplying its entire
completion by `8 ^ (s / 2)` cancels this term in the reflected logarithmic
derivative. At zero one must use this entire continuation, not the pointwise
product of the Gamma and L-functions.
-/

open DirichletCharacter Complex Filter
open scoped Topology

namespace Chi8ZeroBudget

local notation "χ" => Chi8Origin.χ
local notation "F" => completedLFunction χ
local notation "E" => Chi8Entire.Λ
local notation "raw" => Chi8Completion.completion (LFunction χ)

private theorem self_dual : χ⁻¹ = χ :=
  (ZMod.isQuadratic_χ₈.comp (Int.castRingHom ℂ)).inv

private theorem logDeriv_entire {s : ℂ} (hs : F s ≠ 0) :
    logDeriv E s = (Real.log 8 : ℂ) / 2 + logDeriv F s := by
  let P : ℂ → ℂ := fun z ↦ (8 : ℂ) ^ (z / 2)
  have h8 : (8 : ℂ) ≠ 0 := by norm_num
  have hP : P s ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl h8)
  have hd := ((hasDerivAt_id s).div_const 2).const_cpow (c := (8 : ℂ)) (Or.inl h8)
  change logDeriv (P * F) s = _
  rw [logDeriv_mul s hP hs hd.differentiableAt (differentiable_completedLFunction Chi8Origin.χ_ne_one s)]
  congr 1
  rw [logDeriv_apply, show deriv P s = _ from hd.deriv]
  change P s * Complex.log 8 * (1 / 2) / P s = _
  rw [← Complex.ofNat_log (n := 8)]
  field_simp

/-- Reflection in the classical normalization has no additive conductor term. -/
public theorem reflected : logDeriv E 0 = -logDeriv E 1 := by
  have h1 : F 1 ≠ 0 := completedLFunction_ne_zero_of_one_le_re χ (Or.inl Chi8Origin.χ_ne_one) (by simp)
  have hp : IsPrimitive χ := Chi8Origin.conductor_eq
  have hr := Masullo.completedDirichlet_logDeriv_reflection hp (by decide) h1
  rw [self_dual, sub_self] at hr
  rw [logDeriv_entire Chi8Origin.completedLFunction_zero_ne_zero, logDeriv_entire h1, hr]
  push_cast
  ring

/-- The budget in the landed normalization, evaluated only at the regular point `1`. -/
@[expose] public noncomputable def C : ℝ := 2 * (deriv raw 1 / raw 1).re

/-- The endpoint difference for the entire continuation equals the landed budget. -/
public theorem endpoint_difference : (logDeriv E 1 - logDeriv E 0).re = C := by
  rw [reflected, sub_neg_eq_add, add_re, ← two_mul, logDeriv_apply,
    Chi8Entire.eq_near_one.deriv_eq, Chi8Entire.eq_near_one.eq_of_nhds]
  rfl

/-- The reflected difference inherits the strict bound at one. -/
public theorem endpoint_difference_lt : (logDeriv E 1 - logDeriv E 0).re < 3 / 2 := by
  rw [endpoint_difference]
  exact Chi8Budget.completed_budget

open Chi8ZeroKernel

/-- Absolute convergence of the nonnegative weights does not require the critical line. -/
public theorem summable_weight : Summable weight :=
  Chi8Origin.summable_analyticOrderNatAt_div_norm_sq

/-- Subtracting two endpoint expansions with the same affine constant identifies
and bounds the actual sum. The two expansions are analytic hypotheses. -/
public theorem budget_of_endpoint_expansions {a c : ℂ}
    (hline : ∀ ρ : Chi8ZeroKernel.Zero, (ρ : ℂ).re = 1 / 2)
    (h₁ : HasSum (regularizedTerm a 1) (logDeriv E 1 - c))
    (h₀ : HasSum (regularizedTerm a 0) (logDeriv E 0 - c)) :
    HasSum weight C ∧ ∑' ρ, weight ρ < 3 / 2 := by
  have h := hasSum_weight hline h₁ h₀
  exact ⟨endpoint_difference ▸ h, h.tsum_eq.trans_lt endpoint_difference_lt⟩

/-- A finite zero product with its affine exponential prefactor. This includes
finite genus-one products: the compensating exponentials are affine in `s`. -/
@[expose] public noncomputable def approximant (a b : ℂ) (S : Finset Chi8ZeroKernel.Zero) (s : ℂ) :=
  exp (a + b * s) * ∏ ρ ∈ S, (s - (ρ : ℂ)) ^ multiplicity ρ

private theorem approximant_diff (a b : ℂ) (S : Finset Chi8ZeroKernel.Zero) :
    Differentiable ℂ (approximant a b S) := by unfold approximant; fun_prop

private theorem approximant_logDeriv (a b s : ℂ) (S : Finset Chi8ZeroKernel.Zero)
    (hs : ∀ ρ ∈ S, s ≠ (ρ : ℂ)) : logDeriv (approximant a b S) s =
      b + ∑ ρ ∈ S, (multiplicity ρ : ℂ) * (1 / (s - (ρ : ℂ))) := by
  let P (ρ : Chi8ZeroKernel.Zero) (z : ℂ) := (z - (ρ : ℂ)) ^ multiplicity ρ
  have hn (ρ) (h : ρ ∈ S) : P ρ s ≠ 0 := pow_ne_zero _ (sub_ne_zero.mpr (hs ρ h))
  have hd (ρ) : Differentiable ℂ (P ρ) := by unfold P; fun_prop
  have he := ((hasDerivAt_id s).const_mul b |>.const_add a).cexp
  unfold approximant
  change logDeriv (fun z ↦ exp (a + b * z) * ∏ ρ ∈ S, P ρ z) s = _
  simp_rw [← Finset.prod_apply]
  change logDeriv ((fun z ↦ exp (a + b * z)) * ∏ ρ ∈ S, P ρ) s = _
  rw [logDeriv_mul (f := fun z : ℂ ↦ exp (a+b * z)) (g := ∏ ρ ∈ S, P ρ) s (exp_ne_zero _)
    (by simpa using Finset.prod_ne_zero_iff.mpr hn)
    he.differentiableAt (DifferentiableAt.finsetProd fun ρ _ ↦ hd ρ s), logDeriv_prod hn
    (fun ρ _ ↦ hd ρ s)]
  congr 1
  · rw [logDeriv_apply, show deriv (fun z : ℂ ↦ exp (a + b * z)) s = exp (a + b * s) * (b * 1) from he.deriv]
    field_simp
  · apply Finset.sum_congr rfl
    intro ρ _
    change logDeriv (fun z : ℂ ↦ (z - (ρ : ℂ)) ^ multiplicity ρ) s = _
    rw [logDeriv_fun_pow (f := fun z : ℂ ↦ z - (ρ : ℂ)) (by fun_prop), logDeriv_apply,
      show deriv (fun z : ℂ ↦ z - (ρ : ℂ)) s = 1 from ((hasDerivAt_id s).sub_const (ρ : ℂ)).deriv]

/-- Locally uniform approximation by finite zero products near both endpoints
suffices. No convergence of the exponential prefactors is required. The
approximation hypothesis is the global analytic input, not proved here. -/
public theorem hasSum_of_products {a b : Finset Chi8ZeroKernel.Zero → ℂ} {U : Set ℂ}
    (hU : IsOpen U) (h₀ : 0 ∈ U) (h₁ : 1 ∈ U)
    (hprod : TendstoLocallyUniformlyOn (fun S ↦ approximant (a S) (b S) S) E atTop U)
    (hline : ∀ ρ : Chi8ZeroKernel.Zero, (ρ : ℂ).re = 1 / 2) : HasSum weight C := by
  have hd := Eventually.of_forall (f := atTop) fun S ↦
    (approximant_diff (a S) (b S) S).differentiableOn (s := U)
  have hl := (Complex.logDeriv_tendsto hU h₁ hprod hd Chi8Entire.one_ne_zero).sub
    (Complex.logDeriv_tendsto hU h₀ hprod hd Chi8Entire.zero_ne_zero)
  rw [← endpoint_difference]
  refine (Complex.continuous_re.continuousAt.tendsto.comp hl).congr fun S ↦ ?_
  change (logDeriv (approximant (a S) (b S) S) 1 - logDeriv (approximant (a S) (b S) S) 0).re = _
  have h1 (ρ : Chi8ZeroKernel.Zero) : (1 : ℂ) ≠ ρ := fun h ↦
    ρ.property.2.1.ne (congrArg Complex.re h).symm
  have h0 (ρ : Chi8ZeroKernel.Zero) : (0 : ℂ) ≠ ρ := fun h ↦
    ρ.property.1.ne (congrArg Complex.re h)
  rw [approximant_logDeriv _ _ _ _ (fun ρ _ ↦ h1 ρ),
    approximant_logDeriv _ _ _ _ (fun ρ _ ↦ h0 ρ), add_sub_add_left_eq_sub,
    ← Finset.sum_sub_distrib, Complex.re_sum]
  refine Finset.sum_congr rfl fun ρ _ ↦ ?_
  have h := congrArg Complex.re (regularizedTerm_one_sub_zero 0 ρ (hline ρ))
  simpa only [regularizedTerm, mul_add, add_sub_add_right_eq_sub, Complex.ofReal_re] using h

end Chi8ZeroBudget
