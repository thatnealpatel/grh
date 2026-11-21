module

public import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.MeanValue

/-! # Taylor estimate for weighted inverse dilation on real Schwartz profiles

The derivative and the remainder retain the inverse norm weight. This is
an ingredient of a rational-stage repair of Remark 2.2.4.6, p. 92.
-/

open scoped SchwartzMap
open Set

namespace Masullo

noncomputable section

local notation "B" => 𝓢(ℝ, ℂ)
local notation "p" => SchwartzMap.seminorm ℂ

/-- The weighted inverse dilation by the log parameter `s`. -/
public def schwartzWeightedInverseDilation (s : ℝ) : B →L[ℂ] B :=
  (Real.exp (-s) : ℂ) • SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (ContinuousLinearEquiv.unitsEquivAut ℝ (Units.mk0 _ (Real.exp_ne_zero (-s))))

@[simp] public theorem schwartzWeightedInverseDilation_apply (s : ℝ) (b : B) (x : ℝ) :
    schwartzWeightedInverseDilation s b x = Real.exp (-s) • b (Real.exp (-s) * x) := by
  simp [schwartzWeightedInverseDilation, ContinuousLinearEquiv.unitsEquivAut_apply,
    Complex.real_smul, mul_comm (Real.exp (-s)) x]

/-- The generator of the weighted inverse dilation is the negative Euler operator
minus the identity. -/
public def schwartzInverseDilationGenerator : B →L[ℂ] B :=
  -ContinuousLinearMap.id ℂ B -
    (SchwartzMap.smulLeftCLM ℂ Complex.ofReal).comp (SchwartzMap.derivCLM ℂ ℂ)

@[simp] public theorem schwartzInverseDilationGenerator_apply (b : B) (x : ℝ) :
    schwartzInverseDilationGenerator b x = -b x - x • deriv b x := by
  simp only [schwartzInverseDilationGenerator, ContinuousLinearMap.id_apply,
    ContinuousLinearMap.comp_apply, sub_apply, neg_apply,
    SchwartzMap.smulLeftCLM_apply_apply Complex.hasTemperateGrowth_ofReal,
    Complex.real_smul, smul_eq_mul, SchwartzMap.derivCLM_apply]

local notation "U" => schwartzWeightedInverseDilation
local notation "G" => schwartzInverseDilationGenerator

private theorem hasDerivAt_jet (b : B) (d : ℕ) (x : ℝ) :
    HasDerivAt (iteratedDeriv d b) (iteratedDeriv (d + 1) b x) x := by
  rw [iteratedDeriv_succ]
  exact (ContDiff.differentiable_iteratedDeriv' d (b.smooth (d + 1)) x).hasDerivAt

private theorem generator_jet (b : B) (d : ℕ) (x : ℝ) :
    iteratedDeriv d (G b) x = (-(d : ℝ) - 1) • iteratedDeriv d b x -
      x • iteratedDeriv (d + 1) b x := by
  induction d generalizing x with
  | zero => simp
  | succ d ih =>
    rw [iteratedDeriv_succ, show iteratedDeriv d (G b) = _ from funext ih]
    have h := ((hasDerivAt_jet b d x).const_smul (-(d : ℝ) - 1)).fun_sub
      ((hasDerivAt_id x).fun_smul (hasDerivAt_jet b (d + 1) x))
    rw [show deriv (fun x ↦ (-(d : ℝ) - 1) • iteratedDeriv d b x -
        x • iteratedDeriv (d + 1) b x) x = _ from h.deriv]
    push_cast
    simp only [id_eq]
    rw [add_comm (x • iteratedDeriv (d + 1 + 1) b x), sub_add_eq_sub_sub, ← sub_smul]
    congr 2
    ring

private theorem dilation_jet (s : ℝ) (b : B) (d : ℕ) (x : ℝ) :
    iteratedDeriv d (U s b) x = Real.exp ((-(d : ℝ) - 1) * s) •
      iteratedDeriv d b (Real.exp (-s) * x) := by
  rw [show (⇑(U s b)) = fun t ↦ Real.exp (-s) • b (Real.exp (-s) * t) from
    funext (schwartzWeightedInverseDilation_apply s b)]
  rw [iteratedDeriv_fun_const_smul_field]
  change Real.exp (-s) • iteratedDeriv d (fun t ↦ b (Real.exp (-s) * t)) x = _
  have h := congrFun (iteratedDeriv_comp_const_smul
    (f := (⇑b : ℝ → ℂ)) (b.smooth d) (Real.exp (-s))) x
  rw [h, smul_smul, ← Real.exp_nat_mul, ← Real.exp_add]
  rw [show -s + (d : ℝ) * -s = (-(d : ℝ) - 1) * s by ring]

private theorem hasDerivAt_dilation_jet (b : B) (d : ℕ) (x s : ℝ) :
    HasDerivAt (fun u : ℝ ↦ iteratedDeriv d (U u b) x) (iteratedDeriv d (U s (G b)) x) s := by
  simp only [dilation_jet]
  rw [generator_jet]
  let c : ℝ := -(d : ℝ) - 1
  have hc : HasDerivAt (fun u ↦ Real.exp (c * u)) (Real.exp (c * s) * c) s := by
    simpa only [mul_one, id_eq] using ((hasDerivAt_id s).const_mul c).exp
  have he : HasDerivAt (fun u ↦ Real.exp (-u)) (-Real.exp (-s)) s := by
    simpa only [mul_neg, mul_one] using (hasDerivAt_neg s).exp
  have h := hc.fun_smul ((hasDerivAt_jet b d (Real.exp (-s) * x)).scomp s (he.mul_const x))
  convert h using 1 <;> try rfl
  change Real.exp (c * s) • (c • iteratedDeriv d b (Real.exp (-s) * x) -
      (Real.exp (-s) * x) • iteratedDeriv (d + 1) b (Real.exp (-s) * x)) = _
  simp only [Function.comp_apply, ← smul_smul, neg_mul, neg_smul, smul_sub, smul_neg]
  abel

private theorem dilation_jet_bound (b : B) (a d : ℕ) (x s : ℝ) (hs : |s| ≤ 1) :
    |x| ^ a * ‖iteratedDeriv d (U s b) x‖ ≤ Real.exp (|(a : ℝ) - d - 1|) * p a d b := by
  rw [dilation_jet, norm_smul, Real.norm_of_nonneg (Real.exp_pos _).le]
  have hx : |x| ^ a = Real.exp ((a : ℝ) * s) * |Real.exp (-s) * x| ^ a := by
    rw [abs_mul, abs_of_pos (Real.exp_pos _), mul_pow, ← Real.exp_nat_mul, ← mul_assoc,
      ← Real.exp_add]
    simp
  rw [hx, mul_mul_mul_comm, ← Real.exp_add]
  have he : (a : ℝ) * s + (-(d : ℝ) - 1) * s ≤ |(a : ℝ) - d - 1| := by
    rw [show (a : ℝ) * s + (-(d : ℝ) - 1) * s = ((a : ℝ) - d - 1) * s by ring]
    calc
      _ ≤ |((a : ℝ) - d - 1) * s| := le_abs_self _
      _ ≤ _ := by
        rw [abs_mul]
        exact mul_le_of_le_one_right (abs_nonneg _) hs
  exact mul_le_mul (Real.exp_le_exp.mpr he) (SchwartzMap.le_seminorm' ℂ a d b _) (by positivity)
    (by positivity)

/-- Two mean value bounds suffice; no integration in Schwartz space is needed. -/
private theorem firstOrderRemainder {f f' f'' : ℝ → ℂ} (s : ℝ) {C : ℝ}
    (hf : ∀ u, HasDerivAt f (f' u) u) (hf' : ∀ u, HasDerivAt f' (f'' u) u)
    (hC : ∀ u, |u| ≤ |s| → ‖f'' u‖ ≤ C) (h0 : 0 ≤ C) :
    ‖f s - f 0 - s • f' 0‖ ≤ C * |s| ^ 2 := by
  let I : Set ℝ := Icc (-|s|) |s|
  have hzero : (0 : ℝ) ∈ I := ⟨neg_nonpos.mpr (abs_nonneg _), abs_nonneg _⟩
  have hs : s ∈ I := ⟨neg_abs_le _, le_abs_self _⟩
  have hconv : Convex ℝ I := convex_Icc _ _
  have hfirst (u : ℝ) (hu : u ∈ I) : ‖f' u - f' 0‖ ≤ C * |s| := by
    have h := hconv.norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun v _ ↦ (hf' v).hasDerivWithinAt) (fun v hv ↦ hC v (abs_le.mpr hv)) hzero hu
    rw [sub_zero, Real.norm_eq_abs] at h
    exact h.trans (mul_le_mul_of_nonneg_left (abs_le.mpr hu) h0)
  have hd (u : ℝ) : HasDerivAt (fun v ↦ f v - f 0 - v • f' 0) (f' u - f' 0) u := by
    simpa only [one_smul, id_eq] using
      ((hf u).sub_const (f 0)).fun_sub ((hasDerivAt_id u).smul_const (f' 0))
  have h := hconv.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun u _ ↦ (hd u).hasDerivWithinAt) hfirst hzero hs
  simpa only [sub_self, zero_smul, sub_zero, Real.norm_eq_abs, mul_assoc, pow_two] using h

/-- First-order Taylor remainder in each real Schwartz seminorm, uniform in the
profile once the same seminorm of its second generator derivative is bounded. -/
public theorem seminorm_weightedInverseDilation_difference_quotient (a d : ℕ) (b : B) {s : ℝ}
    (hs : s ≠ 0) (hs₁ : |s| ≤ 1) :
    p a d (s⁻¹ • (U s b - b) - G b) ≤
      Real.exp (|(a : ℝ) - d - 1|) * |s| * p a d (G (G b)) := by
  have hrem : p a d (U s b - b - s • G b) ≤
      Real.exp (|(a : ℝ) - d - 1|) * p a d (G (G b)) * |s| ^ 2 := by
    apply SchwartzMap.seminorm_le_bound' ℂ _ _ _ (by positivity)
    intro x
    have hj (g h : B) : iteratedDeriv d (g - h : B) x =
        iteratedDeriv d g x - iteratedDeriv d h x :=
      iteratedDeriv_sub (g.smooth d).contDiffAt (h.smooth d).contDiffAt
    have hj_smul (c : ℝ) (g : B) : iteratedDeriv d (c • g : B) x = c • iteratedDeriv d g x :=
      iteratedDeriv_const_smul_field _ _
    rw [hj, hj, hj_smul]
    let f (c : B) (u : ℝ) := |x| ^ a • iteratedDeriv d (U u c) x
    have hf (c : B) (u : ℝ) : HasDerivAt (f c) (f (G c) u) u :=
      (hasDerivAt_dilation_jet c d x u).const_smul (|x| ^ a)
    have hbound (u : ℝ) (hu : |u| ≤ |s|) : ‖f (G (G b)) u‖ ≤
        Real.exp (|(a : ℝ) - d - 1|) * p a d (G (G b)) := by
      dsimp only [f]
      rw [norm_smul, Real.norm_of_nonneg (by positivity)]
      exact dilation_jet_bound _ _ _ _ _ (hu.trans hs₁)
    have h := firstOrderRemainder s (hf b) (hf (G b)) hbound (by positivity)
    have hzero (c : B) : f c 0 = |x| ^ a • iteratedDeriv d c x := by
      simp [f, dilation_jet]
    rw [hzero, hzero] at h
    simpa only [f, ← smul_sub, smul_comm s (|x| ^ a), norm_smul,
      Real.norm_of_nonneg (show 0 ≤ |x| ^ a by positivity)] using h
  rw [show s⁻¹ • (U s b - b) - G b = s⁻¹ • (U s b - b - s • G b) by
    rw [smul_sub s⁻¹ (U s b - b), smul_smul, inv_mul_cancel₀ hs, one_smul]]
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ), map_smul_eq_mul]
  change ‖((s⁻¹ : ℝ) : ℂ)‖ * _ ≤ _
  rw [Complex.norm_real, Real.norm_eq_abs, abs_inv]
  have hs' : |s| ≠ 0 := abs_ne_zero.mpr hs
  calc
    _ ≤ |s|⁻¹ * (Real.exp (|(a : ℝ) - d - 1|) * p a d (G (G b)) * |s| ^ 2) :=
      mul_le_mul_of_nonneg_left hrem (by positivity)
    _ = _ := by field_simp [hs']

end
end Masullo
