module

public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-! # The floor-grid local mean–mean contribution

The two exponential kernel legs separate into a weighted moment of the cutoff `ρ`
and a half-exponential moment of the bump `b`. Integration by parts gives the
negative sign because the second leg uses `deriv b`.
-/

open MeasureTheory Set
open scoped ContDiff

namespace Masullo

/-- The exponential kernel on each leg of the local mean–mean term. -/
@[expose] public noncomputable def floorGridMeanKernel (x : ℝ) : ℝ :=
  2 * Real.exp (-x / 2)

/-- The weight on the outer variable of the local mean–mean term. -/
@[expose] public noncomputable def floorGridMeanWeight (a x : ℝ) : ℝ :=
  Real.exp (2 * a * |x|) * (1 + x ^ 2) ^ 2

/-- The concrete two-leg mean–mean term, with `b` the undifferentiated bump. -/
@[expose] public noncomputable def floorGridMeanPair (a : ℝ) (ρ b : ℝ → ℝ) (c : ℝ) : ℝ :=
  ∫ x, ρ x * floorGridMeanWeight a x * (c * floorGridMeanKernel x) *
    (∫ z, deriv b z * (c * floorGridMeanKernel (x - z)))

/-- The coefficient of `c ^ 2`, expressed using two moments of undifferentiated inputs. -/
@[expose] public noncomputable def floorGridMeanCoeff (a : ℝ) (ρ b : ℝ → ℝ) : ℝ :=
  -2 * (∫ x, ρ x * floorGridMeanWeight a x * Real.exp (-x)) *
    (∫ z, b z * Real.exp (z / 2))

private theorem kernel_sub (x z : ℝ) :
    floorGridMeanKernel (x - z) = floorGridMeanKernel x * Real.exp (z / 2) := by
  rw [floorGridMeanKernel, floorGridMeanKernel,
    show -(x - z) / 2 = -x / 2 + z / 2 by ring, Real.exp_add, mul_assoc]

private theorem kernel_sq (x : ℝ) :
    floorGridMeanKernel x ^ 2 = 4 * Real.exp (-x) := by
  calc
    _ = 4 * (Real.exp (-x / 2) * Real.exp (-x / 2)) := by
      unfold floorGridMeanKernel
      ring
    _ = _ := by rw [← Real.exp_add, show -x / 2 + -x / 2 = -x by ring]

private theorem deriv_halfMoment {b : ℝ → ℝ} (hb : ContDiff ℝ 1 b)
    (hcb : HasCompactSupport b) :
    (∫ z, deriv b z * Real.exp (z / 2)) = -(1 / 2) * ∫ z, b z * Real.exp (z / 2) := by
  let e (z : ℝ) := Real.exp (z / 2)
  let d (z : ℝ) := (1 / 2 : ℝ) * e z
  have he : Continuous e := by dsimp [e]; fun_prop
  have hd : Continuous d := continuous_const.mul he
  have hed (z : ℝ) : HasDerivAt e (d z) z := by
    simpa [e, d, mul_comm] using ((hasDerivAt_id z).div_const 2).exp
  -- Compact support makes both products and the differentiated product integrable,
  -- so there is no boundary term in whole-line integration by parts.
  have h := integral_mul_deriv_eq_deriv_mul_of_integrable (u := b) (u' := deriv b)
    (v := e) (v' := d) (fun z _ ↦ (hb.differentiable one_ne_zero z).hasDerivAt)
    (fun z _ ↦ hed z)
    ((hb.continuous.mul hd).integrable_of_hasCompactSupport hcb.mul_right)
    ((hb.continuous_deriv_one.mul he).integrable_of_hasCompactSupport hcb.deriv.mul_right)
    ((hb.continuous.mul he).integrable_of_hasCompactSupport hcb.mul_right)
  have hfactor (z : ℝ) : b z * d z = (1 / 2 : ℝ) * (b z * e z) := by dsimp [d]; ring
  change (∫ z, b z * d z) = -(∫ z, deriv b z * e z) at h
  simp_rw [hfactor, integral_const_mul] at h
  simpa only [neg_neg, neg_mul] using (congrArg Neg.neg h).symm

/-- The pair is exactly quadratic in `c`, including at `c = 0`.
The identity itself does not require positivity or a restriction on the location of the support. -/
public theorem floorGridMeanPair_eq (a : ℝ) (ρ : ℝ → ℝ) {b : ℝ → ℝ} (c : ℝ)
    (hb : ContDiff ℝ 1 b) (hcb : HasCompactSupport b) :
    floorGridMeanPair a ρ b c = floorGridMeanCoeff a ρ b * c ^ 2 := by
  have hinner (x : ℝ) :
      (∫ z, deriv b z * (c * floorGridMeanKernel (x - z))) =
        (-(1 / 2) * ∫ z, b z * Real.exp (z / 2)) * (c * floorGridMeanKernel x) := by
    calc
      _ = ∫ z, (deriv b z * Real.exp (z / 2)) * (c * floorGridMeanKernel x) := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun z ↦ by
          dsimp only
          rw [kernel_sub]
          ring
      _ = _ := by rw [integral_mul_const, deriv_halfMoment hb hcb]
  unfold floorGridMeanPair floorGridMeanCoeff
  calc
    _ = ∫ x, (-2 * (∫ z, b z * Real.exp (z / 2)) * c ^ 2) *
        (ρ x * floorGridMeanWeight a x * Real.exp (-x)) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x ↦ by
        dsimp only
        rw [hinner x]
        calc
          _ = -(1 / 2) * (∫ z, b z * Real.exp (z / 2)) * c ^ 2 *
              (ρ x * floorGridMeanWeight a x * floorGridMeanKernel x ^ 2) := by ring
          _ = _ := by rw [kernel_sq]; ring
    _ = _ := by rw [integral_const_mul]; ring

private theorem integral_mul_pos {f k : ℝ → ℝ} (hf : Continuous f)
    (hcf : HasCompactSupport f) (hf0 : 0 ≤ f) (hfne : f ≠ 0)
    (hk : Continuous k) (hkpos : ∀ x, 0 < k x) : 0 < ∫ x, f x * k x := by
  obtain ⟨x, hx⟩ := Function.ne_iff.mp hfne
  exact (hf.mul hk).integral_pos_of_hasCompactSupport_nonneg_ne_zero hcf.mul_right
    (fun y ↦ mul_nonneg (hf0 y) (hkpos y).le) (mul_ne_zero hx (hkpos x).ne')

/-- Both moments are strictly positive for nonzero nonnegative compactly supported inputs.
No condition on `a` or on the location of the supports is needed. -/
public theorem floorGridMeanCoeff_neg (a : ℝ) {ρ b : ℝ → ℝ}
    (hρ : Continuous ρ) (hcρ : HasCompactSupport ρ) (hρ0 : 0 ≤ ρ) (hρne : ρ ≠ 0)
    (hb : Continuous b) (hcb : HasCompactSupport b) (hb0 : 0 ≤ b) (hbne : b ≠ 0) :
    floorGridMeanCoeff a ρ b < 0 := by
  have hρm := integral_mul_pos hρ hcρ hρ0 hρne
    (show Continuous (fun x ↦ floorGridMeanWeight a x * Real.exp (-x)) by
      unfold floorGridMeanWeight
      fun_prop)
    (fun x ↦ by unfold floorGridMeanWeight; positivity)
  have hbm := integral_mul_pos hb hcb hb0 hbne
    (show Continuous (fun z : ℝ ↦ Real.exp (z / 2)) by fun_prop) (fun z ↦ Real.exp_pos _)
  rw [floorGridMeanCoeff, show (∫ x, ρ x * floorGridMeanWeight a x * Real.exp (-x)) =
    ∫ x, ρ x * (floorGridMeanWeight a x * Real.exp (-x)) by simp only [mul_assoc]]
  exact mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (by norm_num) hρm) hbm

/-- At every nonzero `c` the local mean–mean contribution is strictly negative. -/
public theorem floorGridMeanPair_neg (a : ℝ) {ρ b : ℝ → ℝ} {c : ℝ}
    (hρ : Continuous ρ) (hcρ : HasCompactSupport ρ) (hρ0 : 0 ≤ ρ) (hρne : ρ ≠ 0)
    (hb : ContDiff ℝ 1 b) (hcb : HasCompactSupport b) (hb0 : 0 ≤ b) (hbne : b ≠ 0)
    (hc : c ≠ 0) : floorGridMeanPair a ρ b c < 0 := by
  rw [floorGridMeanPair_eq a ρ c hb hcb]
  exact mul_neg_of_neg_of_pos (floorGridMeanCoeff_neg a hρ hcρ hρ0 hρne
    hb.continuous hcb hb0 hbne) (sq_pos_of_ne_zero hc)

/-- The local mean–mean contribution does not vanish when `c ≠ 0`. -/
public theorem floorGridMeanPair_ne_zero (a : ℝ) {ρ b : ℝ → ℝ} {c : ℝ}
    (hρ : Continuous ρ) (hcρ : HasCompactSupport ρ) (hρ0 : 0 ≤ ρ) (hρne : ρ ≠ 0)
    (hb : ContDiff ℝ 1 b) (hcb : HasCompactSupport b) (hb0 : 0 ≤ b) (hbne : b ≠ 0)
    (hc : c ≠ 0) : floorGridMeanPair a ρ b c ≠ 0 :=
  (floorGridMeanPair_neg a hρ hcρ hρ0 hρne hb hcb hb0 hbne hc).ne

/-- A qualifying `b` exists, and it can also serve as `ρ`. Its closed support is
contained in `(0, log 2)`. -/
public theorem exists_floorGridMeanBump :
    ∃ b : ℝ → ℝ, ContDiff ℝ ∞ b ∧ HasCompactSupport b ∧
      tsupport b ⊆ Ioo 0 (Real.log 2) ∧ 0 ≤ b ∧ b ≠ 0 := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let m := Real.log 2 / 2
  let b : ContDiffBump m := ⟨Real.log 2 / 8, Real.log 2 / 4, by linarith, by linarith⟩
  refine ⟨b, b.contDiff, b.hasCompactSupport, ?_, b.nonneg', ?_⟩
  · rw [b.tsupport_eq]
    intro x hx
    rw [Metric.mem_closedBall, Real.dist_eq, abs_le] at hx
    change -(Real.log 2 / 4) ≤ x - Real.log 2 / 2 ∧
      x - Real.log 2 / 2 ≤ Real.log 2 / 4 at hx
    exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  · have hone : b m = 1 := b.one_of_mem_closedBall (Metric.mem_closedBall_self b.rIn_pos.le)
    exact Function.ne_iff.mpr ⟨m, by change b m ≠ 0; simp [hone]⟩

end Masullo
