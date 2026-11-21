module

public import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.Deriv.Support
public import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# The compact-test Laplace estimate

A project estimate for the cutoff argument at the interface of Masullo's
(13.3.1.2)–(13.3.1.3), p. 522 of the pinned edition. Two integrations by
parts give quadratic decay with no zero-moment hypothesis. This does not
establish equality of the full and capped distributions.
-/

open Filter MeasureTheory Set
open scoped ContDiff Topology

namespace Masullo

/-- The Laplace test transform with positive sign in the exponent. -/
@[expose] public noncomputable def positiveLaplaceTest (w : ℂ) (g : ℝ → ℂ) : ℂ :=
  ∫ x : ℝ in Ioi (0 : ℝ), Complex.exp (w * (x : ℂ)) * g x

private theorem positiveLaplaceTest_deriv (w : ℂ) {g : ℝ → ℂ}
    (hg : ContDiff ℝ 1 g) (hcg : HasCompactSupport g) (hg0 : g 0 = 0) :
    positiveLaplaceTest w (deriv g) = -(w * positiveLaplaceTest w g) := by
  let u : ℝ → ℂ := fun x ↦ Complex.exp (w * (x : ℂ))
  let u' : ℝ → ℂ := fun x ↦ w * u x
  have hu : Continuous u := by dsimp [u]; fun_prop
  have hu' : Continuous u' := continuous_const.mul hu
  have hdu (x : ℝ) : HasDerivAt u (u' x) x := by
    have hc : HasDerivAt (fun y : ℝ ↦ (y : ℂ)) 1 x := by
      -- Pass through the slope limit to reconcile Mathlib's real module instances on ℂ.
      apply hasDerivAt_iff_tendsto_slope.mpr
      have h := ((hasDerivAt_id x).ofReal_comp).tendsto_slope
      simpa only [id_eq, Complex.ofReal_one] using! h
    simpa only [u, u', mul_one, mul_comm] using (hc.const_mul w).cexp
  have hprod : HasCompactSupport (u * g) := hcg.mul_left
  have hzero : Tendsto (u * g) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℂ)) := by
    have h : ContinuousWithinAt (u * g) (Ioi (0 : ℝ)) 0 :=
      (hu.mul hg.continuous).continuousAt.continuousWithinAt
    simpa only [Pi.mul_apply, hg0, mul_zero] using h.tendsto
  have hinfty : Tendsto (u * g) atTop (𝓝 (0 : ℂ)) :=
    hprod.is_zero_at_infty.mono_left atTop_le_cocompact
  have h₁ : IntegrableOn (u * deriv g) (Ioi (0 : ℝ)) :=
    (hu.mul (hg.continuous_deriv le_rfl)).integrable_of_hasCompactSupport
      hcg.deriv.mul_left |>.integrableOn
  have h₂ : IntegrableOn (u' * g) (Ioi (0 : ℝ)) :=
    (hu'.mul hg.continuous).integrable_of_hasCompactSupport hcg.mul_left |>.integrableOn
  simpa only [Pi.mul_def, u', mul_assoc, integral_const_mul, sub_self, zero_sub,
    positiveLaplaceTest, u] using
    (integral_Ioi_mul_deriv_eq_deriv_mul (fun x _ ↦ hdu x)
      (fun x _ ↦ (hg.differentiable one_ne_zero x).hasDerivAt) h₁ h₂ hzero hinfty)

private theorem norm_positiveLaplaceTest_le (w : ℂ) (a : ℝ) (hwa : w.re ≤ a)
    {g : ℝ → ℂ} (hg : Continuous g) (hcg : HasCompactSupport g) :
    ‖positiveLaplaceTest w g‖ ≤ ∫ x : ℝ in Ioi (0 : ℝ), Real.exp (a * x) * ‖g x‖ := by
  let u : ℝ → ℂ := fun x ↦ Complex.exp (w * (x : ℂ))
  let v : ℝ → ℝ := fun x ↦ Real.exp (a * x)
  have hu : Continuous u := by dsimp [u]; fun_prop
  have hv : Continuous v := by dsimp [v]; fun_prop
  have hi : IntegrableOn (u * g) (Ioi (0 : ℝ)) :=
    (hu.mul hg).integrable_of_hasCompactSupport hcg.mul_left |>.integrableOn
  have hj : IntegrableOn (fun x ↦ v x * ‖g x‖) (Ioi (0 : ℝ)) :=
    (hv.mul hg.norm).integrable_of_hasCompactSupport
      (hcg.comp_left (g := fun z : ℂ ↦ ‖z‖) norm_zero).mul_left |>.integrableOn
  refine (norm_integral_le_integral_norm (μ := volume.restrict (Ioi (0 : ℝ))) (u * g)).trans ?_
  refine integral_mono_ae hi.norm hj ?_
  filter_upwards [ae_restrict_mem (μ := volume) (measurableSet_Ioi : MeasurableSet (Ioi (0 : ℝ)))]
    with x hx
  change ‖u x * g x‖ ≤ v x * ‖g x‖
  rw [norm_mul]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  simp only [u, v, Complex.norm_exp, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, sub_zero]
  exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hwa (le_of_lt (mem_Ioi.mp hx)))

/-- A compact test away from zero gives quadratic decay in the Laplace parameter,
weighted by a uniform upper bound on its real part. -/
public theorem norm_positiveLaplaceTest_mul_weight_le (w : ℂ) (a : ℝ) (hwa : w.re ≤ a)
    {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f) (hcf : HasCompactSupport f)
    (hs : tsupport f ⊆ Ioi (0 : ℝ)) :
    (1 + ‖w‖ ^ 2) * ‖positiveLaplaceTest w f‖ ≤
      (∫ x : ℝ in Ioi (0 : ℝ), Real.exp (a * x) * ‖f x‖) +
        (∫ x : ℝ in Ioi (0 : ℝ), Real.exp (a * x) * ‖deriv (deriv f) x‖) := by
  have h0 {g : ℝ → ℂ} (h : tsupport g ⊆ Ioi (0 : ℝ)) : g 0 = 0 := by
    apply Function.notMem_support.mp
    intro hz
    exact (lt_irrefl (0 : ℝ)) (h (subset_tsupport g hz))
  have hf' : ContDiff ℝ ∞ (deriv f) := (contDiff_infty_iff_deriv.mp hf).2
  have horder : (1 : ℕ∞ω) ≤ ∞ := WithTop.coe_le_coe.mpr le_top
  have h₁ : ContDiff ℝ 1 f := hf.of_le horder
  have h₂ : ContDiff ℝ 1 (deriv f) := hf'.of_le horder
  have hd0 : deriv f 0 = 0 := h0 (tsupport_deriv_subset.trans hs)
  have hsecond : positiveLaplaceTest w (deriv (deriv f)) = w ^ 2 * positiveLaplaceTest w f := by
    rw [positiveLaplaceTest_deriv w h₂ hcf.deriv hd0, positiveLaplaceTest_deriv w h₁ hcf (h0 hs)]
    simp [pow_two, mul_assoc]
  have hn : ‖positiveLaplaceTest w (deriv (deriv f))‖ = ‖w‖ ^ 2 * ‖positiveLaplaceTest w f‖ := by
    rw [hsecond, norm_mul, norm_pow]
  rw [add_mul, one_mul, ← hn]
  exact add_le_add (norm_positiveLaplaceTest_le w a hwa hf.continuous hcf)
    (norm_positiveLaplaceTest_le w a hwa (h₂.continuous_deriv le_rfl) hcf.deriv.deriv)

/-- A uniform quadratic majorant for the Laplace transform multiplied by a coefficient. -/
public theorem norm_mul_positiveLaplaceTest_le {w d : ℂ} {a C : ℝ} {f : ℝ → ℂ}
    (hw : w.re ≤ a) (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    (ht : tsupport f ⊆ Ioi (0 : ℝ))
    (hC : (∫ x in Ioi (0 : ℝ), Real.exp (a * x) * ‖f x‖) +
      (∫ x in Ioi (0 : ℝ), Real.exp (a * x) * ‖deriv (deriv f) x‖) ≤ C) :
    ‖d * positiveLaplaceTest w f‖ ≤ C * (‖d‖ / (1 + ‖w‖ ^ 2)) := by
  have hpos : 0 < 1 + ‖w‖ ^ 2 := by positivity
  have h := (norm_positiveLaplaceTest_mul_weight_le w a hw hf hc ht).trans hC
  rw [norm_mul]
  calc
    ‖d‖ * ‖positiveLaplaceTest w f‖ ≤ ‖d‖ * (C / (1 + ‖w‖ ^ 2)) :=
      mul_le_mul_of_nonneg_left ((le_div_iff₀ hpos).2 (by simpa only [mul_comm] using h))
        (norm_nonneg _)
    _ = C * (‖d‖ / (1 + ‖w‖ ^ 2)) := by simp only [div_eq_mul_inv, mul_left_comm]

end Masullo
