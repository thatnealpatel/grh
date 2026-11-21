module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Lemmas.LogMellinDerivative

/-! # Compactly supported Mellin integrals in log coordinates -/

open Filter MeasureTheory
open scoped ContDiff Topology

namespace Masullo

/-- The Mellin transform of the multiplicative test `t ↦ g (log t)`, written
in log coordinates as in (B.2.1.29). -/
@[expose] public noncomputable def compactLogMellin (g : ℝ → ℂ) (s : ℂ) : ℂ :=
  ∫ x : ℝ, g x * Complex.exp (s * x)

private theorem continuous_logMellin_kernel (s : ℂ) :
    Continuous (fun x : ℝ ↦ Complex.exp (s * x)) :=
  Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)

/-- Compact support supplies the exponential majorant for dominated differentiation
at each complex parameter, even without differentiability of the profile. -/
public theorem differentiable_compactLogMellin {g : ℝ → ℂ} (hg : Continuous g)
    (hc : HasCompactSupport g) : Differentiable ℂ (compactLogMellin g) := by
  intro s
  let F := fun x : ℝ ↦ g x * Complex.exp (s * x)
  let e := fun x : ℝ ↦ Real.exp (3 * |x|)
  have hF : Continuous F := hg.mul (continuous_logMellin_kernel s)
  have hF' : HasCompactSupport F := hc.mul_right
  have he : Continuous e := by dsimp [e]; fun_prop
  obtain ⟨C, hC⟩ := (hF.norm.mul he).bounded_above_of_compact_support hF'.norm.mul_right
  have hC₀ := (norm_nonneg _).trans (hC 0)
  have hdecay (x : ℝ) : ‖F x‖ ≤ C * Real.exp (-(3 * (1 : ℝ)) * |x|) := by
    rw [show -(3 * (1 : ℝ)) * |x| = -(3 * |x|) by ring, Real.exp_neg]
    apply (le_mul_inv_iff₀ (Real.exp_pos _)).mpr
    simpa only [Pi.mul_apply, e, Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (norm_nonneg (_ : ℂ)), abs_of_pos (Real.exp_pos _)] using hC x
  exact (hasDerivAt_logMellin_of_decay hg s zero_lt_one hC₀ hdecay).2.2.differentiableAt

private theorem compactLogMellin_deriv (s : ℂ) {g : ℝ → ℂ}
    (hg : Continuous g) (hd : Differentiable ℝ g) (hdc : Continuous (deriv g))
    (hc : HasCompactSupport g) :
    compactLogMellin (deriv g) s = -s * compactLogMellin g s := by
  let u : ℝ → ℂ := fun x ↦ Complex.exp (s * x)
  let u' : ℝ → ℂ := fun x ↦ s * u x
  have hu : Continuous u := continuous_logMellin_kernel s
  have hdu (x : ℝ) : HasDerivAt u (u' x) x := by
    have hx : HasDerivAt (fun y : ℝ ↦ (y : ℂ)) 1 x := by
      apply hasDerivAt_iff_tendsto_slope.mpr
      simpa only [id_eq, Complex.ofReal_one] using! ((hasDerivAt_id x).ofReal_comp).tendsto_slope
    simpa only [u, u', mul_one, mul_comm] using (hx.const_mul s).cexp
  have hi : Integrable (u * deriv g) :=
    (hu.mul hdc).integrable_of_hasCompactSupport hc.deriv.mul_left
  have hj : Integrable (u' * g) :=
    ((continuous_const.mul hu).mul hg).integrable_of_hasCompactSupport hc.mul_left
  have hprod : HasCompactSupport (u * g) := hc.mul_left
  have hz := hprod.is_zero_at_infty
  have h := integral_mul_deriv_eq_deriv_mul (fun x _ ↦ hdu x)
    (fun x _ ↦ (hd x).hasDerivAt) hi hj (hz.mono_left atBot_le_cocompact)
    (hz.mono_left atTop_le_cocompact)
  simp only [u', mul_assoc, integral_const_mul, sub_self, zero_sub] at h
  simpa only [compactLogMellin, u, mul_comm (g _), mul_comm (deriv g _), neg_mul] using h

/-- Differentiating the log profile preserves compact support. -/
public theorem hasCompactSupport_iteratedDeriv_logProfile {g : ℝ → ℂ}
    (hc : HasCompactSupport g) (N : ℕ) : HasCompactSupport (iteratedDeriv N g) := by
  induction N with
  | zero => simpa only [iteratedDeriv_zero] using hc
  | succ N ih => simpa only [iteratedDeriv_succ] using ih.deriv

/-- Whole-line integration by parts, iterated with no division at `s = 0`.
This is the multiplication form of (B.2.1.31). -/
public theorem compactLogMellin_iteratedDeriv {g : ℝ → ℂ} (hg : ContDiff ℝ ∞ g)
    (hc : HasCompactSupport g) (s : ℂ) (N : ℕ) :
    compactLogMellin (iteratedDeriv N g) s = (-s) ^ N * compactLogMellin g s := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hd := hg.differentiable_iteratedDeriv N (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top N))
    have hdc := hg.continuous_iteratedDeriv (N + 1) (WithTop.coe_le_coe.mpr le_top)
    rw [iteratedDeriv_succ] at hdc
    rw [iteratedDeriv_succ, compactLogMellin_deriv s hd.continuous hd hdc
      (hasCompactSupport_iteratedDeriv_logProfile hc N), ih, pow_succ', mul_assoc]

/-- The common integral majorant on a closed strip, as in (B.2.1.30)
and (B.2.1.34). -/
public theorem norm_compactLogMellin_le {g : ℝ → ℂ} (hg : Continuous g)
    (hc : HasCompactSupport g) {s : ℂ} {A : ℝ} (hs : |s.re| ≤ A) :
    ‖compactLogMellin g s‖ ≤ ∫ x : ℝ, ‖g x‖ * Real.exp (A * |x|) := by
  have hi : Integrable (fun x : ℝ ↦ g x * Complex.exp (s * x)) :=
    (hg.mul (continuous_logMellin_kernel s)).integrable_of_hasCompactSupport hc.mul_right
  have hj : Integrable (fun x : ℝ ↦ ‖g x‖ * Real.exp (A * |x|)) :=
    (hg.norm.mul (by fun_prop)).integrable_of_hasCompactSupport hc.norm.mul_right
  refine (norm_integral_le_integral_norm _).trans (integral_mono hi.norm hj fun x ↦ ?_)
  rw [norm_mul, Complex.norm_exp, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, sub_zero]
  apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (norm_nonneg _)
  calc
    s.re * x ≤ |s.re| * |x| := by rw [← abs_mul]; exact le_abs_self _
    _ ≤ A * |x| := mul_le_mul_of_nonneg_right hs (abs_nonneg _)

end Masullo
