module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-! # Integration by parts for the positive exponential phase on the real line -/

open Complex Filter Function MeasureTheory Set
open scoped ContDiff Topology

namespace Masullo.PositiveLogBumpDecay

private noncomputable def phase (t x : ℝ) : ℂ := Complex.exp (I * (t : ℂ) * (x : ℂ))

private theorem hasDerivAt_phase (t x : ℝ) :
    HasDerivAt (phase t) (I * (t : ℂ) * phase t x) x := by
  have h := ((Complex.ofRealCLM.hasDerivAt (x := x)).const_mul (I * (t : ℂ))).cexp
  simpa only [Complex.ofRealCLM_apply, Complex.ofReal_one, mul_one, phase,
    mul_comm (Complex.exp _) (I * (t : ℂ))] using! h

private theorem norm_phase (t x : ℝ) : ‖phase t x‖ = 1 := by
  rw [phase, mul_assoc, ← Complex.ofReal_mul, Complex.norm_exp_I_mul_ofReal]

private theorem integral_phase_succ {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    (k : ℕ) (t : ℝ) :
    (∫ x, iteratedDeriv (k + 1) f x * phase t x) =
      -(I * (t : ℂ)) * ∫ x, iteratedDeriv k f x * phase t x := by
  have hcs (n : ℕ) : HasCompactSupport (iteratedDeriv n f) := by
    induction n with
    | zero => simpa using hc
    | succ n ih =>
      rw [iteratedDeriv_succ]
      exact ih.mono' ((subset_tsupport _).trans tsupport_deriv_subset)
  have hcont (n : ℕ) := hf.continuous_iteratedDeriv n (by simp)
  have hph : Continuous (phase t) := continuous_iff_continuousAt.mpr
    fun x ↦ (hasDerivAt_phase t x).continuousAt
  have hI (n : ℕ) : Integrable (iteratedDeriv n f * phase t) :=
    ((hcont n).mul hph).integrable_of_hasCompactSupport (hcs n).mul_right
  have hD := hf.differentiable_iteratedDeriv k (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top k))
  let c := I * (t : ℂ)
  have hI' : Integrable (iteratedDeriv k f * fun x ↦ c * phase t x) := by
    convert (hI k).const_mul c using 1
    ext x
    simp only [Pi.mul_apply]
    ring
  have he := integral_mul_deriv_eq_deriv_mul_of_integrable
    (u := iteratedDeriv k f) (v := phase t)
    (fun x _ ↦ (hD x).hasDerivAt) (fun x _ ↦ hasDerivAt_phase t x) hI'
    (by simpa only [iteratedDeriv_succ] using hI (k + 1)) (hI k)
  simp only [← iteratedDeriv_succ] at he
  have hfactor (x : ℝ) : iteratedDeriv k f x * (I * (t : ℂ) * phase t x) =
      c * (iteratedDeriv k f x * phase t x) := by dsimp [c]; ring
  simp_rw [hfactor, integral_const_mul] at he
  simpa only [neg_neg, ← neg_mul, c] using (congrArg Neg.neg he).symm

/-- Repeated integration by parts costs one factor of `|t|` per derivative. Compact support
removes the boundary terms via the whole-line integrable integration-by-parts theorem. -/
public theorem norm_integral_exp_mul_eq (k : ℕ) (t : ℝ) {f : ℝ → ℂ}
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) :
    |t| ^ k * ‖∫ x, f x * Complex.exp (I * (t : ℂ) * (x : ℂ))‖ =
      ‖∫ x, iteratedDeriv k f x * Complex.exp (I * (t : ℂ) * (x : ℂ))‖ := by
  change |t| ^ k * ‖∫ x, f x * phase t x‖ = ‖∫ x, iteratedDeriv k f x * phase t x‖
  induction k with
  | zero => simp
  | succ k ih =>
    rw [integral_phase_succ hf hc k t, norm_mul, norm_neg, norm_mul, Complex.norm_I, one_mul,
      Complex.norm_real, Real.norm_eq_abs, pow_succ', mul_assoc, ih]

/-- Whole-line Fourier decay from a uniform derivative bound on an interval containing the support
of that derivative. -/
public theorem norm_integral_exp_le_of_derivative_bound (k : ℕ) {t l r C : ℝ} (ht : t ≠ 0)
    (hlr : l ≤ r) {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    (hs : support (iteratedDeriv k f) ⊆ Icc l r)
    (hC : ∀ x ∈ Icc l r, ‖iteratedDeriv k f x‖ ≤ C) :
    ‖∫ x, f x * Complex.exp (I * (t : ℂ) * (x : ℂ))‖ ≤ (r - l) * C / |t| ^ k := by
  have hrestrict : (∫ x, iteratedDeriv k f x * phase t x) =
      ∫ x in Icc l r, iteratedDeriv k f x * phase t x := by
    rw [← setIntegral_univ (μ := volume) (f := fun x ↦ iteratedDeriv k f x * phase t x)]
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero MeasurableSet.univ (subset_univ _)
    intro x hx
    rw [notMem_support.mp (fun h ↦ hx.2 (hs h)), zero_mul]
  apply (le_div_iff₀ (pow_pos (abs_pos.mpr ht) k)).mpr
  rw [mul_comm, norm_integral_exp_mul_eq k t hf hc]
  change ‖∫ x, iteratedDeriv k f x * phase t x‖ ≤ _
  rw [hrestrict]
  have hnorm := norm_setIntegral_le_of_norm_le_const
    (f := fun x ↦ iteratedDeriv k f x * phase t x) (μ := volume) (s := Icc l r)
    measure_Icc_lt_top (fun x hx ↦ by simpa [norm_mul, norm_phase] using hC x hx)
  rwa [Real.volume_real_Icc_of_le hlr, mul_comm] at hnorm

end Masullo.PositiveLogBumpDecay
