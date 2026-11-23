module

public import Lemmas.CompactLogMellinAdjoint
public import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-! # Analytic factor for a polynomially filtered log density -/

open Filter Set
open scoped Topology

namespace Masullo

private noncomputable def densityFactor (r : ℝ) : ℕ → ℂ → ℂ
  | 0 => fun z ↦ (1 - z)⁻¹
  | n + 1 => fun z ↦ (r : ℂ) * densityFactor r n z - 2 * z * deriv (densityFactor r n) z

private theorem densityFactor_analytic (r : ℝ) (n : ℕ) :
    AnalyticOnNhd ℂ (densityFactor r n) (Metric.ball 0 1) := by
  induction n with
  | zero =>
    intro z hz
    change AnalyticAt ℂ (fun w : ℂ ↦ (1 - w)⁻¹) z
    refine (analyticAt_const.sub analyticAt_id).inv ?_
    intro h
    have hz' : ‖z‖ < (1 : ℝ) := by simpa [Metric.mem_ball, dist_zero_right] using hz
    have heq : z = 1 := (sub_eq_zero.mp h).symm
    simp [heq] at hz'
  | succ n ih =>
    intro z hz
    change AnalyticAt ℂ (fun w ↦ (r : ℂ) * densityFactor r n w -
      2 * w * deriv (densityFactor r n) w) z
    exact (analyticAt_const.mul (ih z hz)).sub
      ((analyticAt_const.mul analyticAt_id).mul (ih z hz).deriv)

private theorem densityFactor_zero (r : ℝ) (n : ℕ) :
    densityFactor r n 0 = (r : ℂ) ^ n := by
  induction n with
  | zero => simp [densityFactor]
  | succ n ih => simp [densityFactor, ih, pow_succ']

private theorem hasDerivAt_densityFactor_re (r : ℝ) (n : ℕ) {s : ℝ} (hs : 0 < s) :
    HasDerivAt (fun x : ℝ ↦ Real.exp (r*x) *
      (densityFactor r n (Complex.ofReal (Real.exp (-2*x)))).re)
      (Real.exp (r*s) * (densityFactor r (n + 1) (Complex.ofReal (Real.exp (-2*s)))).re) s := by
  have hz : Complex.ofReal (Real.exp (-2*s)) ∈ Metric.ball 0 1 := by
    rw [Metric.mem_ball, dist_zero_right, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
    exact Real.exp_lt_one_iff.mpr (by linarith)
  have hA : HasDerivAt (fun y : ℝ ↦ (densityFactor r n (Complex.ofReal y)).re)
      (deriv (densityFactor r n) (Complex.ofReal (Real.exp (-2*s)))).re (Real.exp (-2*s)) :=
    (densityFactor_analytic r n _ hz).differentiableAt.hasDerivAt.real_of_complex
  have he (a : ℝ) : HasDerivAt (fun x ↦ Real.exp (a*x)) (Real.exp (a*s) * a) s := by
    simpa using ((hasDerivAt_id s).const_mul a).exp
  convert (he r).mul (hA.comp s (he (-2))) using 1
  · rfl
  · simp only [densityFactor, Function.comp_apply, Complex.sub_re, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.re_ofNat, Complex.im_ofNat,
      zero_mul, mul_zero, sub_zero, add_zero]
    ring

private theorem iteratedDeriv_densityFactor (r : ℝ) (n : ℕ) {s : ℝ} (hs : 0 < s) :
    iteratedDeriv n (fun x ↦ Real.exp (r*x) / (1 - Real.exp (-2*x))) s =
      Real.exp (r*s) * (densityFactor r n (Complex.ofReal (Real.exp (-2*s)))).re := by
  induction n generalizing s with
  | zero =>
    rw [iteratedDeriv_zero, densityFactor, div_eq_mul_inv]
    congr 1
    change (1 - Real.exp (-2*s))⁻¹ = ((1 - Complex.ofReal (Real.exp (-2*s)))⁻¹).re
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub, ← Complex.ofReal_inv, Complex.ofReal_re]
  | succ n ih =>
    rw [iteratedDeriv_succ]
    have hpos : ∀ᶠ x in 𝓝 s, x ∈ Ioi (0 : ℝ) := isOpen_Ioi.mem_nhds hs
    have h : iteratedDeriv n (fun x ↦ Real.exp (r*x) / (1 - Real.exp (-2*x))) =ᶠ[𝓝 s]
        (fun x ↦ Real.exp (r*x) * (densityFactor r n (Complex.ofReal (Real.exp (-2*x)))).re) :=
      hpos.mono (fun _ hx ↦ ih hx)
    exact h.deriv_eq.trans (hasDerivAt_densityFactor_re r n hs).deriv

/-- Factor the filtered density on the positive log axis through an analytic function of
`exp (-2*s)`. Its constant term in real part is the adjoint multiplier at `r`. -/
public theorem exists_filteredLogDensity_factor (P : Polynomial ℝ) (r : ℝ) :
    ∃ A : ℂ → ℂ, AnalyticOnNhd ℂ A (Metric.ball 0 1) ∧
      (A 0).re = P.eval (-r) ∧
      ∀ s : ℝ, 0 < s →
        logPolynomialAdjoint P (fun x ↦ Real.exp (r*x) / (1 - Real.exp (-2*x))) s =
          Real.exp (r*s) * (A (Complex.ofReal (Real.exp (-2*s)))).re := by
  let A : ℂ → ℂ := fun z ↦ ∑ n ∈ P.support,
    (↑(P.coeff n * (-1 : ℝ) ^ n) : ℂ) * densityFactor r n z
  have hre (z : ℂ) : (A z).re =
      ∑ n ∈ P.support, P.coeff n * (-1 : ℝ) ^ n * (densityFactor r n z).re := by
    simp only [A]
    rw [← Complex.reCLM_apply, map_sum]
    simp only [Complex.reCLM_apply, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero]
  refine ⟨A, Finset.analyticOnNhd_fun_sum _ (fun n _ z hz ↦
    analyticAt_const.mul (densityFactor_analytic r n z hz)), ?_, ?_⟩
  · rw [hre, Polynomial.eval_eq_sum, Polynomial.sum]
    refine Finset.sum_congr rfl fun n _ ↦ ?_
    rw [densityFactor_zero, ← Complex.ofReal_pow, Complex.ofReal_re, mul_assoc, ← mul_pow,
      neg_one_mul]
  · intro s hs
    rw [logPolynomialAdjoint, hre, Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ ↦ ?_
    rw [iteratedDeriv_densityFactor r n hs]
    ring

end Masullo
