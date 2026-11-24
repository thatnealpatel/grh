module

public import Lemmas.WeilPairAmplitude
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# Depth-sensitive price for a shallow reflected Weil pair

Source: `db84b3c3:.godel/bob/deep-retained-excess.md:17`, used in
`.godel/bob/uncut-trace-normal.md:7–9`.

Scope: a pointwise bound on the signed charge of one same-ordinate reflected
pair for `D ≥ 1`, `C ≥ 1`, `1/2 < β < 1`, `0 ≤ ε ≤ 1`, and depth
`(β - 1/2) * D ≤ C`, at any real offset. The test uses the exact finite halves
and analytic multiplier, with no phase restriction. The price uses the sum of
both Poisson kernels, without a further sum over pairs or a zero-free premise.

Owning check session: `01a20f51-211d-73b8-9726-8aa026238fa2`.
-/

namespace WeilGrayPair

private theorem charge_le_of_shallow_amplitude {D C β ε A : ℝ} (hD : 0 < D)
    (hC : 1 ≤ C) (hβ₀ : 1 / 2 < β) (hβ₁ : β < 1) (hcC : (β - 1 / 2) * D ≤ C)
    (hA : 0 ≤ A) (x : ℝ)
    (hamp : ‖phaseAmplitude ((β - 1 / 2) * D) (weightedTest ε D β x)‖ ^ 2 ≤
      A / ‖shiftedZero β x‖ ^ 2) :
    -(weightedTest ε D β x ^ 2).re ≤
      2 * (Real.cosh C - 1) * A * (1 + 2 / D) * pairKernel D β x := by
  let c := (β - 1 / 2) * D
  let Z := weightedTest ε D β x
  let P := phaseAmplitude c Z
  have hc : 0 < c := mul_pos (sub_pos.mpr hβ₀) hD
  have hcosh : Real.cosh c ≤ Real.cosh C := by
    apply Real.cosh_le_cosh.mpr
    rwa [abs_of_pos hc, abs_of_nonneg (by linarith : 0 ≤ C)]
  have hphase : -Real.cosh C ≤ Real.cosh c * Real.cos (2 * Complex.arg P) := calc
    _ ≤ -Real.cosh c := neg_le_neg hcosh
    _ = Real.cosh c * (-1) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.neg_one_le_cos _) (Real.cosh_pos c).le
  have hcoeff : 0 ≤ 2 * (Real.cosh C - 1) := by linarith [Real.one_le_cosh C]
  have hs : ‖shiftedZero β x‖ ^ 2 = β ^ 2 + x ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    change β * β + x * x = β ^ 2 + x ^ 2
    ring
  rw [hs] at hamp
  change -(Z ^ 2).re ≤ _
  calc
    _ ≤ 2 * (Real.cosh C - 1) * ‖P‖ ^ 2 := by
      rw [re_sq_eq_phase hc Z]
      change -(2 * ‖P‖ ^ 2 * (1 + Real.cosh c * Real.cos (2 * Complex.arg P))) ≤ _
      nlinarith only [mul_le_mul_of_nonneg_left hphase (show 0 ≤ 2 * ‖P‖ ^ 2 by positivity)]
    _ ≤ 2 * (Real.cosh C - 1) * (A / (β ^ 2 + x ^ 2)) :=
      mul_le_mul_of_nonneg_left hamp hcoeff
    _ = (2 * (Real.cosh C - 1) * A) * (1 / (β ^ 2 + x ^ 2)) := by ring
    _ ≤ (2 * (Real.cosh C - 1) * A) * ((1 + 2 / D) * pairKernel D β x) :=
      mul_le_mul_of_nonneg_left (reciprocal_le_pairKernel hD hβ₀ hβ₁ x) (mul_nonneg hcoeff hA)
    _ = _ := by ring

private theorem norm_multiplierRoot_le_of_cos {ε β θ : ℝ} (hθ : 0 ≤ Real.cos θ)
    (hθy : Real.cos θ ≤ Real.cos (ε * (β - 1 / 2))) (x : ℝ) :
    ‖multiplierRoot ε (shiftedArgument β x)‖ ≤ Real.exp ((1 - Real.cos θ) / 2) := by
  let t := ε * x
  let y := ε * (β - 1 / 2)
  have hz : (ε : ℂ) * shiftedArgument β x = (t : ℂ) + (-y : ℝ) * Complex.I := by
    apply Complex.ext
    · simp [t, y, shiftedArgument, Complex.mul_re]
    · simp [t, y, shiftedArgument, Complex.mul_im]
      ring
  have hreal : (Complex.cosh ((t : ℂ) + (-y : ℝ) * Complex.I)).re =
      Real.cosh t * Real.cos y := by
    rw [Complex.cosh_add, Complex.cosh_mul_I, Complex.sinh_mul_I, ← Complex.ofReal_cosh,
      ← Complex.ofReal_sinh, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    simp only [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im, Real.cos_neg, mul_zero, zero_mul, sub_zero, add_zero]
  rw [multiplierRoot, hz, Complex.norm_exp, Real.exp_le_exp, Complex.div_ofNat_re,
    Complex.sub_re, Complex.one_re, hreal]
  have h := hθy.trans (le_mul_of_one_le_left (hθ.trans hθy) (Real.one_le_cosh t))
  change Real.cos θ ≤ Real.cosh t * Real.cos y at h
  linarith only [h]

private theorem phaseAmplitude_sq_le_shallow {D C β ε : ℝ} (hD : 1 ≤ D)
    (hβ₀ : 1 / 2 < β) (hβ₁ : β < 1) (hε₀ : 0 ≤ ε) (hε₁ : ε ≤ 1)
    (hcC : (β - 1 / 2) * D ≤ C) (x : ℝ) :
    ‖phaseAmplitude ((β - 1 / 2) * D) (weightedTest ε D β x)‖ ^ 2 ≤
      (Real.exp (1 - Real.cos (ε * min (C / D) (1 / 2))) + 251000 * Real.exp 1 / D) /
        ‖shiftedZero β x‖ ^ 2 := by
  let s := shiftedZero β x
  let r := multiplierRoot ε (shiftedArgument β x)
  let e := Complex.exp ((x : ℂ) * ((D / 2 : ℝ) : ℂ) * Complex.I)
  let P := phaseAmplitude ((β - 1 / 2) * D) (weightedTest ε D β x)
  let T := 1 + |x|
  let θ := ε * min (C / D) (1 / 2)
  let q := Real.exp ((1 - Real.cos θ) / 2)
  let B := Real.exp (1 / 2)
  let E := 500 * B / D
  have hD₀ : 0 < D := by linarith
  have hβ : 0 < β := by linarith
  have hT : 0 < T := by dsimp [T]; positivity
  have hE : 0 ≤ E := by dsimp [E, B]; positivity
  have hsn : 0 < ‖s‖ := hβ.trans_le (by
    simpa [s, shiftedZero, abs_of_pos hβ] using Complex.abs_re_le_norm s)
  have hsT : ‖s‖ ≤ T := calc
    _ ≤ β + |x| := by
      simpa [s, shiftedZero, abs_of_pos hβ] using Complex.norm_le_abs_re_add_abs_im s
    _ ≤ _ := by dsimp [T]; linarith
  have hErr : ‖P - e * r / s‖ * ‖s‖ ≤ E := by
    have h : ‖P - e * r / s‖ ≤ (500 * B) / (D * T) :=
      phaseAmplitude_error_le hD hβ₀ hβ₁ hε₀ hε₁ x
    calc
      _ ≤ ‖P - e * r / s‖ * T := mul_le_mul_of_nonneg_left hsT (norm_nonneg _)
      _ ≤ (500 * B / (D * T)) * T := mul_le_mul_of_nonneg_right h hT.le
      _ = E := by rw [← div_div, div_mul_cancel₀ _ hT.ne']
  have hy₀ : 0 ≤ ε * (β - 1 / 2) := mul_nonneg hε₀ (sub_nonneg.mpr hβ₀.le)
  have hyθ : ε * (β - 1 / 2) ≤ θ :=
    mul_le_mul_of_nonneg_left (le_min ((le_div_iff₀ hD₀).mpr hcC) (by linarith)) hε₀
  have hθ : θ ≤ 1 / 2 := calc
    _ ≤ ε * (1 / 2) := mul_le_mul_of_nonneg_left (min_le_right _ _) hε₀
    _ ≤ _ := by linarith
  have hcosθ : 0 ≤ Real.cos θ :=
    Real.cos_nonneg_of_mem_Icc ⟨by linarith [hy₀.trans hyθ, Real.pi_gt_three],
      by linarith [Real.pi_gt_three]⟩
  have hcosθy : Real.cos θ ≤ Real.cos (ε * (β - 1 / 2)) :=
    Real.cos_le_cos_of_nonneg_of_le_pi hy₀ (by linarith [Real.pi_gt_three]) hyθ
  have hMain : ‖e * r / s‖ * ‖s‖ ≤ q := by
    have he : ‖e‖ = 1 := by
      dsimp only [e]
      rw [← Complex.ofReal_mul]
      exact Complex.norm_exp_ofReal_mul_I _
    rw [norm_div, div_mul_cancel₀ _ hsn.ne', norm_mul, he, one_mul]
    exact norm_multiplierRoot_le_of_cos hcosθ hcosθy x
  have hP : ‖P‖ * ‖s‖ ≤ q + E := by
    have htri := norm_add_le (P - e * r / s) (e * r / s)
    rw [sub_add_cancel] at htri
    calc
      _ ≤ (‖P - e * r / s‖ + ‖e * r / s‖) * ‖s‖ := mul_le_mul_of_nonneg_right htri hsn.le
      _ ≤ _ := by rw [add_mul, add_comm q E]; exact add_le_add hErr hMain
  have hqB : q ≤ B := Real.exp_le_exp.mpr (by linarith)
  have hEB : E ≤ 500 * B := by
    apply (div_le_iff₀ hD₀).mpr
    exact le_mul_of_one_le_right (by dsimp [B]; positivity) hD
  have hq₂ : q ^ 2 = Real.exp (1 - Real.cos θ) := by
    dsimp only [q]
    rw [pow_two, ← Real.exp_add, add_halves]
  have hB₂ : B ^ 2 = Real.exp 1 := by
    dsimp only [B]
    rw [pow_two, ← Real.exp_add, add_halves]
  change ‖P‖ ^ 2 ≤ (Real.exp (1 - Real.cos θ) + 251000 * Real.exp 1 / D) / ‖s‖ ^ 2
  apply (le_div_iff₀ (pow_pos hsn 2)).mpr
  rw [← mul_pow]
  apply (pow_le_pow_left₀ (by positivity) hP 2).trans
  calc
    _ = q ^ 2 + 2 * (q * E) + E * E := by ring
    _ ≤ q ^ 2 + 2 * (B * E) + E * (500 * B) := by
      linarith only [mul_le_mul_of_nonneg_right hqB hE, mul_le_mul_of_nonneg_left hEB hE]
    _ = _ := by
      rw [← hq₂, ← hB₂]
      dsimp only [E]
      ring

/-- The signed price of a shallow reflected pair, with no phase condition.
The correction constant `251000 * exp 1` is absolute, including in the depth
cutoff `C`. -/
public theorem shallowWeilPairCharge_le {D C β ε : ℝ} (hD : 1 ≤ D) (hC : 1 ≤ C)
    (hβ₀ : 1 / 2 < β) (hβ₁ : β < 1) (hε₀ : 0 ≤ ε) (hε₁ : ε ≤ 1)
    (hcC : (β - 1 / 2) * D ≤ C) (x : ℝ) :
    -(weightedTest ε D β x ^ 2).re ≤
      2 * (Real.cosh C - 1) *
        (Real.exp (1 - Real.cos (ε * min (C / D) (1 / 2))) + 251000 * Real.exp 1 / D) *
        (1 + 2 / D) * pairKernel D β x := by
  have hD₀ : 0 < D := by linarith
  refine charge_le_of_shallow_amplitude hD₀ hC hβ₀ hβ₁ hcC ?_ x ?_
  · positivity
  · exact phaseAmplitude_sq_le_shallow hD hβ₀ hβ₁ hε₀ hε₁ hcC x

end WeilGrayPair
