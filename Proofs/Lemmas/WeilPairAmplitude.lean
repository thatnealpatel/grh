module

public import Lemmas.WeilGrayPair
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Uniform amplitude of the finite Weil pair

Source: `1d56883c42befcdc4375f63d983f30dc76e2aba3:.godel/bob/weil-phase-bands.md`,
lines 13–45, in particular equation (2).

Scope: the uniform estimate for the exact inverse amplitude of the two finite
halves with the analytic complex square root, for `D ≥ 1`, `1/2 < β < 1`,
all real offsets, and `0 ≤ ε ≤ 1`. This discharges `hamp` for the single
reflected gray pair. Band membership still uses the exact phase.

Owning check session: `01a20f35-88fa-72a0-aedd-8c10c7068d1c`.
-/

open scoped ComplexConjugate

namespace WeilGrayPair

private theorem mul_exp_neg_le_one (t : ℝ) : t * Real.exp (-t) ≤ 1 := by
  rw [Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ (Real.exp_pos t), one_mul]
  linarith [Real.add_one_le_exp t]

private theorem root_exponent_parts (t y : ℝ) :
    let w := (1 - Complex.cosh ((t : ℂ) + (-y : ℝ) * Complex.I)) / 2
    w.re = (1 - Real.cosh t * Real.cos y) / 2 ∧ w.im = Real.sinh t * Real.sin y / 2 := by
  dsimp only
  rw [Complex.cosh_add, Complex.cosh_mul_I, Complex.sinh_mul_I]
  simp only [← Complex.ofReal_cosh, ← Complex.ofReal_sinh, ← Complex.ofReal_cos,
    ← Complex.ofReal_sin, Real.cos_neg, Real.sin_neg, Complex.div_ofNat_re,
    Complex.div_ofNat_im, Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im,
    Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
    Complex.ofReal_re, Complex.ofReal_im]
  constructor <;> ring

private theorem root_bounds {ε β : ℝ} (hε₀ : 0 ≤ ε) (hε₁ : ε ≤ 1)
    (hb₀ : 0 ≤ β - 1 / 2) (hb₁ : β - 1 / 2 ≤ 1 / 2) (x : ℝ) :
    let r := multiplierRoot ε (shiftedArgument β x)
    ‖r‖ ≤ Real.exp ((1 - Real.cos (ε / 2)) / 2) ∧
      ‖r - conj r‖ ≤ 4 * Real.exp (1 / 2) * (β - 1 / 2) := by
  dsimp only
  let t := ε * x
  let y := ε * (β - 1 / 2)
  let w := (1 - Complex.cosh ((t : ℂ) + (-y : ℝ) * Complex.I)) / 2
  have hr : multiplierRoot ε (shiftedArgument β x) = Complex.exp w := by
    have hz : (ε : ℂ) * shiftedArgument β x = (t : ℂ) + (-y : ℝ) * Complex.I := by
      apply Complex.ext
      · simp [t, y, shiftedArgument, Complex.mul_re]
      · simp [t, y, shiftedArgument, Complex.mul_im]
        ring
    simp only [multiplierRoot, hz, w]
  rw [hr, Complex.norm_exp]
  obtain ⟨hwre, hwim⟩ := root_exponent_parts t y
  change w.re = _ at hwre
  change w.im = _ at hwim
  have hy₀ : 0 ≤ y := mul_nonneg hε₀ hb₀
  have hy₁ : y ≤ ε / 2 := by
    calc
      y ≤ ε * (1 / 2) := mul_le_mul_of_nonneg_left hb₁ hε₀
      _ = _ := by ring
  have hyb : y ≤ β - 1 / 2 := by simpa [y] using mul_le_mul_of_nonneg_right hε₁ hb₀
  have hcos : 1 / 2 ≤ Real.cos y := by
    rw [← Real.cos_pi_div_three]
    exact Real.cos_le_cos_of_nonneg_of_le_pi hy₀ (by linarith [Real.pi_pos])
      (by linarith [Real.pi_gt_three])
  have hcos' : Real.cos (ε / 2) ≤ Real.cos y :=
    Real.cos_le_cos_of_nonneg_of_le_pi hy₀ (by linarith [Real.pi_gt_three]) hy₁
  have hT : 1 ≤ Real.cosh t := by
    rw [Real.cosh_eq]
    linarith [Real.add_one_le_exp t, Real.add_one_le_exp (-t)]
  constructor
  · rw [Real.exp_le_exp, hwre]
    have h := mul_le_mul_of_nonneg_right hT (show 0 ≤ Real.cos y by linarith)
    linarith
  · have habs : |Real.sinh t| ≤ Real.cosh t := by
      apply (sq_le_sq₀ (abs_nonneg _) (Real.cosh_pos t).le).mp
      rw [sq_abs]
      linarith [Real.cosh_sq_sub_sinh_sq t]
    have hw : w.re ≤ 1 / 2 + -(Real.cosh t / 4) := by
      rw [hwre]
      have h := mul_le_mul_of_nonneg_left hcos (Real.cosh_pos t).le
      linarith
    have hdecay : Real.exp w.re * Real.cosh t ≤ 4 * Real.exp (1 / 2) := by
      calc
        _ ≤ Real.exp (1 / 2 + -(Real.cosh t / 4)) * Real.cosh t :=
          mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hw) (Real.cosh_pos t).le
        _ = (4 * Real.exp (1 / 2)) *
            ((Real.cosh t / 4) * Real.exp (-(Real.cosh t / 4))) := by rw [Real.exp_add]; ring
        _ ≤ _ := mul_le_of_le_one_right (by positivity) (mul_exp_neg_le_one _)
    have hconj (z : ℂ) : ‖z - conj z‖ = 2 * |z.im| := by
      have hz : z - conj z = ((2 * z.im : ℝ) : ℂ) * Complex.I := by
        apply Complex.ext
        · simp [Complex.mul_re]
        · simp [Complex.mul_im]
          ring
      rw [hz, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_mul]
      norm_num
    rw [hconj, Complex.exp_im, abs_mul, abs_of_pos (Real.exp_pos _)]
    calc
      _ ≤ 2 * (Real.exp w.re * |w.im|) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left Real.abs_sin_le_abs (Real.exp_pos _).le) (by norm_num)
      _ = Real.exp w.re * |Real.sinh t| * |Real.sin y| := by
        rw [hwim, abs_div, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
        ring
      _ ≤ (Real.exp w.re * Real.cosh t) * (β - 1 / 2) :=
        mul_le_mul (mul_le_mul_of_nonneg_left habs (Real.exp_pos _).le)
          ((Real.abs_sin_le_abs : |Real.sin y| ≤ |y|).trans (by rwa [abs_of_nonneg hy₀]))
          (abs_nonneg _) (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_right hdecay hb₀

private theorem phaseAmplitude_sub_bound {c : ℝ} (hc : 0 < c) (X Y : ℂ) :
    ‖phaseAmplitude c ((Real.exp (c / 2) : ℂ) * X + (Real.exp (-c / 2) : ℂ) * Y) - X‖ ≤
      ‖Y - conj X‖ / (Real.exp c - 1) := by
  let δ := Y - conj X
  have hden : 0 < Real.exp c - Real.exp (-c) :=
    sub_pos.mpr (Real.exp_lt_exp.mpr (by linarith))
  have hdenC : ((Real.exp c - Real.exp (-c) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hden.ne'
  have hmul (u v : ℝ) : (Real.exp u : ℂ) * (Real.exp v : ℂ) = (Real.exp (u + v) : ℂ) := by
    rw [← Complex.ofReal_mul, ← Real.exp_add]
  have huu := hmul (c / 2) (c / 2)
  rw [add_halves] at huu
  have hvv := hmul (-c / 2) (-c / 2)
  rw [add_halves] at hvv
  have huv := hmul (c / 2) (-c / 2)
  rw [show c / 2 + -c / 2 = 0 by ring, Real.exp_zero, Complex.ofReal_one] at huv
  have heq : phaseAmplitude c ((Real.exp (c / 2) : ℂ) * X + (Real.exp (-c / 2) : ℂ) * Y) - X =
      (δ - (Real.exp (-c) : ℂ) * conj δ) / ((Real.exp c - Real.exp (-c) : ℝ) : ℂ) := by
    simp only [phaseAmplitude, map_add, map_mul, map_sub, Complex.conj_ofReal, Complex.conj_conj, δ]
    apply (eq_div_iff hdenC).mpr
    rw [sub_mul, div_mul_cancel₀ _ hdenC, Complex.ofReal_sub]
    linear_combination
      X * huu - conj X * huv + Y * huv - conj Y * hvv
  have hfactor : Real.exp c - Real.exp (-c) = (1 + Real.exp (-c)) * (Real.exp c - 1) := by
    have h := Real.exp_neg c
    have hh : Real.exp (-c) * Real.exp c = 1 := by rw [h, inv_mul_cancel₀ (Real.exp_pos c).ne']
    linear_combination -hh
  rw [heq, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hden]
  calc
    _ ≤ ((1 + Real.exp (-c)) * ‖δ‖) / (Real.exp c - Real.exp (-c)) := by
      apply div_le_div_of_nonneg_right _ hden.le
      calc
        _ ≤ ‖δ‖ + ‖(Real.exp (-c) : ℂ) * conj δ‖ := norm_sub_le _ _
        _ = _ := by
          rw [norm_mul, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs,
            abs_of_pos (Real.exp_pos _)]
          ring
    _ = _ := by rw [hfactor, mul_div_mul_left _ _ (by positivity)]

private noncomputable abbrev endpointExp (L : ℝ) (v : ℂ) : ℂ :=
  Complex.exp (-(L : ℂ) * v)

private theorem norm_endpointExp (L : ℝ) (v : ℂ) :
    ‖endpointExp L v‖ = Real.exp (-(L * v.re)) := by
  rw [endpointExp, Complex.norm_exp]
  simp [Complex.mul_re]

private theorem norm_endpointExp_le_one {L : ℝ} {v : ℂ} (hL : 0 ≤ L) (hv : 0 ≤ v.re) :
    ‖endpointExp L v‖ ≤ 1 := by
  rw [norm_endpointExp, ← Real.exp_zero, Real.exp_le_exp]
  exact neg_nonpos.mpr (mul_nonneg hL hv)

private theorem endpointIntegral_mul {L : ℝ} {v : ℂ} (hv : v ≠ 0) :
    endpointIntegral L v * v = 1 - endpointExp L v := by
  rw [endpointIntegral, ite_eq_right hv, div_mul_cancel₀ _ hv]

private theorem endpointIntegral_norm_le_div {L : ℝ} {v : ℂ} (hL : 0 ≤ L) (hv : 0 ≤ v.re)
    (hv₀ : v ≠ 0) : ‖endpointIntegral L v‖ ≤ 2 / ‖v‖ := by
  rw [endpointIntegral, ite_eq_right hv₀, norm_div]
  apply div_le_div_of_nonneg_right _ (norm_nonneg v)
  refine (norm_sub_le _ _).trans ?_
  rw [norm_one]
  linarith [norm_endpointExp_le_one hL hv]

private theorem quarter_le_norm {v : ℂ} (hv : 1 / 4 ≤ v.re) : 1 / 4 ≤ ‖v‖ :=
  hv.trans ((le_abs_self _).trans (Complex.abs_re_le_norm v))

private theorem offset_le_five_norm {v : ℂ} {x : ℝ} (hv : 1 / 4 ≤ v.re)
    (hi : |v.im| = |x|) : 1 + |x| ≤ 5 * ‖v‖ := by
  have hx := Complex.abs_im_le_norm v
  rw [hi] at hx
  linarith [quarter_le_norm hv]

private theorem endpointIntegral_norm_le_eight {L : ℝ} {v : ℂ}
    (hL : 0 ≤ L) (hv : 1 / 4 ≤ v.re) : ‖endpointIntegral L v‖ ≤ 8 := by
  have hn : 0 < ‖v‖ := lt_of_lt_of_le (by norm_num) (quarter_le_norm hv)
  apply (endpointIntegral_norm_le_div hL (by linarith) (norm_pos_iff.mp hn)).trans
  apply (div_le_iff₀ hn).mpr
  linarith [quarter_le_norm hv]

private theorem weighted_endpointIntegral_small {L : ℝ} {v : ℂ} {x : ℝ}
    (hL : 0 ≤ L) (hv : 1 / 4 ≤ v.re) (hi : |v.im| = |x|) :
    (1 + |x|) * ‖endpointIntegral L v‖ ≤ 10 := by
  have hn : 0 < ‖v‖ := lt_of_lt_of_le (by norm_num) (quarter_le_norm hv)
  calc
    _ ≤ (1 + |x|) * (2 / ‖v‖) :=
      mul_le_mul_of_nonneg_left (endpointIntegral_norm_le_div hL (by linarith)
        (norm_pos_iff.mp hn)) (by positivity)
    _ ≤ 10 := by
      rw [← mul_div_assoc, div_le_iff₀ hn]
      linarith [offset_le_five_norm hv hi]

private theorem weighted_endpointIntegral_full {L : ℝ} {v : ℂ} {x : ℝ}
    (hL : 0 ≤ L) (hv : 0 < v.re) (hi : |v.im| = |x|) :
    (1 + |x|) * ‖endpointIntegral L v‖ ≤ 2 * L + 2 := by
  have hv₀ : v ≠ 0 := by
    intro h
    simp [h] at hv
  have hn := norm_pos_iff.mpr hv₀
  have hL' : ‖endpointIntegral L v‖ ≤ 2 * L := by
    rw [endpointIntegral, ite_eq_right hv₀, norm_div, div_le_iff₀ hn]
    have hz : ‖-(L : ℂ) * v‖ = L * ‖v‖ := by
      rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hL]
    rw [mul_assoc, ← hz]
    by_cases hz₁ : ‖-(L : ℂ) * v‖ ≤ 1
    · simpa only [norm_sub_rev (1 : ℂ), Complex.exp_zero] using
        (Complex.norm_exp_sub_one_le hz₁)
    · calc
        _ ≤ ‖(1 : ℂ)‖ + ‖endpointExp L v‖ := norm_sub_le _ _
        _ ≤ 2 := by
          rw [norm_one]
          linarith [norm_endpointExp_le_one hL hv.le]
        _ ≤ _ := by linarith
  have hx : |x| * ‖endpointIntegral L v‖ ≤ 2 := by
    calc
      _ ≤ ‖v‖ * ‖endpointIntegral L v‖ :=
        mul_le_mul_of_nonneg_right (hi ▸ Complex.abs_im_le_norm v) (norm_nonneg _)
      _ ≤ ‖v‖ * (2 / ‖v‖) :=
        mul_le_mul_of_nonneg_left (endpointIntegral_norm_le_div hL hv.le hv₀) hn.le
      _ = _ := by rw [mul_div_cancel₀ _ hn.ne']
  rw [add_mul, one_mul]
  exact add_le_add hL' hx

-- Compare the two finite endpoints by factoring the exponential of their real displacement.
private theorem weighted_endpointIntegral_sub {L d x : ℝ} {v w : ℂ} (hL : 0 ≤ L)
    (hd : 0 ≤ d) (hv : 1 / 4 ≤ v.re) (hi : |v.im| = |x|) (hw : w = v + (d : ℂ)) :
    (1 + |x|) * ‖endpointIntegral L v - endpointIntegral L w‖ ≤ 60 * d := by
  have hwre : 1 / 4 ≤ w.re := by rw [hw, Complex.add_re, Complex.ofReal_re]; linarith
  have hvn : 0 < ‖v‖ := lt_of_lt_of_le (by norm_num) (quarter_le_norm hv)
  have hwn : 0 < ‖w‖ := lt_of_lt_of_le (by norm_num) (quarter_le_norm hwre)
  have hLdecay : L * ‖endpointExp L v‖ ≤ 4 := by
    have h := mul_le_mul_of_nonneg_left hv hL
    calc
      _ ≤ L * Real.exp (-(L / 4)) := by
        rw [norm_endpointExp]
        exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) hL
      _ = 4 * ((L / 4) * Real.exp (-(L / 4))) := by ring
      _ ≤ _ := by
        have h := mul_exp_neg_le_one (L / 4)
        linarith
  have hexp : endpointExp L w - endpointExp L v =
      endpointExp L v * ((Real.exp (-(L * d)) - 1 : ℝ) : ℂ) := by
    rw [hw, endpointExp, mul_add, show -(L : ℂ) * (d : ℂ) = ((-(L * d) : ℝ) : ℂ) by push_cast; ring,
      Complex.exp_add, ← Complex.ofReal_exp, Complex.ofReal_sub, Complex.ofReal_one]
    simp only [endpointExp, mul_sub, mul_one]
  have hE : ‖endpointExp L w - endpointExp L v‖ ≤ 4 * d := by
    have h₀ : Real.exp (-(L * d)) ≤ 1 := by
      rw [← Real.exp_zero, Real.exp_le_exp]
      exact neg_nonpos.mpr (mul_nonneg hL hd)
    rw [hexp, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (sub_nonpos.mpr h₀)]
    calc
      _ ≤ ‖endpointExp L v‖ * (L * d) :=
        mul_le_mul_of_nonneg_left (by linarith [Real.add_one_le_exp (-(L * d))]) (norm_nonneg _)
      _ = (L * ‖endpointExp L v‖) * d := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hLdecay hd
  have heq : endpointIntegral L v - endpointIntegral L w =
      ((endpointExp L w - endpointExp L v) + (d : ℂ) * endpointIntegral L w) / v := by
    apply (eq_div_iff (norm_pos_iff.mp hvn)).mpr
    rw [sub_mul, endpointIntegral_mul (norm_pos_iff.mp hvn),
      show (d : ℂ) = w - v by rw [hw]; ring, sub_mul]
    linear_combination -endpointIntegral_mul (L := L) (norm_pos_iff.mp hwn)
  have hnum : ‖(endpointExp L w - endpointExp L v) + (d : ℂ) * endpointIntegral L w‖ ≤ 12 * d := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hd]
    linarith [add_le_add hE (mul_le_mul_of_nonneg_left (endpointIntegral_norm_le_eight hL hwre) hd)]
  rw [heq, norm_div]
  calc
    _ ≤ (1 + |x|) * (12 * d / ‖v‖) :=
      mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hnum hvn.le) (by positivity)
    _ ≤ _ := by
      rw [← mul_div_assoc, div_le_iff₀ hvn]
      linarith [mul_le_mul_of_nonneg_right (offset_le_five_norm hv hi) (show 0 ≤ 12 * d by positivity)]

private theorem norm_carrier (x L : ℝ) : ‖Complex.exp ((x : ℂ) * (L : ℂ) * Complex.I)‖ = 1 := by
  rw [Complex.norm_exp]
  simp [Complex.mul_re, Complex.mul_im]

private theorem rootMajorant_le {ε : ℝ} (hε₀ : 0 ≤ ε) (hε₁ : ε ≤ 1) :
    Real.exp ((1 - Real.cos (ε / 2)) / 2) ≤ Real.exp (1 / 2) := by
  rw [Real.exp_le_exp]
  have hcos : 1 / 2 ≤ Real.cos (ε / 2) := by
    rw [← Real.cos_pi_div_three]
    exact Real.cos_le_cos_of_nonneg_of_le_pi (by linarith) (by linarith [Real.pi_pos])
      (by linarith [Real.pi_gt_three])
  linarith

private theorem quadratic_le_exp_sub_one {c D : ℝ} (hD : 0 ≤ D) (hc : D / 4 ≤ c) :
    D ^ 2 / 64 ≤ Real.exp c - 1 := by
  have h : 1 + D / 8 ≤ Real.exp (c / 2) := by linarith [Real.add_one_le_exp (c / 2)]
  have hsq := pow_le_pow_left₀ (show 0 ≤ 1 + D / 8 by positivity) h 2
  rw [show Real.exp (c / 2) ^ 2 = Real.exp c by rw [pow_two, ← Real.exp_add, add_halves]] at hsq
  nlinarith only [hsq, hD]

/-- Equation (2) for the exact inverse amplitude. The absolute constant
`500 * exp (1/2)` is independent of `D`, `β`, `x`, and `ε`. -/
public theorem phaseAmplitude_error_le {D β ε : ℝ} (hD : 1 ≤ D) (hβ₀ : 1 / 2 < β)
    (hβ₁ : β < 1) (hε₀ : 0 ≤ ε) (hε₁ : ε ≤ 1) (x : ℝ) :
    ‖phaseAmplitude ((β - 1 / 2) * D) (weightedTest ε D β x) -
      Complex.exp ((x : ℂ) * ((D / 2 : ℝ) : ℂ) * Complex.I) *
        multiplierRoot ε (shiftedArgument β x) / shiftedZero β x‖ ≤
      (500 * Real.exp (1 / 2)) / (D * (1 + |x|)) := by
  let b := β - 1 / 2
  let L := D / 2
  let c := b * D
  let s := shiftedZero β x
  let v := 1 - s
  let r := multiplierRoot ε (shiftedArgument β x)
  let e := Complex.exp ((x : ℂ) * (L : ℂ) * Complex.I)
  let X := e * r * endpointIntegral L s
  let Y := conj e * r * endpointIntegral L v
  let P := phaseAmplitude c (weightedTest ε D β x)
  let T := 1 + |x|
  let M := Real.exp (1 / 2)
  have hD₀ : 0 < D := by linarith
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hb : 0 < b := sub_pos.mpr hβ₀
  have hc : 0 < c := mul_pos hb hD₀
  have hden : 0 < Real.exp c - 1 := sub_pos.mpr (by simpa using Real.exp_lt_exp.mpr hc)
  have hT : 0 < T := by dsimp [T]; positivity
  have hM : 0 < M := Real.exp_pos _
  have hs : 1 / 4 ≤ s.re := by change 1 / 4 ≤ β; linarith
  have hv : 0 < v.re := by simp [v, s, shiftedZero]; linarith
  have hsi : |s.im| = |x| := rfl
  have hvi : |v.im| = |x| := by simp [v, s, shiftedZero]
  have hsn : 0 < ‖s‖ := lt_of_lt_of_le (by norm_num) (quarter_le_norm hs)
  have he : ‖e‖ = 1 := norm_carrier x L
  have hce : ‖conj e‖ = 1 := (Complex.norm_conj e).trans he
  have hZ : weightedTest ε D β x = (Real.exp (c / 2) : ℂ) * X + (Real.exp (-c / 2) : ℂ) * Y := by
    have hec : conj e = Complex.exp (-((x : ℂ) * (L : ℂ) * Complex.I)) := by
      dsimp only [e]
      rw [← Complex.exp_conj]
      simp [map_mul, Complex.conj_I, mul_neg]
    simp only [weightedTest, testTransform, X, Y, e, hec, r, v, s, c, b, L]
    ring
  obtain ⟨hr, hrc⟩ := root_bounds hε₀ hε₁ hb.le (by linarith : β - 1 / 2 ≤ 1 / 2) x
  change ‖r‖ ≤ _ at hr
  change ‖r - conj r‖ ≤ 4 * M * b at hrc
  have hrM : ‖r‖ ≤ M := hr.trans (rootMajorant_le hε₀ hε₁)
  have hPX : T * ‖P - X‖ ≤ T * ‖Y - conj X‖ / (Real.exp c - 1) := by
    rw [mul_div_assoc]
    apply mul_le_mul_of_nonneg_left _ hT.le
    change ‖phaseAmplitude c (weightedTest ε D β x) - X‖ ≤ _
    rw [hZ]
    exact phaseAmplitude_sub_bound hc X Y
  have hPX' : T * ‖P - X‖ ≤ 384 * M / D := by
    by_cases hnear : β ≤ 3 / 4
    · -- The two reflected endpoints and the two roots coalesce at the line.
      have hvq : 1 / 4 ≤ v.re := by simp [v, s, shiftedZero]; linarith
      have hw : conj s = v + ((2 * b : ℝ) : ℂ) := by
        apply Complex.ext
        · simp [v, s, b, shiftedZero]
          ring
        · simp [v, s, shiftedZero]
      have hws : 1 / 4 ≤ (conj s).re := by simpa only [Complex.conj_re] using hs
      have hwi : |(conj s).im| = |x| := by simpa only [Complex.conj_im, abs_neg] using hsi
      have hd := weighted_endpointIntegral_sub hL (show 0 ≤ 2 * b by positivity) hvq hvi hw
      have hws' := weighted_endpointIntegral_small hL hws hwi
      change T * ‖endpointIntegral L v - endpointIntegral L (conj s)‖ ≤ 60 * (2 * b) at hd
      change T * ‖endpointIntegral L (conj s)‖ ≤ 10 at hws'
      have hs₀ := norm_pos_iff.mp hsn
      have hcs₀ : conj s ≠ 0 := by simpa using hs₀
      have hca : conj (endpointIntegral L s) = endpointIntegral L (conj s) := by
        simp [endpointIntegral, hs₀, hcs₀, ← Complex.exp_conj]
      have hδ : Y - conj X = conj e *
          (r * (endpointIntegral L v - endpointIntegral L (conj s)) +
            (r - conj r) * endpointIntegral L (conj s)) := by
        simp only [X, Y, map_mul, hca]
        ring
      have hδ' : T * ‖Y - conj X‖ ≤ 160 * M * b := by
        rw [hδ, norm_mul, hce, one_mul]
        calc
          _ ≤ T * (‖r * (endpointIntegral L v - endpointIntegral L (conj s))‖ +
              ‖(r - conj r) * endpointIntegral L (conj s)‖) :=
            mul_le_mul_of_nonneg_left (norm_add_le _ _) hT.le
          _ = ‖r‖ * (T * ‖endpointIntegral L v - endpointIntegral L (conj s)‖) +
              ‖r - conj r‖ * (T * ‖endpointIntegral L (conj s)‖) := by
            rw [norm_mul, norm_mul]
            ring
          _ ≤ M * (60 * (2 * b)) + (4 * M * b) * 10 :=
            add_le_add (mul_le_mul hrM hd (by positivity) hM.le)
              (mul_le_mul hrc hws' (by positivity) (by positivity))
          _ = _ := by ring
      have hlinear : b * D ≤ Real.exp c - 1 := by change c ≤ _; linarith [Real.add_one_le_exp c]
      calc
        _ ≤ (160 * M * b) / (Real.exp c - 1) :=
          hPX.trans (div_le_div_of_nonneg_right hδ' hden.le)
        _ ≤ (160 * M) / D := by
          rw [div_le_div_iff₀ hden hD₀, mul_assoc]
          exact mul_le_mul_of_nonneg_left hlinear (by positivity)
        _ ≤ _ := div_le_div_of_nonneg_right (by linarith) hD₀.le
    · -- Away from the line the exponential denominator pays for both endpoints.
      have hDc : D / 4 ≤ c := by
        have h := mul_le_mul_of_nonneg_right (show 1 / 4 ≤ b by dsimp [b]; linarith) hD₀.le
        dsimp [c]
        linarith
      have hquadratic := quadratic_le_exp_sub_one hD₀.le hDc
      have hL' : 2 * L + 2 ≤ 3 * D := by dsimp [L]; linarith
      have hs' : T * ‖endpointIntegral L s‖ ≤ 3 * D :=
        (weighted_endpointIntegral_full hL (by linarith) hsi).trans hL'
      have hv' : T * ‖endpointIntegral L v‖ ≤ 3 * D :=
        (weighted_endpointIntegral_full hL hv hvi).trans hL'
      have hδ : T * ‖Y - conj X‖ ≤ 6 * M * D := by
        calc
          _ ≤ T * (‖Y‖ + ‖conj X‖) := mul_le_mul_of_nonneg_left (norm_sub_le _ _) hT.le
          _ = ‖r‖ * (T * ‖endpointIntegral L v‖ + T * ‖endpointIntegral L s‖) := by
            simp only [Complex.norm_conj X, X, Y, norm_mul, he, hce, one_mul]
            ring
          _ ≤ M * (3 * D + 3 * D) :=
            mul_le_mul hrM (add_le_add hv' hs') (by positivity) hM.le
          _ = _ := by ring
      calc
        _ ≤ (6 * M * D) / (Real.exp c - 1) :=
          hPX.trans (div_le_div_of_nonneg_right hδ hden.le)
        _ ≤ _ := by
          rw [div_le_div_iff₀ hden hD₀]
          calc
            _ = (384 * M) * (D ^ 2 / 64) := by ring
            _ ≤ _ := mul_le_mul_of_nonneg_left hquadratic (by positivity)
  have hX : T * ‖X - e * r / s‖ ≤ 20 * M / D := by
    have htail : ‖endpointExp L s‖ ≤ 4 / D := by
      have h : D / 4 ≤ L * s.re := by
        change D / 4 ≤ (D / 2) * β
        nlinarith only [mul_nonneg (show 0 ≤ β - 1 / 2 by linarith) hD₀.le]
      calc
        _ ≤ Real.exp (-(D / 4)) := by
          rw [norm_endpointExp, Real.exp_le_exp]
          exact neg_le_neg h
        _ ≤ 4 / D := by
          apply (le_div_iff₀ hD₀).mpr
          nlinarith only [mul_exp_neg_le_one (D / 4)]
    have hXeq : X - e * r / s = -(e * r * endpointExp L s / s) := by
      simp only [X, endpointIntegral, ite_eq_right (norm_pos_iff.mp hsn), endpointExp, div_eq_mul_inv]
      ring
    rw [hXeq, norm_neg, norm_div, norm_mul, norm_mul, he, one_mul]
    calc
      _ = (T / ‖s‖) * (‖r‖ * ‖endpointExp L s‖) := by ring
      _ ≤ 5 * (M * (4 / D)) :=
        mul_le_mul ((div_le_iff₀ hsn).mpr (offset_le_five_norm hs hsi))
          (mul_le_mul hrM htail (by positivity) hM.le) (by positivity) (by norm_num)
      _ = _ := by ring
  change ‖P - e * r / s‖ ≤ (500 * M) / (D * T)
  apply (le_div_iff₀ (mul_pos hD₀ hT)).mpr
  have hsum : T * ‖P - e * r / s‖ ≤ 500 * M / D := by
    rw [show P - e * r / s = (P - X) + (X - e * r / s) by ring]
    calc
      _ ≤ T * (‖P - X‖ + ‖X - e * r / s‖) := mul_le_mul_of_nonneg_left (norm_add_le _ _) hT.le
      _ ≤ 384 * M / D + 20 * M / D := by rw [mul_add]; exact add_le_add hPX' hX
      _ ≤ _ := by
        rw [← add_div]
        exact div_le_div_of_nonneg_right (by linarith) hD₀.le
  have hsum' := (le_div_iff₀ hD₀).mp hsum
  simpa only [mul_assoc, mul_left_comm, mul_comm] using hsum'

/-- A finite amplitude coefficient `G + C/D`, where `G` is the strip bound for
`|gε|` and the error constant is absolute. -/
@[expose] public noncomputable def amplitudeBudget (ε D : ℝ) : ℝ :=
  Real.exp (1 - Real.cos (ε / 2)) + 251000 * Real.exp 1 / D

/-- The squared, normalized form of the amplitude estimate, with exactly the
coercions and normalization required by `grayWeilPairCharge_le`. -/
public theorem phaseAmplitude_sq_le {D β ε : ℝ} (hD : 1 ≤ D) (hβ₀ : 1 / 2 < β)
    (hβ₁ : β < 1) (hε₀ : 0 ≤ ε) (hε₁ : ε ≤ 1) (x : ℝ) :
    ‖phaseAmplitude ((β - 1 / 2) * D) (weightedTest ε D β x)‖ ^ 2 ≤
      amplitudeBudget ε D / ‖shiftedZero β x‖ ^ 2 := by
  let s := shiftedZero β x
  let r := multiplierRoot ε (shiftedArgument β x)
  let e := Complex.exp ((x : ℂ) * ((D / 2 : ℝ) : ℂ) * Complex.I)
  let P := phaseAmplitude ((β - 1 / 2) * D) (weightedTest ε D β x)
  let T := 1 + |x|
  let q := Real.exp ((1 - Real.cos (ε / 2)) / 2)
  let M := Real.exp (1 / 2)
  let E := 500 * M / D
  have hD₀ : 0 < D := by linarith
  have hT : 0 < T := by dsimp [T]; positivity
  have hE : 0 ≤ E := by dsimp [E, M]; positivity
  have hsn : 0 < ‖s‖ :=
    lt_of_lt_of_le (by norm_num) (quarter_le_norm (show 1 / 4 ≤ s.re by change 1 / 4 ≤ β; linarith))
  have hsT : ‖s‖ ≤ T := by
    conv_lhs => rw [← Complex.re_add_im s]
    calc
      _ ≤ ‖(s.re : ℂ)‖ + ‖(s.im : ℂ) * Complex.I‖ := norm_add_le _ _
      _ = β + |x| := by
        simp [s, shiftedZero, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos (show 0 < β by linarith)]
      _ ≤ T := by dsimp [T]; linarith
  have hErr : ‖P - e * r / s‖ * ‖s‖ ≤ E := by
    have h : ‖P - e * r / s‖ ≤ (500 * M) / (D * T) :=
      phaseAmplitude_error_le hD hβ₀ hβ₁ hε₀ hε₁ x
    calc
      _ ≤ ‖P - e * r / s‖ * T := mul_le_mul_of_nonneg_left hsT (norm_nonneg _)
      _ ≤ ((500 * M) / (D * T)) * T := mul_le_mul_of_nonneg_right h hT.le
      _ = E := by rw [← div_div, div_mul_cancel₀ _ hT.ne']
  have hMain : ‖e * r / s‖ * ‖s‖ ≤ q := by
    have he : ‖e‖ = 1 := norm_carrier x (D / 2)
    rw [norm_div, div_mul_cancel₀ _ hsn.ne', norm_mul, he, one_mul]
    exact (root_bounds hε₀ hε₁ (by linarith) (by linarith) x).1
  have hP : ‖P‖ * ‖s‖ ≤ q + E := by
    have htri := norm_add_le (P - e * r / s) (e * r / s)
    rw [sub_add_cancel] at htri
    calc
      _ ≤ (‖P - e * r / s‖ + ‖e * r / s‖) * ‖s‖ := mul_le_mul_of_nonneg_right htri hsn.le
      _ ≤ _ := by rw [add_mul, add_comm q E]; exact add_le_add hErr hMain
  change ‖P‖ ^ 2 ≤ amplitudeBudget ε D / ‖s‖ ^ 2
  apply (le_div_iff₀ (pow_pos hsn 2)).mpr
  rw [← mul_pow]
  apply (pow_le_pow_left₀ (by positivity) hP 2).trans
  have hqM : q ≤ M := rootMajorant_le hε₀ hε₁
  have hEM : E ≤ 500 * M := by
    apply (div_le_iff₀ hD₀).mpr
    exact le_mul_of_one_le_right (by dsimp [M]; positivity) hD
  have hq₂ : q ^ 2 = Real.exp (1 - Real.cos (ε / 2)) := by
    dsimp only [q]
    rw [pow_two, ← Real.exp_add, add_halves]
  have hM₂ : M ^ 2 = Real.exp 1 := by
    dsimp only [M]
    rw [pow_two, ← Real.exp_add, add_halves]
  calc
    _ = q ^ 2 + 2 * (q * E) + E * E := by ring
    _ ≤ q ^ 2 + 2 * (M * E) + E * (500 * M) := by
      linarith only [mul_le_mul_of_nonneg_right hqM hE, mul_le_mul_of_nonneg_left hEM hE]
    _ = _ := by
      rw [amplitudeBudget, ← hq₂, ← hM₂]
      dsimp only [E]
      ring

/-- The finite gray-pair price with the exact amplitude hypothesis discharged. -/
public theorem grayWeilPairCharge_le_of_small_epsilon {D R β K ε : ℝ}
    (hD : 1 ≤ D) (hR : 0 < R) (hβ₀ : 1 / 2 < β) (hβ₁ : β < 1) (hK : 1 ≤ K)
    (hε₀ : 0 ≤ ε) (hε₁ : ε ≤ 1) (x : ℝ)
    (hgray : IsGray K ((β - 1 / 2) * D)
      (phaseAmplitude ((β - 1 / 2) * D) (weightedTest ε D β x))) :
    -(weightedTest ε D β x ^ 2).re / R ≤
      2 * (K - 1) * amplitudeBudget ε D * (1 + 2 / D) / R * pairKernel D β x := by
  have hD₀ : 0 < D := by linarith
  have hA : 0 ≤ amplitudeBudget ε D := by unfold amplitudeBudget; positivity
  exact grayWeilPairCharge_le hD₀ hR hβ₀ hβ₁ hK hA ε x hgray
    (phaseAmplitude_sq_le hD hβ₀ hβ₁ hε₀ hε₁ x)

end WeilGrayPair
