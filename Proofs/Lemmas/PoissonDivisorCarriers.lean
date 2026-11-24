module

public import Lemmas.PoissonCarrierFreezing
public import Lemmas.ZetaZeroSummability
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Positive-width Poisson averaging of the uncut divisor carriers

Sources: `4c47eae3:.godel/bob/uncut-poisson-transfer.md:9–15` (the summed
application) and `fb2dc2ff:.godel/bob/uncut-defect-price.md:32–43` (the
real-axis envelopes and freezing step). Lean baseline: `e97a8a47`.

Scope: only the explicit low and oscillatory terms, with the depth switch,
ordinates, normalization and smoothing parameter held fixed in the average.
This does not prove an estimate for the omitted screen remainder, any shifted
contour identity, or the full screen transfer.

Owning check session: `01a20e90-1953-703f-a5c5-0300053aba36`.
-/

open MeasureTheory

namespace PoissonDivisorCarriers

open SignedPoissonDefect (poisson kernel)

/-- The inverse-square majorant `ℓ`. -/
@[expose] public noncomputable def envelope (x : ℝ) : ℝ := (1 / 4 + x ^ 2)⁻¹

/-- The real-axis smoothing factor `gε`. -/
@[expose] public noncomputable def smoothing (ε x : ℝ) : ℝ :=
  Real.exp (1 - Real.cosh (ε * x))

/-- The baseline subtracted only at shallow depth. -/
@[expose] public noncomputable def baseline : ℝ := 2 - 2 / Real.exp 1

/-- The signed amplitude; the supporting depth `bD = 1` is shallow. -/
@[expose] public noncomputable def depthCoefficient (c : ℝ) : ℝ :=
  if c ≤ 1 then 2 * Real.cosh c else -2 * Real.sinh 1 * Real.exp (1 - c)

/-- The low-frequency summand `L_b`. -/
@[expose] public noncomputable def low (ε D b x : ℝ) : ℝ :=
  if b * D ≤ 1 then (2 * smoothing ε x - baseline) * envelope x else 0

/-- The oscillatory summand `G_b`. The inverse square of `1/2 + ix` supplies
both `ℓ` and the phase `−2 arctan (2x)`. -/
@[expose] public noncomputable def oscillatory (ε D b x : ℝ) : ℝ :=
  depthCoefficient (b * D) *
    (Complex.exp (↑(D * x) * Complex.I) *
      ((smoothing ε x : ℂ) * ((1 / 2 : ℂ) + (x : ℂ) * Complex.I)⁻¹ ^ 2)).re

/-- Count a right member with its full multiplicity and a line zero with half. -/
@[expose] public noncomputable def pairWeight (b : ℝ) (m : ℕ) : ℝ :=
  if b = 0 then (m : ℝ) / 2 else m

private theorem envelope_pos (x : ℝ) : 0 < envelope x := by
  unfold envelope
  positivity

private theorem one_add_sq_inv_le_envelope (x : ℝ) : (1 + x ^ 2)⁻¹ ≤ envelope x := by
  unfold envelope
  exact inv_anti₀ (by positivity) (by linarith)

private theorem envelope_le_quad (x : ℝ) : envelope x ≤ 4 / (1 + x ^ 2) := by
  rw [envelope, ← one_div]
  apply (div_le_div_iff₀ (by positivity) (by positivity)).2
  nlinarith [sq_nonneg x]

private theorem smoothing_pos (ε x : ℝ) : 0 < smoothing ε x := Real.exp_pos _

private theorem smoothing_le_one (ε x : ℝ) : smoothing ε x ≤ 1 := by
  have h : Real.cosh 0 ≤ Real.cosh (ε * x) := Real.cosh_le_cosh.mpr (by simpa only [abs_zero] using abs_nonneg (ε * x))
  rw [Real.cosh_zero] at h
  exact Real.exp_le_one_iff.mpr (sub_nonpos.mpr h)

private theorem abs_sinh_le_cosh (u : ℝ) : |Real.sinh u| ≤ Real.cosh u := by
  apply abs_le.mpr
  constructor
  · have h := Real.sinh_lt_cosh (-u)
    rw [Real.sinh_neg, Real.cosh_neg] at h
    linarith
  · exact (Real.sinh_lt_cosh u).le

private theorem hasDerivAt_smoothing (ε x : ℝ) :
    HasDerivAt (smoothing ε) (-(Real.sinh (ε * x) * ε) * smoothing ε x) x := by
  have hd : HasDerivAt (smoothing ε)
      (smoothing ε x * -(Real.sinh (ε * x) * ε)) x := by
    exact ((((hasDerivAt_id x).const_mul ε).cosh).const_sub 1).exp.congr_deriv (by simp [smoothing])
  exact hd.congr_deriv (mul_comm ..)

private theorem smoothing_derivative_bound (ε x : ℝ) :
    |-(Real.sinh (ε * x) * ε) * smoothing ε x| ≤ |ε| := by
  have hg : 0 ≤ smoothing ε x := (Real.exp_pos _).le
  have hcosh : Real.cosh (ε * x) ≤ Real.exp (Real.cosh (ε * x) - 1) := by
    linarith [Real.add_one_le_exp (Real.cosh (ε * x) - 1)]
  rw [abs_mul, abs_neg, abs_mul, abs_of_nonneg hg]
  calc
    _ = |ε| * (|Real.sinh (ε * x)| * smoothing ε x) := by ring
    _ ≤ |ε| * (Real.exp (Real.cosh (ε * x) - 1) * smoothing ε x) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right ((abs_sinh_le_cosh _).trans hcosh) hg) (abs_nonneg _)
    _ = |ε| := by
      rw [smoothing, ← Real.exp_add, show Real.cosh (ε * x) - 1 + (1 - Real.cosh (ε * x)) = 0 by ring,
        Real.exp_zero, mul_one]

private theorem hasDerivAt_envelope (x : ℝ) :
    HasDerivAt envelope (-(2 * x) / (1 / 4 + x ^ 2) ^ 2) x := by
  let a (y : ℝ) := 1 / 4 + y ^ 2
  have ha : HasDerivAt a (2 * x) x := by
    simpa only [Pi.pow_apply, id_eq, Nat.cast_ofNat, Nat.reduceSub, pow_one, mul_one] using
      (((hasDerivAt_id x).pow 2).const_add (1 / 4 : ℝ))
  have hn : a x ≠ 0 := ne_of_gt (by dsimp [a]; positivity)
  exact ((hasDerivAt_inv hn).comp x ha).congr_deriv (by rw [div_eq_mul_inv]; ring)

private theorem envelope_derivative_bound (x : ℝ) :
    |-(2 * x) / (1 / 4 + x ^ 2) ^ 2| ≤ 2 * envelope x := by
  have hd : 0 < (1 / 4 : ℝ) + x ^ 2 := by positivity
  have hx : |x| ≤ 1 / 4 + x ^ 2 := by nlinarith [sq_nonneg (|x| - 1 / 2), sq_abs x]
  rw [abs_div, abs_neg, abs_mul, abs_of_pos (show (0 : ℝ) < 2 by norm_num),
    abs_of_pos (sq_pos_of_pos hd), envelope]
  calc
    _ ≤ 2 * (1 / 4 + x ^ 2) / (1 / 4 + x ^ 2) ^ 2 := by gcongr
    _ = _ := by field_simp

private noncomputable def lowEnv (ε x : ℝ) : ℂ :=
  ↑((2 * smoothing ε x - baseline) * envelope x)

private noncomputable def phaseDenom (x : ℝ) : ℂ := (1 / 2 : ℂ) + (x : ℂ) * Complex.I

private noncomputable def highEnv (ε x : ℝ) : ℂ :=
  (smoothing ε x : ℂ) * (phaseDenom x)⁻¹ ^ 2

private theorem phaseDenom_norm_sq (x : ℝ) : ‖phaseDenom x‖ ^ 2 = 1 / 4 + x ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  norm_num [phaseDenom, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  ring

private theorem phaseDenom_ne_zero (x : ℝ) : phaseDenom x ≠ 0 := by
  intro h
  have hsq := phaseDenom_norm_sq x
  simp only [h, norm_zero, zero_pow (by decide : 2 ≠ 0)] at hsq
  linarith [sq_nonneg x]

private theorem phaseDenom_inv_norm_sq (x : ℝ) : ‖(phaseDenom x)⁻¹‖ ^ 2 = envelope x := by
  rw [norm_inv, inv_pow, phaseDenom_norm_sq, envelope]

/-- The complex carrier has exactly the real phase in the divisor formula. -/
public theorem oscillatory_eq_cos (ε D b x : ℝ) :
    oscillatory ε D b x = depthCoefficient (b * D) * smoothing ε x * envelope x *
      Real.cos (D * x - 2 * Real.arctan (2 * x)) := by
  have hre : (phaseDenom x).re = 1 / 2 := by simp [phaseDenom, Complex.mul_re]
  have him : (phaseDenom x).im = x := by simp [phaseDenom, Complex.mul_im]
  have hpos : 0 < (phaseDenom x).re := by rw [hre]; norm_num
  have harg : (phaseDenom x).arg = Real.arctan (2 * x) := by
    rw [← Real.arctan_tan (Complex.neg_pi_div_two_lt_arg_iff.mpr (Or.inl hpos))
        (Complex.arg_lt_pi_div_two_iff.mpr (Or.inl hpos)), Complex.tan_arg, hre, him]
    congr 1
    ring
  have hpolar := Complex.norm_mul_exp_arg_mul_I (phaseDenom x)
  rw [harg] at hpolar
  have hinv : (phaseDenom x)⁻¹ ^ 2 = (envelope x : ℂ) *
      Complex.exp (↑(-(2 * Real.arctan (2 * x))) * Complex.I) := by
    calc
      _ = ((‖phaseDenom x‖ : ℂ) * Complex.exp (↑(Real.arctan (2 * x)) * Complex.I))⁻¹ ^ 2 :=
        congrArg (fun z : ℂ ↦ z⁻¹ ^ 2) hpolar.symm
      _ = (↑(‖phaseDenom x‖⁻¹ ^ 2) : ℂ) *
          Complex.exp (↑(-(2 * Real.arctan (2 * x))) * Complex.I) := by
        rw [Complex.ofReal_pow, Complex.ofReal_inv, mul_inv, mul_pow, ← Complex.exp_neg,
          ← Complex.exp_nat_mul]
        congr 2
        push_cast
        ring
      _ = _ := by rw [← norm_inv, phaseDenom_inv_norm_sq]
  change depthCoefficient (b * D) * (Complex.exp (↑(D * x) * Complex.I) *
    ((smoothing ε x : ℂ) * (phaseDenom x)⁻¹ ^ 2)).re = _
  rw [hinv]
  have hprod : Complex.exp (↑(D * x) * Complex.I) *
      ((smoothing ε x : ℂ) * ((envelope x : ℂ) *
        Complex.exp (↑(-(2 * Real.arctan (2 * x))) * Complex.I))) =
      (smoothing ε x : ℂ) * ((envelope x : ℂ) *
        Complex.exp (↑(D * x - 2 * Real.arctan (2 * x)) * Complex.I)) := by
    rw [show (↑(D * x - 2 * Real.arctan (2 * x)) : ℂ) * Complex.I =
      ↑(D * x) * Complex.I + ↑(-(2 * Real.arctan (2 * x))) * Complex.I by push_cast; ring,
      Complex.exp_add]
    ring
  rw [hprod, Complex.re_ofReal_mul, Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]
  ring

private theorem phaseDenom_inv_norm_le (x : ℝ) : ‖(phaseDenom x)⁻¹‖ ≤ 2 := by
  have h : 1 / 2 ≤ ‖phaseDenom x‖ := by
    have hn := norm_nonneg (phaseDenom x)
    have hs := phaseDenom_norm_sq x
    by_contra! hc
    nlinarith only [hn, hs, sq_nonneg x, mul_pos (sub_pos.mpr hc)
      (show 0 < ‖phaseDenom x‖ + 1 / 2 by positivity)]
  rw [norm_inv]
  simpa using inv_anti₀ (by norm_num : (0 : ℝ) < 1 / 2) h

private theorem hasDerivAt_highDenom (x : ℝ) :
    HasDerivAt (fun u : ℝ ↦ (phaseDenom u)⁻¹ ^ 2)
      (-2 * Complex.I * (phaseDenom x)⁻¹ ^ 3) x := by
  have hz : HasDerivAt phaseDenom Complex.I x := by
    change HasDerivAt (fun y : ℝ ↦ (1 / 2 : ℂ) + (y : ℂ) * Complex.I) _ x
    simpa only [id_eq, Complex.ofReal_one, one_mul] using
      (((hasDerivAt_id x).ofReal_comp).mul_const Complex.I).const_add (1 / 2 : ℂ)
  convert ((hz.inv (phaseDenom_ne_zero x)).pow 2) using 1
  change _ = (2 : ℂ) * (phaseDenom x)⁻¹ ^ (2 - 1) * (-Complex.I / phaseDenom x ^ 2)
  rw [div_eq_mul_inv, ← inv_pow]
  norm_num
  ring

private theorem smooth_contDiff (ε : ℝ) : ContDiff ℝ 1 (smoothing ε) := by
  change ContDiff ℝ 1 (fun x : ℝ ↦ Real.exp (1 - Real.cosh (ε * x)))
  exact (contDiff_const.sub (Real.contDiff_cosh.comp (by fun_prop))).exp

private theorem lowEnv_contDiff (ε : ℝ) : ContDiff ℝ 1 (lowEnv ε) := by
  have hg := smooth_contDiff ε
  have he : ContDiff ℝ 1 envelope := by
    unfold envelope
    apply ContDiff.inv (by fun_prop)
    intro x
    positivity
  exact Complex.ofRealCLM.contDiff.comp (((contDiff_const.mul hg).sub contDiff_const).mul he)

private theorem highEnv_contDiff (ε : ℝ) : ContDiff ℝ 1 (highEnv ε) := by
  have hz : ContDiff ℝ 1 phaseDenom := by
    unfold phaseDenom
    exact contDiff_const.add (Complex.ofRealCLM.contDiff.mul contDiff_const)
  exact (Complex.ofRealCLM.contDiff.comp (smooth_contDiff ε)).mul
    ((hz.inv phaseDenom_ne_zero).pow 2)

private theorem lowCoeff_bound (ε x : ℝ) : |2 * smoothing ε x - baseline| ≤ 2 + |baseline| := by
  apply (abs_sub _ _).trans
  rw [abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ 2 by norm_num),
    abs_of_pos (smoothing_pos ε x)]
  linarith [smoothing_le_one ε x]

private theorem lowEnv_value (ε x : ℝ) : ‖lowEnv ε x‖ ≤ (2 + |baseline|) * envelope x := by
  rw [lowEnv, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_pos (envelope_pos x)]
  exact mul_le_mul_of_nonneg_right (lowCoeff_bound ε x) (envelope_pos x).le

private theorem lowEnv_deriv (ε x : ℝ) :
    ‖deriv (lowEnv ε) x‖ ≤ (2 * |ε| + 2 * (2 + |baseline|)) * envelope x := by
  let g' := -(Real.sinh (ε * x) * ε) * smoothing ε x
  let e' := -(2 * x) / (1 / 4 + x ^ 2) ^ 2
  have hd : HasDerivAt (lowEnv ε)
      (↑(2 * g' * envelope x + (2 * smoothing ε x - baseline) * e') : ℂ) x :=
    ((((hasDerivAt_smoothing ε x).const_mul 2).sub_const baseline).mul
      (hasDerivAt_envelope x)).ofReal_comp
  rw [hd.deriv, Complex.norm_real, Real.norm_eq_abs]
  calc
    _ ≤ |2 * g' * envelope x| + |(2 * smoothing ε x - baseline) * e'| := abs_add_le ..
    _ ≤ 2 * |ε| * envelope x + (2 + |baseline|) * (2 * envelope x) := by
      simp only [abs_mul, abs_of_pos (envelope_pos x), abs_of_nonneg (show (0 : ℝ) ≤ 2 by norm_num)]
      have hg : |g'| ≤ |ε| := smoothing_derivative_bound ε x
      have he : |e'| ≤ 2 * envelope x := envelope_derivative_bound x
      have hk := lowCoeff_bound ε x
      gcongr
      exact (envelope_pos x).le
    _ = _ := by ring

private theorem highEnv_value (ε x : ℝ) : ‖highEnv ε x‖ ≤ envelope x := by
  rw [highEnv, norm_mul, Complex.norm_real, Real.norm_of_nonneg (smoothing_pos ε x).le,
    norm_pow, phaseDenom_inv_norm_sq]
  exact mul_le_of_le_one_left (envelope_pos x).le (smoothing_le_one ε x)

private theorem highEnv_deriv (ε x : ℝ) :
    ‖deriv (highEnv ε) x‖ ≤ (|ε| + 4) * envelope x := by
  let g' := -(Real.sinh (ε * x) * ε) * smoothing ε x
  have hd : HasDerivAt (highEnv ε)
      ((g' : ℂ) * (phaseDenom x)⁻¹ ^ 2 +
        (smoothing ε x : ℂ) * (-2 * Complex.I * (phaseDenom x)⁻¹ ^ 3)) x :=
    ((hasDerivAt_smoothing ε x).ofReal_comp).mul (hasDerivAt_highDenom x)
  rw [hd.deriv]
  refine (norm_add_le ..).trans ?_
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_pow, phaseDenom_inv_norm_sq,
    norm_mul, Complex.norm_real, Real.norm_of_nonneg (smoothing_pos ε x).le]
  have hz : ‖-2 * Complex.I * (phaseDenom x)⁻¹ ^ 3‖ ≤ 4 * envelope x := by
    rw [norm_mul, norm_mul, Complex.norm_I, mul_one, norm_neg, norm_pow,
      pow_succ _ 2, phaseDenom_inv_norm_sq]
    have hn : ‖(2 : ℂ)‖ = 2 := by simp
    rw [hn]
    calc
      _ ≤ 2 * (envelope x * 2) := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (phaseDenom_inv_norm_le x) (envelope_pos x).le) (by norm_num)
      _ = _ := by ring
  calc
    _ ≤ |ε| * envelope x + 1 * (4 * envelope x) :=
      add_le_add (mul_le_mul_of_nonneg_right (smoothing_derivative_bound ε x) (envelope_pos x).le)
        (mul_le_mul (smoothing_le_one ε x) hz (norm_nonneg _) zero_le_one)
    _ = _ := by ring

private theorem poisson_nonneg {h : ℝ} (hh : 0 < h) (y : ℝ) : 0 ≤ poisson h y := by
  unfold poisson kernel
  positivity

private theorem poisson_continuous {h : ℝ} (hh : 0 < h) : Continuous (poisson h) := by
  unfold poisson kernel
  exact (continuous_const.div (by fun_prop) (fun y ↦
    (show 0 < h ^ 2 + y ^ 2 by positivity).ne')).div_const _

private theorem envelope_continuous : Continuous envelope := by
  unfold envelope
  exact Continuous.inv₀ (by fun_prop) (fun x ↦ by positivity)

-- The majorant for absolute convergence is the convolution of the positive
-- envelope itself: it is twice a Cauchy kernel of width 1/2.
private theorem integral_poisson_envelope {h : ℝ} (hh : 0 < h) (x : ℝ) :
    (∫ y : ℝ, poisson h y * envelope (x - y)) = 2 * kernel (h + 1 / 2) x := by
  have he (u : ℝ) : envelope u = 2 * kernel (1 / 2) u := by
    unfold envelope kernel
    norm_num [div_eq_mul_inv]
    ring
  simp_rw [he, mul_left_comm (poisson h _) 2, integral_const_mul,
    SignedPoissonDefect.poisson_convolution_kernel hh (by norm_num : (1 / 2 : ℝ) ≠ 0),
    Real.sign_of_pos (by norm_num : (0 : ℝ) < 1 / 2), abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2),
    one_mul]

private theorem integrable_poisson_envelope {h : ℝ} (hh : 0 < h) (x : ℝ) :
    Integrable (fun y : ℝ ↦ poisson h y * envelope (x - y)) := by
  apply Integrable.of_integral_ne_zero
  rw [integral_poisson_envelope hh x]
  unfold kernel
  positivity

private theorem integral_poisson_envelope_le {h : ℝ} (hh : 0 < h) (hh₁ : h ≤ 1) (x : ℝ) :
    (∫ y : ℝ, poisson h y * envelope (x - y)) ≤ 3 * envelope x := by
  rw [integral_poisson_envelope hh x, kernel, envelope, ← div_eq_mul_inv, ← mul_div_assoc]
  refine div_le_div₀ (by positivity) (by linarith) (by positivity) ?_
  nlinarith [sq_nonneg h]

private noncomputable def realCarrier (ω : ℝ) (f : ℝ → ℂ) (x : ℝ) : ℝ :=
  (Complex.exp (↑(ω * x) * Complex.I) * f x).re

private theorem realCarrier_continuous {f : ℝ → ℂ} (hf : Continuous f) (ω : ℝ) :
    Continuous (realCarrier ω f) := by
  unfold realCarrier
  fun_prop

private theorem abs_realCarrier_le (ω : ℝ) (f : ℝ → ℂ) (x : ℝ) :
    |realCarrier ω f x| ≤ ‖f x‖ := by
  apply (Complex.abs_re_le_norm _).trans
  rw [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]

private theorem realCarrier_low (ε x : ℝ) :
    realCarrier 0 (lowEnv ε) x = (2 * smoothing ε x - baseline) * envelope x := by
  simp [realCarrier, lowEnv]

private theorem abs_depthCoefficient_le {c : ℝ} (hc : 0 ≤ c) :
    |depthCoefficient c| ≤ 2 * Real.cosh 1 := by
  unfold depthCoefficient
  split_ifs with h
  · rw [abs_of_pos (mul_pos (by norm_num) (Real.cosh_pos _))]
    have hcosh : Real.cosh c ≤ Real.cosh 1 := by
      simpa only [abs_of_nonneg hc, abs_one] using (Real.cosh_le_cosh.mpr (by
        simpa only [abs_of_nonneg hc, abs_one] using h : |c| ≤ |(1 : ℝ)|))
    gcongr
  · rw [abs_mul, abs_mul, abs_neg, abs_of_nonneg (show (0 : ℝ) ≤ 2 by norm_num),
      abs_of_pos (Real.exp_pos _)]
    have he : Real.exp (1 - c) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    calc
      _ ≤ 2 * Real.cosh 1 * 1 := by gcongr; exact abs_sinh_le_cosh _
      _ = _ := mul_one _

private theorem continuous_low (ε D b : ℝ) : Continuous (low ε D b) := by
  by_cases hb : b * D ≤ 1
  · have he : low ε D b = realCarrier 0 (lowEnv ε) := by
      funext x
      rw [low, ite_eq_left hb, realCarrier_low]
    rw [he]
    exact realCarrier_continuous (lowEnv_contDiff ε).continuous 0
  · have he : low ε D b = fun _ ↦ 0 := by
      funext x
      rw [low, ite_eq_right hb]
    rw [he]
    exact continuous_const

private theorem continuous_oscillatory (ε D b : ℝ) : Continuous (oscillatory ε D b) :=
  continuous_const.mul (realCarrier_continuous (highEnv_contDiff ε).continuous D)

private theorem abs_low_le (ε D b x : ℝ) :
    |low ε D b x| ≤ (2 + |baseline|) * envelope x := by
  unfold low
  split_ifs with hb
  · rw [← realCarrier_low]
    exact (abs_realCarrier_le ..).trans (lowEnv_value ε x)
  · simp only [abs_zero]
    exact mul_nonneg (by positivity) (envelope_pos x).le

private theorem abs_oscillatory_le {D b : ℝ} (hD : 0 < D) (hb : 0 ≤ b) (ε x : ℝ) :
    |oscillatory ε D b x| ≤ (2 * Real.cosh 1) * envelope x := by
  change |depthCoefficient (b * D) * realCarrier D (highEnv ε) x| ≤ _
  rw [abs_mul]
  exact mul_le_mul (abs_depthCoefficient_le (mul_nonneg hb hD.le))
    ((abs_realCarrier_le ..).trans (highEnv_value ε x)) (abs_nonneg _) (by positivity)

private theorem integrable_complex_carrier {h : ℝ} (hh : 0 < h) {f : ℝ → ℂ}
    (hf : Continuous f) {M : ℝ} (hv : ∀ t, ‖f t‖ ≤ M * envelope t) (ω x : ℝ) :
    Integrable (fun y : ℝ ↦ (poisson h y : ℂ) * Complex.exp (↑(ω * (x - y)) * Complex.I) *
      f (x - y)) := by
  apply ((integrable_poisson_envelope hh x).const_mul M).mono'
  · have hp := poisson_continuous hh
    exact (by fun_prop : Continuous _).aestronglyMeasurable
  · refine .of_forall fun y ↦ ?_
    rw [norm_mul, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one,
      Complex.norm_real, Real.norm_of_nonneg (poisson_nonneg hh y), mul_left_comm M]
    exact mul_le_mul_of_nonneg_left (hv _) (poisson_nonneg hh y)

-- Take the real part of the pinned complex freezing theorem, after verifying
-- integrability so that `re` really does pass through the Bochner integral.
private theorem abs_poisson_realCarrier_sub_le {f : ℝ → ℂ} (hf : Continuous f) {M B h ω x : ℝ}
    (hh : 0 < h) (hv : ∀ t, ‖f t‖ ≤ M * envelope t)
    (hB : ‖(∫ y : ℝ, (poisson h y : ℂ) * Complex.exp (↑(ω * (x - y)) * Complex.I) *
      f (x - y)) - (Real.exp (-h * |ω|) : ℂ) * Complex.exp (↑(ω * x) * Complex.I) * f x‖ ≤ B) :
    |(∫ y : ℝ, poisson h y * realCarrier ω f (x - y)) -
      Real.exp (-h * |ω|) * realCarrier ω f x| ≤ B := by
  have hI := (Complex.reCLM.integral_comp_comm (integrable_complex_carrier hh hf hv ω x)).symm
  change (∫ y : ℝ, (poisson h y : ℂ) * Complex.exp (↑(ω * (x - y)) * Complex.I) *
      f (x - y)).re = ∫ y : ℝ, ((poisson h y : ℂ) *
        Complex.exp (↑(ω * (x - y)) * Complex.I) * f (x - y)).re at hI
  simp only [Complex.re_ofReal_mul, mul_assoc] at hI
  change _ = (∫ y : ℝ, poisson h y * realCarrier ω f (x - y)) at hI
  rw [← hI]
  have hRe := (Complex.abs_re_le_norm _).trans hB
  simpa only [Complex.sub_re, mul_assoc, Complex.re_ofReal_mul, realCarrier] using hRe

private theorem integrable_poisson_shift {h M : ℝ} (hh : 0 < h) (x : ℝ) {f : ℝ → ℝ}
    (hf : Continuous f) (hbound : ∀ u, |f u| ≤ M * envelope u) :
    Integrable (fun y : ℝ ↦ poisson h y * f (x - y)) := by
  apply ((integrable_poisson_envelope hh x).const_mul M).mono'
  · have hp := poisson_continuous hh
    exact (by fun_prop : Continuous _).aestronglyMeasurable
  · refine .of_forall fun y ↦ ?_
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (poisson_nonneg hh y), mul_left_comm M]
    exact mul_le_mul_of_nonneg_left (hbound _) (poisson_nonneg hh y)

/-- The low-frequency part plus `r` times the oscillatory part of one pair. -/
@[expose] public noncomputable def atom (ε D b r x : ℝ) : ℝ :=
  low ε D b x + r * oscillatory ε D b x

private theorem atom_continuous (ε D b r : ℝ) : Continuous (atom ε D b r) :=
  (continuous_low ε D b).add (continuous_const.mul (continuous_oscillatory ε D b))

private theorem abs_atom_le {D b r : ℝ} (hD : 0 < D) (hb : 0 ≤ b) (hr : |r| ≤ 1)
    (ε x : ℝ) : |atom ε D b r x| ≤ (2 + |baseline| + 2 * Real.cosh 1) * envelope x := by
  unfold atom
  refine (abs_add_le ..).trans ?_
  rw [abs_mul]
  calc
    _ ≤ (2 + |baseline|) * envelope x + 1 * ((2 * Real.cosh 1) * envelope x) :=
      add_le_add (abs_low_le ..)
        (mul_le_mul hr (abs_oscillatory_le hD hb ε x) (abs_nonneg _) zero_le_one)
    _ = _ := by ring

private theorem abs_poisson_atom_sub_le (ε : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ {D b h : ℝ}, 0 < D → 0 ≤ b → 0 < h → h ≤ 1 → ∀ x : ℝ,
      |(∫ y : ℝ, poisson h y * atom ε D b 1 (x - y)) -
        atom ε D b (Real.exp (-h * D)) x| ≤ C * h * Real.log (2 / h) * envelope x := by
  obtain ⟨C, hC, freeze⟩ := PoissonCarrierFreezing.norm_poisson_carrier_sub_le
  let M := 4 * (1 + (2 * |ε| + 2 * (2 + |baseline|)) + (|ε| + 4))
  have hM : 0 < M := by dsimp [M]; positivity
  refine ⟨C * M * (1 + 2 * Real.cosh 1), by positivity, ?_⟩
  intro D b h hD hb hh hh₁ x
  have hlog : 0 ≤ Real.log (2 / h) :=
    Real.log_nonneg ((le_div_iff₀ hh).2 (by linarith))
  have freezeReal (f : ℝ → ℂ) (hf : ContDiff ℝ 1 f)
      (hfv : ∀ u, ‖f u‖ ≤ (M / 4) * envelope u)
      (hfd : ∀ u, ‖deriv f u‖ ≤ (M / 4) * envelope u) (ω : ℝ) :
      |(∫ y : ℝ, poisson h y * realCarrier ω f (x - y)) -
        Real.exp (-h * |ω|) * realCarrier ω f x| ≤ C * M * h * Real.log (2 / h) * envelope x := by
    have convertWeight (u : ℝ) : (M / 4) * envelope u ≤ M / (1 + u ^ 2) := by
      calc
        _ ≤ (M / 4) * (4 / (1 + u ^ 2)) :=
          mul_le_mul_of_nonneg_left (envelope_le_quad u) (by positivity)
        _ = _ := by ring
    apply abs_poisson_realCarrier_sub_le hf.continuous hh hfv
    refine (freeze f hf M (fun u ↦ (hfv u).trans (convertWeight u))
      (fun u ↦ (hfd u).trans (convertWeight u)) h hh hh₁ x ω).trans ?_
    rw [div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left (one_add_sq_inv_le_envelope x) (by positivity)
  have hL : |(∫ y : ℝ, poisson h y * low ε D b (x - y)) - low ε D b x| ≤
      C * M * h * Real.log (2 / h) * envelope x := by
    by_cases hs : b * D ≤ 1
    · have hhL := freezeReal (lowEnv ε) (lowEnv_contDiff ε)
        (fun u ↦ (lowEnv_value ε u).trans (mul_le_mul_of_nonneg_right
          (by dsimp [M]; linarith [abs_nonneg ε, abs_nonneg baseline]) (envelope_pos u).le))
        (fun u ↦ (lowEnv_deriv ε u).trans (mul_le_mul_of_nonneg_right
          (by dsimp [M]; linarith [abs_nonneg ε]) (envelope_pos u).le)) 0
      simpa only [low, ite_eq_left hs, abs_zero, mul_zero, Real.exp_zero, one_mul,
        realCarrier_low] using hhL
    · simpa only [low, ite_eq_right hs, mul_zero, integral_zero, sub_zero, abs_zero] using
        (show 0 ≤ C * M * h * Real.log (2 / h) * envelope x from by
          have := (envelope_pos x).le
          positivity)
  have hG : |(∫ y : ℝ, poisson h y * oscillatory ε D b (x - y)) -
      Real.exp (-h * D) * oscillatory ε D b x| ≤
        (2 * Real.cosh 1) * (C * M * h * Real.log (2 / h) * envelope x) := by
    have hhG := freezeReal (highEnv ε) (highEnv_contDiff ε)
      (fun u ↦ (highEnv_value ε u).trans (le_mul_of_one_le_left (envelope_pos u).le
        (by dsimp [M]; linarith [abs_nonneg ε, abs_nonneg baseline])))
      (fun u ↦ (highEnv_deriv ε u).trans (mul_le_mul_of_nonneg_right
        (by dsimp [M]; linarith [abs_nonneg ε, abs_nonneg baseline]) (envelope_pos u).le)) D
    simp only [abs_of_pos hD] at hhG
    let j := depthCoefficient (b * D)
    change |(∫ y : ℝ, poisson h y * (j * realCarrier D (highEnv ε) (x - y))) -
      Real.exp (-h * D) * (j * realCarrier D (highEnv ε) x)| ≤ _
    simp_rw [mul_left_comm (poisson h _) j, integral_const_mul,
      mul_left_comm (Real.exp (-h * D)) j, ← mul_sub, abs_mul]
    exact mul_le_mul (abs_depthCoefficient_le (mul_nonneg hb hD.le)) hhG (abs_nonneg _)
      (by positivity)
  have hiL := integrable_poisson_shift hh x (continuous_low ε D b) (abs_low_le ε D b)
  have hiG := integrable_poisson_shift hh x (continuous_oscillatory ε D b)
    (abs_oscillatory_le hD hb ε)
  simp only [atom, one_mul, mul_add]
  rw [integral_add hiL hiG, add_sub_add_comm]
  calc
    _ ≤ _ := abs_add_le ..
    _ ≤ _ := add_le_add hL hG
    _ = _ := by ring

private theorem pairWeight_nonneg (b : ℝ) (m : ℕ) : 0 ≤ pairWeight b m := by
  unfold pairWeight
  split <;> positivity

private theorem pairWeight_le (b : ℝ) (m : ℕ) : pairWeight b m ≤ (m : ℝ) := by
  unfold pairWeight
  split
  · linarith [Nat.cast_nonneg (α := ℝ) m]
  · rfl

private theorem envelope_sub_le (u t : ℝ) : envelope (u - t) ≤ (2 + 8 * t ^ 2) * envelope u := by
  unfold envelope
  rw [← one_div, ← div_eq_mul_inv]
  apply (div_le_div_iff₀ (by positivity) (by positivity)).2
  nlinarith only [sq_nonneg (u - 2 * t), mul_nonneg (sq_nonneg t) (sq_nonneg (u - t))]

/-- Convergence of the weighted inverse squares at one center implies
convergence at every height. -/
public theorem summable_centered_envelope {ι : Type*} (b γ : ι → ℝ) (m : ι → ℕ)
    (hs : Summable (fun i ↦ pairWeight (b i) (m i) * envelope (γ i))) (t : ℝ) :
    Summable (fun i ↦ pairWeight (b i) (m i) * envelope (γ i - t)) := by
  apply (hs.mul_left (2 + 8 * t ^ 2)).of_nonneg_of_le
  · intro i
    exact mul_nonneg (pairWeight_nonneg ..) (envelope_pos _).le
  · intro i
    rw [mul_left_comm (2 + 8 * t ^ 2)]
    exact mul_le_mul_of_nonneg_left (envelope_sub_le ..) (pairWeight_nonneg ..)

/-- The two carrier terms in the frozen divisor sum, normalized by `R`.
`r = 1` is the original sum and `r = exp (−hD)` is the leading average. -/
@[expose] public noncomputable def divisorSum {ι : Type*} (b γ : ι → ℝ) (m : ι → ℕ)
    (ε D R r t : ℝ) : ℝ :=
  (∑' i, pairWeight (b i) (m i) * atom ε D (b i) r (γ i - t)) / R

/-- The weighted local envelope at the same center and normalization. -/
@[expose] public noncomputable def localEnvelope {ι : Type*} (b γ : ι → ℝ) (m : ι → ℕ)
    (R t : ℝ) : ℝ :=
  (∑' i, pairWeight (b i) (m i) * envelope (γ i - t)) / R

-- The L¹ majorant is summable, not just the pointwise atom majorant.
private theorem integrable_tsum_of_integral_norm {ι : Type*} [Countable ι]
    {F : ι → ℝ → ℝ} (hF : ∀ i, Integrable (F i))
    (hS : Summable fun i ↦ ∫ y, ‖F i y‖) : Integrable (fun y ↦ ∑' i, F i y) := by
  have hm (i : ι) := (hF i).aestronglyMeasurable
  refine ⟨AEStronglyMeasurable.tsum hm, ?_⟩
  rw [hasFiniteIntegral_iff_eNorm]
  have heq (i : ι) : (∫⁻ y, ‖F i y‖ₑ) = ENNReal.ofReal (∫ y, ‖F i y‖) := by
    rw [ofReal_integral_eq_lintegral_ofReal (hF i).norm (ae_of_all _ fun _ ↦ norm_nonneg _)]
    simp only [ofReal_norm]
  calc
    _ ≤ ∫⁻ y, ∑' i, ‖F i y‖ₑ := lintegral_mono fun _ ↦ eNorm_tsum_le_tsum_eNorm
    _ = ∑' i, ∫⁻ y, ‖F i y‖ₑ := lintegral_tsum fun i ↦ (hm i).aemeasurable.eNorm
    _ = ENNReal.ofReal (∑' i, ∫ y, ‖F i y‖) := by
      simp_rw [heq]
      exact (ENNReal.ofReal_tsum_of_nonneg (fun _ ↦ integral_nonneg fun _ ↦ norm_nonneg _) hS).symm
    _ < ⊤ := ENNReal.ofReal_lt_top

/-- Positive-width transfer for the explicit carrier sum. The constant depends
only on `ε`; in particular it is uniform in `D`, the switch depths, the
ordinates, the multiplicities, the height, and `0 < h ≤ 1`. The equality
asserts the integral/series interchange and the inequality leaves the low
term unchanged and attenuates the oscillatory term by `exp (−hD)`. -/
public theorem poisson_divisorSum_sub_le {ι : Type*} [Countable ι] (ε : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (b γ : ι → ℝ) (m : ι → ℕ), (∀ i, 0 ≤ b i) →
      Summable (fun i ↦ pairWeight (b i) (m i) * envelope (γ i)) →
      ∀ {D h R : ℝ}, 0 < D → 0 < h → h ≤ 1 → 0 < R → ∀ t : ℝ,
        Integrable (fun y : ℝ ↦ poisson h y * divisorSum b γ m ε D R 1 (t - y)) ∧
        (∫ y : ℝ, poisson h y * divisorSum b γ m ε D R 1 (t - y)) =
          (∑' i, pairWeight (b i) (m i) *
            (∫ y : ℝ, poisson h y * atom ε D (b i) 1 (γ i - t - y))) / R ∧
        |(∫ y : ℝ, poisson h y * divisorSum b γ m ε D R 1 (t - y)) -
          divisorSum b γ m ε D R (Real.exp (-h * D)) t| ≤
            C * h * Real.log (2 / h) * localEnvelope b γ m R t := by
  obtain ⟨C, hC, hfreeze⟩ := abs_poisson_atom_sub_le ε
  refine ⟨C, hC, ?_⟩
  intro b γ m hb hs D h R hD hh hh₁ hR t
  let ν (i : ι) := pairWeight (b i) (m i)
  let x (i : ι) := γ i - t
  let M := 2 + |baseline| + 2 * Real.cosh 1
  let r := Real.exp (-h * D)
  let A (i : ι) := atom ε D (b i) 1
  let F (i : ι) (y : ℝ) := ν i * (poisson h y * A i (x i - y))
  let B (i : ι) := ν i * atom ε D (b i) r (x i)
  have hν (i : ι) : 0 ≤ ν i := pairWeight_nonneg ..
  have hS : Summable fun i ↦ ν i * envelope (x i) := summable_centered_envelope b γ m hs t
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hA (i : ι) (u : ℝ) : |A i u| ≤ M * envelope u := abs_atom_le hD (hb i) (by norm_num) ε u
  have hi (i : ι) : Integrable (F i) :=
    (integrable_poisson_shift hh (x i) (atom_continuous ..) (hA i)).const_mul (ν i)
  have hbound (i : ι) (y : ℝ) : ‖F i y‖ ≤
      (M * ν i) * (poisson h y * envelope (x i - y)) := by
    dsimp only [F]
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (hν i),
      abs_of_nonneg (poisson_nonneg hh y)]
    calc
      _ ≤ ν i * (poisson h y * (M * envelope (x i - y))) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (hA i _) (poisson_nonneg hh y)) (hν i)
      _ = _ := by ring
  have hL1 : Summable (fun i ↦ ∫ y, ‖F i y‖) := by
    apply (hS.mul_left (3 * M)).of_nonneg_of_le (fun i ↦ integral_nonneg fun y ↦ norm_nonneg _) ?_
    intro i
    calc
      _ ≤ ∫ y, (M * ν i) * (poisson h y * envelope (x i - y)) :=
        integral_mono (hi i).norm ((integrable_poisson_envelope hh _).const_mul _) (hbound i)
      _ = (M * ν i) * ∫ y, poisson h y * envelope (x i - y) := integral_const_mul ..
      _ ≤ (M * ν i) * (3 * envelope (x i)) :=
        mul_le_mul_of_nonneg_left (integral_poisson_envelope_le hh hh₁ _) (mul_nonneg hM (hν i))
      _ = _ := by ring
  have hHas := hasSum_integral_of_summable_integral_norm hi hL1
  have hp (y : ℝ) : poisson h y * divisorSum b γ m ε D R 1 (t + y) = (∑' i, F i y) / R := by
    rw [divisorSum, ← mul_div_assoc]
    congr 1
    rw [← tsum_mul_left]
    apply tsum_congr
    intro i
    simp only [F, A, x, ν, ← sub_sub]
    ac_rfl
  let Q (y : ℝ) := poisson h y * divisorSum b γ m ε D R 1 (t + y)
  have hQ : Integrable Q := by
    simpa only [Q, hp] using (integrable_tsum_of_integral_norm hi hL1).div_const R
  have hneg (y : ℝ) : Q (-y) = poisson h y * divisorSum b γ m ε D R 1 (t - y) := by
    simp [Q, poisson, kernel, sub_eq_add_neg]
  have hI : Integrable (fun y : ℝ ↦ poisson h y * divisorSum b γ m ε D R 1 (t - y)) := by
    simpa only [hneg] using hQ.comp_neg
  have hConv : (∫ y : ℝ, poisson h y * divisorSum b γ m ε D R 1 (t - y)) =
      (∑' i, ∫ y, F i y) / R := by
    simp_rw [← hneg, integral_neg_eq_self, Q, hp, integral_div, hHas.tsum_eq]
  refine ⟨hI, ?_, ?_⟩
  · rw [hConv]
    congr 1
    apply tsum_congr
    intro i
    exact integral_const_mul ..
  · have hr : |r| ≤ 1 := by
      rw [abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hh.le) hD.le)
    have hB : Summable B := by
      apply (hS.mul_left M).of_norm_bounded
      intro i
      dsimp only [B]
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hν i), mul_left_comm M]
      exact mul_le_mul_of_nonneg_left (abs_atom_le hD (hb i) hr ε _) (hν i)
    let K := C * h * Real.log (2 / h)
    have hE (i : ι) : |(∫ y, F i y) - B i| ≤ K * (ν i * envelope (x i)) := by
      simp only [F, B, integral_const_mul, ← mul_sub, abs_mul, abs_of_nonneg (hν i)]
      calc
        _ ≤ ν i * (K * envelope (x i)) :=
          mul_le_mul_of_nonneg_left (hfreeze hD (hb i) hh hh₁ _) (hν i)
        _ = _ := by ring
    have hES := (hS.mul_left K).of_nonneg_of_le (fun i ↦ abs_nonneg ((∫ y, F i y) - B i)) hE
    have hTotal : |(∑' i, ∫ y, F i y) - ∑' i, B i| ≤ K * ∑' i, ν i * envelope (x i) := by
      rw [← hHas.summable.tsum_sub hB, ← tsum_mul_left]
      have hn := norm_tsum_le_tsum_norm (f := fun i ↦ (∫ y, F i y) - B i)
        (by simpa only [Real.norm_eq_abs] using hES)
      rw [Real.norm_eq_abs] at hn
      exact hn.trans (hES.tsum_le_tsum hE (hS.mul_left K))
    rw [hConv, divisorSum, ← sub_div, abs_div, abs_of_pos hR, localEnvelope, ← mul_div_assoc]
    exact div_le_div_of_nonneg_right hTotal hR.le

open Masullo

/-- Distinct zeta zeros on or to the right of the critical line, in the
open strip. A line zero is included here and halved by `pairWeight`. -/
public abbrev RightZetaZero := {ρ : criticalStripZetaZeros // (1 / 2 : ℝ) ≤ (ρ : ℂ).re}

/-- Depth from the critical line. -/
@[expose] public noncomputable def zetaDepth (ρ : RightZetaZero) : ℝ :=
  (ρ.1 : ℂ).re - 1 / 2

/-- Ordinate of a right or line zero. -/
@[expose] public noncomputable def zetaOrdinate (ρ : RightZetaZero) : ℝ := (ρ.1 : ℂ).im

/-- Weighted inverse squares for the actual divisor, with analytic orders
and half weight on the line. -/
public theorem summable_zeta_envelope (t : ℝ) :
    Summable (fun ρ : RightZetaZero ↦
      pairWeight (zetaDepth ρ) (zetaZeroOrder ρ.1) * envelope (zetaOrdinate ρ - t)) := by
  apply summable_centered_envelope zetaDepth zetaOrdinate (fun ρ ↦ zetaZeroOrder ρ.1) _ t
  have hs := summable_zetaZeroOrder_div_one_add_norm_sq.subtype
    (fun ρ : criticalStripZetaZeros ↦ (1 / 2 : ℝ) ≤ (ρ : ℂ).re)
  apply (hs.mul_left 8).of_nonneg_of_le
  · intro ρ
    exact mul_nonneg (pairWeight_nonneg ..) (envelope_pos _).le
  · intro ρ
    have hre := pow_le_pow_left₀ (abs_nonneg _) (abs_re_shiftedZetaZero_lt ρ.1).le 2
    rw [sq_abs] at hre
    have him : (shiftedZetaZero ρ.1).im = zetaOrdinate ρ := by simp [shiftedZetaZero, zetaOrdinate]
    have hsize : 1 + ‖shiftedZetaZero ρ.1‖ ^ 2 ≤ 8 * (1 / 4 + zetaOrdinate ρ ^ 2) := by
      rw [Complex.sq_norm, Complex.normSq_apply, him]
      nlinarith only [hre, sq_nonneg (zetaOrdinate ρ)]
    have he : envelope (zetaOrdinate ρ) ≤ 8 / (1 + ‖shiftedZetaZero ρ.1‖ ^ 2) := by
      rw [envelope, ← one_div]
      exact (div_le_div_iff₀ (by positivity) (by positivity)).2 (by linarith)
    change _ ≤ 8 * ((zetaZeroOrder ρ.1 : ℝ) / (1 + ‖shiftedZetaZero ρ.1‖ ^ 2))
    calc
      _ ≤ (zetaZeroOrder ρ.1 : ℝ) * (8 / (1 + ‖shiftedZetaZero ρ.1‖ ^ 2)) :=
        mul_le_mul (pairWeight_le ..) he (envelope_pos _).le (Nat.cast_nonneg _)
      _ = _ := by ring

/-- The frozen carrier sum over the right and line zeta divisor. -/
@[expose] public noncomputable def zetaDivisorSum (ε D R r t : ℝ) : ℝ :=
  divisorSum zetaDepth zetaOrdinate (fun ρ ↦ zetaZeroOrder ρ.1) ε D R r t

/-- The local inverse-square budget for the right and line zeta divisor. -/
@[expose] public noncomputable def zetaLocalEnvelope (R t : ℝ) : ℝ :=
  localEnvelope zetaDepth zetaOrdinate (fun ρ ↦ zetaZeroOrder ρ.1) R t

/-- The positive-width estimate for the actual right and line zeta divisor,
with summability discharged and the weighted local budget at the original
height. No bound on that budget by an exterior trace is asserted. -/
public theorem poisson_zetaDivisorSum_sub_le (ε : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ {D h R : ℝ}, 0 < D → 0 < h → h ≤ 1 → 0 < R → ∀ t : ℝ,
      Integrable (fun y : ℝ ↦ poisson h y * zetaDivisorSum ε D R 1 (t - y)) ∧
      (∫ y : ℝ, poisson h y * zetaDivisorSum ε D R 1 (t - y)) =
        (∑' ρ : RightZetaZero, pairWeight (zetaDepth ρ) (zetaZeroOrder ρ.1) *
          (∫ y : ℝ, poisson h y * atom ε D (zetaDepth ρ) 1 (zetaOrdinate ρ - t - y))) / R ∧
      |(∫ y : ℝ, poisson h y * zetaDivisorSum ε D R 1 (t - y)) -
        zetaDivisorSum ε D R (Real.exp (-h * D)) t| ≤
          C * h * Real.log (2 / h) * zetaLocalEnvelope R t := by
  obtain ⟨C, hC, htransfer⟩ := poisson_divisorSum_sub_le (ι := RightZetaZero) ε
  refine ⟨C, hC, ?_⟩
  intro D h R hD hh hh₁ hR t
  have hs : Summable (fun ρ : RightZetaZero ↦
      pairWeight (zetaDepth ρ) (zetaZeroOrder ρ.1) * envelope (zetaOrdinate ρ)) := by
    simpa only [sub_zero] using summable_zeta_envelope 0
  exact htransfer zetaDepth zetaOrdinate (fun ρ ↦ zetaZeroOrder ρ.1)
    (fun ρ ↦ sub_nonneg.mpr ρ.property) hs hD hh hh₁ hR t
end PoissonDivisorCarriers
