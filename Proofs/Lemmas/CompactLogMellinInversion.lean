module

public import Props.CompactLogMellin
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Tactic.FieldSimp

/-! # Fourier inversion of the direct and reflected right-line Mellin tests -/

open Complex MeasureTheory
open scoped ContDiff FourierTransform

namespace Masullo

-- Convert from Mathlib's Fourier convention to ordinary angular frequency.
private theorem angularFourier_inversion {h W : ℝ → ℂ} (hh : Continuous h)
    (hi : Integrable h) (hW : Integrable W)
    (hFourier : ∀ t : ℝ, W t = 𝓕⁻ h ((2 * Real.pi)⁻¹ * t)) (y : ℝ) :
    (∫ t, W t * exp (-(t : ℂ) * y * I)) / (2 * (Real.pi : ℂ)) = h y := by
  let a : ℝ := 2 * Real.pi
  have ha : 0 < a := by dsimp [a]; positivity
  have hFourier' : W = fun t ↦ 𝓕⁻ h (a⁻¹ * t) := funext hFourier
  have hf : Integrable (𝓕⁻ h) :=
    (integrable_comp_mul_left_iff _ (inv_ne_zero ha.ne')).mp (hFourier' ▸ hW)
  have hf' : Integrable (𝓕 h) := by
    simpa only [Real.fourierInv_eq_fourier_neg, neg_neg] using hf.comp_neg
  have hinv := congrFun (hh.fourier_fourierInv_eq hi hf') y
  rw [Real.fourier_real_eq_integral_exp_smul] at hinv
  let F (v : ℝ) := exp ((↑(-2 * Real.pi * v * y) : ℂ) * I) • 𝓕⁻ h v
  have hscale (t : ℝ) : W t * exp (-(t : ℂ) * y * I) = F (a⁻¹ * t) := by
    dsimp only [F]
    rw [congrFun hFourier' t, show -2 * Real.pi * (a⁻¹ * t) * y = -t * y by
      dsimp [a]; field_simp [Real.pi_ne_zero]]
    simp only [Complex.ofReal_mul, Complex.ofReal_neg, smul_eq_mul, mul_comm]
  rw [← show (a : ℂ) = 2 * (Real.pi : ℂ) by simp [a]]
  change (∫ t, W t * exp (-(t : ℂ) * y * I)) / (a : ℂ) = h y
  simp_rw [hscale]
  rw [Measure.integral_comp_mul_left, inv_inv, abs_of_pos ha, Complex.real_smul,
    show (∫ v, F v) = h y from hinv]
  exact mul_div_cancel_left₀ _ (Complex.ofReal_ne_zero.mpr ha.ne')

/-- Absolute integrability of the compact log Mellin test on any vertical line. -/
public theorem integrable_compactLogMellin_vertical {g : ℝ → ℂ}
    (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g) (a : ℝ) :
    Integrable (fun t : ℝ ↦ compactLogMellin g ((a : ℂ) + (t : ℂ) * I)) := by
  obtain ⟨B, _, hB⟩ := compactLogMellin_vertical_decay hg hc |a| 4
  have hΦ : Continuous (compactLogMellin g) := continuous_iff_continuousAt.mpr fun s ↦
    (analyticAt_compactLogMellin hg.continuous hc s).continuousAt
  have hi : Integrable (fun t : ℝ ↦ (1 + ‖t‖) ^ (-(4 : ℝ))) :=
    integrable_one_add_norm (by simp)
  refine (hi.const_mul B).mono' (hΦ.comp (by fun_prop)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun t ↦ ?_)
  rw [Real.norm_eq_abs, Real.rpow_neg (by positivity : 0 ≤ 1 + |t|),
    show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  simpa only [div_eq_mul_inv] using hB a t le_rfl

/-- Absolute integrability of the reflected compact log Mellin test. -/
public theorem integrable_compactLogMellin_reflected_vertical {g : ℝ → ℂ}
    (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g) (a : ℝ) :
    Integrable (fun t : ℝ ↦ compactLogMellin g (1 - ((a : ℂ) + (t : ℂ) * I))) := by
  convert (integrable_compactLogMellin_vertical hg hc (1 - a)).comp_neg using 2 with t
  push_cast
  ring_nf

private theorem compactLogMellin_eq_fourierInv (g : ℝ → ℂ) (a t : ℝ) :
    compactLogMellin g ((a : ℂ) + (t : ℂ) * I) =
      𝓕⁻ (fun x : ℝ ↦ g x * exp ((a : ℂ) * x)) ((2 * Real.pi)⁻¹ * t) := by
  rw [compactLogMellin, Real.fourierInv_eq']
  congr 1
  funext x
  have hphase : (2 * Real.pi * inner ℝ x ((2 * Real.pi)⁻¹ * t) : ℝ) = t * x := by
    rw [Real.inner_apply]
    field_simp [Real.pi_ne_zero]
  rw [hphase, Complex.ofReal_mul, smul_eq_mul, add_mul, exp_add,
    show (t : ℂ) * I * x = (t : ℂ) * x * I by ring]
  ring

/-- Angular-frequency Mellin inversion with the factor `exp(-sy)` already
included, for the direct term of (B.4.2.10). -/
public theorem compactLogMellin_right_line_evaluation {g : ℝ → ℂ}
    (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g) (a y : ℝ) :
    (∫ t : ℝ, compactLogMellin g ((a : ℂ) + (t : ℂ) * I) *
      exp (-((a : ℂ) + (t : ℂ) * I) * y)) / (2 * (Real.pi : ℂ)) = g y := by
  let h (x : ℝ) := g x * exp ((a : ℂ) * x)
  have hh : Continuous h := by have := hg.continuous; unfold h; fun_prop
  have hi : Integrable h := hh.integrable_of_hasCompactSupport hc.mul_right
  have hInv := angularFourier_inversion hh hi (integrable_compactLogMellin_vertical hg hc a)
    (compactLogMellin_eq_fourierInv g a) y
  have heq (t : ℝ) : exp (-((a : ℂ) + (t : ℂ) * I) * y) =
      exp (-(a : ℂ) * y) * exp (-(t : ℂ) * y * I) := by
    rw [← exp_add]
    congr 1
    ring
  have hprod (t : ℝ) : compactLogMellin g ((a : ℂ) + (t : ℂ) * I) *
      exp (-((a : ℂ) + (t : ℂ) * I) * y) = exp (-(a : ℂ) * y) *
        (compactLogMellin g ((a : ℂ) + (t : ℂ) * I) * exp (-(t : ℂ) * y * I)) := by
    rw [heq]
    ring
  simp_rw [hprod, integral_const_mul, mul_div_assoc]
  rw [hInv]
  change exp (-(a : ℂ) * y) * (g y * exp ((a : ℂ) * y)) = g y
  rw [mul_left_comm, ← exp_add, ← add_mul, neg_add_cancel, zero_mul, exp_zero, mul_one]

/-- Reflecting the Mellin parameter is the log reflection with the
weight `exp(-x)`. It does not reverse the right-line orientation. -/
private theorem compactLogMellin_reflect (g : ℝ → ℂ) (s : ℂ) :
    compactLogMellin g (1 - s) = compactLogMellin (fun x : ℝ ↦ exp (-x) * g (-x)) s := by
  unfold compactLogMellin
  rw [← integral_neg_eq_self (fun x : ℝ ↦ g x * exp ((1 - s) * x)) volume]
  congr 1
  funext x
  change g (-x) * exp ((1 - s) * ((-x : ℝ) : ℂ)) = (exp (-x) * g (-x)) * exp (s * x)
  rw [mul_comm (exp _) (g _), mul_assoc, ← exp_add]
  push_cast
  congr 2
  ring

/-- Angular-frequency Mellin inversion on the same upward right line,
for the reflected term of (B.4.2.11). -/
public theorem compactLogMellin_reflected_right_line_evaluation {g : ℝ → ℂ}
    (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g) (a y : ℝ) :
    (∫ t : ℝ, compactLogMellin g (1 - ((a : ℂ) + (t : ℂ) * I)) *
      exp (-((a : ℂ) + (t : ℂ) * I) * y)) / (2 * (Real.pi : ℂ)) = exp (-y) * g (-y) := by
  simp_rw [compactLogMellin_reflect g]
  have hExp : ContDiff ℝ ∞ (fun x : ℝ ↦ exp (-x)) :=
    Complex.contDiff_exp.comp Complex.ofRealCLM.contDiff.neg
  have hd : ContDiff ℝ ∞ (fun x : ℝ ↦ exp (-x) * g (-x)) :=
    hExp.mul (hg.comp contDiff_neg)
  exact compactLogMellin_right_line_evaluation hd
    (hc.comp_homeomorph (Homeomorph.neg ℝ)).mul_left a y

private noncomputable def reflectedLogProfile (g : ℝ → ℂ) (x : ℝ) : ℂ :=
  g x * exp (2 * x) + g (-x) * exp x

private theorem reflectedMellin_eq_fourierInv (g : ℝ → ℂ) (hg : Continuous g)
    (hc : HasCompactSupport g) (t : ℝ) :
    let s : ℂ := 2 + (t : ℂ) * I
    compactLogMellin g s + compactLogMellin g (1 - s) =
      𝓕⁻ (reflectedLogProfile g) ((2 * Real.pi)⁻¹ * t) := by
  dsimp only
  let s : ℂ := 2 + (t : ℂ) * I
  let f (x : ℝ) := g x * exp (s * x)
  let k (x : ℝ) := g x * exp ((1 - s) * x)
  have hf : Continuous f := by dsimp [f]; fun_prop
  have hk : Continuous k := by dsimp [k]; fun_prop
  have hfi : Integrable f := hf.integrable_of_hasCompactSupport hc.mul_right
  have hki : Integrable k := hk.integrable_of_hasCompactSupport hc.mul_right
  change (∫ x, f x) + (∫ x, k x) = _
  rw [← integral_neg_eq_self k volume, ← integral_add hfi hki.comp_neg, Real.fourierInv_eq']
  congr 1
  funext x
  have hphase : (2 * Real.pi * inner ℝ x ((2 * Real.pi)⁻¹ * t) : ℝ) = t * x := by
    rw [Real.inner_apply]
    field_simp [Real.pi_ne_zero]
  rw [hphase, Complex.ofReal_mul, smul_eq_mul]
  dsimp [f, k, s, reflectedLogProfile]
  rw [show ((2 + (t : ℂ) * I) * (x : ℂ)) = 2 * (x : ℂ) + (t : ℂ) * x * I by ring,
    show ((1 - (2 + (t : ℂ) * I)) * ((-x : ℝ) : ℂ)) = (x : ℂ) + (t : ℂ) * x * I by
      push_cast; ring, Complex.exp_add, Complex.exp_add]
  ring

/-- In ordinary angular frequency, inversion of the combined Mellin test
recovers the weighted profile and its reflection. -/
public theorem compactLogMellin_reflected_inversion {g : ℝ → ℂ}
    (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g) (y : ℝ) :
    let s := fun t : ℝ ↦ (2 : ℂ) + (t : ℂ) * I
    let W := fun t ↦ compactLogMellin g (s t) + compactLogMellin g (1 - s t)
    (∫ t, W t * exp (-(t : ℂ) * y * I)) / (2 * (Real.pi : ℂ)) =
      g y * exp (2 * y) + g (-y) * exp y := by
  dsimp only
  let h := reflectedLogProfile g
  let a : ℝ := 2 * Real.pi
  let W (t : ℝ) := compactLogMellin g (2 + (t : ℂ) * I) +
      compactLogMellin g (1 - (2 + (t : ℂ) * I))
  have hFourier (t : ℝ) : W t = 𝓕⁻ h (a⁻¹ * t) :=
    reflectedMellin_eq_fourierInv g hg.continuous hc t
  have hh : Continuous h := by
    have := hg.continuous
    unfold h reflectedLogProfile
    fun_prop
  have hhcomp : HasCompactSupport h :=
    hc.mul_right.add (hc.comp_homeomorph (Homeomorph.neg ℝ)).mul_right
  have hW : Integrable W := (integrable_compactLogMellin_vertical hg hc 2).add
    (integrable_compactLogMellin_reflected_vertical hg hc 2)
  exact angularFourier_inversion hh (hh.integrable_of_hasCompactSupport hhcomp) hW hFourier y

/-- Expand the positive real base power at `2 + it` without a logarithm
branch ambiguity. -/
public theorem rightLine_cpow_inv {n : ℝ} (hn : 0 < n) (t : ℝ) :
    ((n : ℂ) ^ ((2 : ℂ) + (t : ℂ) * I))⁻¹ =
      ((n : ℂ) ^ (2 : ℕ))⁻¹ * exp (-(t : ℂ) * Real.log n * I) := by
  have hn' := Complex.ofReal_ne_zero.mpr hn.ne'
  rw [Complex.cpow_def_of_ne_zero hn', ← Complex.ofReal_log hn.le, ← Complex.exp_neg,
    show -((Real.log n : ℂ) * (2 + (t : ℂ) * I)) =
      -((Real.log n : ℂ) + Real.log n) + (-(t : ℂ) * Real.log n * I) by ring,
    Complex.exp_add, Complex.exp_neg, Complex.exp_add, Complex.ofReal_log hn.le,
    Complex.exp_log hn', pow_two]

end Masullo
