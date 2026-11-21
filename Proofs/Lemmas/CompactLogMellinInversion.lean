module

public import Props.CompactLogMellin
import Lemmas.ZetaRightLine
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Tactic.FieldSimp

/-! # Fourier inversion of the reflected right-line Mellin test -/

open Complex MeasureTheory
open scoped ContDiff FourierTransform

namespace Masullo

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
  have ha : 0 < a := by dsimp [a]; positivity
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
  obtain ⟨B, _, hB⟩ := compactLogMellin_vertical_decay hg hc 2 4
  have hΦ : Continuous (compactLogMellin g) := continuous_iff_continuousAt.mpr fun s ↦
    (analyticAt_compactLogMellin hg.continuous hc s).continuousAt
  have hW : Integrable W := integrable_completedZeta_reflected_test hΦ (B := B)
    (fun t ↦ by simpa using hB 2 t (by norm_num))
    (fun t ↦ by simpa using hB (-1) t (by norm_num))
  have hf : Integrable (𝓕⁻ h) :=
    (integrable_comp_mul_left_iff _ (inv_ne_zero ha.ne')).mp (by simpa only [← hFourier] using hW)
  have hf' : Integrable (𝓕 h) := by
    simpa only [Real.fourierInv_eq_fourier_neg, neg_neg] using hf.comp_neg
  have hinv := congrFun (hh.fourier_fourierInv_eq (hh.integrable_of_hasCompactSupport hhcomp) hf') y
  rw [Real.fourier_real_eq_integral_exp_smul] at hinv
  let F (v : ℝ) := exp ((↑(-2 * Real.pi * v * y) : ℂ) * I) • 𝓕⁻ h v
  have hscale (t : ℝ) : W t * exp (-(t : ℂ) * y * I) = F (a⁻¹ * t) := by
    dsimp only [F]
    rw [hFourier, show -2 * Real.pi * (a⁻¹ * t) * y = -t * y by
      dsimp [a]; field_simp [Real.pi_ne_zero]]
    simp only [Complex.ofReal_mul, Complex.ofReal_neg, smul_eq_mul, mul_comm]
  rw [← show (a : ℂ) = 2 * (Real.pi : ℂ) by simp [a]]
  change (∫ t, W t * exp (-(t : ℂ) * y * I)) / (a : ℂ) = h y
  simp_rw [hscale]
  rw [Measure.integral_comp_mul_left, inv_inv, abs_of_pos ha, Complex.real_smul,
    show (∫ v, F v) = h y from hinv]
  exact mul_div_cancel_left₀ _ (Complex.ofReal_ne_zero.mpr ha.ne')

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
