module

public import Props.ZetaContourLogDeriv
import Props.RationalExplicitFormulaResidues
import Lemmas.RationalCompletedZetaZeros
import Lemmas.ZetaContourHeights
import Mathlib.Tactic.Ring

/-!
# Growth on the rational completed-zeta contour

For (B.4.2.1), p. 614, Masullo cites Lang for the growth of the completed
logarithmic derivative. In place of Lang's global product estimate, use
`entireZeta_logDeriv_le_moving_disk` and subtract the two pole terms.
On the selected horizontal edges, the quadratic separation margin costs
at most two powers of the actual height. On the vertical edges there is
fixed separation, and compactness and reflection give the all-height bound.
These are the inputs to the contour limit, not the limit itself.
-/

open Complex Filter Metric Set
open scoped Topology

namespace Masullo

/-- Away from the poles and zeros, undoing the pole clearing subtracts the
logarithmic derivatives of the linear factors at `0` and `1`. -/
public theorem completedZeta_logDeriv_eq_entireZeta {z : ℂ} (h0 : z ≠ 0) (h1 : z ≠ 1)
    (hz : completedRiemannZeta z ≠ 0) :
    logDeriv completedRiemannZeta z = logDeriv entireZeta z - 1 / z - 1 / (z - 1) := by
  have heq : completedRiemannZeta =ᶠ[𝓝 z] fun w ↦ entireZeta w / (w * (w - 1)) := by
    filter_upwards [eventually_ne_nhds h0, eventually_ne_nhds h1] with w hw0 hw1
    exact completedZeta_eq_quotient hw0 hw1
  have hf : entireZeta z ≠ 0 := by
    intro hf
    exact hz (by rw [completedZeta_eq_quotient h0 h1, hf, zero_div])
  have hs := sub_ne_zero.mpr h1
  rw [(logDeriv_congr_nhds heq).eq_of_nhds,
    logDeriv_fun_div (g := fun w : ℂ ↦ w * (w - 1)) z hf (mul_ne_zero h0 hs)
      (entireZeta_analyticOnNhd z trivial).differentiableAt (by fun_prop),
    logDeriv_fun_mul (f := fun w : ℂ ↦ w) (g := fun w : ℂ ↦ w - 1) z h0 hs
      (by fun_prop) (by fun_prop), logDeriv_id',
    logDeriv_apply (fun w : ℂ ↦ w - 1)]
  have hd : deriv (fun w : ℂ ↦ w - 1) z = 1 := by simp
  rw [hd, sub_add_eq_sub_sub]

private theorem completedZeta_logDeriv_le_entireZeta_add_two {z : ℂ}
    (ht : 1 ≤ |z.im|) (hz : completedRiemannZeta z ≠ 0) :
    ‖logDeriv completedRiemannZeta z‖ ≤ ‖logDeriv entireZeta z‖ + 2 := by
  have h0 : z ≠ 0 := by rintro rfl; norm_num at ht
  have h1 : z ≠ 1 := by rintro rfl; norm_num at ht
  have hp (w : ℂ) (hw : 1 ≤ |w.im|) : ‖1 / w‖ ≤ 1 := by
    rw [norm_div, norm_one]
    have hn := hw.trans (abs_im_le_norm w)
    exact (div_le_one (zero_lt_one.trans_le hn)).mpr hn
  have h₀ := hp z ht
  have h₁ := hp (z - 1) (by simpa using ht)
  rw [completedZeta_logDeriv_eq_entireZeta h0 h1 hz]
  exact (norm_sub_le _ _).trans (by linarith [norm_sub_le (logDeriv entireZeta z) (1 / z)])

private theorem completedZeta_ne_zero_of_separated {z : ℂ} (h0 : z ≠ 0) (h1 : z ≠ 1)
    {δ : ℝ} (hδ : 0 < δ) (hsep : ∀ ρ : criticalStripZetaZeros, δ ≤ ‖z - (ρ : ℂ)‖) :
    completedRiemannZeta z ≠ 0 := by
  intro hz
  let ρ : criticalStripZetaZeros := ⟨z,
    (completedZeta_eq_zero_iff_mem_criticalStripZetaZeros h0 h1).mp hz⟩
  exact hδ.not_ge (by simpa [ρ] using hsep ρ)

/-- Every unit interval with integer left endpoint of modulus at least two
contains an ordinate separated from all zeros, with a uniform cubic bound
in the actual height on the entire closed horizontal edge. -/
public theorem exists_height_completedZeta_logDeriv_le :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ m : ℤ, 2 ≤ |(m : ℝ)| → ∃ t : ℝ,
      (m : ℝ) < t ∧ t < (m : ℝ) + 1 ∧
      (∀ ρ : criticalStripZetaZeros, c / (1 + |(m : ℝ)|) ^ 2 ≤ |t - (ρ : ℂ).im|) ∧
      ∀ σ ∈ Icc (-1 : ℝ) 2,
        ‖logDeriv completedRiemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ≤ C * (1 + |t|) ^ 3 := by
  obtain ⟨c, hc, hchoose⟩ := exists_height_separated_from_zeta_zeros
  obtain ⟨D, K, hD, hK, hlocal⟩ := entireZeta_logDeriv_le_moving_disk
  refine ⟨c, D + 2 + 4 * K / c, hc, by positivity, fun m hm ↦ ?_⟩
  obtain ⟨t, hmt, htm, hsep⟩ := hchoose m
  refine ⟨t, hmt, htm, hsep, fun σ hσ ↦ ?_⟩
  let z : ℂ := (σ : ℂ) + (t : ℂ) * I
  let δ : ℝ := c / (1 + |(m : ℝ)|) ^ 2
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hm' : |(m : ℝ)| ≤ |t| + 1 := by
    exact abs_le.mpr ⟨by linarith [neg_abs_le t], by linarith [le_abs_self t]⟩
  have ht : 1 ≤ |t| := by linarith
  have him : z.im = t := by simp [z]
  have him₁ : 1 ≤ |z.im| := by rwa [him]
  have hz0 : z ≠ 0 := by intro h; rw [h] at him₁; norm_num at him₁
  have hz1 : z ≠ 1 := by intro h; rw [h] at him₁; norm_num at him₁
  -- Real-part inclusion gives the disk; imaginary-part separation excludes zeros.
  have hball : z ∈ closedBall (2 + (t : ℂ) * I) 3 := by
    rw [mem_closedBall, dist_eq_norm,
      show z - (2 + (t : ℂ) * I) = ((σ - 2 : ℝ) : ℂ) by push_cast; dsimp [z]; ring,
      norm_real, Real.norm_eq_abs, abs_le]
    exact ⟨by linarith [hσ.1], by linarith [hσ.2]⟩
  have hdist (ρ : criticalStripZetaZeros) : δ ≤ ‖z - (ρ : ℂ)‖ :=
    (hsep ρ).trans (by simpa only [sub_im, him] using abs_im_le_norm (z - (ρ : ℂ)))
  have hn := completedZeta_ne_zero_of_separated hz0 hz1 hδ hdist
  have hL : ‖logDeriv entireZeta z‖ ≤ D * (1 + |t|) + K * (1 + |t|) / δ :=
    hlocal t ht z hball δ hδ hdist
  -- Convert the inverse margin to a quadratic cost in the actual height.
  have hbudget : K * (1 + |t|) / δ ≤ (4 * K / c) * (1 + |t|) ^ 3 := by
    dsimp only [δ]
    rw [div_div_eq_mul_div]
    calc
      _ ≤ K * (1 + |t|) * (2 * (1 + |t|)) ^ 2 / c := by
        gcongr
        linarith
      _ = _ := by ring
  have ht₃ : 1 + |t| ≤ (1 + |t|) ^ 3 := le_self_pow₀ (by simp) (by decide)
  calc
    ‖logDeriv completedRiemannZeta z‖ ≤ ‖logDeriv entireZeta z‖ + 2 :=
      completedZeta_logDeriv_le_entireZeta_add_two him₁ hn
    _ ≤ D * (1 + |t|) + (4 * K / c) * (1 + |t|) ^ 3 + 2 := by linarith
    _ ≤ (D + 2 + 4 * K / c) * (1 + |t|) ^ 3 := by
      have hlinear := mul_le_mul_of_nonneg_left ht₃ hD.le
      have hp : 1 ≤ (1 + |t|) ^ 3 := (by simp : 1 ≤ 1 + |t|).trans ht₃
      linarith

/-- On the two zero-free vertical edges, the completed logarithmic derivative
has a uniform linear bound, including at bounded heights. -/
public theorem completedZeta_logDeriv_le_vertical :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ,
      ‖logDeriv completedRiemannZeta (2 + (t : ℂ) * I)‖ ≤ C * (1 + |t|) ∧
      ‖logDeriv completedRiemannZeta (-1 + (t : ℂ) * I)‖ ≤ C * (1 + |t|) := by
  obtain ⟨D, K, hD, hK, hlocal⟩ := entireZeta_logDeriv_le_moving_disk
  let r : ℝ → ℂ := fun t ↦ 2 + (t : ℂ) * I
  have hr0 (t : ℝ) : r t ≠ 0 := by intro h; have := congrArg Complex.re h; norm_num [r] at this
  have hr1 (t : ℝ) : r t ≠ 1 := by intro h; have := congrArg Complex.re h; norm_num [r] at this
  have hrsep (t : ℝ) (ρ : criticalStripZetaZeros) : 1 ≤ ‖r t - (ρ : ℂ)‖ := by
    have hρ := (mem_criticalStripZetaZeros.mp ρ.property).2.2
    refine le_trans ?_ (abs_re_le_norm (r t - (ρ : ℂ)))
    simp only [sub_re, r, add_re, re_ofNat, mul_I_re, ofReal_im, neg_zero, add_zero]
    exact (by linarith : 1 ≤ 2 - (ρ : ℂ).re).trans (le_abs_self _)
  have hnr (t : ℝ) : completedRiemannZeta (r t) ≠ 0 :=
    completedZeta_ne_zero_of_separated (hr0 t) (hr1 t) zero_lt_one (hrsep t)
  -- At bounded heights use analyticity and the maximum on a compact interval.
  have hcont : Continuous (fun t ↦ ‖logDeriv completedRiemannZeta (r t)‖) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    have ha := analyticAt_completedZeta (hr0 t) (hr1 t)
    exact ((ha.deriv.div ha (hnr t)).continuousAt.comp (by dsimp [r]; fun_prop)).norm
  obtain ⟨t₀, _, hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr (by norm_num : (-1 : ℝ) ≤ 1))
    hcont.continuousOn
  let C := D + K + 2 + ‖logDeriv completedRiemannZeta (r t₀)‖
  have hC : 0 < C := by dsimp [C]; positivity
  have hright (t : ℝ) : ‖logDeriv completedRiemannZeta (r t)‖ ≤ C * (1 + |t|) := by
    by_cases ht : 1 ≤ |t|
    · have hL := hlocal t ht (r t) (mem_closedBall_self (by norm_num)) 1 zero_lt_one (hrsep t)
      have ht' : 1 ≤ |(r t).im| := by simpa [r] using ht
      have hb := completedZeta_logDeriv_le_entireZeta_add_two ht' (hnr t)
      rw [div_one] at hL
      dsimp only [C]
      nlinarith only [hb, hL, abs_nonneg t, norm_nonneg (logDeriv completedRiemannZeta (r t₀)),
        mul_nonneg (abs_nonneg t) (norm_nonneg (logDeriv completedRiemannZeta (r t₀)))]
    · have ht' : t ∈ Icc (-1 : ℝ) 1 := abs_le.mp (le_of_not_ge ht)
      exact (hmax ht').trans (by dsimp [C]; nlinarith [mul_nonneg hC.le (abs_nonneg t)])
  refine ⟨C, hC, fun t ↦ ⟨hright t, ?_⟩⟩
  -- Reflection transports the bound to the left line, reversing the height.
  let z : ℂ := -1 + (t : ℂ) * I
  have hz0 : z ≠ 0 := by intro h; have := congrArg Complex.re h; norm_num [z] at this
  have hz1 : z ≠ 1 := by intro h; have := congrArg Complex.re h; norm_num [z] at this
  change ‖logDeriv completedRiemannZeta z‖ ≤ _
  rw [completedZeta_logDeriv_reflection hz0 hz1, norm_neg,
    show 1 - z = r (-t) by simp only [z, r, ofReal_neg]; ring]
  simpa only [abs_neg] using hright (-t)

end Masullo
