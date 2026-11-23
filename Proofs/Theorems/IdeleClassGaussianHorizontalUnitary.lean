module

public import Theorems.IdeleClassGaussianContinuation
public import Mathlib.Analysis.Meromorphic.Divisor
import Theorems.FiniteHeckeEulerProductLowerBound
import Lemmas.AnalyticHorizontalHeights

/-! # Linear divisor counts and separated heights for unitary Hecke characters

The local Gamma lower bounds and the finite Euler product bound control the
center of Jensen's disk for the *same* entire numerator as in the Gaussian
continuation. Its full-order count on the closed disk gives a single ordinate
for both horizontal edges. The poles are translated by the actual character
phase, so the conclusion concerns separation from zeros of the pole-cleared
numerator, not a bound for the logarithmic derivative at a possible pole.

This supplies inputs to the horizontal argument invoked in §B.4.2.1, p. 614,
and Definition B.3.1.1 and Lemma B.3.1.2, pp. 604–605 (source comparison
provisional). It does not use a functional equation or locate the zeros.

Owning candidate check session: `01a205e0-3602-798e-bd35-abc4a6037af2`.
-/

open Complex IsDedekindDomain Metric NumberField

namespace Masullo

variable {K : Type*} [Field K] [NumberField K]

local notation "C" => IdeleClassGroup (𝓞 K) K
local notation "I₁" => ideleNormOne (K := K)
local notation "C₁" => ideleClassNormOne (K := K)
local notation "W" => (NumberField.Units.dirichletUnitTheorem.w₀ : InfinitePlace K)
local notation "τ" => ideleClassLogSplit (ideleClassLogSection W) (ideleClassLogNorm_section W)

private theorem exists_exp_le_norm_completedHeckeEulerProduct_rightLine
    (χ : HeckeCharacter (𝓞 K) K) (hχ : ∀ a : C, ‖χ a‖ = 1)
    (hlocal : ∀ v : InfinitePlace K, ∃ A : ℝ, 0 < A ∧ ∀ t : ℝ,
      Real.exp (-A * (1 + |t|)) ≤ ‖localHeckeGammaFactor χ hχ v (2 + (t : ℂ) * I)‖) :
    ∃ A : ℝ, 0 < A ∧ ∀ t : ℝ,
      Real.exp (-A * (1 + |t|)) ≤ ‖completedHeckeEulerProduct χ hχ (2 + (t : ℂ) * I)‖ := by
  classical
  choose a ha hloc using hlocal
  let S := ∑ v : InfinitePlace K, a v
  let b := finiteHeckeRightLineLoss K
  have hS : 0 ≤ S := Finset.sum_nonneg fun v _ ↦ (ha v).le
  refine ⟨S + |b| + 1, by positivity, fun t ↦ ?_⟩
  let Y := 1 + |t|
  let c : ℂ := 2 + (t : ℂ) * I
  have hY : 1 ≤ Y := le_add_of_nonneg_right (abs_nonneg t)
  have hb : b ≤ (|b| + 1) * Y := calc
    b ≤ |b| + 1 := by linarith [le_abs_self b]
    _ ≤ (|b| + 1) * Y := le_mul_of_one_le_right (by positivity) hY
  have harch : Real.exp (-S * Y) ≤ ‖∏ v, localHeckeGammaFactor χ hχ v c‖ := by
    rw [show -S * Y = ∑ v : InfinitePlace K, -a v * Y by
      simp only [S, Finset.sum_mul, Finset.sum_neg_distrib, neg_mul],
      Real.exp_sum, norm_prod]
    exact Finset.prod_le_prod₀ (fun _ _ ↦ Real.exp_nonneg _) (fun v _ ↦ hloc v t)
  change _ ≤ ‖(∏ v, localHeckeGammaFactor χ hχ v c) * finiteHeckeCharacterEulerProduct χ c‖
  rw [norm_mul]
  calc
    _ ≤ Real.exp (-S * Y - b) := by
      apply Real.exp_le_exp.mpr
      change -(S + |b| + 1) * Y ≤ -S * Y - b
      linarith only [hb]
    _ = Real.exp (-S * Y) * Real.exp (-b) := by rw [sub_eq_add_neg, Real.exp_add]
    _ ≤ _ := mul_le_mul harch (exp_le_norm_finiteHeckeCharacterEulerProduct χ hχ
      (s := c) (by simp [c])) (Real.exp_nonneg _) (norm_nonneg _)

private theorem norm_le_quadratic_on_center_sphere {H : ℂ → ℂ} {B : ℝ} (hB : 0 ≤ B)
    (hg : ∀ s : ℂ, -4 ≤ s.re → s.re ≤ 8 → ‖H s‖ ≤ B * (1 + |s.im|)^2)
    (t : ℝ) {z : ℂ} (hz : z ∈ sphere (2 + (t : ℂ) * I) 6) :
    ‖H z‖ ≤ (49 * B + 1) * (1 + |t|)^2 := by
  let c : ℂ := 2 + (t : ℂ) * I
  have hd : ‖z - c‖ = 6 := by simpa only [mem_sphere, dist_eq_norm] using hz
  have hr := abs_re_le_norm (z - c)
  have hi := abs_im_le_norm (z - c)
  rw [hd, sub_re, show c.re = 2 by simp [c]] at hr
  rw [hd, sub_im, show c.im = t by simp [c]] at hi
  have ha : |z.im| ≤ 6 + |t| := by
    have h := abs_add_le (z.im - t) t
    rw [sub_add_cancel] at h
    linarith
  calc
    ‖H z‖ ≤ B * (1 + |z.im|)^2 := hg z (by linarith [(abs_le.mp hr).1])
      (by linarith [(abs_le.mp hr).2])
    _ ≤ B * (7 * (1 + |t|))^2 := by
      gcongr
      linarith [abs_nonneg t]
    _ = (49 * B) * (1 + |t|)^2 := by ring
    _ ≤ (49 * B + 1) * (1 + |t|)^2 := by gcongr; linarith

private theorem exists_closedBall_divisor_count_of_center_bound {H : ℂ → ℂ}
    (hH : Differentiable ℂ H) {B A : ℝ} (hB : 0 ≤ B) (hA : 0 < A)
    (hstrip : ∀ s : ℂ, -4 ≤ s.re → s.re ≤ 8 → ‖H s‖ ≤ B * (1 + |s.im|)^2)
    (hlower : ∀ t : ℝ, Real.exp (-A * (1 + |t|)) ≤ ‖H (2 + (t : ℂ) * I)‖) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ t : ℝ, let c : ℂ := 2 + (t : ℂ) * I
      H c ≠ 0 ∧ ((∑ᶠ ρ, MeromorphicOn.divisor H (closedBall c 5) ρ : ℤ) : ℝ) ≤ C₀ * (1 + |t|) := by
  let M₀ := 49 * B + 1
  have hM₀ : 1 ≤ M₀ := by dsimp [M₀]; linarith
  have hM₀pos := zero_lt_one.trans_le hM₀
  let b := Real.log M₀ + 2 + A
  have hb : 0 < b := by dsimp [b]; linarith [Real.log_nonneg hM₀]
  let d := Real.log (6 / 5 : ℝ)
  have hd : 0 < d := Real.log_pos (by norm_num)
  refine ⟨b / d, div_pos hb hd, ?_⟩
  intro t c
  let Y := 1 + |t|
  let M := M₀ * Y^2
  have hY : 1 ≤ Y := le_add_of_nonneg_right (abs_nonneg t)
  have hYpos := zero_lt_one.trans_le hY
  have hM : 1 ≤ M := one_le_mul_of_one_le_of_one_le hM₀ (one_le_pow₀ hY)
  have hnorm : 0 < ‖H c‖ := (Real.exp_pos _).trans_le (hlower t)
  have hc := norm_pos_iff.mp hnorm
  have hlog := Real.log_le_log (Real.exp_pos _) (hlower t)
  rw [Real.log_exp] at hlog
  have hcost : Real.log (M / ‖H c‖) ≤ b * Y := by
    rw [Real.log_div (zero_lt_one.trans_le hM).ne' hnorm.ne']
    have hMlog : Real.log M = Real.log M₀ + 2 * Real.log Y := by
      dsimp only [M]
      rw [Real.log_mul hM₀pos.ne' (pow_ne_zero _ hYpos.ne'), Real.log_pow]
      norm_num
    rw [hMlog]
    have hYlog := Real.log_le_sub_one_of_pos hYpos
    have hBlin := le_mul_of_one_le_right (Real.log_nonneg hM₀) hY
    change -A * Y ≤ Real.log ‖H c‖ at hlog
    dsimp only [b]
    linarith only [hlog, hYlog, hBlin]
  have hsphere : ∀ z ∈ sphere c 6, ‖H z‖ ≤ M := fun z hz ↦
    norm_le_quadratic_on_center_sphere hB hstrip t hz
  have hj := AnalyticOnNhd.sum_divisor_le (f := H) (c := c) (r := 5) (R := 6)
    (by norm_num) (by norm_num) hM (fun z _ ↦ hH.analyticAt z) hc (by simpa using hsphere)
  rw [abs_of_pos (by norm_num : (0 : ℝ) < 5)] at hj
  refine ⟨hc, ?_⟩
  calc
    _ ≤ Real.log (M / ‖H c‖) / d := hj
    _ ≤ b * Y / d := div_le_div_of_nonneg_right hcost hd.le
    _ = (b / d) * Y := by ring

variable [∀ v : InfinitePlace K, MeasurableSpace v.Completionˣ]
  [∀ v : InfinitePlace K, BorelSpace v.Completionˣ]
  [MeasurableSpace (IdeleClassGroup (𝓞 K) K)] [BorelSpace (IdeleClassGroup (𝓞 K) K)]
  [MeasurableSpace (ideleNormOne (K := K))]
  [MeasurableSpace (ideleClassNormOne (K := K))] [BorelSpace (ideleClassNormOne (K := K))]
  [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)ˣ]
  [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletionIntegers K)ˣ]
  [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)ˣ]
  [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletionIntegers K)ˣ]
  [MeasurableSpace (IdeleGroup (𝓞 K) K)] [BorelSpace (IdeleGroup (𝓞 K) K)]
  [BorelSpace (ideleNormOne (K := K))]

/-- Local exponential lower bounds at the infinite places give a linear
full-order count and separated horizontal edges for the exact pole-cleared
Gaussian continuation. The single `T` works at both `T` and `-T`. -/
public theorem exists_completedHeckeEulerProduct_gaussianContinuation_horizontal_of_local
    (χ : HeckeCharacter (𝓞 K) K) (hχ : ∀ a : C, ‖χ a‖ = 1)
    (v : InfinitePlace K) (r : ClassGroup (𝓞 K) → I₁) (hr : ∀ p, ideleIdealClassNormOne (r p) = p)
    (hlocal : ∀ w : InfinitePlace K, ∃ A : ℝ, 0 < A ∧ ∀ t : ℝ,
      Real.exp (-A * (1 + |t|)) ≤ ‖localHeckeGammaFactor χ hχ w (2 + (t : ℂ) * I)‖) :
    ∃ (lam : ℝ) (L H : ℂ → ℂ),
      let z₀ := -((lam : ℂ) * I)
      let z₁ := 1 + z₀
      (∀ x : ℝ, χ (τ (Multiplicative.ofAdd x, 1)) = exp (((lam * x : ℝ) : ℂ) * I)) ∧
      Meromorphic L ∧ (∀ s, s ≠ z₁ → s ≠ z₀ → DifferentiableAt ℂ L s) ∧
      ((∃ h : C₁, χ (h : C) ≠ 1) → Differentiable ℂ L) ∧
      (∀ s, 1 < s.re → L s = completedHeckeEulerProduct χ hχ s) ∧
      Differentiable ℂ H ∧ (∀ s, s ≠ z₁ → s ≠ z₀ → H s = (s - z₁) * (s - z₀) * L s) ∧
      (∀ a b : ℝ, ∃ M : ℝ, 0 ≤ M ∧ ∀ s : ℂ, a ≤ s.re → s.re ≤ b →
        ‖H s‖ ≤ M * (1 + |s.im|)^2) ∧
      (∃ A : ℝ, 0 < A ∧ ∀ t : ℝ, Real.exp (-A * (1 + |t|)) ≤ ‖H (2 + (t : ℂ) * I)‖) ∧
      ∃ C₀ : ℝ, 0 < C₀ ∧
        (∀ t : ℝ, let c : ℂ := 2 + (t : ℂ) * I
          H c ≠ 0 ∧ ((∑ᶠ ρ, MeromorphicOn.divisor H (closedBall c 5) ρ : ℤ) : ℝ) ≤ C₀ * (1 + |t|)) ∧
        ∀ n : ℕ, 1 ≤ n → ∃ T : ℝ, (n : ℝ) < T ∧ T < (n : ℝ) + 1 ∧
          ∀ z : ℂ, -1 ≤ z.re → z.re ≤ 2 → |z.im| = T →
            z ∈ closedBall (2 + (z.im : ℂ) * I) 3 ∧
              ∀ ρ : ℂ, H ρ = 0 → 1 / (16 * (C₀ + 1) * (1 + (n : ℝ))) ≤ ‖z - ρ‖ := by
  obtain ⟨T, ν, F, E, μ, lam, h⟩ := exists_completedHeckeEulerProduct_gaussianContinuation χ hχ v r hr
  dsimp only at h
  obtain ⟨_, _, _, _, _, _, _, hphase, hmero, hdiffL, hentireL, hEuler, H, hH, _, _, hclear,
    hgrowth⟩ := h
  -- Keep both witnesses from the continuation above; only use their product identity on Re s = 2.
  refine ⟨lam, _, H, hphase, hmero, hdiffL, hentireL, hEuler, hH, hclear, hgrowth, ?_⟩
  obtain ⟨A, hA, hAprod⟩ := exists_exp_le_norm_completedHeckeEulerProduct_rightLine χ hχ hlocal
  have hlower (t : ℝ) : Real.exp (-A * (1 + |t|)) ≤ ‖H (2 + (t : ℂ) * I)‖ := by
    let c : ℂ := 2 + (t : ℂ) * I
    let z₀ : ℂ := -((lam : ℂ) * I)
    let z₁ : ℂ := 1 + z₀
    have hc₀ : (c - z₀).re = 2 := by simp [c, z₀]
    have hc₁ : (c - z₁).re = 1 := by simp [c, z₁, z₀]; norm_num
    have hnorm₀ : 1 ≤ ‖c - z₀‖ := by linarith [re_le_norm (c - z₀)]
    have hnorm₁ : 1 ≤ ‖c - z₁‖ := by linarith [re_le_norm (c - z₁)]
    have hne₀ := sub_ne_zero.mp (norm_pos_iff.mp (zero_lt_one.trans_le hnorm₀))
    have hne₁ := sub_ne_zero.mp (norm_pos_iff.mp (zero_lt_one.trans_le hnorm₁))
    have he := hEuler c (by simp [c])
    have hce : H c = (c - z₁) * (c - z₀) * completedHeckeEulerProduct χ hχ c := by
      calc
        H c = _ := hclear c hne₁ hne₀
        _ = _ := by rw [he]
    rw [hce, norm_mul, norm_mul]
    exact (hAprod t).trans (le_mul_of_one_le_left (norm_nonneg _)
      (one_le_mul_of_one_le_of_one_le hnorm₁ hnorm₀))
  obtain ⟨B, hB, hstrip⟩ := hgrowth (-4) 8
  obtain ⟨C₀, hC₀, hcount⟩ := exists_closedBall_divisor_count_of_center_bound hH hB hA hstrip hlower
  refine ⟨⟨A, hA, hlower⟩, C₀, hC₀, hcount, fun n hn ↦ ?_⟩
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  obtain ⟨T, hT, hsep⟩ := exists_symmetric_horizontal_separation (fun z _ ↦ hH.analyticAt z)
    hC₀ hcount hn'
  exact ⟨T, hT.1, hT.2, hsep⟩

end Masullo
