module

public import Lemmas.AnalyticGoodHeightDisk
public import Theorems.IdeleClassGaussianHorizontalCount

/-! # Logarithmic derivative on good horizontal edges

The completed Hecke continuation is nonvanishing and has a uniform quadratic
logarithmic-derivative bound at common positive and negative heights.
-/

open Complex Filter IsDedekindDomain Metric NumberField
open scoped Topology

namespace Masullo

/-- Transfer the logarithmic-derivative bound across the two clearing factors.
Their norms are at least their imaginary displacements, so at heights more
than one above `|lam|` they each cost at most one. -/
private theorem logDeriv_le_of_gaussian_clearing {L H : ℂ → ℂ} {lam : ℝ} {z : ℂ}
    (hL : ∀ s, s ≠ 1 - (lam : ℂ) * I → s ≠ -((lam : ℂ) * I) → DifferentiableAt ℂ L s)
    (hclear : ∀ s, s ≠ 1 - (lam : ℂ) * I → s ≠ -((lam : ℂ) * I) →
      H s = (s - (1 - (lam : ℂ) * I)) * (s - -((lam : ℂ) * I)) * L s)
    (hH : H z ≠ 0) (hz : |lam| + 1 < |z.im|) :
    L z ≠ 0 ∧ ‖logDeriv L z‖ ≤ ‖logDeriv H z‖ + 2 := by
  let a : ℂ := 1 - (lam : ℂ) * I
  let b : ℂ := -((lam : ℂ) * I)
  have hab (w : ℂ) (hw : w.im = -lam) : 1 < ‖z - w‖ := by
    have h := abs_add_le (z.im - w.im) w.im
    rw [sub_add_cancel, hw, abs_neg] at h
    have h' := Complex.abs_im_le_norm (z - w)
    rw [sub_im, hw] at h'
    linarith only [hz, h, h']
  have ha := hab a (by simp [a])
  have hb := hab b (by simp [b])
  have hza := sub_ne_zero.mp (norm_pos_iff.mp (zero_lt_one.trans ha))
  have hzb := sub_ne_zero.mp (norm_pos_iff.mp (zero_lt_one.trans hb))
  have hLz : L z ≠ 0 := by
    intro hz0
    exact hH (by rw [hclear z hza hzb, hz0, mul_zero])
  have heq : H =ᶠ[𝓝 z] fun w ↦ (w - a) * (w - b) * L w := by
    filter_upwards [eventually_ne_nhds hza, eventually_ne_nhds hzb] with w hwa hwb
    exact hclear w hwa hwb
  have hlog : logDeriv H z = (1 / (z - a) + 1 / (z - b)) + logDeriv L z := by
    rw [(logDeriv_congr_nhds heq).eq_of_nhds,
      logDeriv_fun_mul (f := fun w : ℂ ↦ (w - a) * (w - b)) (g := L) z
        (mul_ne_zero (sub_ne_zero.mpr hza) (sub_ne_zero.mpr hzb)) hLz
        (by fun_prop) (hL z hza hzb),
      logDeriv_fun_mul (f := fun w : ℂ ↦ w - a) (g := fun w : ℂ ↦ w - b) z
        (sub_ne_zero.mpr hza) (sub_ne_zero.mpr hzb) (by fun_prop) (by fun_prop)]
    simp [logDeriv_apply]
  have hrearr : logDeriv L z = logDeriv H z - 1 / (z - a) - 1 / (z - b) := by
    rw [hlog]
    abel
  have hone (w : ℂ) (hw : 1 < ‖z - w‖) : ‖1 / (z - w)‖ ≤ 1 := by
    rw [norm_div, norm_one]
    exact (div_le_iff₀ (zero_lt_one.trans hw)).2 (by simpa using hw.le)
  refine ⟨hLz, ?_⟩
  rw [hrearr]
  calc
    _ ≤ ‖logDeriv H z - 1 / (z - a)‖ + ‖1 / (z - b)‖ := norm_sub_le _ _
    _ ≤ (‖logDeriv H z‖ + ‖1 / (z - a)‖) + ‖1 / (z - b)‖ := by
      gcongr
      exact norm_sub_le _ _
    _ ≤ ‖logDeriv H z‖ + 2 := by linarith [hone a ha, hone b hb]

variable {K : Type*} [Field K] [NumberField K]

local notation "C" => IdeleClassGroup (𝓞 K) K
local notation "I₁" => ideleNormOne (K := K)
local notation "C₁" => ideleClassNormOne (K := K)
local notation "W" => (NumberField.Units.dirichletUnitTheorem.w₀ : InfinitePlace K)
local notation "τ" => ideleClassLogSplit (ideleClassLogSection W) (ideleClassLogNorm_section W)

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

/-- The same Gaussian continuation that agrees with the completed Hecke Euler
product on the right is nonzero and has quadratic logarithmic-derivative
growth on both closed horizontal edges at a common sequence of heights. -/
public theorem exists_completedHeckeEulerProduct_gaussianContinuation_horizontal_logDeriv
    (χ : HeckeCharacter (𝓞 K) K) (hχ : ∀ a : C, ‖χ a‖ = 1)
    (v : InfinitePlace K) (r : ClassGroup (𝓞 K) → I₁) (hr : ∀ p, ideleIdealClassNormOne (r p) = p) :
    ∃ (lam : ℝ) (L H : ℂ → ℂ),
      let z₀ := -((lam : ℂ) * I)
      let z₁ := 1 + z₀
      (∀ x : ℝ, χ (τ (Multiplicative.ofAdd x, 1)) = exp (((lam * x : ℝ) : ℂ) * I)) ∧
      Meromorphic L ∧ (∀ s, s ≠ z₁ → s ≠ z₀ → DifferentiableAt ℂ L s) ∧
      ((∃ h : C₁, χ (h : C) ≠ 1) → Differentiable ℂ L) ∧
      (∀ s, 1 < s.re → L s = completedHeckeEulerProduct χ hχ s) ∧
      Differentiable ℂ H ∧ (∀ s, s ≠ z₁ → s ≠ z₀ → H s = (s - z₁) * (s - z₀) * L s) ∧
      ∃ D : ℝ, 0 < D ∧ ∃ T : ℕ → ℝ,
        (∀ n : ℕ, (n : ℝ) < T n ∧ |lam| + 1 < T n) ∧
        ∀ n (σ : ℝ), -1 ≤ σ → σ ≤ 2 →
          (L ((σ : ℂ) + (T n : ℂ) * I) ≠ 0 ∧
            ‖logDeriv L ((σ : ℂ) + (T n : ℂ) * I)‖ ≤ D * (1 + T n)^2) ∧
          (L ((σ : ℂ) + ((-T n : ℝ) : ℂ) * I) ≠ 0 ∧
            ‖logDeriv L ((σ : ℂ) + ((-T n : ℝ) : ℂ) * I)‖ ≤ D * (1 + T n)^2) := by
  classical
  obtain ⟨lam, L, H, hfreq, hmer, hdiff, hentire, heuler, hH, hclear, hstrip,
      ⟨A, hA, hlower⟩, C₀, hC₀, hcount, hheight⟩ :=
    exists_completedHeckeEulerProduct_gaussianContinuation_horizontal χ hχ v r hr
  obtain ⟨B, hB, hstripB⟩ := hstrip (-4) 8
  obtain ⟨m₀, hm₀⟩ := exists_nat_ge (|lam| + 1)
  have hm₀pos : 1 ≤ m₀ := by exact_mod_cast (show (1 : ℝ) ≤ m₀ by
    linarith [abs_nonneg lam])
  have hchoice (n : ℕ) := hheight (n + m₀) (by omega)
  choose T hTlo _ hTsep using hchoice
  have hT (n : ℕ) : (n : ℝ) < T n ∧ |lam| + 1 < T n := by
    have hlo := hTlo n
    push_cast at hlo
    exact ⟨lt_of_le_of_lt (le_add_of_nonneg_right (Nat.cast_nonneg m₀)) hlo,
      hm₀.trans_lt ((le_add_of_nonneg_left (Nat.cast_nonneg n)).trans_lt hlo)⟩
  let M₀ := 49 * B + 1
  let U₀ := Real.log M₀ + 2 + A
  have hM₀ : 1 ≤ M₀ := by dsimp [M₀]; linarith
  have hU₀ : 0 ≤ U₀ := by dsimp [U₀]; linarith [Real.log_nonneg hM₀]
  let D := 8 * (U₀ + C₀ * Real.log 5 + 1) + C₀ * (16 * (C₀ + 1)) + 2
  have hlog5 : 0 ≤ Real.log 5 := Real.log_nonneg (by norm_num)
  have hD : 0 < D := by dsimp [D]; positivity
  refine ⟨lam, L, H, hfreq, hmer, hdiff, hentire, heuler, hH, hclear, D, hD, T, hT, ?_⟩
  have hedge (n : ℕ) (z : ℂ) (hzlo : -1 ≤ z.re) (hzhi : z.re ≤ 2) (hzT : |z.im| = T n) :
      L z ≠ 0 ∧ ‖logDeriv L z‖ ≤ D * (1 + T n)^2 := by
    let c : ℂ := 2 + (z.im : ℂ) * I
    let Y := 1 + |z.im|
    let M := M₀ * Y^2
    let δ := 1 / (16 * (C₀ + 1) * (1 + ((n + m₀ : ℕ) : ℝ)))
    have hY : 1 ≤ Y := le_add_of_nonneg_right (abs_nonneg z.im)
    have hYpos := zero_lt_one.trans_le hY
    have hMpos : 0 < M := mul_pos (zero_lt_one.trans_le hM₀) (pow_pos hYpos _)
    have hδ : 0 < δ := by dsimp [δ]; positivity
    obtain ⟨hz, hsep⟩ := hTsep n z hzlo hzhi hzT
    have hHz : H z ≠ 0 := fun hzero ↦ hδ.not_ge (by simpa only [sub_self, norm_zero] using hsep z hzero)
    obtain ⟨hc, hN⟩ := hcount z.im
    have hbox (w : ℂ) (hw : w ∈ sphere c 6) : ‖H w‖ ≤ M := by
      have hd : ‖w - c‖ = 6 := by simpa only [mem_sphere, dist_eq_norm] using hw
      have hre := abs_re_le_norm (w - c)
      have him := abs_im_le_norm (w - c)
      rw [hd, sub_re, show c.re = 2 by simp [c]] at hre
      rw [hd, sub_im, show c.im = z.im by simp [c]] at him
      have ha : |w.im| ≤ 6 + |z.im| := by
        have h := abs_add_le (w.im - z.im) z.im
        rw [sub_add_cancel] at h
        linarith
      have hscale : 1 + |w.im| ≤ 7 * Y := by dsimp [Y]; linarith [abs_nonneg z.im]
      calc
        ‖H w‖ ≤ B * (1 + |w.im|)^2 := hstripB w (by linarith [(abs_le.mp hre).1])
          (by linarith [(abs_le.mp hre).2])
        _ ≤ B * (7 * Y)^2 := by gcongr
        _ = (49 * B) * Y^2 := by ring
        _ ≤ M := by dsimp [M, M₀]; gcongr; linarith
    have hloss : Real.log (M / ‖H c‖) ≤ U₀ * Y := by
      have hlog := Real.log_le_log (Real.exp_pos _) (hlower z.im)
      rw [Real.log_exp] at hlog
      change -A * Y ≤ Real.log ‖H c‖ at hlog
      rw [Real.log_div hMpos.ne' (norm_ne_zero_iff.mpr hc)]
      have hMlog : Real.log M = Real.log M₀ + 2 * Real.log Y := by
        dsimp only [M]
        rw [Real.log_mul (zero_lt_one.trans_le hM₀).ne' (pow_ne_zero _ hYpos.ne'), Real.log_pow]
        norm_num
      rw [hMlog]
      have hYlog := Real.log_le_sub_one_of_pos hYpos
      have hM₀log := le_mul_of_one_le_right (Real.log_nonneg hM₀) hY
      dsimp only [U₀]
      linarith only [hlog, hYlog, hM₀log]
    have hbound := norm_logDeriv_le_of_moving_disk_bounds (fun w _ ↦ hH.analyticAt w)
      hc hMpos hbox hloss hN hz hδ (fun ρ _ hρ ↦ hsep ρ hρ)
    obtain ⟨hLz, hLbound⟩ := logDeriv_le_of_gaussian_clearing
      (by simpa [sub_eq_add_neg] using hdiff) (by simpa [sub_eq_add_neg] using hclear)
      hHz (hzT ▸ (hT n).2)
    have hYsq : Y ≤ Y^2 := by simpa only [pow_two] using le_mul_of_one_le_right hYpos.le hY
    have hYsq₁ : 1 ≤ Y^2 := hY.trans hYsq
    have hmY : 1 + ((n + m₀ : ℕ) : ℝ) ≤ Y := by
      dsimp [Y]; rw [hzT]; linarith [hTlo n]
    have hprod : (C₀ * Y) / δ ≤ (C₀ * (16 * (C₀ + 1))) * Y^2 := by
      dsimp only [δ]
      rw [one_div, div_inv_eq_mul]
      calc
        _ ≤ C₀ * Y * (16 * (C₀ + 1) * Y) := by gcongr
        _ = _ := by ring
    have hlin : 8 * (U₀ * Y + C₀ * Y * Real.log 5 + 1) ≤
        8 * (U₀ + C₀ * Real.log 5 + 1) * Y^2 := by
      have h₁ := mul_le_mul_of_nonneg_left hYsq hU₀
      have h₂ := mul_le_mul_of_nonneg_left hYsq hC₀.le
      have h₃ := mul_le_mul_of_nonneg_right h₂ hlog5
      linarith only [h₁, h₃, hYsq₁]
    refine ⟨hLz, ?_⟩
    have hfinal : ‖logDeriv L z‖ ≤ D * Y^2 := by
      dsimp only [D]
      linarith only [hLbound, hbound, hprod, hlin, hYsq₁]
    simpa [Y, hzT] using hfinal
  intro n σ hσlo hσhi
  have hTpos : 0 < T n := (Nat.cast_nonneg n).trans_lt (hT n).1
  constructor
  · exact hedge n ((σ : ℂ) + (T n : ℂ) * I) (by simpa using hσlo) (by simpa using hσhi)
      (by simp [abs_of_pos hTpos])
  · exact hedge n ((σ : ℂ) + ((-T n : ℝ) : ℂ) * I) (by simpa using hσlo) (by simpa using hσhi)
      (by simp [abs_of_pos hTpos])

end Masullo
