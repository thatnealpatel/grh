module

public import Theorems.IdeleClassGaussianContinuation
public import Mathlib.Analysis.Calculus.LogDeriv
public import Mathlib.Analysis.Meromorphic.Divisor
import Theorems.CompletedHeckeEulerProductRightLine
import Lemmas.AnalyticGoodHeightDisk
import Lemmas.OneParameterCharacter
import Mathlib.Analysis.Complex.JensenFormula

/-! # Moving-disk estimates for the completed trivial Hecke product

Section B.4.2.1, p. 614, invokes Lang for slow growth of the completed
logarithmic derivative in (B.4.2.1), as needed for (B.4.2.2). We use the
entire pole-cleared numerator for a replacement input to the horizontal
estimate in Definition B.3.1.1, p. 604, used by Lemma B.3.1.2, pp. 604–605.
These local bounds are not a near-pole growth condition for the completed
logarithmic derivative and do not give separated heights or a contour limit.

The repaired fixed-Gaussian continuation provides the entire numerator and
its quadratic strip bound. The section phase in (3.2.2.4)–(5), p. 125, in the
coordinates of (3.1.1.1), p. 119, is constant for the trivial character.
The checked Euler-domain lower bound controls the logarithmic cost at the
center; Jensen then counts the full analytic orders on the closed disk.
Source reading: Provisional, from pinned Markdown and numbered PDF layout.
-/

open Complex IsDedekindDomain MeasureTheory MeromorphicOn Metric NumberField

namespace Masullo

variable {K : Type*} [Field K] [NumberField K]

local notation "χ₀" => (1 : HeckeCharacter (𝓞 K) K)
local notation "W" => (NumberField.Units.dirichletUnitTheorem.w₀ : InfinitePlace K)
local notation "τ" => ideleClassLogSplit (ideleClassLogSection W) (ideleClassLogNorm_section W)

private theorem quadratic_sphere_bound {H : ℂ → ℂ} {B : ℝ} (hB : 0 ≤ B)
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

/-- The continued completed trivial Hecke product has an entire pole-cleared
numerator whose full closed-disk divisor has mass `O(1 + |t|)` about `2 + it`.
The sphere envelope and its center cost also hold for this same numerator. -/
public theorem exists_completedHeckeEulerProduct_one_gaussianContinuation_zeroCount
    (v : InfinitePlace K) (r : ClassGroup (𝓞 K) → ideleNormOne (K := K))
    (hr : ∀ p, ideleIdealClassNormOne (r p) = p) :
    ∃ L H : ℂ → ℂ, Meromorphic L ∧
      (∀ s, s ≠ 0 → s ≠ 1 → DifferentiableAt ℂ L s) ∧
      (∀ s, 1 < s.re → L s = completedHeckeEulerProduct χ₀ (fun _ ↦ norm_one) s) ∧
      Differentiable ℂ H ∧ (∀ s, s ≠ 0 → s ≠ 1 → H s = (s - 1) * s * L s) ∧
      (∀ a b : ℝ, ∃ M : ℝ, 0 ≤ M ∧ ∀ s : ℂ, a ≤ s.re → s.re ≤ b →
        ‖H s‖ ≤ M * (1 + |s.im|)^2) ∧
      ∃ C₀ C : ℝ, 1 ≤ C₀ ∧ 0 < C ∧ ∀ t : ℝ,
        let c : ℂ := 2 + (t : ℂ) * I
        let M := C₀ * (1 + |t|)^2
        H c ≠ 0 ∧ (∀ z ∈ sphere c 6, ‖H z‖ ≤ M) ∧
          Real.log (M / ‖H c‖) ≤ C * (1 + |t|) ∧
          ((∑ᶠ z, divisor H (closedBall c 5) z : ℤ) : ℝ) ≤ C * (1 + |t|) := by
  obtain ⟨T, ν, F, E, μ, lam, h⟩ :=
    exists_completedHeckeEulerProduct_gaussianContinuation χ₀ (fun _ ↦ norm_one) v r hr
  dsimp only at h
  obtain ⟨_, _, _, _, _, _, _, hphase, hmero, hdiffL, _, hEuler, H, hdiffH, _, _, hclear,
    hgrowth⟩ := h
  -- The trivial character has the zero frequency on the very same section.
  obtain ⟨u, _, hu⟩ := existsUnique_unitary_oneParameterCharacter (fun x : ℝ ↦ χ₀
    (τ (Multiplicative.ofAdd x, 1))) (by simpa using
      (continuous_const : Continuous (fun _ : ℝ ↦ (1 : ℂ)))) (by simp) (by simp) (by simp)
  have hlam : lam = 0 := (hu lam hphase).trans (hu 0 (by simp)).symm
  subst lam
  simp only [ofReal_zero, zero_mul, neg_zero, add_zero, sub_zero] at hmero hdiffL hEuler hclear
  refine ⟨_, H, hmero, fun s h₀ h₁ ↦ hdiffL s h₁ h₀, hEuler, hdiffH,
    fun s h₀ h₁ ↦ hclear s h₁ h₀, hgrowth, ?_⟩
  obtain ⟨B, hB, hstrip⟩ := hgrowth (-4) 8
  let C₀ := 49 * B + 1
  have hC₀ : 1 ≤ C₀ := by dsimp [C₀]; linarith
  have hC₀pos : 0 < C₀ := zero_lt_one.trans_le hC₀
  let d := Real.log (6 / 5 : ℝ)
  have hd : 0 < d := Real.log_pos (by norm_num)
  have hd₁ : d ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 6 / 5)
    dsimp [d]; linarith
  let A := Real.log C₀ + trivialHeckeRightLineLoss K
  let b := (Module.finrank ℚ K : ℝ) * Real.pi / 4
  let B₀ := |A| + |2 + b| + 1
  have hB₀ : 0 < B₀ := by dsimp [B₀]; positivity
  refine ⟨C₀, B₀ / d, hC₀, div_pos hB₀ hd, ?_⟩
  intro t c M
  have hcre : c.re = 2 := by simp [c]
  have hc₀ : c ≠ 0 := by intro hc; rw [hc, zero_re] at hcre; norm_num at hcre
  have hc₁ : c ≠ 1 := by intro hc; rw [hc, one_re] at hcre; norm_num at hcre
  have hce : H c = c * (c - 1) * completedHeckeEulerProduct χ₀ (fun _ ↦ norm_one) c := by
    rw [hclear c hc₁ hc₀, hEuler c (by rw [hcre]; norm_num), mul_comm (c - 1) c]
  have hp : completedHeckeEulerProduct χ₀ (fun _ ↦ norm_one) c ≠ 0 :=
    norm_pos_iff.mp ((Real.exp_pos _).trans_le (completedHeckeEulerProduct_one_rightLine_lower_bound K t))
  have hc : H c ≠ 0 := by rw [hce]; exact mul_ne_zero (mul_ne_zero hc₀ (sub_ne_zero.mpr hc₁)) hp
  have hbd : ∀ z ∈ sphere c 6, ‖H z‖ ≤ M := fun z hz ↦ quadratic_sphere_bound hB hstrip t hz
  have hY : 1 ≤ 1 + |t| := by linarith [abs_nonneg t]
  have hYpos := zero_lt_one.trans_le hY
  have hM : 1 ≤ M := one_le_mul_of_one_le_of_one_le hC₀ (one_le_pow₀ hY)
  have hcost := log_div_norm_poleCleared_completedHeckeEulerProduct_one_rightLine K t
    (zero_lt_one.trans_le hM)
  change Real.log (M / ‖c * (c - 1) * completedHeckeEulerProduct χ₀ (fun _ ↦ norm_one) c‖) ≤ _ at hcost
  rw [← hce] at hcost
  have hlog : Real.log M = Real.log C₀ + 2 * Real.log (1 + |t|) := by
    dsimp [M]
    rw [Real.log_mul hC₀pos.ne' (pow_ne_zero _ hYpos.ne'), Real.log_pow]
    norm_num
  have hcost' : Real.log (M / ‖H c‖) ≤ B₀ * (1 + |t|) := by
    rw [hlog] at hcost
    have hlin := Real.log_le_sub_one_of_pos hYpos
    calc
      _ ≤ A + (2 + b) * |t| := by dsimp [A, b]; linarith
      _ ≤ B₀ * (1 + |t|) := by
        dsimp [B₀]
        nlinarith [le_abs_self A, mul_le_mul_of_nonneg_right (le_abs_self (2 + b)) (abs_nonneg t),
          mul_nonneg (abs_nonneg A) (abs_nonneg t), abs_nonneg (2 + b), abs_nonneg t]
  refine ⟨hc, hbd, ?_, ?_⟩
  · apply hcost'.trans
    gcongr
    exact (le_div_iff₀ hd).mpr (by nlinarith)
  · -- Jensen counts the compactly supported analytic divisor, including the boundary.
    have hj := AnalyticOnNhd.sum_divisor_le (f := H) (c := c) (r := 5) (R := 6)
      (by norm_num) (by norm_num) hM (fun z _ ↦ hdiffH.analyticAt z) hc (by simpa using hbd)
    rw [abs_of_pos (by norm_num : (0 : ℝ) < 5)] at hj
    calc
      _ ≤ Real.log (M / ‖H c‖) / d := hj
      _ ≤ B₀ * (1 + |t|) / d := div_le_div_of_nonneg_right hcost' hd.le
      _ = (B₀ / d) * (1 + |t|) := by ring

/-- Keep the same continued product and numerator as in the moving-disk
Jensen bound. Off the zeros by `δ > 0`, the logarithmic derivative of the
numerator is bounded by an affine height budget times `1 + 1 / δ`. -/
public theorem exists_completedHeckeEulerProduct_one_gaussianContinuation_logDeriv
    (v : InfinitePlace K) (r : ClassGroup (𝓞 K) → ideleNormOne (K := K))
    (hr : ∀ p, ideleIdealClassNormOne (r p) = p) :
    ∃ L H : ℂ → ℂ, Meromorphic L ∧
      (∀ s, s ≠ 0 → s ≠ 1 → DifferentiableAt ℂ L s) ∧
      (∀ s, 1 < s.re → L s = completedHeckeEulerProduct χ₀ (fun _ ↦ norm_one) s) ∧
      Differentiable ℂ H ∧ (∀ s, s ≠ 0 → s ≠ 1 → H s = (s - 1) * s * L s) ∧
      (∀ a b : ℝ, ∃ M : ℝ, 0 ≤ M ∧ ∀ s : ℂ, a ≤ s.re → s.re ≤ b →
        ‖H s‖ ≤ M * (1 + |s.im|)^2) ∧
      (∃ C₀ C : ℝ, 1 ≤ C₀ ∧ 0 < C ∧ ∀ t : ℝ,
        let c : ℂ := 2 + (t : ℂ) * I
        let M := C₀ * (1 + |t|)^2
        H c ≠ 0 ∧ (∀ z ∈ sphere c 6, ‖H z‖ ≤ M) ∧
          Real.log (M / ‖H c‖) ≤ C * (1 + |t|) ∧
          ((∑ᶠ z, divisor H (closedBall c 5) z : ℤ) : ℝ) ≤ C * (1 + |t|)) ∧
      ∃ D K₀ : ℝ, 0 < D ∧ 0 < K₀ ∧ ∀ t : ℝ,
        ∀ z ∈ closedBall (2 + (t : ℂ) * I) 3, ∀ δ : ℝ, 0 < δ →
          (∀ ρ ∈ closedBall (2 + (t : ℂ) * I) 5, H ρ = 0 → δ ≤ ‖z - ρ‖) →
          ‖logDeriv H z‖ ≤ D * (1 + |t|) + K₀ * (1 + |t|) / δ := by
  obtain ⟨L, H, hmero, hdiffL, hEuler, hdiffH, hclear, hstrip, hJ⟩ :=
    exists_completedHeckeEulerProduct_one_gaussianContinuation_zeroCount v r hr
  refine ⟨L, H, hmero, hdiffL, hEuler, hdiffH, hclear, hstrip, hJ, ?_⟩
  obtain ⟨C₀, C, hC₀, hC, hJ⟩ := hJ
  let D := 8 * (C + C * Real.log 5 + 1)
  have hlog5 : 0 ≤ Real.log 5 := Real.log_nonneg (by norm_num)
  have hD : 0 < D := by dsimp [D]; positivity
  refine ⟨D, C, hD, hC, fun t z hz δ hδ hsep ↦ ?_⟩
  obtain ⟨hc, hbd, hloss, hcount⟩ := hJ t
  have hY : 1 ≤ 1 + |t| := le_add_of_nonneg_right (abs_nonneg t)
  have hM : 0 < C₀ * (1 + |t|)^2 :=
    mul_pos (zero_lt_one.trans_le hC₀) (pow_pos (zero_lt_one.trans_le hY) _)
  -- The finite divisor costs its mass divided by δ; the remaining part
  -- costs only the Jensen center loss and the same mass times log 5.
  calc
    _ ≤ 8 * (C * (1 + |t|) + (C * (1 + |t|)) * Real.log 5 + 1) + C * (1 + |t|) / δ :=
      norm_logDeriv_le_of_moving_disk_bounds (fun w _ ↦ hdiffH.analyticAt w) hc hM
        hbd hloss hcount hz hδ hsep
    _ ≤ D * (1 + |t|) + C * (1 + |t|) / δ := by
      dsimp [D]
      linarith only [hY]

end Masullo
