module

public import Theorems.IdeleClassGaussianZeroCount
import Lemmas.AnalyticHorizontalHeights

/-! # Horizontal edges for the completed trivial Hecke product

In §B.4.2.1, p. 614, Masullo invokes slow growth of (B.4.2.1) to apply the
asymptotic residue theorem. This repairs the horizontal input in Definition
B.3.1.1 (1)–(2), p. 604, used in Lemma B.3.1.2, pp. 604–605: Count the
zeros in two fixed disks, select a common pair of separated ordinates, and
transfer the moving-disk estimate to the completed logarithmic derivative.
The estimate is in the actual height, not just the index of a sequence.
The counted version also keeps the Jensen bound for the **same** numerator;
this is the input for absolute zero summability in (B.4.2.2). This module
does not supply the vertical input or prove the contour identity.
Source reading: Provisional, from pinned Markdown and numbered PDF layout.
-/

open Complex IsDedekindDomain MeasureTheory NumberField

namespace Masullo

variable {K : Type*} [Field K] [NumberField K]

local notation "χ₀" => (1 : HeckeCharacter (𝓞 K) K)

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

/-- The same pole-cleared numerator used to find good horizontal heights
retains its linear Jensen bound on the full-order disk count. -/
public theorem exists_completedHeckeEulerProduct_one_gaussianContinuation_horizontal_count
    (v : InfinitePlace K) (r : ClassGroup (𝓞 K) → ideleNormOne (K := K))
    (hr : ∀ p, ideleIdealClassNormOne (r p) = p) :
    ∃ L H : ℂ → ℂ, Meromorphic L ∧
      (∀ s, s ≠ 0 → s ≠ 1 → DifferentiableAt ℂ L s) ∧
      (∀ s, 1 < s.re → L s = completedHeckeEulerProduct χ₀ (fun _ ↦ norm_one) s) ∧
      Differentiable ℂ H ∧ (∀ s, s ≠ 0 → s ≠ 1 → H s = (s - 1) * s * L s) ∧
      (∃ C > (0 : ℝ), ∀ t : ℝ,
        ((∑ᶠ z, MeromorphicOn.divisor H (Metric.closedBall (2 + (t : ℂ) * I) 5) z : ℤ) : ℝ) ≤
          C * (1 + |t|)) ∧
      ∃ B : ℝ, 0 < B ∧ ∀ n : ℕ, 1 ≤ n → ∃ T : ℝ, (n : ℝ) < T ∧ T < (n : ℝ) + 1 ∧
        ∀ z : ℂ, -1 ≤ z.re → z.re ≤ 2 → |z.im| = T →
          L z ≠ 0 ∧ ‖logDeriv L z‖ ≤ B * (1 + |z.im|)^2 := by
  obtain ⟨L, H, hmero, hdiffL, hEuler, hdiffH, hclear, _, hJ, D, K₀, hD, hK₀, hlocal⟩ :=
    exists_completedHeckeEulerProduct_one_gaussianContinuation_logDeriv v r hr
  obtain ⟨_, C, _, hC, hcount⟩ := hJ
  refine ⟨L, H, hmero, hdiffL, hEuler, hdiffH, hclear, ⟨C, hC, fun t ↦ (hcount t).2.2.2⟩,
    D + K₀ * (16 * (C + 1)) + 2, by positivity, fun n hn ↦ ?_⟩
  -- Exclude the ordinates of zeros in both fixed disks, reflecting the lower ones.
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  obtain ⟨T, hT, hsep⟩ := exists_symmetric_horizontal_separation
    (fun z _ ↦ hdiffH.analyticAt z) hC (fun t ↦ ⟨(hcount t).1, (hcount t).2.2.2⟩) hn'
  refine ⟨T, hT.1, hT.2, fun z hzl hzu hz ↦ ?_⟩
  obtain ⟨hdisk, hsepz⟩ := hsep z hzl hzu hz
  let δ : ℝ := 1 / (16 * (C + 1) * (1 + (n : ℝ)))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hHz : H z ≠ 0 := by
    intro h
    have hdist := hsepz z h
    rw [sub_self, norm_zero] at hdist
    exact hδ.not_ge hdist
  -- Transfer the estimate on the entire numerator by subtracting the two pole terms.
  have ht : 1 ≤ |z.im| := by rw [hz]; exact hn'.trans hT.1.le
  have hbd := hlocal z.im z hdisk δ hδ (fun ρ _ hρ ↦ hsepz ρ hρ)
  obtain ⟨hL, htransfer⟩ := nonzero_and_norm_logDeriv_le_of_poleCleared hdiffH hclear hHz ht
  refine ⟨hL, htransfer.trans ((add_le_add_left hbd 2).trans ?_)⟩
  have hnT : (n : ℝ) ≤ |z.im| := hz ▸ hT.1.le
  have hA : 0 ≤ 16 * (C + 1) := by positivity
  have hY : 1 ≤ 1 + |z.im| := le_add_of_nonneg_right (abs_nonneg _)
  have hY' : 1 + |z.im| ≤ (1 + |z.im|)^2 := by nlinarith
  calc
    _ = D * (1 + |z.im|) + K₀ * (16 * (C + 1)) * (1 + |z.im|) * (1 + (n : ℝ)) + 2 := by
      dsimp [δ]; rw [one_div, div_inv_eq_mul]; ring
    _ ≤ D * (1 + |z.im|)^2 + K₀ * (16 * (C + 1)) * (1 + |z.im|) * (1 + |z.im|) +
        2 * (1 + |z.im|)^2 := by
      gcongr
      linarith
    _ = _ := by ring

/-- The continued completed trivial Hecke product is nonzero on both
closed horizontal edges at common heights in each unit interval above one.
Its logarithmic derivative has a uniform quadratic bound on those edges. -/
public theorem exists_completedHeckeEulerProduct_one_gaussianContinuation_horizontal
    (v : InfinitePlace K) (r : ClassGroup (𝓞 K) → ideleNormOne (K := K))
    (hr : ∀ p, ideleIdealClassNormOne (r p) = p) :
    ∃ L H : ℂ → ℂ, Meromorphic L ∧
      (∀ s, s ≠ 0 → s ≠ 1 → DifferentiableAt ℂ L s) ∧
      (∀ s, 1 < s.re → L s = completedHeckeEulerProduct χ₀ (fun _ ↦ norm_one) s) ∧
      Differentiable ℂ H ∧ (∀ s, s ≠ 0 → s ≠ 1 → H s = (s - 1) * s * L s) ∧
      ∃ B : ℝ, 0 < B ∧ ∀ n : ℕ, 1 ≤ n → ∃ T : ℝ, (n : ℝ) < T ∧ T < (n : ℝ) + 1 ∧
        ∀ z : ℂ, -1 ≤ z.re → z.re ≤ 2 → |z.im| = T →
          L z ≠ 0 ∧ ‖logDeriv L z‖ ≤ B * (1 + |z.im|)^2 := by
  obtain ⟨L, H, hmero, hdiffL, hEuler, hdiffH, hclear, _, hgood⟩ :=
    exists_completedHeckeEulerProduct_one_gaussianContinuation_horizontal_count v r hr
  exact ⟨L, H, hmero, hdiffL, hEuler, hdiffH, hclear, hgood⟩

end Masullo
