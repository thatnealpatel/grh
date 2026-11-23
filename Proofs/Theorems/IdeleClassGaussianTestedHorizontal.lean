module

public import Theorems.IdeleClassGaussianHorizontalLogDeriv
public import Props.CompactLogMellin
import Lemmas.TestedRectangleEdges
import Mathlib.Tactic.Linarith

/-! # Tested horizontal limits for the Gaussian Hecke continuation

Quadratic logarithmic-derivative growth along the common good heights
suffices for vanishing of the two tested horizontal contour integrals.
This is the horizontal input only, not a residue or zero-location theorem.
-/

open Complex Filter IsDedekindDomain NumberField Set
open scoped ContDiff Topology

namespace Masullo

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

/-- The Gaussian continuation of the actual completed Hecke Euler product
has both closed edges nonvanishing at common good heights, with a quadratic
logarithmic-derivative bound uniform in the test. The same bound forces the
horizontal integrals against each compact smooth log test to tend to zero.
Reversing the orientation of either integral just negates it. -/
public theorem exists_completedHeckeEulerProduct_gaussianContinuation_tested_horizontal
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
        (∀ n (σ : ℝ), -1 ≤ σ → σ ≤ 2 →
          (L ((σ : ℂ) + (T n : ℂ) * I) ≠ 0 ∧
            ‖logDeriv L ((σ : ℂ) + (T n : ℂ) * I)‖ ≤ D * (1 + T n)^2) ∧
          (L ((σ : ℂ) + ((-T n : ℝ) : ℂ) * I) ≠ 0 ∧
            ‖logDeriv L ((σ : ℂ) + ((-T n : ℝ) : ℂ) * I)‖ ≤ D * (1 + T n)^2)) ∧
        ∀ (g : ℝ → ℂ), ContDiff ℝ ∞ g → HasCompactSupport g →
          let F := fun (σ t : ℝ) ↦ compactLogMellin g ((σ : ℂ) + (t : ℂ) * I) *
            logDeriv L ((σ : ℂ) + (t : ℂ) * I)
          Tendsto (fun n ↦ ∫ σ : ℝ in (-1)..2, F σ (T n)) atTop (𝓝 0) ∧
            Tendsto (fun n ↦ ∫ σ : ℝ in (-1)..2, F σ (-T n)) atTop (𝓝 0) := by
  obtain ⟨lam, L, H, hphase, hmer, hdiff, hdiffAll, hEuler, hHdiff, hclear,
    D, hD, T, hT, hH⟩ :=
    exists_completedHeckeEulerProduct_gaussianContinuation_horizontal_logDeriv χ hχ v r hr
  refine ⟨lam, L, H, hphase, hmer, hdiff, hdiffAll, hEuler, hHdiff, hclear,
    D, hD, T, hT, hH, ?_⟩
  intro g hg hc
  obtain ⟨B, hB, hdecay⟩ := compactLogMellin_vertical_decay hg hc 2 3
  have htest (σ : ℝ) (hσ : σ ∈ Icc (-1 : ℝ) 2) (t : ℝ) :=
    hdecay σ t (abs_le.mpr ⟨by linarith [hσ.1], hσ.2⟩)
  have hlarge : Tendsto T atTop atTop :=
    tendsto_atTop_mono (fun n ↦ (hT n).1.le) tendsto_natCast_atTop_atTop
  have hpos (n : ℕ) : |T n| = T n :=
    abs_of_nonneg ((Nat.cast_nonneg n).trans (hT n).1.le)
  have hhorizontal {w : ℕ → ℝ} (hw : ∀ n, |w n| = T n) (hL : ∀ n σ,
      σ ∈ Icc (-1 : ℝ) 2 →
      ‖logDeriv L ((σ : ℂ) + (w n : ℂ) * I)‖ ≤ D * (1 + T n)^2) :=
    tendsto_tested_logDeriv_horizontal (L := L) hB.le
      (show Tendsto (fun n ↦ |w n|) atTop atTop by simpa only [hw] using hlarge)
      htest (fun n σ hσ ↦ by simpa only [hw] using hL n σ hσ)
  exact ⟨hhorizontal (w := T) hpos (fun n σ hσ ↦ (hH n σ hσ.1 hσ.2).1.2),
    hhorizontal (w := fun n ↦ -T n) (fun n ↦ (abs_neg _).trans (hpos n))
      (fun n σ hσ ↦ (hH n σ hσ.1 hσ.2).2.2)⟩

end Masullo
