module

public import Theorems.CompletedHeckeEulerProductGammaLowerBound
public import Theorems.IdeleClassGaussianHorizontalUnitary

/-! # Horizontal separation for the Gaussian Hecke continuation

Discharge the center-bound interface for the actual completed Euler product.
The full-order count and the good heights use one and the same continued
Gaussian numerator. This supplies a contour prerequisite, not a functional
equation, a contour identity, or a zero-location theorem.
-/

open Complex IsDedekindDomain Metric NumberField

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

/-- For a unitary Hecke character the pole-cleared Gaussian continuation
has a linear count on closed disks and a common separated height for both
horizontal edges. The Euler identity is for the very same continuation. -/
public theorem exists_completedHeckeEulerProduct_gaussianContinuation_horizontal
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
      (∀ a b : ℝ, ∃ M : ℝ, 0 ≤ M ∧ ∀ s : ℂ, a ≤ s.re → s.re ≤ b →
        ‖H s‖ ≤ M * (1 + |s.im|)^2) ∧
      (∃ A : ℝ, 0 < A ∧ ∀ t : ℝ, Real.exp (-A * (1 + |t|)) ≤ ‖H (2 + (t : ℂ) * I)‖) ∧
      ∃ C₀ : ℝ, 0 < C₀ ∧
        (∀ t : ℝ, let c : ℂ := 2 + (t : ℂ) * I
          H c ≠ 0 ∧ ((∑ᶠ ρ, MeromorphicOn.divisor H (closedBall c 5) ρ : ℤ) : ℝ) ≤ C₀ * (1 + |t|)) ∧
        ∀ n : ℕ, 1 ≤ n → ∃ T : ℝ, (n : ℝ) < T ∧ T < (n : ℝ) + 1 ∧
          ∀ z : ℂ, -1 ≤ z.re → z.re ≤ 2 → |z.im| = T →
            z ∈ closedBall (2 + (z.im : ℂ) * I) 3 ∧
              ∀ ρ : ℂ, H ρ = 0 → 1 / (16 * (C₀ + 1) * (1 + (n : ℝ))) ≤ ‖z - ρ‖ :=
  exists_completedHeckeEulerProduct_gaussianContinuation_horizontal_of_local χ hχ v r hr
    (exists_localHeckeGammaFactor_rightLine_lower_bound χ hχ)

end Masullo
