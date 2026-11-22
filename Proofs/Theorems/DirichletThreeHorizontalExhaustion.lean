module

public import Lemmas.DirichletThreeBareHeights
public import Props.DirichletThreeCompletedEdges

/-!
# Horizontal exhaustion for the quadratic character of conductor three

The completion is Mathlib's, without a conductor power. This theorem does not
identify an idelic completion or exhaust the residues in the strip.
-/

open Complex Filter Set
open scoped ContDiff Topology

namespace Masullo

local notation "completed₃" => DirichletCharacter.completedLFunction padicRamifiedThreeCharacter

/-- One sequence of heights works at both signs for the entire closed strip
and for the horizontal integrals of every smooth compact log profile. -/
public theorem padicRamifiedThree_completed_horizontal :
    ∃ (T : ℕ → ℝ) (C : ℝ) (m : ℕ), 0 < C ∧
      (∀ n : ℕ, T n ∈ Ioo ((n : ℝ) + 1) ((n : ℝ) + 2)) ∧
      (∀ n, ∀ σ ∈ Icc (-1 / 2 : ℝ) (3 / 2), ∀ t : ℝ, |t| = T n →
        let s := (σ : ℂ) + (t : ℂ) * I
        completed₃ s ≠ 0 ∧ ‖logDeriv completed₃ s‖ ≤ C * (1 + T n) ^ m) ∧
      (∀ (g : ℝ → ℂ), ContDiff ℝ ∞ g → HasCompactSupport g →
        (Tendsto (fun n ↦ ∫ σ in (-1 / 2 : ℝ)..(3 / 2),
          let s := (σ : ℂ) + (T n : ℂ) * I
          compactLogMellin g s * logDeriv completed₃ s) atTop (𝓝 0)) ∧
        (Tendsto (fun n ↦ ∫ σ in (-1 / 2 : ℝ)..(3 / 2),
          let s := (σ : ℂ) - (T n : ℂ) * I
          compactLogMellin g s * logDeriv completed₃ s) atTop (𝓝 0))) :=
  padicRamifiedThree_completed_horizontal_of_bare padicRamifiedThree_bare_good_heights

end Masullo
