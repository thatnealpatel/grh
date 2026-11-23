module

public import Theorems.IdeleClassGaussianHorizontal
public import Theorems.CompletedHeckeOneReflection
public import Props.PoleClearedRectangleResidues
public import Props.CompactLogMellin

/-! # Finite residue rectangles for the completed trivial Hecke product

In (B.4.2.2), p. 614, Masullo uses the asymptotic residue theorem
(B.3.2.1), pp. 605–606, for the completed logarithmic derivative.
This is its finite-rectangle ingredient (B.3.2.3), with the orientation
from Figure 3. The Gaussian continuation, positive pole-cleared values,
and the checked edge estimates justify the contour for this very same
`L` and `H`. The compact log profiles give an entire test as in the
coordinates of (B.2.1.29), pp. 598–599. No contour limit is taken here.
Source reading provisional (pinned Markdown and numbered PDF layout).
-/

open Complex IsDedekindDomain MeasureTheory NumberField Set
open scoped ContDiff

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

/-- At each good height for the given continuation, a single finite set of
all ordinary interior zeros works for every smooth compact-log test.
The two vertical and both horizontal bounds are retained on the same `L`
for the subsequent contour exhaustion. -/
public theorem completedHecke_one_rectangle_at_good_heights
    (v : InfinitePlace K) (r : ClassGroup (𝓞 K) → ideleNormOne (K := K))
    (hr : ∀ p, ideleIdealClassNormOne (r p) = p) {L H : ℂ → ℂ}
    (hL : Meromorphic L) (hdiffL : ∀ s, s ≠ 0 → s ≠ 1 → DifferentiableAt ℂ L s)
    (hEuler : ∀ s, 1 < s.re → L s = completedHeckeEulerProduct χ₀ (fun _ ↦ norm_one) s)
    (hH : Differentiable ℂ H) (hclear : ∀ s, s ≠ 0 → s ≠ 1 → H s = (s - 1) * s * L s)
    {B : ℝ} (hgood : ∀ n : ℕ, 1 ≤ n → ∃ T : ℝ, (n : ℝ) < T ∧ T < (n : ℝ) + 1 ∧
      ∀ z : ℂ, -1 ≤ z.re → z.re ≤ 2 → |z.im| = T →
        L z ≠ 0 ∧ ‖logDeriv L z‖ ≤ B * (1 + |z.im|)^2) :
    ∃ C > (0 : ℝ), (∀ z : ℂ, z.re = -1 ∨ z.re = 2 →
        L z ≠ 0 ∧ ‖logDeriv L z‖ ≤ C * (1 + |z.im|)) ∧
      ∀ n : ℕ, 1 ≤ n → ∃ T : ℝ, (n : ℝ) < T ∧ T < (n : ℝ) + 1 ∧
        (∀ z : ℂ, -1 ≤ z.re → z.re ≤ 2 → |z.im| = T →
          L z ≠ 0 ∧ ‖logDeriv L z‖ ≤ B * (1 + |z.im|)^2) ∧
        ∃ Z : Finset ℂ, (∀ z, z ∈ Z ↔ z ∈ Ioo (-1 : ℝ) 2 ×ℂ Ioo (-T) T ∧ H z = 0) ∧
          ∀ (g : ℝ → ℂ), ContDiff ℝ ∞ g → HasCompactSupport g →
            rectangleIntegral (-1) 2 (-T) T (fun s ↦ compactLogMellin g s * logDeriv L s) =
              (2 * Real.pi * I) * ((∑ z ∈ Z, (analyticOrderNatAt H z : ℂ) *
                compactLogMellin g z) - compactLogMellin g 0 - compactLogMellin g 1) := by
  obtain ⟨hp, h₀⟩ := completedHecke_one_poleCleared_values v r hr hEuler hH hclear
  have h₁ : H 1 ≠ 0 := fun h ↦ by simp [h] at hp
  have h₀' : H 0 ≠ 0 := by rw [h₀]; exact mul_ne_zero (exp_ne_zero _) h₁
  obtain ⟨Cₗ, hCₗ, hl⟩ := completedHecke_one_leftLine_nonzero_logDeriv_bound
    v r hr hEuler hH hclear hdiffL
  obtain ⟨Cᵣ, hCᵣ, hh⟩ := completedHecke_rightLine_nonzero_logDeriv_bound
    χ₀ (fun _ ↦ norm_one) hEuler (a := 2) (by norm_num)
  have hvert (z : ℂ) (hz : z.re = -1 ∨ z.re = 2) :
      L z ≠ 0 ∧ ‖logDeriv L z‖ ≤ (max Cₗ Cᵣ) * (1 + |z.im|) := by
    rcases hz with h | h
    · obtain ⟨hnz, hb⟩ : L z ≠ 0 ∧ ‖logDeriv L z‖ ≤ Cₗ * (1 + |z.im|) := by
        have hz' : (-1 : ℂ) + (z.im : ℂ) * I = z := by
          simpa only [h, ofReal_neg, ofReal_one] using re_add_im z
        simpa only [hz'] using hl z.im
      exact ⟨hnz, hb.trans (mul_le_mul_of_nonneg_right (le_max_left ..) (by positivity))⟩
    · obtain ⟨hnz, hb⟩ : L z ≠ 0 ∧ ‖logDeriv L z‖ ≤ Cᵣ * (1 + |z.im|) := by
        simpa only [← h, ofReal_ofNat, re_add_im] using hh z.im
      exact ⟨hnz, hb.trans (mul_le_mul_of_nonneg_right (le_max_right ..) (by positivity))⟩
  refine ⟨max Cₗ Cᵣ, hCₗ.trans_le (le_max_left ..), hvert, fun n hn ↦ ?_⟩
  obtain ⟨T, hnT, hTn, hhor⟩ := hgood n hn
  have hT : 0 < T := (Nat.cast_nonneg n).trans_lt hnT
  have hbd (z : ℂ)
      (hz : z ∈ (Icc (-1 : ℝ) 2 ×ℂ Icc (-T) T) \ (Ioo (-1 : ℝ) 2 ×ℂ Ioo (-T) T)) :
      L z ≠ 0 := by
    obtain ⟨hre, him⟩ := mem_reProdIm.mp hz.1
    by_cases hv : z.re = -1 ∨ z.re = 2
    · exact (hvert z hv).1
    have hre' : z.re ∈ Ioo (-1 : ℝ) 2 :=
      ⟨hre.1.lt_of_ne (fun h ↦ hv (.inl h.symm)), hre.2.lt_of_ne (fun h ↦ hv (.inr h))⟩
    have hi : z.im = -T ∨ z.im = T := by
      by_contra! h
      exact hz.2 (mem_reProdIm.mpr ⟨hre', him.1.lt_of_ne (Ne.symm h.1), him.2.lt_of_ne h.2⟩)
    exact (hhor z hre.1 hre.2 (by rcases hi with h | h <;> simp [h, abs_of_pos hT])).1
  obtain ⟨Z, hZ, hR⟩ := rectangleIntegral_logDeriv_of_two_poles hT hL hH hclear h₀' h₁ hbd
  exact ⟨T, hnT, hTn, hhor, Z, hZ, fun g hg hcg ↦
    hR (fun z _ ↦ analyticAt_compactLogMellin hg.continuous hcg z)⟩

end Masullo
