module

public import Props.CompactLogMellin
public import Props.RectangleResidue
public import Mathlib.Analysis.Calculus.LogDeriv
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Lemmas.TestedRectangleEdges
import Mathlib.Tactic.Linarith

/-!
# Exhaustion of the tested rectangle boundary

In (B.3.2.4)–(5), p. 606, Masullo suppresses the horizontal edges and
passes to absolutely convergent vertical integrals. For the fixed
outer lines in (B.4.2.2), p. 614, use the actual-height bounds of
`completedHecke_one_rectangle_at_good_heights` and uniform compact-log
Mellin decay instead of a slow-growth hypothesis phrased in the sequence
index. Keep the orientation of Fig. 3, p. 605, and both vertical
Jacobians. This is the boundary limit, not exhaustion of the divisor.
Source reading provisional (pinned Markdown and numbered PDF layout).
-/

open Complex Filter MeasureTheory Set
open scoped ContDiff Topology

namespace Masullo

/-- The two upward vertical integrands are absolutely integrable, and the
counterclockwise boundary tends to their difference with the `ds = i dt`
factors. The edge hypotheses refer to one function `L` and one sequence of
heights, independent of the test. -/
public theorem tendsto_rectangleIntegral_compactLogMellin_logDeriv {L : ℂ → ℂ}
    (hdiff : ∀ s, s ≠ 0 → s ≠ 1 → DifferentiableAt ℂ L s)
    {C D : ℝ} (hV : ∀ z : ℂ, z.re = -1 ∨ z.re = 2 →
      L z ≠ 0 ∧ ‖logDeriv L z‖ ≤ C * (1 + |z.im|))
    {T : ℕ → ℝ} (hT₀ : ∀ n, 0 ≤ T n) (hT : Tendsto T atTop atTop)
    (hH : ∀ n z, -1 ≤ z.re → z.re ≤ 2 → |z.im| = T n →
      ‖logDeriv L z‖ ≤ D * (1 + |z.im|) ^ 2)
    {g : ℝ → ℂ} (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g) :
    let F := fun s ↦ compactLogMellin g s * logDeriv L s
    let V := fun (σ t : ℝ) ↦ F ((σ : ℂ) + (t : ℂ) * I)
    Integrable (V 2) ∧ Integrable (V (-1)) ∧
      Tendsto (fun n ↦ rectangleIntegral (-1) 2 (-T n) (T n) F) atTop
        (𝓝 (I * (∫ t, V 2 t) - I * (∫ t, V (-1) t))) := by
  let Φ := compactLogMellin g
  obtain ⟨B, hB, hdecay⟩ := compactLogMellin_vertical_decay hg hc 2 3
  have htest (σ : ℝ) (hσ : σ ∈ Icc (-1 : ℝ) 2) (t : ℝ) :=
    hdecay σ t (abs_le.mpr ⟨by linarith [hσ.1], hσ.2⟩)
  have hΦ : Continuous Φ := continuous_iff_continuousAt.mpr fun s ↦
    (analyticAt_compactLogMellin hg.continuous hc s).continuousAt
  -- (B.3.2.5): The cubic test bound times linear growth has an
  -- integrable inverse-square envelope on each full vertical line.
  have hv (σ : ℝ) (hσ : σ = -1 ∨ σ = 2) :=
    integrable_tested_logDeriv_vertical hΦ hdiff hB.le hσ (hdecay σ · (by
      rcases hσ with h | h <;> rw [h] <;> norm_num)) (fun t ↦ by
      simpa using hV ((σ : ℂ) + (t : ℂ) * I) (by simpa using hσ))
  have hr := hv 2 (.inr rfl)
  have hl := hv (-1) (.inl rfl)
  refine ⟨hr, hl, ?_⟩
  -- Lemma B.3.1.2 is needed in (B.3.2.4): Actual heights tend to infinity,
  -- and inverse-cubic test decay beats the quadratic bound on both edges.
  have hlarge : Tendsto (fun n ↦ |T n|) atTop atTop :=
    tendsto_atTop_mono (fun n ↦ le_abs_self _) hT
  have hhorizontal {w : ℕ → ℝ} (hw : ∀ n, |w n| = |T n|) :=
    tendsto_tested_logDeriv_horizontal (L := L) hB.le
      (show Tendsto (fun n ↦ |w n|) atTop atTop by simpa only [hw] using hlarge) htest
      (fun n σ hσ ↦ by
        have hpos : |w n| = T n := (hw n).trans (abs_of_nonneg (hT₀ n))
        simpa using hH n ((σ : ℂ) + (w n : ℂ) * I) (by simpa using hσ.1)
          (by simpa using hσ.2) (by simpa using hpos))
  have hbot := hhorizontal (w := fun n ↦ -T n) (fun n ↦ abs_neg _)
  have htop := hhorizontal (w := T) (fun _ ↦ rfl)
  have hneg := tendsto_neg_atTop_atBot.comp hT
  simpa [rectangleIntegral, Φ] using
    (((hbot.sub htop).add ((intervalIntegral_tendsto_integral hr hneg hT).const_mul I)).sub
        ((intervalIntegral_tendsto_integral hl hneg hT).const_mul I))

end Masullo
