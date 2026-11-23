module

public import Theorems.RationalIdeleRadialExplicitFormula
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Tactic.Linarith

/-!
# Left limits of scalar strip sums

An absolutely summable full-multiplicity family has a scalar width limit from
below. The limit uses the open strip, even if some zeros have radius exactly
that of the limiting strip. This does not address projected operators or a trace
identity.
-/

open Complex Filter MeasureTheory Set
open scoped ContDiff Topology

namespace Masullo

/-- Multiplicity at radius `r` in a strip of half-width `β`, with a prescribed
edge multiplicity when `r = β`. -/
@[expose] public noncomputable def stripWidthMultiplicity (β r : ℝ) (full edge : ℕ) : ℕ :=
  if r < β then full else if β < r then 0 else edge

/-- As `β` tends to `α` from below, the scalar sums tend to the full-order sum
strictly inside `α`. Each index meets an edge only at its own radius, so `edge`
can prescribe any bounded choice there, independently of all other indices.
In particular this applies to every positive `α`. -/
public theorem tendsto_stripWidth_zeroSum {ι : Type*} {radius : ι → ℝ}
    {full edge : ι → ℕ} {f : ι → ℂ} {α : ℝ}
    (hEdge : ∀ i, edge i ≤ full i) (hsum : Summable (fun i ↦ ‖(full i : ℂ) * f i‖)) :
    Tendsto (fun β ↦ ∑' i, (stripWidthMultiplicity β (radius i) (full i) (edge i) : ℂ) * f i)
      (𝓝[Set.Iio α] α) (𝓝 (∑' i : {i | radius i < α}, (full i : ℂ) * f i)) := by
  rw [tsum_subtype {i | radius i < α} (fun i ↦ (full i : ℂ) * f i)]
  refine tendsto_tsum_of_dominated_convergence hsum (fun i ↦ ?_) <|
    Eventually.of_forall fun β i ↦ ?_
  · refine tendsto_const_nhds.congr' ?_
    by_cases hi : radius i < α
    · filter_upwards [nhdsWithin_le_nhds (eventually_gt_nhds hi)] with β hβ
      simp [stripWidthMultiplicity, hβ, Set.indicator, hi]
    · -- An index on or outside the limiting edge is strictly outside every β < α.
      have hleft : ∀ᶠ β in 𝓝[Set.Iio α] α, β < α := eventually_mem_nhdsWithin
      filter_upwards [hleft] with β hβ
      have ho : β < radius i := hβ.trans_le (le_of_not_gt hi)
      simp [stripWidthMultiplicity, ho, ho.not_gt, Set.indicator, hi]
  · rw [norm_mul, norm_mul, Complex.norm_natCast, Complex.norm_natCast]
    refine mul_le_mul_of_nonneg_right (Nat.cast_le.mpr ?_) (norm_nonneg _)
    unfold stripWidthMultiplicity
    split_ifs <;> simp [hEdge i]

set_option linter.concreteInstances false in
/-- The width limit for the rational idelic radial Mellin test on the distinct
critical-strip zeta zeros. Each test value is weighted by its selected order
once, and the limiting sum uses the full analytic order only at interior zeros. -/
public theorem tendsto_rationalRadial_stripWidth_zeroSum
    [MeasurableSpace RationalIdeleClasses] [BorelSpace RationalIdeleClasses]
    {F : ℝ → ℂ} (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F)
    {α : ℝ} {edge : criticalStripZetaZeros → ℕ} (hEdge : ∀ ρ, edge ρ ≤ zetaZeroOrder ρ) :
    Tendsto (fun β ↦ ∑' ρ : criticalStripZetaZeros,
      (stripWidthMultiplicity β |(shiftedZetaZero ρ).re| (zetaZeroOrder ρ) (edge ρ) : ℂ) *
        rationalIdeleRadialMellin F ρ)
      (𝓝[Set.Iio α] α) (𝓝 (∑' ρ : {ρ : criticalStripZetaZeros | |(shiftedZetaZero ρ).re| < α},
        (zetaZeroOrder ρ.val : ℂ) * rationalIdeleRadialMellin F ρ.val)) := by
  refine tendsto_stripWidth_zeroSum hEdge ?_
  -- Apply absolute summability to the half-twisted log profile, without using
  -- the explicit-formula identity.
  let g (t : ℝ) := exp (-(t : ℂ) / 2) * F t
  have hg : ContDiff ℝ ∞ g := (contDiff_exp.comp (ofRealCLM.contDiff.neg.div_const 2)).mul hF
  obtain ⟨B, hB, hdecay⟩ := compactLogMellin_vertical_decay hg hc.mul_left 2 4
  simpa only [(rationalIdeleRadialMellin_eq_compactLogMellin hF.continuous hc _).2] using
    summable_norm_completedZeta_contour_terms hB.le
      (fun σ hσ t ↦ hdecay σ t (abs_le.mpr ⟨by linarith [hσ.1], hσ.2⟩))

end Masullo
