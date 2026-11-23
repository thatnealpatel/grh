module

public import Lemmas.FilteredLogDensity
public import Lemmas.CompactLogMellinAdjoint
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Lemmas.BernoulliDisplacement
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Order.Filter.AtTopBot.Field
import Mathlib.Tactic.Ring

/-!
# Separate the below-one trace densities after moving the Mellin filter

This is an original step in the rational short-test construction for
Masullo's Theorem 12.5.1.1, pp. 519–520, (12.5.1.3–4). The two densities
are those of the rational raw multiplier and projected local model,
not two evaluations of the manuscript's multiplier (p. 517,
(12.4.1.8–12)). Nonproportionality makes it possible to choose a seed
annihilating the filtered raw pairing without annihilating the filtered
projected pairing. No trace identity or summability of zeros is assumed.
-/

open Filter MeasureTheory Set
open scoped Topology

namespace Masullo

/-- In the below-one log coordinate, the projection has rate `β - 5/2`,
while killing the polar term of the raw density leaves rate at most `-5/2`.
No scalar multiple of the filtered raw density is the filtered projected
density on an open positive-log seed domain. -/
public theorem filteredLogDensity_not_eqOn_mul {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {D : ℝ} (hμ : μ (Icc 0 D)ᶜ = 0) {P : Polynomial ℝ}
    (hpolar : P.eval (1 / 2) = 0) {β : ℝ} (hβ : 0 < β)
    (hproj : P.eval (5 / 2 - β) ≠ 0) {I : Set ℝ}
    (hI : IsOpen I) (hne : I.Nonempty) (hpos : I ⊆ Ioi 0) (c : ℝ) :
    ¬ EqOn (filteredLogDensity μ P (β - 5 / 2))
      (fun t ↦ c * filteredLogDensity μ P (-1 / 2) t) I := by
  intro heq
  obtain ⟨t₀, ht₀⟩ := hne
  -- A proportionality on the seed domain would extend to all positive logs.
  have hall := AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq
      (filteredLogDensity_analyticOnNhd hμ P (β - 5 / 2))
      (analyticOnNhd_const.mul (filteredLogDensity_analyticOnNhd hμ P (-1 / 2)))
      ((convex_Ioi (0 : ℝ)).isPreconnected) (hpos ht₀)
      (Filter.eventually_of_mem (hI.mem_nhds ht₀) fun _ ht ↦ heq ht)
  -- Killing the first raw term shifts its rate down by two.
  have hraw (t : ℝ) (ht : t ∈ Ioi (0 : ℝ)) :
      filteredLogDensity μ P (-1 / 2) t = filteredLogDensity μ P (-5 / 2) t := by
    have hs := filteredLogDensity_sub_exp hμ P (-1 / 2) ht
    simpa only [neg_div, neg_neg, hpolar, zero_mul, mul_zero, zero_add,
      show -(1 / 2 : ℝ) - 2 = -(5 / 2 : ℝ) by ring] using hs
  -- Normalize both sides by the projected rate. The raw side goes to zero.
  have hdecay : Tendsto (fun t : ℝ ↦ Real.exp (-β * t)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp ((tendsto_const_mul_atBot_of_neg (neg_neg_of_pos hβ)).2 tendsto_id)
  have hz : Tendsto (fun t : ℝ ↦ c * (Real.exp (-β * t) *
      (Real.exp (5 / 2 * t) * filteredLogDensity μ P (-5 / 2) t))) atTop (𝓝 0) := by
    simpa only [neg_div, neg_neg, zero_mul, mul_zero] using
      (hdecay.mul (filteredLogDensity_tendsto hμ P (-5 / 2))).const_mul c
  have hzero : Tendsto (fun t : ℝ ↦ Real.exp (-(β - 5 / 2) * t) *
      filteredLogDensity μ P (β - 5 / 2) t) atTop (𝓝 0) := by
    apply hz.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    rw [hall (show t ∈ Ioi (0 : ℝ) from ht)]
    dsimp only
    rw [hraw t ht, show -(β - 5 / 2) * t = -β * t + 5 / 2 * t by ring, Real.exp_add]
    ring
  -- The projected limit is a nonzero polynomial value times a positive moment.
  have hlimit := filteredLogDensity_tendsto hμ P (β - 5 / 2)
  have hmoment := integral_real_exp_pos_of_carried_by_compact isCompact_Icc hμ (β - 5 / 2)
  rw [show -(β - 5 / 2) = 5 / 2 - β by ring] at hlimit
  exact (mul_ne_zero hproj hmoment.ne') (tendsto_nhds_unique (by
    simpa only [show -(β - 5 / 2) = 5 / 2 - β by ring] using hlimit) hzero)

end Masullo
