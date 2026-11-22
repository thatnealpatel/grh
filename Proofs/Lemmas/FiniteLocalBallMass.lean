module

public import Lemmas.FiniteLocalNormShell
import Lemmas.FiniteCompletionCompact
public import Mathlib.MeasureTheory.Measure.Haar.Basic

/-! # Multiplicative Haar masses on integral elements at a finite place -/

open IsDedekindDomain MeasureTheory NumberField Set
open scoped ENNReal

namespace Masullo

variable {K : Type*} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
  [MeasurableSpace (v.adicCompletion K)ˣ] [BorelSpace (v.adicCompletion K)ˣ]
  (μ : Measure (v.adicCompletion K)ˣ) [μ.IsHaarMeasure]
local notation "F" => v.adicCompletion K

omit [BorelSpace (v.adicCompletion K)ˣ] in
/-- The multiplicative unit mass is finite and strictly positive, independently
of the choice of additive Haar. -/
public theorem finiteLocalUnitSet_measure_bounds :
    0 < μ (finiteLocalUnitSet v) ∧ μ (finiteLocalUnitSet v) < ∞ := by
  rw [finiteLocalUnitSet_eq_range]
  let : CompactSpace (v.adicCompletionIntegers K)ˣ := compactSpace_finiteCompletionIntegralUnits K v
  have he := isOpenEmbedding_finiteCompletionIntegralUnits K v
  exact ⟨he.isOpen_range.measure_pos μ (range_nonempty _), (isCompact_range he.continuous).measure_lt_top⟩

/-- The punctured integer ball has infinite multiplicative mass: its valuation
shells are disjoint and all have the same nonzero unit mass. -/
public theorem finiteLocalBall_measure_top : μ {x : Fˣ | ‖(x : F)‖ ≤ 1} = ∞ := by
  obtain ⟨t, ht⟩ := (Valued.v : Valuation F (WithZero (Multiplicative ℤ))).exists_isUniformizer_of_isCyclic_of_nontrivial
  let π := Units.mk0 (t : F) ht.ne_zero
  rw [← finiteLocalNormShell_iUnion v (π : F) ht,
    measure_iUnion (finiteLocalNormShell_disjoint v (π : F) ht) (measurableSet_finiteLocalNormShell v (π : F))]
  simp_rw [finiteLocalNormShell_measure v μ π]
  exact ENNReal.tsum_const_eq_top_of_ne_zero (finiteLocalUnitSet_measure_bounds v μ).1.ne'

end Masullo
