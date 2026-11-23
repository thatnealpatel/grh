module

public import Props.CompactLogMellinFilter
public import Props.FilteredLogDensitySeparation
import Lemmas.CompactSmoothMoments
import Props.CompactLogMellinAdjoint

/-!
# A short filtered test separating the rational trace densities

This is an original rational test construction for the comparison in Masullo's
Theorem 12.5.1.1, pp. 519–520, (12.5.1.3–4). The raw multiplier and weighted
projection are the two densities of the rational model. The construction does
not identify either with the base of the manuscript's global diagonal.
-/

open MeasureTheory Set
open scoped ContDiff

namespace Masullo

local notation "J" => (fun t : ℝ ↦ Real.exp ((-1 / 2) * t) / (1 - Real.exp (-2 * t)))
local notation "U[" β "]" =>
  (fun t : ℝ ↦ Real.exp ((β - 5 / 2) * t) / (1 - Real.exp (-2 * t)))

/-- For any given compact translation filter with the stated polynomial values,
a smooth seed can make the filtered test kill the raw multiplier density while
still detecting the projected density. All pairings are over the whole line. -/
public theorem exists_smooth_test_filtered_density_separation {μ : Measure ℝ}
    [IsProbabilityMeasure μ] {D a b : ℝ} (hμ : μ (Icc 0 D)ᶜ = 0) (ha : 0 < a) (hab : a < b)
    {P : Polynomial ℝ} (hpolar : P.eval (1 / 2) = 0) {β : ℝ} (hβ : 0 < β)
    (hproj : P.eval (5 / 2 - β) ≠ 0) :
    ∃ φ : ℝ → ℝ, ContDiff ℝ ∞ φ ∧ tsupport φ ⊆ Icc a b ∧
      let f := logPolynomialDeriv P (logTranslateAverage μ φ)
      ContDiff ℝ ∞ f ∧ tsupport f ⊆ Icc a (b + D) ∧
        (Integrable (fun t ↦ J t * f t) ∧ (∫ t, J t * f t) = 0) ∧
        (Integrable (fun t ↦ U[β] t * f t) ∧ (∫ t, U[β] t * f t) ≠ 0) := by
  let I := Ioo a b
  let KJ := filteredLogDensity μ P (-1 / 2)
  let KU := filteredLogDensity μ P (β - 5 / 2)
  have hpos : I ⊆ Ioi (0 : ℝ) := fun _ ht ↦ ha.trans ht.1
  have hJ : ContinuousOn KJ I :=
    (filteredLogDensity_analyticOnNhd hμ P (-1 / 2)).continuousOn.mono hpos
  have hU : ContinuousOn KU I :=
    (filteredLogDensity_analyticOnNhd hμ P (β - 5 / 2)).continuousOn.mono hpos
  -- Inclusion of the two moment kernels would force proportional densities.
  have hseed : ∃ φ : ℝ → ℝ, ContDiff ℝ ∞ φ ∧ HasCompactSupport φ ∧ tsupport φ ⊆ I ∧
      (∫ t, φ t * KJ t) = 0 ∧ (∫ t, φ t * KU t) ≠ 0 := by
    by_contra! hnone
    obtain ⟨c, hc⟩ := compactSmooth_moment_relation (ι := Unit) (w := fun _ ↦ KJ)
      isOpen_Ioo (fun _ ↦ hJ) hU fun φ hφ hcpt hs hzero ↦ hnone φ hφ hcpt hs (hzero ())
    apply filteredLogDensity_not_eqOn_mul hμ hpolar hβ hproj isOpen_Ioo
      (nonempty_Ioo.mpr hab) hpos (c ())
    apply eqOn_of_compactSmooth_moments_eq isOpen_Ioo hU (hJ.const_mul (c ()))
    intro φ hφ hcpt hs
    rw [hc φ hφ hcpt hs]
    simp only [Finset.univ_unique, Finset.sum_singleton, mul_left_comm (φ _),
      integral_const_mul]
  obtain ⟨φ, hφ, _, hs, hz, hnz⟩ := hseed
  have hs' := hs.trans Ioo_subset_Icc_self
  obtain ⟨havg, hsupport⟩ := logTranslateAverage_smooth_supported hμ hφ hs'
  obtain ⟨hf, hfs⟩ := logPolynomialDeriv_smooth_supported P havg
  -- Move the filter back from the two adjoint densities to the same seed.
  obtain ⟨hj, _, hjeq⟩ := integral_logPolynomialDeriv_logTranslateAverage hμ P hφ ha hs'
    (contDiffOn_rationalLogTraceDensity (-1 / 2))
  obtain ⟨hu, _, hueq⟩ := integral_logPolynomialDeriv_logTranslateAverage hμ P hφ ha hs'
    (contDiffOn_rationalLogTraceDensity (β - 5 / 2))
  refine ⟨φ, hφ, hs', hf, hfs.trans hsupport, ⟨hj, hjeq.trans ?_⟩, ⟨hu, ?_⟩⟩
  · simpa only [KJ, filteredLogDensity, mul_comm] using hz
  · rw [hueq]
    simpa only [KU, filteredLogDensity, mul_comm] using hnz

/-- Under the reciprocal-height budget, a single short filtered test both
separates the raw and projected densities and kills every prescribed Mellin
sample. The theorem does not assert the budget for the actual omitted zeros. -/
public theorem exists_compactLogMellin_filter_trace_separation (w : ℕ → ℂ)
    (him : ∀ n, (w n).im ≠ 0) (hd : Summable (fun n ↦ Real.pi / |(w n).im|))
    {a b : ℝ} (ha : 0 < a) (hab : a < b) {P : Polynomial ℝ} (hpolar : P.eval (1 / 2) = 0)
    {β : ℝ} (hβ : 0 < β) (hproj : P.eval (5 / 2 - β) ≠ 0) :
    let D := ∑' n, Real.pi / |(w n).im|
    ∃ f : ℝ → ℝ, ContDiff ℝ ∞ f ∧ tsupport f ⊆ Icc a (b + D) ∧
      (Integrable (fun t ↦ J t * f t) ∧ (∫ t, J t * f t) = 0) ∧
      (Integrable (fun t ↦ U[β] t * f t) ∧ (∫ t, U[β] t * f t) ≠ 0) ∧
      ∀ z : ℂ, (P.eval₂ Complex.ofRealHom (-z) = 0 ∨ z ∈ range w) →
        compactLogMellin (fun x ↦ (f x : ℂ)) z = 0 := by
  dsimp only
  obtain ⟨μ, hprob, hμ, _, hfilter⟩ := exists_compactLogMellin_filter w him hd
  let := hprob
  obtain ⟨φ, hφ, hs, hf, hfs, hj, hu⟩ :=
    exists_smooth_test_filtered_density_separation hμ ha hab hpolar hβ hproj
  -- Use the same measure, polynomial, and seed for the Mellin vanishings.
  obtain ⟨_, _, hz⟩ := hfilter P hφ hs
  exact ⟨_, hf, hfs, hj, hu, fun z hw ↦ (hz z).2 hw⟩

end Masullo
