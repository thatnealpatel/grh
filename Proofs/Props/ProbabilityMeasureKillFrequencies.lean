module

public import Lemmas.BernoulliDisplacement

/-!
# A short probability measure annihilating countably many frequencies

This is an original test-function repair, not a theorem of the manuscript.
For Theorem 12.5.1.1, pp. 519–520, (12.5.1.3–4) uses the Mellin samples
in the strip. To compare with the full sum on a short test, the repair
needs a convolution factor that kills the omitted tail, while retaining
strictly positive real moments. The theorem below supplies precisely that
factor given a summable displacement budget. It supplies neither the
budget for the omitted zeros nor an equality of the two trace limits.
See `.godel/obligations/trace-below-shell-q.md` for the scope comparison.
-/

open MeasureTheory Set

namespace Masullo

/-- Given nonreal frequencies and a summable displacement budget, a single Borel
probability measure carried by the closed budget interval kills all the given complex
exponential moments. All complex moments are integrable, and every real exponential
moment is strictly positive. Carrying is stated as zero mass on the complement. -/
public theorem exists_probability_measure_kill_frequencies (w : ℕ → ℂ)
    (him : ∀ n, (w n).im ≠ 0) (hd : Summable (fun n ↦ Real.pi / |(w n).im|)) :
    ∃ μ : Measure ℝ, IsProbabilityMeasure μ ∧
      μ ((Set.Icc 0 (∑' n, Real.pi / |(w n).im|))ᶜ) = 0 ∧
      (∀ z : ℂ, Integrable (fun t : ℝ ↦ Complex.exp (z * (t : ℂ))) μ) ∧
      (∀ n, (∫ t : ℝ, Complex.exp (w n * (t : ℂ)) ∂μ) = 0) ∧
      (∀ r : ℝ, 0 < ∫ t : ℝ, Real.exp (r * t) ∂μ) := by
  let d (n : ℕ) := Real.pi / |(w n).im|
  have hd0 (n : ℕ) : 0 ≤ d n := div_nonneg Real.pi_pos.le (abs_nonneg _)
  -- Use independent bits with a tilted Bernoulli law at each frequency.
  let ν (n : ℕ) := displacementLaw (w n) (d n)
  let (n : ℕ) : IsProbabilityMeasure (ν n) := inferInstanceAs
    (IsProbabilityMeasure (displacementLaw (w n) (d n)))
  let P := Measure.infinitePi ν
  let X := displacementSum d
  have hX : Measurable X := measurable_displacementSum d
  -- The sum is carried by the budget interval pointwise, so its law is carried there.
  let μ := P.map X
  let : IsProbabilityMeasure μ := inferInstanceAs (IsProbabilityMeasure (P.map X))
  let s := Icc 0 (∑' n, d n)
  have hs : μ sᶜ = 0 := by
    rw [Measure.map_apply hX (isCompact_Icc (a := 0) (b := ∑' n, d n)).measurableSet.compl]
    have he : X ⁻¹' sᶜ = ∅ := by
      ext b
      have hb : X b ∈ s := displacementSum_mem_Icc hd hd0 b
      simp [hb]
    rw [he, measure_empty]
  refine ⟨μ, inferInstance, hs, ?_, ?_, integral_real_exp_pos_of_carried_by_compact isCompact_Icc hs⟩
  · intro z
    exact integrable_of_carried_by_compact (by fun_prop) isCompact_Icc hs
  · intro n
    have hz : Continuous (fun t : ℝ ↦ Complex.exp (w n * (t : ℂ))) := by fun_prop
    -- The n-th bit cancels; finite-product factorization and dominated convergence
    -- promote that cancellation to the whole sum, before pushing forward to ℝ.
    rw [integral_map hX.aemeasurable hz.measurable.aestronglyMeasurable]
    exact integral_exp_displacementSum_eq_zero ν (w n) hd hd0 n
      (integral_exp_displacementLaw (w n) (him n))

end Masullo
