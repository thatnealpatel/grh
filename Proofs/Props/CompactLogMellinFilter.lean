module

public import Lemmas.CompactLogMellinPolynomial
public import Lemmas.CompactLogMellinSmoothing
public import Props.ProbabilityMeasureKillFrequencies

/-!
# Short real log tests with prescribed zero Mellin samples

Original test-function construction for the rational comparisons with the
strip sum in Masullo, Theorem 12.5.1.1, pp. 519–520, (12.5.1.3–4).
A small translation budget handles a countable tail; a real polynomial in
the log derivative handles prescribed finite roots without further support
loss. The summable budget is an input, not a conclusion about zeta zeros.
-/

open MeasureTheory Set
open scoped ContDiff

namespace Masullo

/-- Use a single probability measure for all choices of real polynomial and
short smooth seed. The measure kills the tail frequencies, and the polynomial
kills its prescribed roots at the negative Mellin argument. -/
public theorem exists_compactLogMellin_filter (w : ℕ → ℂ)
    (him : ∀ n, (w n).im ≠ 0) (hd : Summable (fun n ↦ Real.pi / |(w n).im|)) :
    let D := ∑' n, Real.pi / |(w n).im|
    ∃ μ : Measure ℝ, IsProbabilityMeasure μ ∧
      μ (Icc 0 D)ᶜ = 0 ∧ (∀ r : ℝ, 0 < ∫ t : ℝ, Real.exp (r * t) ∂μ) ∧
      ∀ (P : Polynomial ℝ) {a b : ℝ} {φ : ℝ → ℝ},
        ContDiff ℝ ∞ φ → tsupport φ ⊆ Icc a b →
        let f := logPolynomialDeriv P (logTranslateAverage μ φ)
        ContDiff ℝ ∞ f ∧ tsupport f ⊆ Icc a (b + D) ∧
          ∀ z : ℂ,
            compactLogMellin (fun x ↦ (f x : ℂ)) z =
              P.eval₂ Complex.ofRealHom (-z) * compactLogMellin (fun x ↦ (φ x : ℂ)) z *
                (∫ t : ℝ, Complex.exp (z * (t : ℂ)) ∂μ) ∧
            ((P.eval₂ Complex.ofRealHom (-z) = 0 ∨ z ∈ range w) →
              compactLogMellin (fun x ↦ (f x : ℂ)) z = 0) := by
  dsimp only
  obtain ⟨μ, hprob, hμ, _, hzeros, hpos⟩ := exists_probability_measure_kill_frequencies w him hd
  let := hprob
  refine ⟨μ, hprob, hμ, hpos, ?_⟩
  intro P a b φ hφ hs
  -- Translate and average first; the log derivative costs no more support.
  obtain ⟨hsmooth, havg⟩ := logTranslateAverage_smooth_supported hμ hφ hs
  obtain ⟨hf, hfsub⟩ := logPolynomialDeriv_smooth_supported P hsmooth
  refine ⟨hf, hfsub.trans havg, fun z ↦ ?_⟩
  have hc : HasCompactSupport (logTranslateAverage μ φ) :=
    isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) havg
  -- The two Mellin factors vanish independently, without dividing by either.
  have heq := (compactLogMellin_logPolynomialDeriv P hsmooth hc z).trans (by
    rw [compactLogMellin_logTranslateAverage hμ hφ.continuous hs z, ← mul_assoc])
  refine ⟨heq, fun hz ↦ ?_⟩
  rw [heq]
  rcases hz with hP | ⟨n, rfl⟩
  · simp [hP]
  · simp [hzeros n]

end Masullo
