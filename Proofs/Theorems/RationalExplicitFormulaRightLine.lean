module

public import Theorems.RationalExplicitFormulaExhaustion
import Lemmas.ZetaRightLine

/-!
# The reflected and split explicit-formula contour over the rationals

This is (B.4.2.4)–(B.4.2.9), p. 615, for the trivial character over `ℚ`
and the line `Re s = 2`, before evaluating either the Archimedean integral
or the individual Mellin integrals at prime powers. The conductor factor is
one, so its logarithmic term is zero.
-/

open Complex MeasureTheory Set

namespace Masullo

/-- The one-line form (B.4.2.4) of the rational contour identity. -/
public theorem completedZeta_contour_reflected {Φ : ℂ → ℂ}
    (hΦ : ∀ z, AnalyticAt ℂ Φ z)
    (hdecay : ∃ B > (0 : ℝ), ∀ σ ∈ Icc (-1 : ℝ) 2, ∀ t : ℝ,
      ‖Φ ((σ : ℂ) + (t : ℂ) * I)‖ ≤ B / (1 + |t|) ^ 4) :
    let s := fun t : ℝ ↦ (2 : ℂ) + (t : ℂ) * I
    let W := fun t ↦ Φ (s t) + Φ (1 - s t)
    Integrable (fun t ↦ W t * logDeriv completedRiemannZeta (s t)) ∧
    Summable (fun ρ : criticalStripZetaZeros ↦ ‖(zetaZeroOrder ρ : ℂ) * Φ (ρ : ℂ)‖) ∧
    (∫ t, W t * logDeriv completedRiemannZeta (s t)) / (2 * (Real.pi : ℂ)) =
      -Φ 0 - Φ 1 + ∑' ρ : criticalStripZetaZeros, (zetaZeroOrder ρ : ℂ) * Φ (ρ : ℂ) := by
  obtain ⟨hright, hleft, hzeros, hcontour⟩ := completedZeta_contour_identity hΦ hdecay
  -- The minus sign missing in the extracted (B.4.2.3) turns subtraction
  -- into addition in (B.4.2.4). Reflection also changes t to -t.
  obtain ⟨href, hleft_eq⟩ := completedZeta_reflect_left_integral hleft
  simp only [add_mul]
  refine ⟨hright.add href, hzeros, ?_⟩
  rw [integral_add hright href]
  rw [hleft_eq, sub_neg_eq_add] at hcontour
  exact hcontour

/-- Split the rational right-line formula into the real Gamma factor and the
finite-place series, before Mellin inversion. The `n`th finite term is
`vonMangoldt n / n^s` (zero at `n = 0`), so only positive powers of primes
contribute. The sum of the L¹ norms of the finite terms is finite. -/
public theorem completedZeta_contour_split {Φ : ℂ → ℂ}
    (hΦ : ∀ z, AnalyticAt ℂ Φ z)
    (hdecay : ∃ B > (0 : ℝ), ∀ σ ∈ Icc (-1 : ℝ) 2, ∀ t : ℝ,
      ‖Φ ((σ : ℂ) + (t : ℂ) * I)‖ ≤ B / (1 + |t|) ^ 4) :
    let s := fun t : ℝ ↦ (2 : ℂ) + (t : ℂ) * I
    let W := fun t ↦ Φ (s t) + Φ (1 - s t)
    let finite := fun n t ↦ W t * LSeries.term
      (fun k ↦ (ArithmeticFunction.vonMangoldt k : ℂ)) (s t) n
    Integrable (fun t ↦ W t * logDeriv Gammaℝ (s t)) ∧
    (∀ n, Integrable (finite n)) ∧ (Summable fun n ↦ ∫ t, ‖finite n t‖) ∧
    Summable (fun ρ : criticalStripZetaZeros ↦ ‖(zetaZeroOrder ρ : ℂ) * Φ (ρ : ℂ)‖) ∧
    ((∫ t, W t * logDeriv Gammaℝ (s t)) - (∑' n, ∫ t, finite n t)) / (2 * (Real.pi : ℂ)) =
      -Φ 0 - Φ 1 + ∑' ρ : criticalStripZetaZeros, (zetaZeroOrder ρ : ℂ) * Φ (ρ : ℂ) := by
  let s (t : ℝ) : ℂ := 2 + (t : ℂ) * I
  let W (t : ℝ) : ℂ := Φ (s t) + Φ (1 - s t)
  obtain ⟨hcompleted, hzeros, hcontour⟩ := completedZeta_contour_reflected hΦ hdecay
  obtain ⟨B, _hB, htest⟩ := hdecay
  have hc : Continuous Φ := continuous_iff_continuousAt.mpr fun z ↦ (hΦ z).continuousAt
  have hW : Integrable W := integrable_completedZeta_reflected_test hc
    (by simpa using htest 2 (by norm_num)) (by simpa using htest (-1) (by norm_num))
  -- (B.4.2.5)–(B.4.2.7): Split the completion on an open half-plane,
  -- combining the finite-place terms using Mathlib's von Mangoldt series.
  have hsplit (t : ℝ) : W t * logDeriv completedRiemannZeta (s t) =
      W t * logDeriv Gammaℝ (s t) + W t * logDeriv riemannZeta (s t) := by
    rw [completedZeta_logDeriv_eq_gamma_add_zeta (by simp [s]), mul_add]
  -- (B.4.2.8)–(B.4.2.9): Summability at real exponent 2 gives an L¹
  -- majorant for the integrated series, including the reflected test.
  obtain ⟨hfinite, hsum, hζ, hζeq⟩ := vonMangoldt_right_line_integrals hW
  have hΓ : Integrable (fun t ↦ W t * logDeriv Gammaℝ (s t)) := by
    convert hcompleted.sub hζ using 1
    funext t
    exact (eq_sub_of_add_eq (hsplit t).symm)
  refine ⟨hΓ, hfinite, hsum, hzeros, ?_⟩
  change (∫ t, W t * logDeriv completedRiemannZeta (s t)) / (2 * (Real.pi : ℂ)) = _ at hcontour
  rw [show (fun t ↦ W t * logDeriv completedRiemannZeta (s t)) = _ from funext hsplit,
    integral_add hΓ hζ, hζeq, ← sub_eq_add_neg] at hcontour
  exact hcontour

end Masullo
