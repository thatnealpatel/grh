module

public import Theorems.RationalExplicitFormulaContour
public import Lemmas.ZetaContourExhaustion
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# The infinite completed-zeta contour over the rationals

Masullo's (B.4.2.2), p. 614, applies the asymptotic residue formula
(B.3.2.2)–(B.3.2.5), pp. 605–606, to the completed Hecke logarithmic
derivative. Here the character is trivial over `ℚ`, the right edge is at 2,
and the fourth-power test bound is the input from vertical Schwartz decay
(B.2.2.1), p. 600. Integrals use `ds = i dt`, and the zero sum uses the
full orders of the distinct open-strip zeros.
-/

open Complex Filter MeasureTheory Set
open scoped Topology

namespace Masullo

/-- The rational contour identity (B.4.2.2) at `a = 2`. Both vertical
integrals converge absolutely, as does the sum of the tested full orders. -/
public theorem completedZeta_contour_identity {Φ : ℂ → ℂ}
    (hΦ : ∀ z, AnalyticAt ℂ Φ z)
    (hdecay : ∃ B > (0 : ℝ), ∀ σ ∈ Icc (-1 : ℝ) 2, ∀ t : ℝ,
      ‖Φ ((σ : ℂ) + (t : ℂ) * I)‖ ≤ B / (1 + |t|) ^ 4) :
    let g := fun s ↦ Φ s * logDeriv completedRiemannZeta s
    Integrable (fun t : ℝ ↦ g (2 + (t : ℂ) * I)) ∧
    Integrable (fun t : ℝ ↦ g (-1 + (t : ℂ) * I)) ∧
    Summable (fun ρ : criticalStripZetaZeros ↦ ‖(zetaZeroOrder ρ : ℂ) * Φ (ρ : ℂ)‖) ∧
    ((∫ t : ℝ, g (2 + (t : ℂ) * I)) - (∫ t : ℝ, g (-1 + (t : ℂ) * I))) /
        (2 * (Real.pi : ℂ)) =
      -Φ 0 - Φ 1 + ∑' ρ : criticalStripZetaZeros, (zetaZeroOrder ρ : ℂ) * Φ (ρ : ℂ) := by
  let g := fun s ↦ Φ s * logDeriv completedRiemannZeta s
  let f := fun ρ : criticalStripZetaZeros ↦ (zetaZeroOrder ρ : ℂ) * Φ (ρ : ℂ)
  obtain ⟨B, hB, htest⟩ := hdecay
  -- Masullo uses absolute convergence on the two lines and a full divisor sum.
  obtain ⟨D, _hD, hDedges⟩ := completedZeta_logDeriv_le_vertical
  have hcont : Continuous Φ := continuous_iff_continuousAt.mpr fun z ↦ (hΦ z).continuousAt
  have hright : Integrable (fun t : ℝ ↦ g (2 + (t : ℂ) * I)) := by
    simpa [g] using integrable_completedZeta_vertical hcont hB.le (Or.inl (rfl : (2 : ℝ) = 2))
      (htest 2 (by norm_num)) (fun t ↦ by simpa using (hDedges t).1)
  have hleft : Integrable (fun t : ℝ ↦ g (-1 + (t : ℂ) * I)) := by
    simpa [g] using integrable_completedZeta_vertical hcont hB.le (Or.inr (rfl : (-1 : ℝ) = -1))
      (htest (-1) (by norm_num)) (fun t ↦ by simpa using (hDedges t).2)
  have hf : Summable (fun ρ ↦ ‖f ρ‖) := summable_norm_completedZeta_contour_terms hB.le htest
  refine ⟨hright, hleft, hf, ?_⟩
  -- In place of the index-based growth inference in (B.3.1.3), use the
  -- checked actual-height bounds at independently selected top and bottom
  -- edges. Absolute summability makes the divisor limit independent of symmetry.
  obtain ⟨C, _hC, u, v, hu, hv, hsign, havoid, hedge⟩ := exists_completedZeta_contour_exhaustion
  have habsu : Tendsto (fun n ↦ |u n|) atTop atTop :=
    tendsto_atTop_mono (fun n ↦ neg_le_abs _) (tendsto_neg_atBot_atTop.comp hu)
  have habsv : Tendsto (fun n ↦ |v n|) atTop atTop :=
    tendsto_atTop_mono (fun n ↦ le_abs_self _) hv
  have hbottom := tendsto_completedZeta_horizontalIntegral hB.le habsu htest (fun n σ hσ ↦
    (hedge n σ hσ).1)
  have htop := tendsto_completedZeta_horizontalIntegral hB.le habsv htest (fun n σ hσ ↦
    (hedge n σ hσ).2)
  let R := ∫ t : ℝ, g (2 + (t : ℂ) * I)
  let L := ∫ t : ℝ, g (-1 + (t : ℂ) * I)
  have hboundary : Tendsto (fun n ↦ rectangleIntegral (-1) 2 (u n) (v n) g)
      atTop (𝓝 (I * R - I * L)) := by
    simpa [rectangleIntegral, g, R, L] using
      (((hbottom.sub htop).add ((intervalIntegral_tendsto_integral hright hu hv).const_mul I)).sub
        ((intervalIntegral_tendsto_integral hleft hu hv).const_mul I))
  -- The finite theorem supplies the signed polar terms and the full orders.
  have hresidues : Tendsto (fun n ↦ rectangleIntegral (-1) 2 (u n) (v n) g)
      atTop (𝓝 ((2 * (Real.pi : ℂ) * I) * (-Φ 0 - Φ 1 + ∑' ρ, f ρ))) := by
    refine ((tendsto_const_nhds.add (tendsto_sum_zetaZeros_boundedIm hu hv hf.of_norm)).const_mul
      (2 * (Real.pi : ℂ) * I)).congr fun n ↦ ?_
    simpa [g, f, show (1 : ℝ) - 2 = -1 by norm_num] using (rectangleIntegral_completedZeta_logDeriv (a := 2) (by norm_num)
      (hsign n).1 (hsign n).2 (havoid n) (fun z _ ↦ hΦ z)).symm
  have heq := tendsto_nhds_unique hboundary hresidues
  change (R - L) / (2 * (Real.pi : ℂ)) = -Φ 0 - Φ 1 + ∑' ρ, f ρ
  have hπ : (Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  apply (div_eq_iff (mul_ne_zero (by norm_num) hπ)).2
  apply mul_right_cancel₀ I_ne_zero
  linear_combination heq

end Masullo
