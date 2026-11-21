module

public import Lemmas.ZetaZeroSummability
public import Props.ZeroMassUniqueness
import Mathlib.Tactic.NormNum

/-!
# Conditional zeta divisor comparison

This is the rational trivial-isotype implication from agreement of the full
zero sum at (B.4.2.2), p. 614, and the capped critical-line sum at
(13.3.1.1)–(13.3.1.3), p. 522, on the common positive-log tests. The
implication is project work. Neither agreement nor the geometric trace
needed to establish it is proved here.
-/

open MeasureTheory Set
open scoped ContDiff

namespace Masullo

/-- The rational spectral cap is one at a critical-line zero and zero off the line. -/
public noncomputable def cappedZetaZeroOrder (ρ : criticalStripZetaZeros) : ℕ :=
  if (ρ : ℂ).re = 1 / 2 then 1 else 0

private theorem cappedZetaZeroOrder_le (ρ : criticalStripZetaZeros) :
    cappedZetaZeroOrder ρ ≤ zetaZeroOrder ρ := by
  unfold cappedZetaZeroOrder
  split
  · exact zetaZeroOrder_pos ρ
  · exact Nat.zero_le _

/-- If the full and capped zeta sums agree on all smooth positive-log tests of
mass zero, every noncentral zero in the open strip is on the critical line
and has order one. Both test sums are absolutely convergent, independently
of their assumed equality. A zero at `1 / 2` would be invisible to these tests. -/
public theorem zetaZero_on_criticalLine_and_simple_of_test_sum_eq
    (heq : ∀ f : ℝ → ℂ, ContDiff ℝ ∞ f → HasCompactSupport f → tsupport f ⊆ Ioi (0 : ℝ) →
      (∫ x in Ioi (0 : ℝ), f x) = 0 →
      (∑' ρ : criticalStripZetaZeros,
        (zetaZeroOrder ρ : ℂ) * positiveLaplaceTest (shiftedZetaZero ρ) f) =
      (∑' ρ : criticalStripZetaZeros,
        (cappedZetaZeroOrder ρ : ℂ) * positiveLaplaceTest (shiftedZetaZero ρ) f)) :
    ∀ ρ : criticalStripZetaZeros, (ρ : ℂ) ≠ 1 / 2 →
      (ρ : ℂ).re = 1 / 2 ∧ zetaZeroOrder ρ = 1 := by
  let d (ρ : criticalStripZetaZeros) : ℂ := (zetaZeroOrder ρ : ℂ) - (cappedZetaZeroOrder ρ : ℂ)
  have hd (ρ : criticalStripZetaZeros) : ‖d ρ‖ ≤ (zetaZeroOrder ρ : ℝ) := by
    dsimp only [d]
    rw [← Nat.cast_sub (cappedZetaZeroOrder_le ρ), Complex.norm_natCast]
    exact_mod_cast Nat.sub_le (zetaZeroOrder ρ) (cappedZetaZeroOrder ρ)
  have hs : Summable (fun ρ ↦ ‖d ρ‖ / (1 + ‖shiftedZetaZero ρ‖ ^ 2)) :=
    summable_zetaZeroOrder_div_one_add_norm_sq.of_nonneg_of_le (fun _ ↦ by positivity)
      (fun ρ ↦ div_le_div_of_nonneg_right (hd ρ) (by positivity))
  have hann (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
      (ht : tsupport f ⊆ Ioi (0 : ℝ)) (hm : (∫ x in Ioi (0 : ℝ), f x) = 0) :
      (∑' ρ, d ρ * positiveLaplaceTest (shiftedZetaZero ρ) f) = 0 := by
    have hfull := summable_norm_zetaZero_mul_positiveLaplaceTest
      (d := fun ρ ↦ (zetaZeroOrder ρ : ℂ)) (fun ρ ↦ (Complex.norm_natCast _).le) hf hc ht
    have hcap := summable_norm_zetaZero_mul_positiveLaplaceTest
      (d := fun ρ ↦ (cappedZetaZeroOrder ρ : ℂ)) (fun ρ ↦ by
        rw [Complex.norm_natCast]
        exact_mod_cast cappedZetaZeroOrder_le ρ) hf hc ht
    simp_rw [d, sub_mul]
    rw [hfull.of_norm.tsum_sub hcap.of_norm, heq f hf hc ht hm, sub_self]
  have hzero := weight_eq_zero_of_zero_mass_annihilation shiftedZetaZero_injective
    (a := 1 / 2) (by norm_num) (fun ρ ↦ ((le_abs_self _).trans_lt
      (abs_re_shiftedZetaZero_lt ρ)).le) shiftedZetaZero_separated hs hann
  intro ρ hρ
  have hord : zetaZeroOrder ρ = cappedZetaZeroOrder ρ :=
    Nat.cast_injective (sub_eq_zero.mp (hzero ρ (sub_ne_zero.mpr hρ)))
  have hline : (ρ : ℂ).re = 1 / 2 := by
    by_contra h
    rw [cappedZetaZeroOrder, ite_eq_right h] at hord
    exact (zetaZeroOrder_pos ρ).ne' hord
  exact ⟨hline, hord.trans (ite_eq_left hline)⟩

end Masullo
