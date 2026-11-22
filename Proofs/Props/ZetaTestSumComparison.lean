module

public import Lemmas.ZetaZeroSummability
public import Props.ZeroMassUniqueness
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.Tactic.NormNum

/-!
# Conditional zeta divisor comparison

These project implications use the full zero sum in (B.4.2.2), p. 614, or
(B.4.4.16), p. 623, with zeros counted by order, on one-sided rational radial
tests. Agreement with the closed-strip spectral sum of (10.3.2.3–4), p. 454,
would give a location bound at that width; arbitrarily small positive widths
would prove RH. Agreement with the capped critical-line sum of (13.3.1.1–3),
p. 522, would also give simplicity away from the center. Neither agreement
nor the common geometric trace evaluation needed for it is proved here.
-/

open MeasureTheory Set
open scoped ContDiff

namespace Masullo

/-- Positive-log test agreement with weights supported on the closed strip of
half-width `a`. In (10.3.2.3–4) these weights are the full orders in the interior
and possibly smaller on the boundary. Only domination by the orders and
vanishing outside the strip are needed here. The mass-zero condition is only
used to reuse the narrower test class of the uniqueness theorem. -/
@[expose] public def ZetaStripTestAgreement (a : ℝ) : Prop :=
  ∃ m : criticalStripZetaZeros → ℕ,
    (∀ ρ, m ρ ≤ zetaZeroOrder ρ) ∧
    (∀ ρ, a < |(shiftedZetaZero ρ).re| → m ρ = 0) ∧
    ∀ f : ℝ → ℂ, ContDiff ℝ ∞ f → HasCompactSupport f → tsupport f ⊆ Ioi (0 : ℝ) →
      (∫ x in Ioi (0 : ℝ), f x) = 0 →
      (∑' ρ : criticalStripZetaZeros,
        (zetaZeroOrder ρ : ℂ) * positiveLaplaceTest (shiftedZetaZero ρ) f) =
      (∑' ρ : criticalStripZetaZeros,
        (m ρ : ℂ) * positiveLaplaceTest (shiftedZetaZero ρ) f)

/-- Agreement on positive-log mass-zero tests recovers every noncentral order. -/
public theorem zetaZeroOrder_eq_of_test_sum_eq {m : criticalStripZetaZeros → ℕ}
    (hm : ∀ ρ, m ρ ≤ zetaZeroOrder ρ)
    (heq : ∀ f : ℝ → ℂ, ContDiff ℝ ∞ f → HasCompactSupport f → tsupport f ⊆ Ioi (0 : ℝ) →
      (∫ x in Ioi (0 : ℝ), f x) = 0 →
      (∑' ρ : criticalStripZetaZeros,
        (zetaZeroOrder ρ : ℂ) * positiveLaplaceTest (shiftedZetaZero ρ) f) =
      (∑' ρ : criticalStripZetaZeros,
        (m ρ : ℂ) * positiveLaplaceTest (shiftedZetaZero ρ) f))
    (ρ : criticalStripZetaZeros) (hρ : (ρ : ℂ) ≠ 1 / 2) : zetaZeroOrder ρ = m ρ := by
  let d (ρ : criticalStripZetaZeros) : ℂ := (zetaZeroOrder ρ : ℂ) - (m ρ : ℂ)
  have hd (ρ : criticalStripZetaZeros) : ‖d ρ‖ ≤ (zetaZeroOrder ρ : ℝ) := by
    dsimp only [d]
    rw [← Nat.cast_sub (hm ρ), Complex.norm_natCast]
    exact_mod_cast Nat.sub_le (zetaZeroOrder ρ) (m ρ)
  have hs : Summable (fun ρ ↦ ‖d ρ‖ / (1 + ‖shiftedZetaZero ρ‖ ^ 2)) :=
    summable_zetaZeroOrder_div_one_add_norm_sq.of_nonneg_of_le (fun _ ↦ by positivity)
      (fun ρ ↦ div_le_div_of_nonneg_right (hd ρ) (by positivity))
  have hann (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
      (ht : tsupport f ⊆ Ioi (0 : ℝ)) (hmass : (∫ x in Ioi (0 : ℝ), f x) = 0) :
      (∑' ρ, d ρ * positiveLaplaceTest (shiftedZetaZero ρ) f) = 0 := by
    have hfull := summable_norm_zetaZero_mul_positiveLaplaceTest
      (d := fun ρ ↦ (zetaZeroOrder ρ : ℂ)) (fun ρ ↦ (Complex.norm_natCast _).le) hf hc ht
    have hweighted := summable_norm_zetaZero_mul_positiveLaplaceTest
      (d := fun ρ ↦ (m ρ : ℂ)) (fun ρ ↦ by
        rw [Complex.norm_natCast]
        exact_mod_cast hm ρ) hf hc ht
    simp_rw [d, sub_mul]
    rw [hfull.of_norm.tsum_sub hweighted.of_norm, heq f hf hc ht hmass, sub_self]
  have hzero := weight_eq_zero_of_zero_mass_annihilation shiftedZetaZero_injective
    (a := 1 / 2) (by norm_num) (fun ρ ↦ ((le_abs_self _).trans_lt
      (abs_re_shiftedZetaZero_lt ρ)).le) shiftedZetaZero_separated hs hann
  exact Nat.cast_injective (sub_eq_zero.mp (hzero ρ (sub_ne_zero.mpr hρ)))

/-- Subtract the two absolutely convergent sums and apply zero-mass uniqueness.
Any zero outside the closed strip would retain its positive full order. No
identification of a boundary weight is needed to deduce this location bound. -/
public theorem zetaZero_in_closedStrip_of_test_agreement {a : ℝ} (ha : 0 ≤ a)
    (h : ZetaStripTestAgreement a) (ρ : criticalStripZetaZeros) :
    |(shiftedZetaZero ρ).re| ≤ a := by
  obtain ⟨m, hm, hout, heq⟩ := h
  by_contra! hρ
  have hne : (ρ : ℂ) ≠ 1 / 2 := by
    intro hc
    have hshift : shiftedZetaZero ρ = 0 := sub_eq_zero.mpr hc
    rw [hshift, Complex.zero_re, abs_zero] at hρ
    exact ha.not_gt hρ
  have hz := zetaZeroOrder_eq_of_test_sum_eq hm heq ρ hne
  rw [hout ρ hρ] at hz
  exact (zetaZeroOrder_pos ρ).ne' hz

/-- Agreement for some positive half-width below each positive bound would
imply RH. This does not require an agreement at width zero, a singleton
Sobolev cap, or a trace formula on tests that meet norm one. -/
public theorem riemannHypothesis_of_strip_test_agreement
    (h : ∀ ε > 0, ∃ a ∈ Ioo (0 : ℝ) ε, ZetaStripTestAgreement a) : RiemannHypothesis := by
  intro s hs htrivial _
  have h₀ : 0 < s.re := lt_of_not_ge fun h₀ ↦
    htrivial ((riemannZeta_eq_zero_iff_of_re_nonpos h₀).mp hs)
  have h₁ : s.re < 1 := lt_of_not_ge fun h₁ ↦ riemannZeta_ne_zero_of_one_le_re h₁ hs
  let ρ : criticalStripZetaZeros := ⟨s, mem_criticalStripZetaZeros.mpr ⟨hs, h₀, h₁⟩⟩
  by_contra hne
  have hp : 0 < |(shiftedZetaZero ρ).re| := by
    apply abs_pos.mpr
    have hre : (shiftedZetaZero ρ).re = s.re - 1 / 2 := by
      simp [shiftedZetaZero, ρ]
    rw [hre, sub_ne_zero]
    exact hne
  obtain ⟨a, ha, hagree⟩ := h _ hp
  exact ha.2.not_ge (zetaZero_in_closedStrip_of_test_agreement ha.1.le hagree ρ)

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
  intro ρ hρ
  have hord := zetaZeroOrder_eq_of_test_sum_eq cappedZetaZeroOrder_le heq ρ hρ
  have hline : (ρ : ℂ).re = 1 / 2 := by
    by_contra h
    rw [cappedZetaZeroOrder, ite_eq_right h] at hord
    exact (zetaZeroOrder_pos ρ).ne' hord
  exact ⟨hline, hord.trans (ite_eq_left hline)⟩

end Masullo
