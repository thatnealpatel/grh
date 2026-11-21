module

public import Lemmas.CutoffSeries
public import Lemmas.SubtractedResolvent
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
# Conditional uniqueness on the positive-log tests

The support and mass conditions describe the common one-sided radial tests
over `ℚ` at (13.3.1.2), p. 522 of Masullo's pinned edition. The uniqueness
argument and its family hypotheses are project work. For the divisor
application, `w i` ranges over distinct shifted zeros and `d i` is the full
order minus the capped weight at that location. The full-versus-capped
comparison is not proved here. A comparison on real tests would extend to
the complex tests below by linearity.
-/

open Filter MeasureTheory Set
open scoped ContDiff Topology

namespace Masullo

/-- A discrete exponential sum annihilating all smooth, compactly supported
positive-log tests of mass zero has no noncentral weight. The transform
`positiveLaplaceTest w f` integrates `exp (w * x) * f x` against Lebesgue
measure on `x > 0`. A weight at zero pairs only with the mass and is not detected. -/
public theorem weight_eq_zero_of_zero_mass_annihilation {ι : Type*} [Countable ι]
    {w d : ι → ℂ} (hw : Function.Injective w) {a : ℝ} (ha : 0 ≤ a)
    (hwa : ∀ i, (w i).re ≤ a)
    (hsep : ∀ z : ℂ, ∃ δ : ℝ, 0 < δ ∧ ∀ i, w i ≠ z → δ ≤ ‖z - w i‖)
    (hs : Summable (fun i ↦ ‖d i‖ / (1 + ‖w i‖ ^ 2)))
    (hann : ∀ f : ℝ → ℂ, ContDiff ℝ ∞ f → HasCompactSupport f → tsupport f ⊆ Ioi (0 : ℝ) →
      (∫ x in Ioi (0 : ℝ), f x) = 0 → (∑' i, d i * positiveLaplaceTest (w i) f) = 0) :
    ∀ i, w i ≠ 0 → d i = 0 := by
  let z₀ : ℝ := a + 1
  have hz₀ : a < z₀ := lt_add_of_pos_right a zero_lt_one
  -- The cutoff lemma corrects against a fixed mass-one bump before taking the limit.
  obtain ⟨c, hc⟩ := hasSum_subtractedReciprocals_of_annihilation ha hwa hz₀ hs hann
  have hz₀' : a < (z₀ : ℂ).re := by simpa only [Complex.ofReal_re] using hz₀
  have hgap (i : ι) : z₀ - a ≤ ‖(z₀ : ℂ) - w i‖ := by
    refine le_trans ?_ (Complex.re_le_norm _)
    simpa only [Complex.sub_re, Complex.ofReal_re] using sub_le_sub_left (hwa i) z₀
  have hne {z : ℂ} (hz : a < z.re) (i : ι) : z - w i ≠ 0 :=
    sub_ne_zero.mpr (fun h ↦ (hz.not_ge) (h ▸ hwa i))
  have hs' : Summable (fun i ↦ ‖d i‖ / (1 + ‖w i‖) ^ 2) := by
    apply hs.of_nonneg_of_le (fun _ ↦ by positivity)
    intro i
    exact div_le_div_of_nonneg_left (norm_nonneg _) (by positivity)
      (by nlinarith [norm_nonneg (w i)])
  -- The mass correction contributes a function analytic off zero.
  let G (z : ℂ) := (z⁻¹ - (z₀ : ℂ)⁻¹) * c
  have hG : AnalyticOnNhd ℂ G ({0} : Set ℂ)ᶜ := by
    intro z hz
    have hz' : z ≠ 0 := by simpa using hz
    exact ((analyticAt_inv hz').sub analyticAt_const).mul analyticAt_const
  refine subtractedResolvent_weight_eq_zero w d hw (z₀ : ℂ) hsep
    ⟨z₀ - a, sub_pos.mpr hz₀, hgap⟩ hs' G hG ⟨(z₀ : ℂ), ?_, ?_⟩
  · rintro (⟨i, hi⟩ | hzero)
    · exact hne hz₀' i (sub_eq_zero.mpr hi.symm)
    · have hz : (z₀ : ℂ) = 0 := by simpa using hzero
      exact (ha.trans_lt hz₀').ne' (by simp [hz])
  · have hopen : IsOpen {z : ℂ | a < z.re} := isOpen_lt continuous_const Complex.continuous_re
    filter_upwards [hopen.eventually_mem hz₀'] with z hz
    -- Rewrite the difference inside the sum; the unsubtracted series need not converge.
    calc
      (∑' i, subtractedResolventTerm w d (z₀ : ℂ) z i) =
          ∑' i, d i * ((z - w i)⁻¹ - ((z₀ : ℂ) - w i)⁻¹) := by
        apply tsum_congr
        intro i
        dsimp [subtractedResolventTerm]
        field_simp [hne hz i, hne hz₀' i]
        ring
      _ = G z := (hc z hz).2.tsum_eq

end Masullo
