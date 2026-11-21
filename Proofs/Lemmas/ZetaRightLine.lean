module

public import Props.RationalExplicitFormulaResidues
public import Mathlib.NumberTheory.LSeries.Dirichlet
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic.Ring

/-! Supporting integrability and change-of-variables lemmas for the rational right line. -/

open Complex Filter MeasureTheory
open scoped Topology

namespace Masullo

/-- Reflect the left edge, with real parameter reversal and the minus sign
from the completed functional equation. -/
public theorem completedZeta_reflect_left_integral {Φ : ℂ → ℂ}
    (h : Integrable (fun t : ℝ ↦ Φ (-1 + (t : ℂ) * I) *
      logDeriv completedRiemannZeta (-1 + (t : ℂ) * I))) :
    let f := fun t : ℝ ↦ Φ (1 - (2 + (t : ℂ) * I)) *
      logDeriv completedRiemannZeta (2 + (t : ℂ) * I)
    Integrable f ∧ (∫ t : ℝ, Φ (-1 + (t : ℂ) * I) *
      logDeriv completedRiemannZeta (-1 + (t : ℂ) * I)) = -(∫ t : ℝ, f t) := by
  let g := fun t : ℝ ↦ Φ (-1 + (t : ℂ) * I) *
    logDeriv completedRiemannZeta (-1 + (t : ℂ) * I)
  dsimp only
  have heq (t : ℝ) : g (-t) = -(Φ (1 - (2 + (t : ℂ) * I)) *
      logDeriv completedRiemannZeta (2 + (t : ℂ) * I)) := by
    have h0 : (-1 + ((-t : ℝ) : ℂ) * I : ℂ) ≠ 0 := by
      intro hh
      have := congrArg re hh
      norm_num at this
    have h1 : (-1 + ((-t : ℝ) : ℂ) * I : ℂ) ≠ 1 := by
      intro hh
      have := congrArg re hh
      norm_num at this
    have hl : (-1 + ((-t : ℝ) : ℂ) * I : ℂ) = 1 - (2 + (t : ℂ) * I) := by
      push_cast
      ring
    have hr : (1 - (-1 + ((-t : ℝ) : ℂ) * I) : ℂ) = 2 + (t : ℂ) * I := by
      rw [hl]
      ring
    dsimp only [g]
    rw [completedZeta_logDeriv_reflection h0 h1, hr, hl, mul_neg]
  have heq' : (fun t ↦ -g (-t)) = fun t : ℝ ↦ Φ (1 - (2 + (t : ℂ) * I)) *
      logDeriv completedRiemannZeta (2 + (t : ℂ) * I) := funext fun t ↦ by rw [heq, neg_neg]
  refine ⟨heq' ▸ h.comp_neg.neg, ?_⟩
  change (∫ t, g t) = _
  rw [← integral_neg_eq_self g volume, integral_congr_ae (Eventually.of_forall heq), integral_neg]

/-- The sum of the right and reflected tests is integrable before inserting a
logarithmic derivative. The reflected ordinate is `-t`. -/
public theorem integrable_completedZeta_reflected_test {Φ : ℂ → ℂ} (hΦ : Continuous Φ)
    {B : ℝ}
    (hr : ∀ t : ℝ, ‖Φ (2 + (t : ℂ) * I)‖ ≤ B / (1 + |t|) ^ 4)
    (hl : ∀ t : ℝ, ‖Φ (-1 + (t : ℂ) * I)‖ ≤ B / (1 + |t|) ^ 4) :
    Integrable (fun t : ℝ ↦ Φ (2 + (t : ℂ) * I) + Φ (1 - (2 + (t : ℂ) * I))) := by
  have hs : Integrable (fun t : ℝ ↦ (1 + ‖t‖) ^ (-(4 : ℝ))) :=
    integrable_one_add_norm (by simp)
  refine (hs.const_mul (2 * B)).mono' (Continuous.aestronglyMeasurable ?_)
    (Eventually.of_forall fun t ↦ ?_)
  · have hr' : Continuous (fun t : ℝ ↦ (2 : ℂ) + (t : ℂ) * I) := by fun_prop
    have hl' : Continuous (fun t : ℝ ↦ 1 - (2 + (t : ℂ) * I)) := by fun_prop
    exact (hΦ.comp hr').add (hΦ.comp hl')
  rw [show (1 - (2 + (t : ℂ) * I) : ℂ) = -1 + ((-t : ℝ) : ℂ) * I by push_cast; ring,
    Real.norm_eq_abs, Real.rpow_neg (by positivity),
    ← (show ((4 : ℕ) : ℝ) = 4 by norm_num), Real.rpow_natCast]
  simpa [abs_neg, div_eq_mul_inv, add_mul, two_mul] using
    (norm_add_le _ _).trans (add_le_add (hr t) (hl (-t)))

/-- On the Euler-product half-plane, the product identity holds as a germ,
so the logarithmic derivative separates into the real factor and zeta. -/
public theorem completedZeta_logDeriv_eq_gamma_add_zeta {s : ℂ} (hs : 1 < s.re) :
    logDeriv completedRiemannZeta s = logDeriv Gammaℝ s + logDeriv riemannZeta s := by
  have heq : completedRiemannZeta =ᶠ[𝓝 s] Gammaℝ * riemannZeta := by
    filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds hs] with z hz
    have h0 : z ≠ 0 := by rintro rfl; norm_num at hz
    have hγ := Gammaℝ_ne_zero_of_re_pos (zero_lt_one.trans hz)
    change completedRiemannZeta z = Gammaℝ z * riemannZeta z
    rw [riemannZeta_def_of_ne_zero h0, mul_div_cancel₀ _ hγ]
  have h1 : s ≠ 1 := by rintro rfl; norm_num at hs
  have hγ := Gammaℝ_ne_zero_of_re_pos (zero_lt_one.trans hs)
  have hγdiff : DifferentiableAt ℂ Gammaℝ s := by
    have hd := (differentiable_Gammaℝ_inv s).inv (inv_ne_zero hγ)
    change DifferentiableAt ℂ (fun z ↦ ((Gammaℝ z)⁻¹)⁻¹) s at hd
    simpa only [inv_inv] using hd
  rw [logDeriv_apply, heq.deriv_eq, heq.eq_of_nhds]
  exact logDeriv_mul s hγ (riemannZeta_ne_zero_of_one_lt_re hs) hγdiff
    (differentiableAt_riemannZeta h1)

/-- The rational finite-place series can be integrated against any integrable
weight on `Re s = 2`. Its L¹ norms sum, not just its signed integrals. -/
public theorem vonMangoldt_right_line_integrals {W : ℝ → ℂ} (hW : Integrable W) :
    let s := fun t : ℝ ↦ (2 : ℂ) + (t : ℂ) * I
    let f := fun n t ↦ W t * LSeries.term (fun k ↦ (ArithmeticFunction.vonMangoldt k : ℂ)) (s t) n
    (∀ n, Integrable (f n)) ∧ (Summable fun n ↦ ∫ t, ‖f n t‖) ∧
    Integrable (fun t ↦ W t * logDeriv riemannZeta (s t)) ∧
    (∫ t, W t * logDeriv riemannZeta (s t)) = -(∑' n, ∫ t, f n t) := by
  let s (t : ℝ) : ℂ := 2 + (t : ℂ) * I
  let a (n : ℕ) : ℂ := ArithmeticFunction.vonMangoldt n
  let f (n : ℕ) (t : ℝ) := W t * LSeries.term a (s t) n
  let c (n : ℕ) : ℝ := ‖LSeries.term a 2 n‖
  have hsum : Summable c := (ArithmeticFunction.LSeriesSummable_vonMangoldt
    (s := 2) (by norm_num)).norm
  have hre (t : ℝ) : (s t).re = 2 := by simp [s]
  have hnorm (n : ℕ) (t : ℝ) : ‖LSeries.term a (s t) n‖ = c n := by
    change ‖LSeries.term a (s t) n‖ = ‖LSeries.term a 2 n‖
    rw [LSeries.norm_term_eq, LSeries.norm_term_eq, hre]
    norm_num
  have hs : Continuous s := by dsimp [s]; fun_prop
  have hc (n : ℕ) : Continuous (fun t ↦ LSeries.term a (s t) n) := by
    rcases eq_or_ne n 0 with rfl | hn
    · simpa only [LSeries.term_zero] using (continuous_const : Continuous (fun _ : ℝ ↦ (0 : ℂ)))
    · simp only [LSeries.term_of_ne_zero hn]
      have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn
      exact continuous_const.div ((continuous_const_cpow' hn').comp hs) (fun t ↦ by simp [hn'])
  have hfi (n : ℕ) : Integrable (f n) := by
    refine (hW.norm.mul_const (c n)).mono' (hW.aestronglyMeasurable.mul (hc n).aestronglyMeasurable)
      (Eventually.of_forall fun t ↦ ?_)
    change ‖W t * LSeries.term a (s t) n‖ ≤ ‖W t‖ * c n
    rw [norm_mul, hnorm]
  have hfs : Summable (fun n ↦ ∫ t, ‖f n t‖) := by
    simp only [f, norm_mul, hnorm, integral_mul_const]
    exact hsum.mul_left _
  have hL (t : ℝ) : -logDeriv riemannZeta (s t) = ∑' n, LSeries.term a (s t) n := by
    simpa only [logDeriv_apply, neg_div, LSeries] using
      (ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div
        (s := s t) (by rw [hre]; norm_num)).symm
  have hζ (t : ℝ) : ‖logDeriv riemannZeta (s t)‖ ≤ ∑' n, c n := by
    rw [← norm_neg, hL, ← show (fun n ↦ ‖LSeries.term a (s t) n‖) = c from funext (hnorm · t)]
    exact norm_tsum_le_tsum_norm (by simpa only [hnorm] using hsum)
  have hζc : Continuous (fun t ↦ logDeriv riemannZeta (s t)) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    have ht : 1 < (s t).re := by rw [hre]; norm_num
    have h1 : s t ≠ 1 := by intro ht'; rw [ht', one_re] at ht; exact lt_irrefl _ ht
    have ha := analyticOn_riemannZeta (s t) h1
    exact (ha.deriv.div ha (riemannZeta_ne_zero_of_one_lt_re ht)).continuousAt.comp hs.continuousAt
  have hζi : Integrable (fun t ↦ W t * logDeriv riemannZeta (s t)) := by
    refine (hW.norm.mul_const (∑' n, c n)).mono'
      (hW.aestronglyMeasurable.mul hζc.aestronglyMeasurable) (Eventually.of_forall fun t ↦ ?_)
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hζ t) (norm_nonneg _)
  refine ⟨hfi, hfs, hζi, ?_⟩
  change (∫ t, W t * logDeriv riemannZeta (s t)) = -(∑' n, ∫ t, f n t)
  rw [integral_tsum_of_summable_integral_norm hfi hfs, ← integral_neg]
  refine integral_congr_ae (Eventually.of_forall fun t ↦ ?_)
  change W t * logDeriv riemannZeta (s t) = -(∑' n, W t * LSeries.term a (s t) n)
  rw [tsum_mul_left, ← hL, mul_neg, neg_neg]

end Masullo
