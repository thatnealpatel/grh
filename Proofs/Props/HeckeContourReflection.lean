module

public import Props.CompactLogMellin
public import Mathlib.Analysis.Calculus.LogDeriv
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Lemmas.CompactLogMellinInversion
import Mathlib.Tactic.Ring

/-!
# Reflecting a completed Hecke contour with its conductor

In (3.2.1.6), p. 123, Masullo writes `G (1 - s) = ε(s) * F s`.
The computation in (B.4.2.3)–(4), pp. 614–615, needs the stronger
exponential form of `ε`, and the chain rule gives a minus on the
reflected logarithmic derivative. We state the exponential germ as
a hypothesis, not as a consequence of entire nonvanishing.
See `.godel/obligations/hecke-right-line-majorant.md` for the different
and conductor obligation. Manuscript comparisons are extraction-based.
-/

open Complex Filter MeasureTheory
open scoped ContDiff Topology

namespace Masullo

/-- Corrected (B.4.2.3) at an ordinary nonzero point. The constant `κ`
is `log A` once the arithmetic formula for the epsilon factor is proved. -/
public theorem completed_logDeriv_reflection {F G : ℂ → ℂ} {C κ z : ℂ}
    (hC : C ≠ 0) (hF : DifferentiableAt ℂ F z) (hG : DifferentiableAt ℂ G (1 - z)) (hz : F z ≠ 0)
    (hFE : (fun s ↦ G (1 - s)) =ᶠ[𝓝 z]
      (fun s ↦ (C * exp (κ * (s - 1 / 2))) * F s)) :
    logDeriv F z = -logDeriv G (1 - z) - κ := by
  let E (s : ℂ) := C * exp (κ * (s - 1 / 2))
  have hE : HasDerivAt E (E z * κ) z := by
    convert ((((hasDerivAt_id z).sub_const (1 / 2)).const_mul κ).cexp.const_mul C) using 1
    · rfl
    · simp [E, mul_assoc]
  have hG' : HasDerivAt (fun s : ℂ ↦ 1 - s) (-1) z :=
    (hasDerivAt_id z).const_sub (1 : ℂ)
  have hE₀ : E z ≠ 0 := mul_ne_zero hC (exp_ne_zero _)
  have hlogE : logDeriv E z = κ := by
    rw [logDeriv_apply, hE.deriv, mul_div_cancel_left₀ _ hE₀]
  have hleft : logDeriv (fun s ↦ G (1 - s)) z = -logDeriv G (1 - z) := by
    rw [logDeriv_fun_comp (f := G) (g := fun s : ℂ ↦ 1 - s) hG hG'.differentiableAt,
      hG'.deriv, mul_neg_one]
  have h := (logDeriv_congr_nhds hFE).eq_of_nhds
  change logDeriv (fun s ↦ G (1 - s)) z = logDeriv (fun s ↦ E s * F s) z at h
  rw [hleft, logDeriv_fun_mul z hE₀ hz hE.differentiableAt hF, hlogE] at h
  linear_combination -h

/-- The left upward integral is the negative of the reflected upward
integral, **minus** the conductor contact. Subtracting the left integral
in (B.4.2.2) therefore produces the **plus** contact in (B.4.2.4).
Integrability on the reflected right line implies it on the left. -/
public theorem completed_reflect_left_integral {F G : ℂ → ℂ} {κ : ℂ} (a : ℝ)
    {g : ℝ → ℂ} (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g)
    (hlog : ∀ t : ℝ,
      let z := ((1 - a : ℝ) : ℂ) + (t : ℂ) * I
      logDeriv F z = -logDeriv G (1 - z) - κ)
    (hright : Integrable (fun t : ℝ ↦
      let s := (a : ℂ) + (t : ℂ) * I
      compactLogMellin g (1 - s) * logDeriv G s)) :
    let L := fun t : ℝ ↦
      let z := ((1 - a : ℝ) : ℂ) + (t : ℂ) * I
      compactLogMellin g z * logDeriv F z
    let R := fun t : ℝ ↦
      let s := (a : ℂ) + (t : ℂ) * I
      compactLogMellin g (1 - s) * logDeriv G s
    Integrable L ∧ (∫ t, L t) / (2 * (Real.pi : ℂ)) =
      -((∫ t, R t) / (2 * (Real.pi : ℂ))) - κ * g 0 := by
  let s (t : ℝ) : ℂ := (a : ℂ) + (t : ℂ) * I
  let z (t : ℝ) : ℂ := ((1 - a : ℝ) : ℂ) + (t : ℂ) * I
  let P (t : ℝ) := compactLogMellin g (z t) * κ
  let L (t : ℝ) := compactLogMellin g (z t) * logDeriv F (z t)
  let R (t : ℝ) := compactLogMellin g (1 - s t) * logDeriv G (s t)
  let c : ℂ := 2 * (Real.pi : ℂ)
  change Integrable L ∧ (∫ t, L t) / c = -((∫ t, R t) / c) - κ * g 0
  have hz (t : ℝ) : z (-t) = 1 - s t := by dsimp [z, s]; push_cast; ring
  have hpoint (t : ℝ) : L (-t) = -R t - P (-t) := by
    have h := hlog (-t)
    change logDeriv F (z (-t)) = -logDeriv G (1 - z (-t)) - κ at h
    change compactLogMellin g (z (-t)) * logDeriv F (z (-t)) = _
    rw [h]
    simp only [R, P, hz, sub_sub_cancel]
    ring
  have hP : Integrable P := (integrable_compactLogMellin_vertical hg hc (1 - a)).mul_const κ
  have hR : Integrable R := hright
  have hL : Integrable L := (hR.comp_neg.neg.sub hP).congr <|
    Eventually.of_forall fun t ↦ by
      change -R (-t) - P t = L t
      simpa only [neg_neg] using (hpoint (-t)).symm
  have hmass : (∫ t, P t) / c = κ * g 0 := by
    have h := compactLogMellin_right_line_evaluation hg hc (1 - a) 0
    have h0 : (∫ t, compactLogMellin g (z t)) / c = g 0 := by simpa [z, c] using h
    rw [show (∫ t, P t) = (∫ t, compactLogMellin g (z t)) * κ from integral_mul_const _ _,
      mul_comm _ κ, mul_div_assoc, h0]
  refine ⟨hL, ?_⟩
  have hRn : Integrable (fun t ↦ -R t) := hR.neg
  rw [← integral_neg_eq_self L volume, integral_congr_ae (Eventually.of_forall hpoint),
    integral_sub hRn hP.comp_neg, integral_neg, sub_div, neg_div,
    integral_neg_eq_self P volume, hmass]

end Masullo
