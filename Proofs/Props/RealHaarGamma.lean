module

public import Props.GammaRealMellin
public import Props.RealLogProfileHaar
import Lemmas.RealLogHaarFold
import Mathlib.Tactic.LinearCombination

/-! # The real Haar and Gamma terms agree over the rationals

Masullo (B.4.2.13)–(14), p. 616, gives the reflected Gamma pairing;
(B.4.4.1)–(2), pp. 619–620, gives the additive pairing and its translated
test. We compare them with the half twist at the same profile. The checked
Gamma evaluation repairs the subtraction in (B.4.2.15). For (B.4.4.16),
p. 623, the real `1/2` is a normalization of **full Haar**, not an extra
factor on the additive Fourier pairing. This is a local comparison only.
-/

open Complex Filter MeasureTheory Set
open scoped ContDiff ENNReal FourierTransform Topology

namespace Masullo

/-- The complete real local functional is the negative of the reflected
Gamma line integral. It includes the contact term, and does not require
the profile to vanish at the identity or to be even. -/
public theorem real_log_profile_fourier_eq_neg_gamma {F : ℝ → ℂ}
    (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F) :
    let g := fun x : ℝ ↦ exp (-(x : ℂ) / 2) * F x
    let s := fun t : ℝ ↦ (2 : ℂ) + (t : ℂ) * I
    (-(∫ ξ, (Real.log |ξ| : ℂ) * 𝓕 (realLogProfileAdditive F) ξ) =
      -((∫ t, (compactLogMellin g (s t) + compactLogMellin g (1 - s t)) *
        logDeriv Gammaℝ (s t)) / (2 * (Real.pi : ℂ)))) := by
  intro g s
  have hg : ContDiff ℝ ∞ g := by
    have he : ContDiff ℝ ∞ (fun x : ℝ ↦ exp (-(x : ℂ) / 2)) := by
      apply Complex.contDiff_exp.comp
      exact (Complex.ofRealCLM.contDiff.neg).div_const 2
    exact he.mul hF
  have hgk : HasCompactSupport g := hc.mul_left
  have hg₀ : g 0 = F 0 := by simp [g]
  let B (x : ℝ) := (2 * g 0 * exp (-2 * (x : ℂ)) - g x - exp (-(x : ℂ)) * g (-x)) /
    (1 - exp (-2 * (x : ℂ)))
  obtain ⟨hB, hΓ⟩ := compactLogMellin_GammaReal_evaluation hg hgk
  change IntegrableOn B (Ioi 0) at hB
  obtain ⟨hd, hk, _⟩ := real_log_profile_additive_test hF hc
  -- Fold both real signs and both log rays at fixed cutoff. Keep the identity
  -- subtraction inside the combined Gamma kernel when removing the cutoff.
  let S (x : ℝ) := 2 * F 0 * exp (-2 * (x : ℂ)) / (1 - exp (-2 * (x : ℂ)))
  have hpoint (x : ℝ) : -B x + S x =
      (F x + F (-x)) * exp (-(x : ℂ) / 2) / (1 - exp (-2 * (x : ℂ))) := by
    have ht : -(x : ℂ) + -((-x : ℝ) : ℂ) / 2 = -(x : ℂ) / 2 := by push_cast; ring
    simp only [B, S, hg₀]
    rw [show exp (-(x : ℂ)) * g (-x) = exp (-(x : ℂ) / 2) * F (-x) by
      rw [show g (-x) = _ from rfl, ← mul_assoc, ← exp_add, ht]]
    simp only [g, div_eq_mul_inv]
    ring
  have hbare := real_log_profile_haar_log_principalValue hF hc
  have hcomp := (RealLogHaarFold.tendsto_setIntegral_Ioi_zero hB).neg.add
    (RealLogHaarFold.tendsto_subtraction_correction (F 0))
  dsimp only at hbare
  have hlim := tendsto_nhds_unique hbare (hcomp.congr' (by
    filter_upwards [eventually_mem_nhdsWithin (a := (0 : ℝ)) (s := Ioi 0)] with ε hε
    have hε' : 0 < ε := hε
    rw [(RealLogHaarFold.fold (hk.toSchwartzMap hd).integrable hε').2]
    change -(∫ x in Ioi ε, B x) + ((∫ x in Ioi ε, S x) + _) = _
    have hBn : IntegrableOn (fun x ↦ -B x) (Ioi ε) :=
      (hB.mono_set (Ioi_subset_Ioi hε'.le)).neg
    have hS : IntegrableOn S (Ioi ε) := (RealLogHaarFold.integral_subtraction (F 0) hε').1
    rw [← integral_neg, ← add_assoc, ← integral_add hBn hS]
    simp_rw [hpoint]))
  -- The primitive contributes `-log 2`; the full Fourier contact term
  -- restores `log (2π) + γ`, leaving precisely the Gamma constant.
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) Real.pi_ne_zero, Complex.ofReal_add,
    Complex.ofReal_add] at hlim
  change (∫ t, (compactLogMellin g (s t) + compactLogMellin g (1 - s t)) *
      logDeriv Gammaℝ (s t)) / (2 * (Real.pi : ℂ)) =
    -((Real.log Real.pi : ℂ) + (Real.eulerMascheroniConstant : ℂ)) * g 0 +
      ∫ x in Ioi (0 : ℝ), B x at hΓ
  rw [hg₀] at hΓ
  linear_combination hlim + hΓ

/-- The symmetric half-Haar cutoff, with both the logarithmic counterterm
and the Fourier contact term restored, tends to the real local term in
(B.4.4.16), i.e., minus the reflected Gamma integral before the outer
minus sign of the idelic explicit formula. -/
public theorem real_log_profile_haar_log_tendsto_neg_gamma {F : ℝ → ℂ}
    (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F) :
    let g := fun x : ℝ ↦ exp (-(x : ℂ) / 2) * F x
    let s := fun t : ℝ ↦ (2 : ℂ) + (t : ℂ) * I
    let μ := (1 / 2 : ℝ≥0∞) • realMultiplicativeHaar
    Tendsto (fun ε : ℝ ↦
      (∫ y in {y : ℝˣ | ε ≤ |Real.log (|(y : ℝ)|)|}, realLogProfileHaarKernel F y ∂μ) +
        (Real.log ε : ℂ) * F 0 +
        ((Real.log (2 * Real.pi) + Real.eulerMascheroniConstant : ℝ) : ℂ) * F 0)
      (𝓝[Ioi 0] 0)
      (𝓝 (-((∫ t, (compactLogMellin g (s t) + compactLogMellin g (1 - s t)) *
        logDeriv Gammaℝ (s t)) / (2 * (Real.pi : ℂ))))) := by
  dsimp only
  have h := (real_log_profile_haar_log_principalValue hF hc).add_const
    (((Real.log (2 * Real.pi) + Real.eulerMascheroniConstant : ℝ) : ℂ) * F 0)
  simpa only [sub_add_cancel, real_log_profile_fourier_eq_neg_gamma hF hc] using h

end Masullo
