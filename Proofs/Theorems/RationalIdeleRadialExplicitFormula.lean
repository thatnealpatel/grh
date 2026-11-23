module

public import Theorems.RationalExplicitFormulaFinitePlaces
public import Theorems.RationalIdeleClassHaar
public import Theorems.RationalLocalRadialSum
public import Props.RealHaarGamma
import Mathlib.Tactic.LinearCombination

/-!
# The rational radial idelic explicit formula

This is the scalar case of (B.4.4.16), p. 623, over `ℚ` for tests pulled
back along log norm. The compact character is trivial. We give the
comparison with (B.4.2.2), p. 614, requested in footnote 27, p. 625.
The zero sum restores the full analytic orders prescribed for the residues.
For the real term, the negative of the displayed right side of
(B.4.3.13), p. 619, uses full Haar and is twice the negative logarithmic
pairing of (B.4.4.1). Thus the `1/2` in (B.4.4.16) normalizes the
full-Haar expression, not the already normalized additive pairing. This
repairs the identification invoked in (B.4.4.20), p. 625. This is not
convergence in the strong distribution topology or an evaluation of the
Chapter 12 trace. Locators use the pinned extraction.
-/

open Complex MeasureTheory NumberField IsDedekindDomain
open scoped ContDiff FourierTransform

namespace Masullo

set_option linter.concreteInstances false

variable [MeasurableSpace RationalIdeleClasses] [BorelSpace RationalIdeleClasses]

/-- The Mellin pairing on the actual idele class group at exponent `s - 1/2`.
At `s = 0` and `s = 1` these are the two polar moments of (B.4.4.16). -/
public noncomputable def rationalIdeleRadialMellin (F : ℝ → ℂ) (s : ℂ) : ℂ :=
  ∫ c : RationalIdeleClasses,
    F (Real.log (ideleClassNorm c)) * exp ((s - 1 / 2) * (Real.log (ideleClassNorm c) : ℂ))
      ∂rationalIdeleClassHaar

/-- The rational norm-one group has mass one, so pushing its quotient Haar
forward by log norm identifies each idelic pairing with the contour's
half-twisted Mellin integral, with no remaining volume factor. -/
public theorem rationalIdeleRadialMellin_eq_compactLogMellin {F : ℝ → ℂ}
    (hF : Continuous F) (hc : HasCompactSupport F) (s : ℂ) :
    Integrable (fun c : RationalIdeleClasses ↦
      F (Real.log (ideleClassNorm c)) * exp ((s - 1 / 2) * (Real.log (ideleClassNorm c) : ℂ)))
        rationalIdeleClassHaar ∧
    rationalIdeleRadialMellin F s = compactLogMellin (fun t ↦ exp (-(t : ℂ) / 2) * F t) s := by
  let f (t : ℝ) := F t * exp ((s - 1 / 2) * (t : ℂ))
  have hf : Continuous f := hF.mul (continuous_exp.comp (continuous_const.mul continuous_ofReal))
  have hi : Integrable f := hf.integrable_of_hasCompactSupport hc.mul_right
  refine ⟨(integrable_rationalIdeleClass_logNorm_iff hf.measurable).mpr hi,
    (integral_rationalIdeleClass_logNorm hi).trans ?_⟩
  apply integral_congr_ae (Filter.Eventually.of_forall fun t ↦ ?_)
  dsimp only [f]
  rw [mul_comm (exp _), mul_assoc, ← exp_add]
  congr 2
  ring

/-- In the below-one coordinate `t = -log |c|`, the Mellin argument of
(B.2.1.29), p. 599, is the negative centered exponent. The normalized
rational log Haar is invariant under this reflection. -/
public theorem rationalIdeleRadialMellin_reflect {f : ℝ → ℂ}
    (hf : Continuous f) (hc : HasCompactSupport f) (s : ℂ) :
    rationalIdeleRadialMellin (fun x ↦ f (-x)) s = compactLogMellin f (-(s - 1 / 2)) := by
  let g (x : ℝ) := f x * exp (-(s - 1 / 2) * (x : ℂ))
  have hg : Continuous g := hf.mul (continuous_exp.comp (continuous_const.mul continuous_ofReal))
  have hgc : HasCompactSupport g := hc.mul_right
  have hreflect : (fun x : ℝ ↦ f (-x) * exp ((s - 1 / 2) * (x : ℂ))) =
      (fun x : ℝ ↦ g (-x)) := by
    funext x
    simp only [g, ofReal_neg, mul_neg, neg_mul, neg_neg]
  change (∫ c, (fun x : ℝ ↦ f (-x) * exp ((s - 1 / 2) * (x : ℂ)))
    (Real.log (ideleClassNorm c)) ∂rationalIdeleClassHaar) = _
  rw [hreflect]
  change (∫ c, (g ∘ Neg.neg) (Real.log (ideleClassNorm c)) ∂rationalIdeleClassHaar) = _
  rw [integral_rationalIdeleClass_logNorm
    ((hg.comp continuous_neg).integrable_of_hasCompactSupport (hgc.comp_homeomorph (Homeomorph.neg ℝ)))]
  exact (Measure.measurePreserving_neg (volume : Measure ℝ)).integral_comp
    (Homeomorph.neg ℝ).measurableEmbedding g

/-- For a smooth compact log profile, the full-order zero sum is the two
polar moments minus the real and finite local terms. The canonical real
term is the negative additive Fourier pairing of (B.4.4.1)–(2), with
no extra half factor: `real_log_profile_fourier_eq_neg_gamma` already
identifies it with the normalized half-Haar term of (B.4.4.16). -/
public theorem rationalIdeleRadial_explicit_formula {F : ℝ → ℂ}
    (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F) :
    let realKernel := fun ξ : ℝ ↦ (Real.log |ξ| : ℂ) * 𝓕 (realLogProfileAdditive F) ξ
    let realTerm := -(∫ ξ, realKernel ξ)
    let finite := fun v : HeightOneSpectrum (𝓞 ℚ) ↦ rationalLocalRadialFourier v F
    let spectral := fun ρ : criticalStripZetaZeros ↦
      (zetaZeroOrder ρ : ℂ) * rationalIdeleRadialMellin F ρ
    Integrable realKernel ∧ Function.HasFiniteSupport finite ∧ Summable (fun ρ ↦ ‖spectral ρ‖) ∧
    (∑' ρ, spectral ρ) = rationalIdeleRadialMellin F 0 + rationalIdeleRadialMellin F 1 -
      realTerm - (∑' v, finite v) := by
  let g (t : ℝ) := exp (-(t : ℂ) / 2) * F t
  have hg : ContDiff ℝ ∞ g :=
    (contDiff_exp.comp (ofRealCLM.contDiff.neg.div_const 2)).mul hF
  -- The rational contour retains the poles at 0 and 1 and the full zero orders.
  obtain ⟨_, _, hzeros, hcontour⟩ := completedZeta_contour_finite_places hg hc.mul_left
  -- Substitute the two checked local comparisons on the same half-twisted test.
  obtain ⟨_, hfinite, hprime⟩ := rationalLocalRadialFourier_tsum_eq_vonMangoldt hc
  have hreal := real_log_profile_fourier_eq_neg_gamma hF hc
  obtain ⟨hd, hk, _⟩ := real_log_profile_additive_test hF hc
  have hrealInt := (real_log_fourier_unit_subtraction (hk.toSchwartzMap hd)).1
  have hM (s : ℂ) : rationalIdeleRadialMellin F s = compactLogMellin g s :=
    (rationalIdeleRadialMellin_eq_compactLogMellin hF.continuous hc s).2
  refine ⟨hrealInt, hfinite, ?_, ?_⟩
  · simpa only [hM] using hzeros
  · -- Transport both poles and each zero term to normalized quotient Haar.
    simp only [hM]
    dsimp only at hcontour hreal hprime
    linear_combination -hcontour + hreal + hprime

end Masullo
