module

public import Lemmas.InteriorLogJet
public import Theorems.RationalThetaMellinLogMoments
import Theorems.RationalThetaIntegrability
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Interior zeta jets annihilate the rational theta closure

This proves the closed-kernel inclusion for the log-line model of
(10.2.2.3)–(10.2.2.6), pp. 445–446. The theta profiles have been twisted
once, as in (10.1.1.3), p. 434. Neither boundary jets nor the converse
inclusion, nor any identification of adelic Haar measures, is asserted.
-/

open MeasureTheory
open scoped FourierTransform SchwartzMap

namespace Masullo

/-- Rational unramified inputs with both zero modes removed. -/
public abbrev RationalThetaInput := {b : 𝓢(ℝ, ℂ) // b 0 = 0 ∧ (𝓕 b) 0 = 0}

private theorem memLp_rationalTheta_weighted (b : RationalThetaInput) (a α s : ℝ)
    (hs : 0 ≤ s) (hα : 0 ≤ α) :
    MemLp (fun x : ℝ ↦ (symmetricStripWeightRoot α s x : ℂ) *
      (Complex.exp ((a : ℂ) * x) * rationalTheta b.val (Real.exp x))) 2 volume := by
  have htheta : Continuous (fun x : ℝ ↦ rationalTheta b.val (Real.exp x)) :=
    (rationalTheta_continuousOn b.val).comp_continuous Real.continuous_exp Real.exp_pos
  have hcont : Continuous (fun x : ℝ ↦ (symmetricStripWeightRoot α s x : ℂ) *
      (Complex.exp ((a : ℂ) * x) * rationalTheta b.val (Real.exp x))) :=
    (Complex.continuous_ofReal.comp (continuous_symmetricStripWeightRoot α s)).mul
    ((by fun_prop : Continuous (fun x : ℝ ↦ Complex.exp ((a : ℂ) * x))).mul htheta)
  apply (memLp_two_iff_integrable_sq_norm hcont.aestronglyMeasurable).2
  convert integrable_rationalTheta_hardySobolev b.val b.property.1 b.property.2 a (-α) α s hs using 1
  ext x
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (symmetricStripWeightRoot_pos α s x).le,
    Complex.norm_exp, Complex.mul_re]
  simp only [Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  rw [← mul_assoc, mul_pow, symmetricStripWeightRoot_mul_exp_sq hα]
  ring

/-- The once-twisted rational theta input in the `L²(dx)` coordinate of the
symmetric-strip Hardy–Sobolev norm. -/
public noncomputable def rationalThetaWeightedLog (a : ℝ) {α s : ℝ}
    (hs : 0 ≤ s) (hα : 0 ≤ α) (b : RationalThetaInput) : Lp ℂ 2 (volume : Measure ℝ) :=
  (memLp_rationalTheta_weighted b a α s hs hα).toLp _

/-- Every interior jet strictly below the open-strip zeta order vanishes
on the weighted log-line closure of the once-twisted rational theta inputs. -/
public theorem rationalThetaWeightedLog_closure_subset_ker (a : ℝ) {α s : ℝ}
    (hs : 0 ≤ s) {ρ : ℂ} (hpos : 0 < ρ.re) (hlt : ρ.re < 1)
    (hρ : |(ρ - (a : ℂ)).re| < α) {m : ℕ}
    (hm : (m : ℕ∞) < analyticOrderAt riemannZeta ρ) :
    closure (Set.range (rationalThetaWeightedLog a hs ((abs_nonneg _).trans hρ.le))) ⊆
      (interiorLogJet hs hρ m).ker := by
  apply closure_minimal _ (interiorLogJet hs hρ m).isClosed_ker
  rintro _ ⟨b, rfl⟩
  change interiorLogJet hs hρ m (rationalThetaWeightedLog a hs _ b) = 0
  rw [rationalThetaWeightedLog, (interiorLogJet_toLp hs hρ m _ _).2]
  exact (rationalTheta_twisted_logMoment_eq_zero b.val b.property.1 b.property.2 a hpos hlt hm).2

end Masullo
