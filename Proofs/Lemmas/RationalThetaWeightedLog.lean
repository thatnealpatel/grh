module

public import Theorems.RationalThetaIntegrability
public import Lemmas.InteriorLogJet
import Mathlib.Analysis.LocallyConvex.ContinuousOfBounded
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-! # The two-mode theta map in weighted log coordinates -/

open MeasureTheory FourierTransform
open scoped FourierTransform SchwartzMap

namespace Masullo

/-- Rational unramified inputs with both zero modes removed. -/
public abbrev RationalThetaInput := {b : 𝓢(ℝ, ℂ) // b 0 = 0 ∧ (𝓕 b) 0 = 0}

public theorem memLp_rationalTheta_weighted (b : RationalThetaInput) (a α s : ℝ)
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
@[expose] public noncomputable def rationalThetaWeightedLog (a : ℝ) {α s : ℝ}
    (hs : 0 ≤ s) (hα : 0 ≤ α) (b : RationalThetaInput) : Lp ℂ 2 (volume : Measure ℝ) :=
  (memLp_rationalTheta_weighted b a α s hs hα).toLp _

private abbrev thetaInputSubmodule : Submodule ℂ 𝓢(ℝ, ℂ) where
  carrier := Set.ofPred (fun b : 𝓢(ℝ, ℂ) ↦ b 0 = (0 : ℂ) ∧ (𝓕 b) 0 = (0 : ℂ))
  zero_mem' := by
    change (0 : 𝓢(ℝ, ℂ)) 0 = 0 ∧ (𝓕 (0 : 𝓢(ℝ, ℂ))) 0 = 0
    simp
  add_mem' := by
    rintro b c ⟨hb, hbF⟩ ⟨hc, hcF⟩
    exact ⟨by simp [hb, hc], by simp [FourierAdd.fourier_add, hbF, hcF]⟩
  smul_mem' := by
    rintro k b ⟨hb, hbF⟩
    exact ⟨by simp [hb], by simp [fourier_smul, hbF]⟩

private theorem rationalTheta_add (b c : 𝓢(ℝ, ℂ)) {t : ℝ} (ht : t ≠ 0) :
    rationalTheta (b + c) t = rationalTheta b t + rationalTheta c t := by
  unfold rationalTheta
  simp only [_root_.add_apply]
  exact (summable_norm_schwartz_int_mul b ht).of_norm.subtype _ |>.tsum_add
    ((summable_norm_schwartz_int_mul c ht).of_norm.subtype _)

private noncomputable def weightedLogLinear (a : ℝ) {α s : ℝ}
    (hs : 0 ≤ s) (hα : 0 ≤ α) : thetaInputSubmodule →ₗ[ℂ] Lp ℂ 2 (volume : Measure ℝ) where
  toFun b := rationalThetaWeightedLog a hs hα b
  map_add' b c := by
    apply Lp.ext
    filter_upwards [(memLp_rationalTheta_weighted (b + c) a α s hs hα).coeFn_toLp,
      (memLp_rationalTheta_weighted b a α s hs hα).coeFn_toLp,
      (memLp_rationalTheta_weighted c a α s hs hα).coeFn_toLp,
      Lp.coeFn_add (rationalThetaWeightedLog a hs hα b) (rationalThetaWeightedLog a hs hα c)]
      with x hbc hb hc hadd
    change rationalThetaWeightedLog a hs hα (b + c) x = _
    rw [hadd]
    simp only [Pi.add_apply, rationalThetaWeightedLog, hbc, hb, hc]
    change _ * (_ * rationalTheta (b.val + c.val) (Real.exp x)) = _
    rw [rationalTheta_add _ _ (Real.exp_pos x).ne', mul_add, mul_add]
  map_smul' k b := by
    apply Lp.ext
    filter_upwards [(memLp_rationalTheta_weighted (k • b) a α s hs hα).coeFn_toLp,
      (memLp_rationalTheta_weighted b a α s hs hα).coeFn_toLp,
      Lp.coeFn_smul k (rationalThetaWeightedLog a hs hα b)] with x hkb hb hsmul
    change rationalThetaWeightedLog a hs hα (k • b) x =
      (k • rationalThetaWeightedLog a hs hα b) x
    rw [hsmul]
    simp only [Pi.smul_apply]
    simp only [rationalThetaWeightedLog, hkb, hb]
    change _ * (_ * rationalTheta (k • b.val) (Real.exp x)) = _
    simp only [rationalTheta, _root_.smul_apply, smul_eq_mul, tsum_mul_left]
    ring

/-- Bounded-family Poisson tail estimates give continuity of the weighted map. -/
public theorem rationalThetaWeightedLog_continuous_of_tail_bounds (a : ℝ) {α s : ℝ}
    (hs : 0 ≤ s) (hα : 0 ≤ α) : Continuous (rationalThetaWeightedLog a hs hα) := by
  change Continuous (weightedLogLinear a hs hα)
  let : FirstCountableTopology thetaInputSubmodule :=
    TopologicalSpace.Subtype.firstCountableTopology thetaInputSubmodule.carrier
  apply LinearMap.continuous_of_locally_bounded
  intro U hU
  let A := max |a - α| |a + α|
  obtain ⟨N, hN⟩ := exists_nat_gt (2 * A + s + 1)
  have hAN : 2 * max |a + -α| |a + α| + s + 1 ≤ 2 * (N : ℝ) := by
    rw [← sub_eq_add_neg]
    have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
    change 2 * A + s + 1 ≤ 2 * (N : ℝ)
    linarith
  obtain ⟨C, hC, htheta⟩ := rationalTheta_uniform_log_bound
    (hU.image thetaInputSubmodule.subtypeL) N
  let d (x : ℝ) := C * Real.exp (-(N : ℝ) * |x|)
  let w (x : ℝ) := symmetricStripWeightRoot α s x * Real.exp (a * x)
  have hd : Continuous d := by dsimp [d]; fun_prop
  have hw : Continuous w := (continuous_symmetricStripWeightRoot α s).mul (by fun_prop)
  have hw0 (x) : 0 ≤ w x := mul_nonneg (symmetricStripWeightRoot_pos ..).le (Real.exp_pos _).le
  have hd0 (x) : 0 ≤ d x := mul_nonneg hC.le (Real.exp_pos _).le
  have hmem : MemLp (fun x ↦ w x * d x) 2 volume := by
    apply (memLp_two_iff_integrable_sq_norm (hw.mul hd).aestronglyMeasurable).2
    have hi := integrable_hardySobolevWeight_mul_norm_sq
      (Complex.continuous_ofReal.comp hd) hs hAN (fun x ↦ by
        change ‖(d x : ℂ)‖ ≤ d x
        rw [Complex.norm_real, Real.norm_of_nonneg (hd0 x)])
    convert hi using 1
    ext x
    simp only [Pi.mul_apply, Function.comp_apply]
    rw [Real.norm_of_nonneg (mul_nonneg (hw0 x) (hd0 x)), mul_pow,
      show w x ^ 2 = _ from symmetricStripWeightRoot_mul_exp_sq hα s a x,
      Complex.norm_real, Real.norm_of_nonneg (hd0 x)]
    ring
  rw [NormedSpace.image_isVonNBounded_iff]
  refine ⟨‖hmem.toLp _‖, fun b hb ↦ Lp.norm_le_norm_of_ae_le ?_⟩
  filter_upwards [(memLp_rationalTheta_weighted b a α s hs hα).coeFn_toLp, hmem.coeFn_toLp]
    with x hx hy
  change ‖rationalThetaWeightedLog a hs hα b x‖ ≤ _
  simp only [rationalThetaWeightedLog, hx, hy]
  rw [norm_mul, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (symmetricStripWeightRoot_pos ..).le, Complex.norm_exp,
    Complex.mul_re, Real.norm_of_nonneg (mul_nonneg (hw0 x) (hd0 x))]
  simp only [Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  rw [← mul_assoc]
  exact mul_le_mul_of_nonneg_left
    (htheta b.val ⟨b, hb, rfl⟩ b.property.1 b.property.2 x) (hw0 x)

end Masullo
