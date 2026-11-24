module

public import Lemmas.BilateralPoissonInverse
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic.Ring

/-!
# Folded Poisson center and slack moments

Source: `75ca254:.godel/bob/full-lattice-deletion-33.md:9–19`.
Consumer: `3042a1a:.godel/bob/unfolded-deletion-33.md:37–41`.
Owning check session: `01a20d85-3fca-796b-bf11-8791e07c4ba8`.

The angle `φ` is measured in radians. We use a folded probability law through
its complex moments `∫ exp(i k φ) dμ = r ^ |k|`. For the source law, `dμ` is
already `P_r(φ) dφ / (2π)`; there is no further angular or integral rescaling.
For a real summable bilateral Laurent series the center uses the square, while
the cosine slack uses the squared modulus. We expand only one factor of each
product and justify that exchange by summable domination. The stencil
specialization identifies the first replies at every integer index. No Gram
solve or rejection, uniqueness, or refit conclusion is asserted.
-/

open MeasureTheory
open scoped ComplexConjugate

namespace Masullo.FoldedPoissonMoments

/-- The positive-sign Fourier character at the angle `φ` in radians. -/
@[expose] public noncomputable def angularChar (k : ℤ) (φ : ℝ) : ℂ :=
  Complex.exp (((k : ℝ) * φ : ℝ) * Complex.I)

/-- The bilateral Laurent series with negative-sign Fourier characters. -/
@[expose] public noncomputable def laurent (a : ℤ → ℝ) (φ : ℝ) : ℂ :=
  ∑' i, (a i : ℂ) * angularChar (-i) φ

/-- The moments of the normalized folded Poisson law, at every integer. -/
@[expose] public def HasPoissonMoments (μ : Measure ℝ) (r : ℝ) : Prop :=
  ∀ k : ℤ, (∫ φ, angularChar k φ ∂μ) = ((r ^ k.natAbs : ℝ) : ℂ)

/-- The real first reply to the positive-sign character. -/
@[expose] public noncomputable def firstReply (μ : Measure ℝ) (a : ℤ → ℝ) (s : ℤ) : ℝ :=
  (∫ φ, angularChar s φ * laurent a φ ∂μ).re

/-- The real Fourier moment of the square of the first mean. -/
@[expose] public noncomputable def squaredCenter (μ : Measure ℝ) (a : ℤ → ℝ) (s : ℤ) : ℝ :=
  (∫ φ, angularChar s φ * laurent a φ ^ 2 ∂μ).re

/-- The cosine moment of the weight `1 - |v|²`. -/
@[expose] public noncomputable def cosineSlackMoment (μ : Measure ℝ) (a : ℤ → ℝ)
    (s : ℤ) : ℝ :=
  ∫ φ, Real.cos ((s : ℝ) * φ) * (1 - ‖laurent a φ‖ ^ 2) ∂μ

private theorem continuous_angularChar (s : ℤ) : Continuous (angularChar s) :=
  Complex.continuous_exp.comp
    ((Complex.continuous_ofReal.comp (continuous_const.mul continuous_id)).mul continuous_const)

private theorem norm_angularChar (s : ℤ) (φ : ℝ) : ‖angularChar s φ‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I _

private theorem angularChar_re (s : ℤ) (φ : ℝ) :
    (angularChar s φ).re = Real.cos ((s : ℝ) * φ) :=
  Complex.exp_ofReal_mul_I_re _

private theorem angularChar_mul (s t : ℤ) (φ : ℝ) :
    angularChar s φ * angularChar t φ = angularChar (s + t) φ := by
  rw [angularChar, angularChar, angularChar, ← Complex.exp_add]
  congr 1
  simp only [Int.cast_add, Complex.ofReal_mul, Complex.ofReal_add]
  ring

private theorem conj_angularChar (s : ℤ) (φ : ℝ) :
    conj (angularChar s φ) = angularChar (-s) φ := by
  simp [angularChar, ← Complex.exp_conj, map_mul]

private theorem summable_norm_modes {a : ℤ → ℝ} (ha : Summable a) (n : ℤ → ℤ) (φ : ℝ) :
    Summable fun i => ‖(a i : ℂ) * angularChar (n i) φ‖ := by
  simpa only [norm_mul, norm_angularChar, mul_one, Complex.norm_real, Real.norm_eq_abs]
    using ha.abs

private theorem aestronglyMeasurable_laurent (μ : Measure ℝ) (a : ℤ → ℝ) :
    AEStronglyMeasurable (laurent a) μ :=
  AEStronglyMeasurable.tsum fun i =>
    ((continuous_angularChar (-i)).const_mul (a i : ℂ)).aestronglyMeasurable

private theorem norm_laurent_le {a : ℤ → ℝ} (ha : Summable a) (φ : ℝ) :
    ‖laurent a φ‖ ≤ ∑' i, |a i| := by
  simpa only [laurent, norm_mul, norm_angularChar, mul_one, Complex.norm_real,
    Real.norm_eq_abs] using norm_tsum_le_tsum_norm (summable_norm_modes ha (fun i => -i) φ)

private theorem aestronglyMeasurable_weight (μ : Measure ℝ) (a : ℤ → ℝ) (s : ℤ) :
    AEStronglyMeasurable (fun φ => angularChar s φ * laurent a φ) μ :=
  (continuous_angularChar s).aestronglyMeasurable.mul (aestronglyMeasurable_laurent μ a)

private theorem norm_weight_le {a : ℤ → ℝ} (ha : Summable a) (s : ℤ) (φ : ℝ) :
    ‖angularChar s φ * laurent a φ‖ ≤ ∑' i, |a i| := by
  simpa only [norm_mul, norm_angularChar, one_mul] using norm_laurent_le ha φ

private theorem integrable_mul_of_bounds {μ : Measure ℝ} [IsFiniteMeasure μ]
    {u w : ℝ → ℂ} (hu : AEStronglyMeasurable u μ) (hw : AEStronglyMeasurable w μ)
    {C D : ℝ} (hC : ∀ φ, ‖u φ‖ ≤ C) (hD : ∀ φ, ‖w φ‖ ≤ D) :
    Integrable (fun φ => u φ * w φ) μ :=
  Integrable.of_bound (hu.mul hw) (C * D) (Filter.Eventually.of_forall fun φ => by
    change ‖u φ * w φ‖ ≤ C * D
    rw [norm_mul]
    exact mul_le_mul (hC φ) (hD φ) (norm_nonneg _) ((norm_nonneg _).trans (hC φ)))

private theorem integral_re_weight {μ : Measure ℝ} [IsFiniteMeasure μ]
    {a : ℤ → ℝ} (ha : Summable a) (s : ℤ) :
    (∫ φ, (angularChar s φ * laurent a φ).re ∂μ) = firstReply μ a s :=
  integral_re (Integrable.of_bound (aestronglyMeasurable_weight μ a s) _
    (Filter.Eventually.of_forall (norm_weight_le ha s)))

private theorem conj_laurent (a : ℤ → ℝ) (φ : ℝ) :
    conj (laurent a φ) = ∑' i, (a i : ℂ) * angularChar i φ := by
  change Complex.conjCLE (∑' i, (a i : ℂ) * angularChar (-i) φ) = _
  rw [Complex.conjCLE.map_tsum]
  simp [conj_angularChar]

-- The only exchange used for the products: the unexpanded factor is part of
-- `w`, and the pointwise summable majorant is the constant-in-angle `C * |a i|`.
private theorem hasSum_integral_modes {μ : Measure ℝ} [IsFiniteMeasure μ]
    {a : ℤ → ℝ} (ha : Summable a) (n : ℤ → ℤ) {w : ℝ → ℂ}
    (hw : AEStronglyMeasurable w μ) {C : ℝ} (hC : ∀ φ, ‖w φ‖ ≤ C) :
    HasSum (fun i => a i * ∫ φ, (w φ * angularChar (n i) φ).re ∂μ)
      (∫ φ, (w φ * (∑' i, (a i : ℂ) * angularChar (n i) φ)).re ∂μ) := by
  let F (i : ℤ) (φ : ℝ) := (w φ * ((a i : ℂ) * angularChar (n i) φ)).re
  have hF (i : ℤ) : AEStronglyMeasurable (F i) μ :=
    Complex.continuous_re.comp_aestronglyMeasurable
      (hw.mul (((continuous_angularChar (n i)).const_mul (a i : ℂ)).aestronglyMeasurable))
  have hbound (i : ℤ) (φ : ℝ) : ‖F i φ‖ ≤ C * |a i| := by
    calc
      ‖F i φ‖ ≤ ‖w φ * ((a i : ℂ) * angularChar (n i) φ)‖ :=
        Complex.abs_re_le_norm _
      _ = ‖w φ‖ * |a i| := by
        simp only [norm_mul, norm_angularChar, mul_one, Complex.norm_real, Real.norm_eq_abs]
      _ ≤ C * |a i| := mul_le_mul_of_nonneg_right (hC φ) (abs_nonneg _)
  have hlim (φ : ℝ) : HasSum (fun i => F i φ)
      ((w φ * (∑' i, (a i : ℂ) * angularChar (n i) φ)).re) := by
    have hs := (summable_norm_modes ha n φ).of_norm.hasSum.mul_left (w φ)
    exact hs.map Complex.reCLM Complex.reCLM.continuous
  have h := hasSum_integral_of_dominated_convergence (fun i (_ : ℝ) => C * |a i|)
    hF (fun i => Filter.Eventually.of_forall (hbound i))
    (Filter.Eventually.of_forall fun _ => ha.abs.mul_left C)
    (integrable_const (∑' i, C * |a i|)) (Filter.Eventually.of_forall hlim)
  refine h.congr_fun fun i => ?_
  rw [← integral_const_mul]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun φ => by
    dsimp only [F]
    rw [mul_left_comm (w φ) (a i : ℂ)]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

private theorem integral_cosine {μ : Measure ℝ} [IsFiniteMeasure μ]
    {r : ℝ} (hμ : HasPoissonMoments μ r) (s : ℤ) :
    (∫ φ, Real.cos ((s : ℝ) * φ) ∂μ) = r ^ s.natAbs := by
  have hχ : Integrable (angularChar s) μ :=
    Integrable.of_bound (continuous_angularChar s).aestronglyMeasurable 1
      (Filter.Eventually.of_forall fun φ => (norm_angularChar s φ).le)
  calc
    _ = ∫ φ, (angularChar s φ).re ∂μ := by simp only [angularChar_re]
    _ = (∫ φ, angularChar s φ ∂μ).re := integral_re hχ
    _ = _ := by rw [hμ s]; rfl

/-- First replies of a summable Laurent series are the Poisson convolution. -/
public theorem hasSum_firstReply {μ : Measure ℝ} [IsFiniteMeasure μ] {r : ℝ}
    (hμ : HasPoissonMoments μ r) {a : ℤ → ℝ} (ha : Summable a) (s : ℤ) :
    HasSum (fun i => a i * r ^ (s - i).natAbs) (firstReply μ a s) := by
  rw [← integral_re_weight ha s]
  have h := hasSum_integral_modes ha (fun i => -i)
    ((continuous_angularChar s).aestronglyMeasurable (μ := μ))
    (fun φ => (norm_angularChar s φ).le)
  refine h.congr_fun fun i => ?_
  simp only [angularChar_mul, ← sub_eq_add_neg, angularChar_re, integral_cosine hμ]

/-- Expand one of the two negative-sign Laurent factors in the square. -/
public theorem squaredCenter_eq_tsum {μ : Measure ℝ} [IsFiniteMeasure μ]
    {a : ℤ → ℝ} (ha : Summable a) (s : ℤ) :
    squaredCenter μ a s = ∑' i, a i * firstReply μ a (s - i) := by
  have hw := aestronglyMeasurable_weight μ a s
  have hb := norm_weight_le ha s
  have h := hasSum_integral_modes ha (fun i => -i) hw hb
  have h' := h.congr_fun fun i => show
      a i * firstReply μ a (s - i) =
        a i * (∫ φ, (angularChar s φ * laurent a φ * angularChar (-i) φ).re ∂μ) by
    simp only [mul_right_comm (angularChar s _), angularChar_mul, ← sub_eq_add_neg,
      integral_re_weight ha]
  have hsq : Integrable (fun φ => angularChar s φ * laurent a φ ^ 2) μ := by
    simpa only [pow_two, ← mul_assoc] using integrable_mul_of_bounds hw
      (aestronglyMeasurable_laurent μ a) hb (norm_laurent_le ha)
  calc
    squaredCenter μ a s = ∫ φ, (angularChar s φ * laurent a φ ^ 2).re ∂μ :=
      (integral_re hsq).symm
    _ = _ := by simpa only [laurent, pow_two, mul_assoc] using h'.tsum_eq.symm

/-- In the squared modulus it is the conjugate factor that is expanded,
so the reply is shifted by `+i` rather than `-i`. -/
public theorem cosineSlackMoment_eq_sub_tsum {μ : Measure ℝ} [IsFiniteMeasure μ] {r : ℝ}
    (hμ : HasPoissonMoments μ r) {a : ℤ → ℝ} (ha : Summable a) (s : ℤ) :
    cosineSlackMoment μ a s = r ^ s.natAbs - ∑' i, a i * firstReply μ a (s + i) := by
  have hv := aestronglyMeasurable_laurent μ a
  have hw := aestronglyMeasurable_weight μ a s
  have hb := norm_weight_le ha s
  have h := hasSum_integral_modes ha id hw hb
  have henergy (φ : ℝ) :
      (angularChar s φ * laurent a φ * conj (laurent a φ)).re =
        Real.cos ((s : ℝ) * φ) * ‖laurent a φ‖ ^ 2 := by
    rw [mul_assoc, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    simp only [Complex.mul_re, angularChar_re, Complex.ofReal_re, Complex.ofReal_im,
      mul_zero, sub_zero]
  have hs : (∑' i, a i * firstReply μ a (s + i)) =
      ∫ φ, Real.cos ((s : ℝ) * φ) * ‖laurent a φ‖ ^ 2 ∂μ := by
    have h' := h.congr_fun fun i => show
        a i * firstReply μ a (s + i) =
          a i * (∫ φ, (angularChar s φ * laurent a φ * angularChar i φ).re ∂μ) by
      simp only [mul_right_comm (angularChar s _), angularChar_mul, integral_re_weight ha]
    simpa only [id, ← conj_laurent, henergy] using h'.tsum_eq
  have hcos : Continuous (fun φ : ℝ => Real.cos ((s : ℝ) * φ)) :=
    Real.continuous_cos.comp (continuous_const.mul continuous_id)
  have hint₁ : Integrable (fun φ => Real.cos ((s : ℝ) * φ)) μ :=
    Integrable.of_bound hcos.aestronglyMeasurable 1
      (Filter.Eventually.of_forall fun φ => Real.abs_cos_le_one ((s : ℝ) * φ))
  have hint₂ : Integrable (fun φ => Real.cos ((s : ℝ) * φ) * ‖laurent a φ‖ ^ 2) μ := by
    have hc : AEStronglyMeasurable (fun φ => conj (laurent a φ)) μ :=
      Complex.conjCLE.continuous.comp_aestronglyMeasurable hv
    have hbc (φ : ℝ) : ‖conj (laurent a φ)‖ ≤ ∑' i, |a i| := by
      simpa only [Complex.norm_conj] using norm_laurent_le ha φ
    have hi : Integrable (fun φ => (angularChar s φ * laurent a φ * conj (laurent a φ)).re) μ :=
      (integrable_mul_of_bounds hw hc hb hbc).re
    simpa only [henergy] using hi
  rw [cosineSlackMoment, hs, ← integral_cosine hμ s]
  simp only [mul_sub, mul_one, integral_sub hint₁ hint₂]

/-- The landed stencil realizes the prescribed real first replies under the
folded probability law. -/
public theorem firstReply_stencil {μ : Measure ℝ} [IsProbabilityMeasure μ] {r : ℝ}
    (hr₀ : 0 < r) (hr₁ : r < 1) (hμ : HasPoissonMoments μ r) {f : ℤ → ℝ}
    (hf : Summable f) (s : ℤ) :
    firstReply μ (BilateralPoissonInverse.stencil r f) s = f s := by
  have h := hasSum_firstReply hμ (BilateralPoissonInverse.summable_stencil r hf) s
  have h' := BilateralPoissonInverse.hasSum_kernel_mul_stencil hr₀ hr₁ hf s
  exact h.unique (h'.congr_fun fun i => mul_comm _ _)

/-- For the stencil coefficients of the first replies, the two angular
integrals are the bilateral center and cosine slack series at every index. -/
public theorem stencil_moments {μ : Measure ℝ} [IsProbabilityMeasure μ] {r : ℝ}
    (hr₀ : 0 < r) (hr₁ : r < 1) (hμ : HasPoissonMoments μ r) {f : ℤ → ℝ}
    (hf : Summable f) (s : ℤ) :
    let a := BilateralPoissonInverse.stencil r f
    squaredCenter μ a s = (∑' i, a i * f (s - i)) ∧
      cosineSlackMoment μ a s = r ^ s.natAbs - ∑' i, a i * f (s + i) := by
  dsimp only
  have ha := BilateralPoissonInverse.summable_stencil r hf
  exact ⟨by simpa only [firstReply_stencil hr₀ hr₁ hμ hf] using
      squaredCenter_eq_tsum (μ := μ) ha s,
    by simpa only [firstReply_stencil hr₀ hr₁ hμ hf] using cosineSlackMoment_eq_sub_tsum hμ ha s⟩

end Masullo.FoldedPoissonMoments
