module

public import Lemmas.StepProfileQuadraticFourier
public import Mathlib.Probability.Distributions.Cauchy
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Measured response of a finite step profile's second-moment disk

Source: `d871755:.godel/bob/four-shift-10-2.md:51–59`, with the kernel conventions of
`d871755:.godel/bob/three-shift-library.md:5–17` and
`d871755:.godel/bob/separated-second-shifts.md:11–33`.

Scope: the fixed first profile `m = -G_B/C₁` (the real jump weights already include
`exp (-z/2)`), arbitrary finite real masks at arbitrary real angular frequencies, and
every given measurable completion of its second-moment disk. Frequencies `l/25`
recover the source mask. The response has the positive scale `C₁`, as required by
the measured multiplier `-(C₁/C₂)h`. No numerical price, realization, or arithmetic
conclusion is asserted.

Owning check session: `01a20d17-2b2a-7097-a6d0-937638b43d97`.
-/

open MeasureTheory Set
open scoped ENNReal NNReal FourierTransform

namespace StepProfileDiskRadius

open StepProfileQuadraticFourier

/-- The Cauchy probability of scale `1/2`, with density `1 / (2π |1/2 + ix|²)`. -/
@[expose] public noncomputable def cauchy : Measure ℝ :=
  ProbabilityTheory.cauchyMeasure 0 (1 / 2)

private instance : IsProbabilityMeasure cauchy :=
  inferInstanceAs (IsProbabilityMeasure (ProbabilityTheory.cauchyMeasure 0 (1 / 2)))

private theorem rate_re (x : ℝ) : (rate x).re = 1 / 2 := by
  norm_num [rate, Complex.div_re, Complex.mul_re]

private theorem norm_sq_rate (x : ℝ) : ‖rate x‖ ^ 2 = (1 / 2 : ℝ) ^ 2 + x ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply, rate_re]
  have hi : (rate x).im = x := by norm_num [rate, Complex.div_im, Complex.mul_im]
  rw [hi]
  ring

private theorem pdf_eq_density (x : ℝ) :
    ProbabilityTheory.cauchyPDFReal 0 (1 / 2) x = density x := by
  rw [ProbabilityTheory.cauchyPDFReal_def, density, norm_sq_rate, sub_zero]
  push_cast
  simp only [one_div, mul_inv]
  ring

/-- The measure used by the response is exactly the density used by both quadratic transforms. -/
public theorem cauchy_eq_withDensity : cauchy = volume.withDensity (fun x ↦ ENNReal.ofReal (density x)) := by
  rw [cauchy, ProbabilityTheory.cauchyMeasure_of_scale_ne_zero 0 (by norm_num)]
  congr 1
  funext x
  rw [ProbabilityTheory.cauchyPDF_def, pdf_eq_density]

private theorem integral_cauchy (f : ℝ → ℂ) :
    (∫ x, f x ∂cauchy) = ∫ x, f x * (density x : ℂ) := by
  have hmeas : Measurable (fun x ↦ ENNReal.ofReal (density x)) := by
    unfold density rate
    fun_prop
  rw [cauchy_eq_withDensity, integral_withDensity_eq_integral_toReal_smul hmeas
    (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top) f]
  congr 1
  funext x
  rw [ENNReal.toReal_ofReal (by unfold density; positivity), Complex.real_smul, mul_comm]

/-- The fixed first moment `-G_B/C₁`, with already half-weighted jumps `b`. -/
@[expose] public noncomputable def firstMoment {ι : Type*} (J : Finset ι)
    (b z : ι → ℝ) (C₁ : ℝ) (x : ℝ) : ℂ :=
  -jumpRepresenter J b z x / (C₁ : ℂ)

/-- The pointwise radius of the conditional second-moment disk. -/
@[expose] public noncomputable def slack {ι : Type*} (J : Finset ι)
    (b z : ι → ℝ) (C₁ : ℝ) (x : ℝ) : ℝ :=
  1 - ‖firstMoment J b z C₁ x‖ ^ 2

/-- The complex trigonometric mask with real coefficients and real angular frequencies. -/
@[expose] public noncomputable def mask {κ : Type*} (K : Finset κ)
    (h ω : κ → ℝ) (x : ℝ) : ℂ :=
  ∑ k ∈ K, (h k : ℂ) * phase (ω k) x

/-- Real transform of the complex square of the first moment, using sum frequencies. -/
@[expose] public noncomputable def S {ι : Type*} (J : Finset ι)
    (b z : ι → ℝ) (C₁ s : ℝ) : ℝ :=
  (∑ j ∈ J, ∑ k ∈ J, b j * b k * sumKernel (s + z j + z k)) / C₁ ^ 2

/-- Real transform of the disk slack, including the constant's Cauchy transform. -/
@[expose] public noncomputable def R {ι : Type*} (J : Finset ι)
    (b z : ι → ℝ) (C₁ s : ℝ) : ℝ :=
  Real.exp (-|s| / 2) -
    (∑ j ∈ J, ∑ k ∈ J, b j * b k * differenceKernel (s + z j - z k)) / C₁ ^ 2

private theorem norm_phase (s x : ℝ) : ‖phase s x‖ = 1 := by
  simp [phase, Complex.norm_exp, Complex.mul_re, Complex.mul_im]

private theorem continuous_phase (s : ℝ) : Continuous (phase s) := by
  unfold phase
  fun_prop

private theorem phase_zero (x : ℝ) : phase 0 x = 1 := by simp [phase]

private theorem rate_ne_zero (x : ℝ) : rate x ≠ 0 := by
  intro hx
  simpa [hx] using rate_re x

private theorem continuous_firstMoment {ι : Type*} (J : Finset ι) (b z : ι → ℝ) (C₁ : ℝ) :
    Continuous (firstMoment J b z C₁) := by
  have hd : Continuous rate := by unfold rate; fun_prop
  have hs : Continuous (fun x ↦ ∑ j ∈ J, (b j : ℂ) * phase (z j) x) :=
    continuous_finsetSum _ fun j _ ↦ continuous_const.mul (continuous_phase (z j))
  exact ((hs.div hd rate_ne_zero).neg).div_const _

/-- The complex integral against the Cauchy probability equals the real sum kernel `S`. -/
public theorem integral_phase_firstMoment_sq {ι : Type*} (J : Finset ι)
    (b z : ι → ℝ) (C₁ s : ℝ) :
    (∫ x, phase s x * firstMoment J b z C₁ x ^ 2 ∂cauchy) = (S J b z C₁ s : ℂ) := by
  rw [integral_cauchy]
  have h (x : ℝ) : phase s x * firstMoment J b z C₁ x ^ 2 * (density x : ℂ) =
      (phase s x * jumpRepresenter J b z x ^ 2 * (density x : ℂ)) / (C₁ : ℂ) ^ 2 := by
    simp only [firstMoment, div_eq_mul_inv]
    ring
  simp_rw [h]
  rw [integral_div, StepProfileQuadraticFourier.integral_sq, S]
  push_cast
  rfl

private theorem integral_phase_norm_firstMoment_sq {ι : Type*} (J : Finset ι)
    (b z : ι → ℝ) (C₁ s : ℝ) :
    (∫ x, phase s x * ((‖firstMoment J b z C₁ x‖ ^ 2 : ℝ) : ℂ) ∂cauchy) =
      ((∑ j ∈ J, ∑ k ∈ J, b j * b k * differenceKernel (s + z j - z k)) / C₁ ^ 2 : ℝ) := by
  rw [integral_cauchy]
  have h (x : ℝ) : phase s x * ((‖firstMoment J b z C₁ x‖ ^ 2 : ℝ) : ℂ) *
      (density x : ℂ) =
      (phase s x * ((‖jumpRepresenter J b z x‖ ^ 2 : ℝ) : ℂ) * (density x : ℂ)) /
        (C₁ : ℂ) ^ 2 := by
    rw [firstMoment, norm_div, norm_neg, Complex.norm_real, Real.norm_eq_abs, div_pow, sq_abs]
    push_cast
    simp only [div_eq_mul_inv]
    ring
  simp_rw [h]
  rw [integral_div, StepProfileQuadraticFourier.integral_norm_sq]
  push_cast
  rfl

-- Fourier inversion for the constant term: the forward transform of the two-sided
-- exponential is `2π` times the Cauchy density at angular frequency `2πξ`.
private noncomputable def twoSidedExp (t : ℝ) : ℂ := (Real.exp (-|t| / 2) : ℂ)

private theorem continuous_twoSidedExp : Continuous twoSidedExp := by
  unfold twoSidedExp
  fun_prop

private theorem integrable_twoSidedExp : Integrable twoSidedExp := by
  have hpos : IntegrableOn twoSidedExp (Ioi 0) := by
    apply (integrableOn_exp_mul_complex_Ioi (a := -(1 / 2 : ℂ)) (by norm_num [Complex.div_re]) 0).congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [twoSidedExp, abs_of_pos ht, Complex.ofReal_exp]
    congr 1
    push_cast
    ring
  have hneg : IntegrableOn twoSidedExp (Iic 0) := by
    rw [← Measure.map_neg_eq_self (volume : Measure ℝ)]
    let e : MeasurableEmbedding (fun t : ℝ ↦ -t) :=
      (Homeomorph.neg ℝ).isClosedEmbedding.measurableEmbedding
    rw [e.integrableOn_map_iff]
    have he (t : ℝ) : twoSidedExp (-t) = twoSidedExp t := by simp [twoSidedExp]
    simpa only [Function.comp_def, he, neg_preimage, neg_Iic, neg_zero] using
      ((integrableOn_Ici_iff_integrableOn_Ioi (f := twoSidedExp)).mpr hpos)
  simpa only [← compl_Ioi, union_compl_self, integrableOn_univ] using hpos.union hneg

private theorem fourier_twoSidedExp (ξ : ℝ) :
    𝓕 twoSidedExp ξ = (↑(2 * Real.pi) : ℂ) * (density ((2 * Real.pi) * ξ) : ℂ) := by
  let w : ℝ := 2 * Real.pi * ξ
  let f (t : ℝ) := phase (-w) t * twoSidedExp t
  have hf : Integrable f := by
    apply integrable_twoSidedExp.norm.mono' ((continuous_phase _).mul
      continuous_twoSidedExp).aestronglyMeasurable
    exact ae_of_all _ fun t ↦ by simp [norm_phase]
  have hpos : EqOn f (fun t ↦ Complex.exp (-rate w * (t : ℂ))) (Ioi 0) := by
    intro t ht
    change phase (-w) t * twoSidedExp t = _
    rw [phase, twoSidedExp, abs_of_pos ht, Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    simp only [rate, Complex.ofReal_neg, Complex.ofReal_div, Complex.ofReal_ofNat]
    ring
  have hneg : EqOn f (fun t ↦ Complex.exp (-rate (-w) * ((-t : ℝ) : ℂ))) (Iic 0) := by
    intro t ht
    change phase (-w) t * twoSidedExp t = _
    rw [phase, twoSidedExp, abs_of_nonpos ht, Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    simp only [rate, Complex.ofReal_neg, Complex.ofReal_div, Complex.ofReal_ofNat]
    ring
  have hexp (t : ℝ) : Complex.exp (↑(-2 * Real.pi * t * ξ) * Complex.I) = phase (-w) t := by
    unfold phase w
    congr 1
    push_cast
    ring
  have hrate (y : ℝ) : (-rate y).re < 0 := by rw [Complex.neg_re, rate_re]; norm_num
  have hconj : starRingEnd ℂ (rate w) = rate (-w) := by
    simp [rate, mul_neg, neg_mul, map_ofNat]
  have hsum : rate w + rate (-w) = 1 := by simp only [rate, Complex.ofReal_neg]; ring
  rw [Real.fourier_real_eq_integral_exp_smul]
  simp only [hexp, smul_eq_mul]
  change (∫ t, f t) = _
  rw [← integral_add_compl measurableSet_Ioi hf, compl_Ioi,
    setIntegral_congr_fun measurableSet_Ioi hpos, setIntegral_congr_fun measurableSet_Iic hneg,
    integral_comp_neg_Iic 0 (fun t : ℝ ↦ Complex.exp (-rate (-w) * (t : ℂ))),
    neg_zero, integral_exp_mul_complex_Ioi (hrate w),
    integral_exp_mul_complex_Ioi (hrate (-w))]
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, neg_div_neg_eq, density,
    Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_mul, Complex.ofReal_pow]
  change 1 / rate w + 1 / rate (-w) =
    (2 * (Real.pi : ℂ)) * (1 / (2 * (Real.pi : ℂ) * (↑‖rate w‖ : ℂ) ^ 2))
  rw [← Complex.ofReal_pow, Complex.sq_norm, ← Complex.mul_conj, hconj]
  field_simp [rate_ne_zero, Complex.ofReal_ne_zero.mpr Real.pi_ne_zero]
  linear_combination hsum

private theorem integral_phase (s : ℝ) :
    (∫ x, phase s x ∂cauchy) = (Real.exp (-|s| / 2) : ℂ) := by
  let a : ℝ := 2 * Real.pi
  have ha : 0 < a := by dsimp [a]; positivity
  have hd : Integrable (fun x ↦ density x) := by
    simpa only [← pdf_eq_density] using ProbabilityTheory.integrable_cauchyPDFReal 0 (γ := 1 / 2)
  have hF : Integrable (𝓕 twoSidedExp) := by
    rw [funext fourier_twoSidedExp]
    exact ((hd.ofReal (𝕜 := ℂ)).comp_mul_left' ha.ne').const_mul _
  have hi := congrFun (continuous_twoSidedExp.fourierInv_fourier_eq integrable_twoSidedExp hF) s
  rw [Real.fourierInv_eq_fourier_neg, Real.fourier_real_eq_integral_exp_smul] at hi
  have hp (x : ℝ) : Complex.exp (↑(-2 * Real.pi * x * -s) * Complex.I) = phase s (a * x) := by
    unfold phase a
    congr 1
    push_cast
    ring
  simp only [fourier_twoSidedExp, hp, smul_eq_mul] at hi
  change (∫ x, (fun y ↦ phase s y * ((a : ℂ) * (density y : ℂ))) (a * x)) = _ at hi
  rw [Measure.integral_comp_mul_left (fun y ↦ phase s y * ((a : ℂ) * (density y : ℂ))) a,
    abs_of_pos (inv_pos.mpr ha), Complex.real_smul, ← integral_const_mul] at hi
  have hc (x : ℝ) : (↑a⁻¹ : ℂ) * (phase s x * ((a : ℂ) * (density x : ℂ))) =
      phase s x * (density x : ℂ) := by
    rw [Complex.ofReal_inv]
    field_simp [Complex.ofReal_ne_zero.mpr ha.ne']
  simp_rw [hc] at hi
  rw [integral_cauchy]
  exact hi

-- Cauchy–Schwarz on the finite measure obtained by weighting by the disk slack.
private theorem integral_norm_le_sqrt {ν : Measure ℝ} [IsFiniteMeasure ν] {H : ℝ → ℂ}
    (hH : AEStronglyMeasurable H ν) (B : ℝ) (hB : ∀ᵐ x ∂ν, ‖H x‖ ≤ B) :
    (∫ x, ‖H x‖ ∂ν) ≤ Real.sqrt ((∫ _, (1 : ℝ) ∂ν) * ∫ x, ‖H x‖ ^ 2 ∂ν) := by
  have hL : MemLp (fun x ↦ ‖H x‖) (ENNReal.ofReal 2) ν :=
    MemLp.of_bound hH.norm B (by simpa only [Real.norm_eq_abs, abs_norm] using hB)
  have h1 : MemLp (fun _ : ℝ ↦ (1 : ℝ)) (ENNReal.ofReal 2) ν := memLp_const _
  have hCS := integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
    (ae_of_all ν fun _ ↦ zero_le_one) (ae_of_all ν fun x ↦ norm_nonneg (H x)) h1 hL
  rw [Real.sqrt_mul (integral_nonneg fun _ ↦ zero_le_one), Real.sqrt_eq_rpow,
    Real.sqrt_eq_rpow]
  simpa only [one_mul, Real.rpow_two, one_pow] using hCS

private theorem ae_norm_firstMoment_le_one {ι : Type*} {J : Finset ι}
    {b z : ι → ℝ} {C₁ : ℝ} (hv : ∀ᵐ x ∂cauchy, 0 ≤ slack J b z C₁ x) :
    ∀ᵐ x ∂cauchy, ‖firstMoment J b z C₁ x‖ ≤ 1 := by
  filter_upwards [hv] with x hx
  apply (sq_le_sq₀ (norm_nonneg _) zero_le_one).mp
  simpa only [slack, sub_nonneg, one_pow] using hx

private theorem slack_le_one {ι : Type*} (J : Finset ι) (b z : ι → ℝ) (C₁ x : ℝ) :
    slack J b z C₁ x ≤ 1 := sub_le_self _ (sq_nonneg _)

private theorem continuous_slack {ι : Type*} (J : Finset ι) (b z : ι → ℝ) (C₁ : ℝ) :
    Continuous (slack J b z C₁) :=
  continuous_const.sub ((continuous_firstMoment J b z C₁).norm.pow 2)

private theorem integrable_phase_mul {f : ℝ → ℂ} (hf : Integrable f cauchy) (s : ℝ) :
    Integrable (fun x ↦ phase s x * f x) cauchy := by
  apply hf.norm.mono' ((continuous_phase s).aestronglyMeasurable.mul hf.aestronglyMeasurable)
  refine ae_of_all _ fun x ↦ ?_
  change ‖phase s x * f x‖ ≤ ‖f x‖
  rw [norm_mul, norm_phase, one_mul]

/-- The constant Cauchy transform minus the explicit norm-square transform is exactly `R`. -/
public theorem integral_phase_slack {ι : Type*} (J : Finset ι) (b z : ι → ℝ) (C₁ s : ℝ)
    (hv : ∀ᵐ x ∂cauchy, 0 ≤ slack J b z C₁ x) :
    (∫ x, phase s x * (slack J b z C₁ x : ℂ) ∂cauchy) = (R J b z C₁ s : ℂ) := by
  have hm := ae_norm_firstMoment_le_one hv
  have hn : Integrable (fun x ↦ ((‖firstMoment J b z C₁ x‖ ^ 2 : ℝ) : ℂ)) cauchy := by
    apply Integrable.of_bound (Complex.continuous_ofReal.comp
      ((continuous_firstMoment J b z C₁).norm.pow 2)).aestronglyMeasurable 1
    filter_upwards [hm] with x hx
    change ‖((‖firstMoment J b z C₁ x‖ ^ 2 : ℝ) : ℂ)‖ ≤ 1
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact pow_le_one₀ (norm_nonneg _) hx
  have hp : Integrable (phase s) cauchy := by
    simpa only [mul_one] using integrable_phase_mul (integrable_const (1 : ℂ)) s
  simp only [slack, Complex.ofReal_sub, Complex.ofReal_one, mul_sub, mul_one]
  rw [integral_sub hp (integrable_phase_mul hn s), integral_phase,
    integral_phase_norm_firstMoment_sq, R, Complex.ofReal_sub]

private theorem continuous_mask {κ : Type*} (K : Finset κ) (h ω : κ → ℝ) :
    Continuous (mask K h ω) :=
  continuous_finsetSum _ fun k _ ↦ continuous_const.mul (continuous_phase (ω k))

private theorem norm_mask_le {κ : Type*} (K : Finset κ) (h ω : κ → ℝ) (x : ℝ) :
    ‖mask K h ω x‖ ≤ ∑ k ∈ K, |h k| := by
  unfold mask
  calc
    _ ≤ ∑ k ∈ K, ‖(h k : ℂ) * phase (ω k) x‖ := norm_sum_le _ _
    _ = _ := by simp only [norm_mul, norm_phase, mul_one, Complex.norm_real, Real.norm_eq_abs]

private theorem integral_mask_mul {κ : Type*} (K : Finset κ) (h ω : κ → ℝ)
    {f : ℝ → ℂ} (hf : Integrable f cauchy) :
    (∫ x, mask K h ω x * f x ∂cauchy) =
      ∑ k ∈ K, (h k : ℂ) * ∫ x, phase (ω k) x * f x ∂cauchy := by
  simp only [mask, Finset.sum_mul, mul_assoc]
  rw [integral_finsetSum K (fun k _ ↦ (integrable_phase_mul hf (ω k)).const_mul (h k : ℂ))]
  exact Finset.sum_congr rfl fun k _ ↦ integral_const_mul _ _

private theorem phase_sub (a b x : ℝ) :
    phase a x * starRingEnd ℂ (phase b x) = phase (a - b) x := by
  unfold phase
  rw [← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, Complex.ofReal_sub]
  ring

private theorem norm_mask_sq {κ : Type*} (K : Finset κ) (h ω : κ → ℝ) (x : ℝ) :
    (↑(‖mask K h ω x‖ ^ 2) : ℂ) =
      ∑ k ∈ K, ∑ l ∈ K, (h k : ℂ) * (h l : ℂ) * phase (ω k - ω l) x := by
  rw [Complex.sq_norm, ← Complex.mul_conj]
  simp only [mask, map_sum, map_mul, Complex.conj_ofReal, Finset.sum_mul]
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ ↦ Finset.sum_congr rfl fun l _ ↦ ?_
  rw [← phase_sub]
  ring

private theorem integral_slack {ι : Type*} (J : Finset ι) (b z : ι → ℝ) (C₁ : ℝ)
    (hv : ∀ᵐ x ∂cauchy, 0 ≤ slack J b z C₁ x) :
    (∫ x, slack J b z C₁ x ∂cauchy) = R J b z C₁ 0 := by
  apply Complex.ofReal_injective
  calc
    _ = ∫ x, (slack J b z C₁ x : ℂ) ∂cauchy := (integral_ofReal (𝕜 := ℂ)).symm
    _ = _ := by
      simpa only [phase_zero, one_mul] using integral_phase_slack J b z C₁ 0 hv

private theorem integral_norm_mask_sq_mul_slack {ι κ : Type*} (J : Finset ι) (b z : ι → ℝ)
    (C₁ : ℝ) (K : Finset κ) (h ω : κ → ℝ) (hv : ∀ᵐ x ∂cauchy, 0 ≤ slack J b z C₁ x) :
    (∫ x, ‖mask K h ω x‖ ^ 2 * slack J b z C₁ x ∂cauchy) =
      ∑ k ∈ K, ∑ l ∈ K, h k * h l * R J b z C₁ (ω k - ω l) := by
  have hvI : Integrable (fun x ↦ (slack J b z C₁ x : ℂ)) cauchy := by
    apply Integrable.of_bound (Complex.continuous_ofReal.comp
      (continuous_slack J b z C₁)).aestronglyMeasurable 1
    filter_upwards [hv] with x hx
    change ‖(slack J b z C₁ x : ℂ)‖ ≤ 1
    simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hx] using slack_le_one J b z C₁ x
  have hi (k l : κ) : Integrable (fun x ↦ (h k : ℂ) * ((h l : ℂ) *
      (phase (ω k - ω l) x * (slack J b z C₁ x : ℂ)))) cauchy :=
    ((integrable_phase_mul hvI _).const_mul _).const_mul _
  apply Complex.ofReal_injective
  calc
    _ = ∫ x, ((‖mask K h ω x‖ ^ 2 * slack J b z C₁ x : ℝ) : ℂ) ∂cauchy :=
      (integral_ofReal (𝕜 := ℂ)).symm
    _ = _ := by
      simp only [Complex.ofReal_mul, Complex.ofReal_sum, norm_mask_sq, Finset.sum_mul, mul_assoc]
      rw [integral_finsetSum K (fun k _ ↦ integrable_finsetSum K (fun l _ ↦ hi k l))]
      refine Finset.sum_congr rfl fun k _ ↦ ?_
      rw [integral_finsetSum K (fun l _ ↦ hi k l)]
      refine Finset.sum_congr rfl fun l _ ↦ ?_
      rw [integral_const_mul, integral_const_mul, integral_phase_slack J b z C₁ _ hv]

-- Transfer Cauchy–Schwarz for `v dμ` back to integrals against `μ`.
private theorem integral_norm_mul_slack_le {ι κ : Type*} (J : Finset ι) (b z : ι → ℝ)
    (C₁ : ℝ) (K : Finset κ) (h ω : κ → ℝ) (hv : ∀ᵐ x ∂cauchy, 0 ≤ slack J b z C₁ x) :
    (∫ x, ‖mask K h ω x‖ * slack J b z C₁ x ∂cauchy) ≤
      Real.sqrt ((∫ x, slack J b z C₁ x ∂cauchy) *
        ∫ x, ‖mask K h ω x‖ ^ 2 * slack J b z C₁ x ∂cauchy) := by
  let v := slack J b z C₁
  let H := mask K h ω
  let ν := cauchy.withDensity (fun x ↦ ENNReal.ofReal (v x))
  have hν : ν ≤ cauchy := by
    rw [← withDensity_one (μ := cauchy)]
    exact withDensity_mono (ae_of_all _ fun x ↦ by
      change ENNReal.ofReal (v x) ≤ 1
      rw [← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal (slack_le_one J b z C₁ x))
  let : IsFiniteMeasure ν := isFiniteMeasure_of_le cauchy hν
  have hvM : Measurable (fun x ↦ ENNReal.ofReal (v x)) :=
    ENNReal.measurable_ofReal.comp (continuous_slack J b z C₁).measurable
  have hνInt (f : ℝ → ℝ) : (∫ x, f x ∂ν) = ∫ x, f x * v x ∂cauchy := by
    rw [integral_withDensity_eq_integral_toReal_smul hvM (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)]
    exact integral_congr_ae (hv.mono fun x hx ↦ by
      change 0 ≤ v x at hx
      change (ENNReal.ofReal (v x)).toReal • f x = f x * v x
      rw [ENNReal.toReal_ofReal hx, smul_eq_mul, mul_comm])
  have hCS := integral_norm_le_sqrt (ν := ν) (H := H) (continuous_mask K h ω).aestronglyMeasurable
    (∑ k ∈ K, |h k|) (ae_of_all _ (norm_mask_le K h ω))
  simpa only [hνInt, one_mul] using hCS

/-- The signed response of every given disk completion has the finite-kernel center and radius.
`R 0` and the difference-frequency sum are the mass and the second mask moment for `v dμ`.
The hypotheses are a.e.; in particular they apply to the pointwise disk constraints. -/
public theorem measured_response_center_radius {ι κ : Type*} (J : Finset ι) (b z : ι → ℝ)
    {C₁ : ℝ} (hC : 0 < C₁) (K : Finset κ) (h ω : κ → ℝ)
    (m₂ g : ℝ → ℂ) (hm₂ : AEMeasurable m₂ cauchy)
    (hv : ∀ᵐ x ∂cauchy, 0 ≤ slack J b z C₁ x) (hg : ∀ᵐ x ∂cauchy, ‖g x‖ ≤ 1)
    (hd : ∀ᵐ x ∂cauchy, m₂ x = firstMoment J b z C₁ x ^ 2 + (slack J b z C₁ x : ℂ) * g x) :
    let Q₀ := C₁ * ∑ k ∈ K, h k * S J b z C₁ (ω k)
    let Q := C₁ * (∫ x, mask K h ω x * m₂ x ∂cauchy).re
    let D := C₁ * ∫ x, ‖mask K h ω x‖ * slack J b z C₁ x ∂cauchy
    Q₀ = C₁ * (∫ x, mask K h ω x * firstMoment J b z C₁ x ^ 2 ∂cauchy).re ∧
      |Q - Q₀| ≤ D ∧
      D ≤ C₁ * Real.sqrt (R J b z C₁ 0 *
        ∑ k ∈ K, ∑ l ∈ K, h k * h l * R J b z C₁ (ω k - ω l)) := by
  dsimp only
  let m := firstMoment J b z C₁
  let H := mask K h ω
  let v := slack J b z C₁
  have hm := ae_norm_firstMoment_le_one hv
  have hmI : Integrable (fun x ↦ m x ^ 2) cauchy := by
    apply Integrable.of_bound ((continuous_firstMoment J b z C₁).pow 2).aestronglyMeasurable 1
    filter_upwards [hm] with x hx
    change ‖m x ^ 2‖ ≤ 1
    rw [norm_pow]
    exact pow_le_one₀ (norm_nonneg _) hx
  have hc' : (∫ x, H x * m x ^ 2 ∂cauchy) = (↑(∑ k ∈ K, h k * S J b z C₁ (ω k)) : ℂ) := by
    rw [integral_mask_mul K h ω hmI]
    simp only [m, integral_phase_firstMoment_sq, Complex.ofReal_sum, Complex.ofReal_mul]
  have hc : (∫ x, H x * m x ^ 2 ∂cauchy).re = ∑ k ∈ K, h k * S J b z C₁ (ω k) := by
    rw [hc', Complex.ofReal_re]
  refine ⟨congrArg (C₁ * ·) hc.symm, ?_, ?radius⟩
  case radius =>
    apply mul_le_mul_of_nonneg_left _ hC.le
    simpa only [integral_slack J b z C₁ hv, integral_norm_mask_sq_mul_slack J b z C₁ K h ω hv]
      using integral_norm_mul_slack_le J b z C₁ K h ω hv
  have hvg : ∀ᵐ x ∂cauchy, ‖(v x : ℂ) * g x‖ ≤ v x := by
    filter_upwards [hv, hg] with x hxv hxg
    change 0 ≤ v x at hxv
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hxv]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hxg hxv
  have hm₂I : Integrable m₂ cauchy := by
    apply Integrable.of_bound hm₂.aestronglyMeasurable 1
    filter_upwards [hvg, hd] with x hxvg hxd
    rw [hxd]
    calc
      _ ≤ ‖m x ^ 2‖ + ‖(v x : ℂ) * g x‖ := norm_add_le _ _
      _ ≤ ‖m x‖ ^ 2 + v x := by rw [norm_pow]; exact add_le_add_right hxvg _
      _ = 1 := by dsimp only [v, slack, m]; ring
  have hiH {f : ℝ → ℂ} (hf : Integrable f cauchy) :
      Integrable (fun x ↦ H x * f x) cauchy :=
    integrable_finsetSum K (fun k _ ↦ (integrable_phase_mul hf (ω k)).const_mul (h k : ℂ)) |>.congr
      (ae_of_all _ fun x ↦ by simp only [H, mask, Finset.sum_mul, mul_assoc])
  have hdiff : (∫ x, H x * m₂ x ∂cauchy) - (∫ x, H x * m x ^ 2 ∂cauchy) =
      ∫ x, H x * (m₂ x - m x ^ 2) ∂cauchy := by
    simpa only [mul_sub] using (integral_sub (hiH hm₂I) (hiH hmI)).symm
  have hHv : Integrable (fun x ↦ ‖H x‖ * v x) cauchy := by
    apply Integrable.of_bound ((continuous_mask K h ω).norm.mul
      (continuous_slack J b z C₁)).aestronglyMeasurable (∑ k ∈ K, |h k|)
    filter_upwards [hv] with x hxv
    change 0 ≤ v x at hxv
    change ‖‖H x‖ * v x‖ ≤ ∑ k ∈ K, |h k|
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (norm_nonneg _) hxv)]
    exact (mul_le_of_le_one_right (norm_nonneg _) (slack_le_one J b z C₁ x)).trans (norm_mask_le K h ω x)
  rw [← hc, ← mul_sub, abs_mul, abs_of_pos hC]
  apply mul_le_mul_of_nonneg_left _ hC.le
  rw [← Complex.sub_re, hdiff]
  calc
    _ ≤ ‖∫ x, H x * (m₂ x - m x ^ 2) ∂cauchy‖ := Complex.abs_re_le_norm _
    _ ≤ ∫ x, ‖H x * (m₂ x - m x ^ 2)‖ ∂cauchy := norm_integral_le_integral_norm _
    _ ≤ ∫ x, ‖H x‖ * v x ∂cauchy := by
      apply integral_mono_of_nonneg (ae_of_all _ fun _ ↦ norm_nonneg _) hHv
      filter_upwards [hd, hvg] with x hxd hxvg
      rw [hxd, add_sub_cancel_left, norm_mul]
      exact mul_le_mul_of_nonneg_left hxvg (norm_nonneg _)

end StepProfileDiskRadius
