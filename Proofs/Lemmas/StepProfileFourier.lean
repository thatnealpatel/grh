module

public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Angular Fourier transform of a finite step profile

The jump numerator used in Bob's witness certificates is recorded at
`059232cff7d3894d8545eb11ffccf9cd2fec1646` in `.godel/bob/translated-step-witness.md`
(“A fixed witness and its certificate”), `.godel/bob/two-height-translated-radial.md`
(“Witness through nine for every translate”), and `.godel/bob/translated-step-11-1.md`
(“The common law and its certificate”). The centered numerator in the first and third
references acquires a factor `exp (2 * I * ξ)` to recover the uncentered numerator here.
The formula and its tail bound apply to the real profiles of those certificates;
no numerical enclosure or prime-side estimate is proved here.
-/

open MeasureTheory Set

namespace StepProfile

/-- A finite real step profile, including each jump at its location. It vanishes before
all jump locations and is constant after them. -/
@[expose] public noncomputable def profile {ι : Type*} (s : Finset ι)
    (z ΔY : ι → ℝ) (x : ℝ) : ℝ :=
  ∑ j ∈ s, if z j ≤ x then ΔY j else 0

private noncomputable def rate (ξ : ℝ) : ℂ := 1 / 2 + (ξ : ℂ) * Complex.I

private theorem rate_re (ξ : ℝ) : (rate ξ).re = 1 / 2 := by
  norm_num [rate, Complex.div_re, Complex.mul_re]

private theorem neg_rate_re_lt (ξ : ℝ) : (-(rate ξ)).re < 0 := by
  rw [Complex.neg_re, rate_re]
  norm_num

private theorem weight_mul_phase (ξ x : ℝ) :
    (Real.exp (-x / 2) : ℂ) * Complex.exp (-((ξ : ℂ) * Complex.I) * (x : ℂ)) =
      Complex.exp (-(rate ξ) * (x : ℂ)) := by
  rw [Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  push_cast
  unfold rate
  ring

private noncomputable def jumpTerm (ξ a d x : ℝ) : ℂ :=
  (d : ℂ) * indicator (Ici a) (fun y : ℝ ↦ Complex.exp (-(rate ξ) * (y : ℂ))) x

private theorem integrable_jumpTerm (ξ a d : ℝ) : Integrable (jumpTerm ξ a d) := by
  have h : Integrable (indicator (Ici a)
      (fun x : ℝ ↦ Complex.exp (-(rate ξ) * (x : ℂ)))) := by
    -- The jump uses the closed ray; its endpoint has Lebesgue measure zero.
    rw [integrable_indicator_iff measurableSet_Ici, IntegrableOn,
      ← Measure.restrict_congr_set (Ioi_ae_eq_Ici (μ := volume) (a := a))]
    exact integrableOn_exp_mul_complex_Ioi (neg_rate_re_lt ξ) a
  exact h.const_mul (d : ℂ)

private theorem integral_jumpTerm (ξ a d : ℝ) :
    (∫ x : ℝ, jumpTerm ξ a d x) =
      (d : ℂ) * (Complex.exp (-(rate ξ) * (a : ℂ)) / rate ξ) := by
  unfold jumpTerm
  rw [integral_const_mul, integral_indicator measurableSet_Ici,
    integral_Ici_eq_integral_Ioi, integral_exp_mul_complex_Ioi (neg_rate_re_lt ξ),
    neg_div_neg_eq]

private theorem weightedProfile_eq_sum {ι : Type*} (s : Finset ι) (z ΔY : ι → ℝ) (ξ : ℝ) :
    (fun x : ℝ ↦ (Real.exp (-x / 2) : ℂ) * (profile s z ΔY x : ℂ) *
      Complex.exp (-((ξ : ℂ) * Complex.I) * (x : ℂ))) =
      fun x : ℝ ↦ ∑ j ∈ s, jumpTerm ξ (z j) (ΔY j) x := by
  funext x
  rw [profile, Complex.ofReal_sum, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  simp only [jumpTerm, indicator_apply, mem_Ici]
  by_cases h : z j ≤ x
  · rw [ite_eq_left h, ite_eq_left h, mul_comm (Real.exp (-x / 2) : ℂ), mul_assoc,
      weight_mul_phase]
  · simp [h]

/-- The weighted step profile with the negative angular phase is Lebesgue integrable
on the whole real line at every frequency. -/
public theorem integrable_angularFourier_integrand {ι : Type*} (s : Finset ι)
    (z ΔY : ι → ℝ) (ξ : ℝ) :
    Integrable (fun x : ℝ ↦ (Real.exp (-x / 2) : ℂ) * (profile s z ΔY x : ℂ) *
      Complex.exp (-((ξ : ℂ) * Complex.I) * (x : ℂ))) := by
  rw [weightedProfile_eq_sum]
  exact integrable_finsetSum s fun j _ ↦ integrable_jumpTerm ξ (z j) (ΔY j)

/-- The whole-line Fourier integral in the negative angular-frequency convention,
with no normalization factor. The formula includes zero frequency and the empty profile. -/
public theorem integral_angularFourier {ι : Type*} (s : Finset ι)
    (z ΔY : ι → ℝ) (ξ : ℝ) :
    (∫ x : ℝ, (Real.exp (-x / 2) : ℂ) * (profile s z ΔY x : ℂ) *
      Complex.exp (-((ξ : ℂ) * Complex.I) * (x : ℂ))) =
      (∑ j ∈ s, (ΔY j : ℂ) * Complex.exp (-(1 / 2 + (ξ : ℂ) * Complex.I) * (z j : ℂ))) /
        (1 / 2 + (ξ : ℂ) * Complex.I) := by
  rw [weightedProfile_eq_sum,
    integral_finsetSum s (fun j _ ↦ integrable_jumpTerm ξ (z j) (ΔY j)), Finset.sum_div]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  simpa only [rate, mul_div_assoc] using integral_jumpTerm ξ (z j) (ΔY j)

private theorem rate_im (ξ : ℝ) : (rate ξ).im = ξ := by
  norm_num [rate, Complex.div_im, Complex.mul_im]

private theorem norm_exp_neg_rate_mul (ξ x : ℝ) :
    ‖Complex.exp (-(rate ξ) * (x : ℂ))‖ = Real.exp (-x / 2) := by
  rw [Complex.norm_exp]
  congr 1
  simp only [Complex.mul_re, Complex.neg_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
    sub_zero, rate_re]
  ring

/-- The tail estimate used by the certificates: the sum of the absolute half-weighted
jumps divided by the magnitude of the nonzero angular frequency. -/
public theorem norm_integral_angularFourier_le {ι : Type*} (s : Finset ι)
    (z ΔY : ι → ℝ) {ξ : ℝ} (hξ : ξ ≠ 0) :
    ‖∫ x : ℝ, (Real.exp (-x / 2) : ℂ) * (profile s z ΔY x : ℂ) *
      Complex.exp (-((ξ : ℂ) * Complex.I) * (x : ℂ))‖ ≤
      (∑ j ∈ s, |ΔY j| * Real.exp (-z j / 2)) / |ξ| := by
  rw [integral_angularFourier]
  change ‖(∑ j ∈ s, (ΔY j : ℂ) * Complex.exp (-(rate ξ) * (z j : ℂ))) / rate ξ‖ ≤ _
  rw [norm_div]
  have hnum : ‖∑ j ∈ s, (ΔY j : ℂ) * Complex.exp (-(rate ξ) * (z j : ℂ))‖ ≤
      ∑ j ∈ s, |ΔY j| * Real.exp (-z j / 2) := by
    simpa only [norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_exp_neg_rate_mul]
      using norm_sum_le s (fun j ↦ (ΔY j : ℂ) * Complex.exp (-(rate ξ) * (z j : ℂ)))
  have hden : |ξ| ≤ ‖rate ξ‖ := by
    simpa only [rate_im] using Complex.abs_im_le_norm (rate ξ)
  have hpos : 0 < |ξ| := abs_pos.mpr hξ
  exact (div_le_div_of_nonneg_right hnum (norm_nonneg _)).trans
    (div_le_div_of_nonneg_left ((norm_nonneg _).trans hnum) hpos hden)

end StepProfile
