module

public import Lemmas.MeasurableSecondMomentLaw
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Probability.Distributions.Cauchy
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Exact completion of the unfolded three-site second replies

Source: `3042a1a:.godel/bob/unfolded-deletion-33.md:24–35`.
Consumer: `c6f94db:.godel/bob/priced-deletion-33.md:23–29`.
Owning check session: `01a20d85-3fca-796b-bf11-8791e07c4ba8`.

Scope: for a measurable first field and a bounded finite real Laurent multiplier,
the exact convolution equations give one measurable conditional four-node law
with all the specified integrated real second replies zero. The general result
uses any finite measure on the real frequency line and any finite set of integer
sites. The unfolded specialization uses the source's normalized measure, spacing,
and three sites; the degree-192 input takes `K = Finset.Icc (-192) 192`.
This is the completion step, not a certificate for the coefficients or a refit.
-/

open MeasureTheory
open scoped BigOperators

namespace Masullo.ThreeSiteMomentCompletion

/-- The positive phase in the reply at angular frequency `s`. -/
@[expose] public noncomputable def phase (s x : ℝ) : ℂ :=
  Complex.exp (((s * x : ℝ) : ℂ) * Complex.I)

/-- The multiplier `exp(-i s₀ x) ∑ₖ vₖ exp(-i k h x)`, with signed Laurent indices. -/
@[expose] public noncomputable def laurentMultiplier (K : Finset ℤ) (v : ℤ → ℝ)
    (s₀ h x : ℝ) : ℂ :=
  phase (-s₀) x * ∑ k ∈ K, (v k : ℂ) * phase (-((k : ℝ) * h)) x

private noncomputable def radius (m : ℝ → ℂ) (x : ℝ) : ℝ := 1 - ‖m x‖ ^ 2

/-- The real disk-radius reply `R_d` at difference index `d`. -/
@[expose] public noncomputable def radiusReply (μ : Measure ℝ) (m : ℝ → ℂ)
    (h : ℝ) (d : ℤ) : ℝ :=
  ∫ x, Real.cos ((d : ℝ) * h * x) * (1 - ‖m x‖ ^ 2) ∂μ

/-- The real disk-center reply `T_j` at the site `s₀ + j h`. -/
@[expose] public noncomputable def centerReply (μ : Measure ℝ) (m : ℝ → ℂ)
    (s₀ h : ℝ) (j : ℤ) : ℝ :=
  (∫ x, phase (s₀ + (j : ℝ) * h) x * m x ^ 2 ∂μ).re

private theorem measurable_phase (s : ℝ) : Measurable (phase s) := by
  unfold phase
  fun_prop

private theorem norm_phase (s x : ℝ) : ‖phase s x‖ = 1 := by
  simp [phase, Complex.norm_exp_mul_I]

private theorem phase_mul_phase (a b x : ℝ) : phase a x * phase b x = phase (a + b) x := by
  simp only [phase, ← Complex.exp_add, add_mul, Complex.ofReal_add]

private theorem measurable_laurentMultiplier (K : Finset ℤ) (v : ℤ → ℝ) (s₀ h : ℝ) :
    Measurable (laurentMultiplier K v s₀ h) :=
  (measurable_phase _).mul (Finset.measurable_sum K fun k _ ↦
    measurable_const.mul (measurable_phase (-((k : ℝ) * h))))

private theorem measurable_radius {m : ℝ → ℂ} (hm : Measurable m) : Measurable (radius m) :=
  measurable_const.sub (hm.norm.pow_const 2)

private theorem sq_norm_le_one (z : ℂ) (hz : ‖z‖ ≤ 1) : ‖z‖ ^ 2 ≤ 1 := by
  simpa only [one_pow] using (sq_le_sq₀ (norm_nonneg z) zero_le_one).2 hz

private theorem radius_nonneg {m : ℝ → ℂ} {x : ℝ} (hm : ‖m x‖ ≤ 1) :
    0 ≤ radius m x := sub_nonneg.mpr (sq_norm_le_one _ hm)

private theorem radius_le_one (m : ℝ → ℂ) (x : ℝ) : radius m x ≤ 1 :=
  sub_le_self _ (sq_nonneg _)

private theorem integrable_center {μ : Measure ℝ} [IsFiniteMeasure μ]
    {m : ℝ → ℂ} (hm : Measurable m) (hm₁ : ∀ x, ‖m x‖ ≤ 1) (s : ℝ) :
    Integrable (fun x ↦ phase s x * m x ^ 2) μ := by
  refine Integrable.of_bound ((measurable_phase s).mul (hm.pow_const 2)).aestronglyMeasurable 1
    (ae_of_all _ fun x ↦ ?_)
  rw [norm_mul, norm_phase, one_mul, norm_pow]
  exact sq_norm_le_one _ (hm₁ x)

private theorem integrable_correction {μ : Measure ℝ} [IsFiniteMeasure μ]
    {m : ℝ → ℂ} (hm : Measurable m) (hm₁ : ∀ x, ‖m x‖ ≤ 1)
    {g : ℝ → ℂ} (hg : Measurable g) (hg₁ : ∀ x, ‖g x‖ ≤ 1) (s : ℝ) :
    Integrable (fun x ↦ phase s x * ((radius m x : ℂ) * g x)) μ := by
  have hr := Complex.measurable_ofReal.comp (measurable_radius hm)
  refine Integrable.of_bound ((measurable_phase s).mul (hr.mul hg)).aestronglyMeasurable 1
    (ae_of_all _ fun x ↦ ?_)
  rw [norm_mul, norm_phase, one_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (radius_nonneg (hm₁ x))]
  exact (mul_le_of_le_one_left (norm_nonneg _) (radius_le_one m x)).trans (hg₁ x)

private theorem integrable_radius_term {μ : Measure ℝ} [IsFiniteMeasure μ]
    {m : ℝ → ℂ} (hm : Measurable m) (hm₁ : ∀ x, ‖m x‖ ≤ 1) (a : ℝ) :
    Integrable (fun x ↦ Real.cos (a * x) * radius m x) μ := by
  have hc : Measurable (fun x : ℝ ↦ Real.cos (a * x)) := by fun_prop
  refine Integrable.of_bound (hc.mul (measurable_radius hm)).aestronglyMeasurable 1
    (ae_of_all _ fun x ↦ ?_)
  rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (radius_nonneg (hm₁ x))]
  exact (mul_le_of_le_one_left (radius_nonneg (hm₁ x)) (Real.abs_cos_le_one _)).trans
    (radius_le_one m x)

-- The carrier cancels before taking the real part; the residual signed index is `j - k`.
private theorem correction_re (K : Finset ℤ) (v : ℤ → ℝ) (m : ℝ → ℂ)
    (s₀ h : ℝ) (j : ℤ) (x : ℝ) :
    (phase (s₀ + (j : ℝ) * h) x * ((radius m x : ℂ) * laurentMultiplier K v s₀ h x)).re =
      ∑ k ∈ K, v k * (Real.cos (((j - k : ℤ) : ℝ) * h * x) * radius m x) := by
  simp only [laurentMultiplier, Finset.mul_sum, Complex.re_sum]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  have hphase : phase (s₀ + (j : ℝ) * h) x * phase (-s₀) x * phase (-((k : ℝ) * h)) x =
      phase (((j - k : ℤ) : ℝ) * h) x := by
    rw [phase_mul_phase, phase_mul_phase]
    congr 1
    push_cast
    ring
  have hmul :
      phase (s₀ + (j : ℝ) * h) x * ((radius m x : ℂ) *
        (phase (-s₀) x * ((v k : ℂ) * phase (-((k : ℝ) * h)) x))) =
      ((v k : ℂ) * (radius m x : ℂ)) *
        (phase (s₀ + (j : ℝ) * h) x * phase (-s₀) x * phase (-((k : ℝ) * h)) x) := by ring
  rw [hmul, hphase, ← Complex.ofReal_mul, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero, phase, Complex.exp_ofReal_mul_I_re]
  ring

private theorem correction_reply {μ : Measure ℝ} [IsFiniteMeasure μ]
    {m : ℝ → ℂ} (hm : Measurable m) (hm₁ : ∀ x, ‖m x‖ ≤ 1)
    (K : Finset ℤ) (v : ℤ → ℝ) (s₀ h : ℝ) (j : ℤ)
    (hc : Integrable (fun x ↦ phase (s₀ + (j : ℝ) * h) x *
      ((radius m x : ℂ) * laurentMultiplier K v s₀ h x)) μ) :
    (∫ x, phase (s₀ + (j : ℝ) * h) x *
      ((radius m x : ℂ) * laurentMultiplier K v s₀ h x) ∂μ).re =
      ∑ k ∈ K, v k * radiusReply μ m h (j - k) := by
  calc
    _ = ∫ x, (phase (s₀ + (j : ℝ) * h) x *
        ((radius m x : ℂ) * laurentMultiplier K v s₀ h x)).re ∂μ := (integral_re hc).symm
    _ = _ := by
      simp_rw [correction_re]
      rw [integral_finsetSum K (fun k _ ↦ (integrable_radius_term hm hm₁
        (((j - k : ℤ) : ℝ) * h)).const_mul (v k))]
      simp_rw [integral_const_mul, radiusReply, radius]

/-- The convolution equations complete the first field by a single measurable law,
whose weighted second-moment integrands are integrable and give zero real reply
at every specified site. -/
public theorem exists_measurable_four_node_law_of_convolution
    (μ : Measure ℝ) [IsFiniteMeasure μ] (J K : Finset ℤ) (v : ℤ → ℝ) (s₀ h : ℝ)
    {m : ℝ → ℂ} (hm : Measurable m) (hm₁ : ∀ x, ‖m x‖ ≤ 1)
    (hg₁ : ∀ x, ‖laurentMultiplier K v s₀ h x‖ ≤ 1)
    (hconv : ∀ j ∈ J, ∑ k ∈ K, v k * radiusReply μ m h (j - k) = centerReply μ m s₀ h j) :
    ∃ (p : Fin 4 → ℝ → ℝ) (z : Fin 4 → ℝ → ℂ),
      (∀ i, Measurable (p i)) ∧ (∀ i, Measurable (z i)) ∧
      (∀ x, (∀ i, 0 ≤ p i x) ∧ (∀ i, ‖z i x‖ = 1) ∧ (∑ i, p i x) = 1 ∧
        (∑ i, (p i x : ℂ) * z i x) = m x) ∧
      ∀ j ∈ J,
        Integrable (fun x ↦ phase (s₀ + (j : ℝ) * h) x * ∑ i, (p i x : ℂ) * z i x ^ 2) μ ∧
        (∫ x, phase (s₀ + (j : ℝ) * h) x * ∑ i, (p i x : ℂ) * z i x ^ 2 ∂μ).re = 0 := by
  let g := laurentMultiplier K v s₀ h
  let n (x : ℝ) := m x ^ 2 - (radius m x : ℂ) * g x
  have hg : Measurable g := measurable_laurentMultiplier K v s₀ h
  have hn : Measurable n := (hm.pow_const 2).sub
    ((Complex.measurable_ofReal.comp (measurable_radius hm)).mul hg)
  have hdisk (x : ℝ) : ‖m x‖ ^ 2 + ‖n x - m x ^ 2‖ ≤ 1 := by
    have heq : n x - m x ^ 2 = -((radius m x : ℂ) * g x) := by dsimp [n]; ring
    rw [heq, norm_neg, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (radius_nonneg (hm₁ x))]
    calc
      _ ≤ ‖m x‖ ^ 2 + radius m x * 1 :=
        add_le_add_right (mul_le_mul_of_nonneg_left (hg₁ x) (radius_nonneg (hm₁ x))) _
      _ = 1 := by simp [radius]
  obtain ⟨p, z, hp, hz, hlaw⟩ :=
    MeasurableSecondMomentLaw.exists_measurable_four_node_law hm hn hdisk
  refine ⟨p, z, hp, hz, fun x ↦ ⟨(hlaw x).1, (hlaw x).2.1, (hlaw x).2.2.1,
    (hlaw x).2.2.2.1⟩, fun j hj ↦ ?_⟩
  have heq (x : ℝ) :
      phase (s₀ + (j : ℝ) * h) x * (∑ i, (p i x : ℂ) * z i x ^ 2) =
        phase (s₀ + (j : ℝ) * h) x * m x ^ 2 -
          phase (s₀ + (j : ℝ) * h) x * ((radius m x : ℂ) * g x) := by
    rw [(hlaw x).2.2.2.2]
    exact mul_sub _ _ _
  have hcenter := integrable_center (μ := μ) hm hm₁ (s₀ + (j : ℝ) * h)
  have hcorr := integrable_correction (μ := μ) hm hm₁ hg hg₁ (s₀ + (j : ℝ) * h)
  simp_rw [heq]
  refine ⟨hcenter.sub hcorr, ?_⟩
  rw [integral_sub hcenter hcorr, Complex.sub_re, correction_reply hm hm₁ K v s₀ h j hcorr]
  exact sub_eq_zero.mpr (hconv j hj).symm

/-- The source measure `dx / (2π |1/2 + ix|²)`, with no change of scale. -/
@[expose] public noncomputable def unfoldedMeasure : Measure ℝ :=
  volume.withDensity (fun x : ℝ ↦ ENNReal.ofReal (1 / (2 * Real.pi *
    ‖(1 / 2 : ℂ) + (x : ℂ) * Complex.I‖ ^ 2)))

private theorem unfoldedMeasure_eq_cauchy :
    unfoldedMeasure = ProbabilityTheory.cauchyMeasure 0 (1 / 2) := by
  rw [unfoldedMeasure, ProbabilityTheory.cauchyMeasure_of_scale_ne_zero 0 (by norm_num)]
  congr 1
  funext x
  rw [ProbabilityTheory.cauchyPDF_def, ProbabilityTheory.cauchyPDFReal_def]
  have hnorm : ‖(1 / 2 : ℂ) + (x : ℂ) * Complex.I‖ ^ 2 = (1 / 2 : ℝ) ^ 2 + x ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    norm_num [Complex.mul_re, Complex.mul_im, pow_two]
  rw [hnorm]
  congr 1
  push_cast
  norm_num [div_eq_mul_inv, mul_inv]
  ring

/-- Unfolded delete-33 specialization: `h = 13/25`, `s₀ = 6/25`, and `j = -1, 0, 1`,
against the source's normalized Cauchy density. The same law works at all three sites. -/
public theorem exists_unfolded_three_site_law (K : Finset ℤ) (v : ℤ → ℝ)
    {m : ℝ → ℂ} (hm : Measurable m) (hm₁ : ∀ x, ‖m x‖ ≤ 1)
    (hg₁ : ∀ x, ‖laurentMultiplier K v (6 / 25) (13 / 25) x‖ ≤ 1)
    (hconv : ∀ j ∈ Finset.Icc (-1 : ℤ) 1,
      ∑ k ∈ K, v k * radiusReply unfoldedMeasure m (13 / 25) (j - k) =
        centerReply unfoldedMeasure m (6 / 25) (13 / 25) j) :
    ∃ (p : Fin 4 → ℝ → ℝ) (z : Fin 4 → ℝ → ℂ),
      (∀ i, Measurable (p i)) ∧ (∀ i, Measurable (z i)) ∧
      (∀ x, (∀ i, 0 ≤ p i x) ∧ (∀ i, ‖z i x‖ = 1) ∧ (∑ i, p i x) = 1 ∧
        (∑ i, (p i x : ℂ) * z i x) = m x) ∧
      ∀ j ∈ Finset.Icc (-1 : ℤ) 1,
        Integrable (fun x ↦ phase (6 / 25 + (j : ℝ) * (13 / 25)) x *
          ∑ i, (p i x : ℂ) * z i x ^ 2) unfoldedMeasure ∧
        (∫ x, phase (6 / 25 + (j : ℝ) * (13 / 25)) x *
          ∑ i, (p i x : ℂ) * z i x ^ 2 ∂unfoldedMeasure).re = 0 := by
  let : IsFiniteMeasure unfoldedMeasure := by rw [unfoldedMeasure_eq_cauchy]; infer_instance
  exact exists_measurable_four_node_law_of_convolution unfoldedMeasure _ K v
    (6 / 25) (13 / 25) hm hm₁ hg₁ hconv

end Masullo.ThreeSiteMomentCompletion
