module

public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! # Fourier transform of a mixed real/complex Gaussian

This computes the trace-pairing Fourier integral for product Lebesgue measure and
provides the continuity, integrability, and rapid decay bounds for lattice Poisson
summation. The complex coordinate measure is `dx dy`.
-/

open MeasureTheory
open scoped BigOperators ComplexConjugate FourierTransform RealInnerProductSpace

namespace Masullo

section Mixed

variable {R C : Type*} [Fintype R] [Fintype C]

/-- The mixed trace pairing. The frequency in the usual real inner product on a complex
coordinate is `2 * conj w`: its inner product with `z` is `2 * (z * w).re`. -/
@[expose] public noncomputable def mixedTracePairing
    (x w : (R → ℝ) × (C → ℂ)) : ℝ :=
  (∑ i, x.1 i * w.1 i) + ∑ j, 2 * (x.2 j * w.2 j).re

/-- Product Gaussian with exponent `-π a x²` at the real places and
`-2π b |z|²` at the complex places. -/
@[expose] public noncomputable def mixedGaussian (a : R → ℝ) (b : C → ℝ)
    (x : (R → ℝ) × (C → ℂ)) : ℂ :=
  (∏ i, Complex.exp (↑(-Real.pi * a i * (x.1 i) ^ 2 : ℝ) : ℂ)) *
    ∏ j, Complex.exp (↑(-Real.pi * (2 * b j) * ‖x.2 j‖ ^ 2 : ℝ) : ℂ)

/-- The Fourier kernel at a real pairing value, with negative sign. -/
@[expose] public noncomputable def gaussianPhase (u : ℝ) : ℂ :=
  Complex.exp (↑(-2 * Real.pi * u : ℝ) * Complex.I)

private theorem gaussianPhase_add (s t : ℝ) :
    gaussianPhase (s + t) = gaussianPhase s * gaussianPhase t := by
  rw [gaussianPhase, gaussianPhase, gaussianPhase, ← Complex.exp_add, mul_add,
    Complex.ofReal_add, add_mul]

open Finset in
private theorem gaussianPhase_sum {ι : Type*} (s : Finset ι) (t : ι → ℝ) :
    gaussianPhase (∑ i ∈ s, t i) = ∏ i ∈ s, gaussianPhase (t i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [gaussianPhase]
  | insert i s hi hs => rw [sum_insert hi, prod_insert hi, gaussianPhase_add, hs]

private theorem realGaussianIntegral (a u : ℝ) (ha : 0 < a) :
    (∫ x : ℝ, gaussianPhase (x * u) * Complex.exp (↑(-Real.pi * a * x ^ 2 : ℝ) : ℂ)) =
      (↑(1 / Real.sqrt a) : ℂ) * Complex.exp (↑(-Real.pi / a * u ^ 2 : ℝ) : ℂ) := by
  have h := congrFun (fourier_gaussian_pi (b := (a : ℂ)) (by simpa using ha)) u
  rw [Real.fourier_real_eq_integral_exp_smul] at h
  convert h using 2
  · funext x
    simp only [gaussianPhase, smul_eq_mul]
    push_cast
    ring_nf
  · rw [Real.sqrt_eq_rpow, Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_cpow ha.le]
    norm_num
  · push_cast
    ring_nf

private theorem traceInnerComplex (z w : ℂ) :
    ⟪((2 : ℝ) • conj w : ℂ), z⟫ = 2 * (z * w).re := by
  simp [Complex.mul_re]
  ring

private theorem complexGaussianIntegral (b : ℝ) (w : ℂ) (hb : 0 < b) :
    (∫ z : ℂ, gaussianPhase (2 * (z * w).re) *
        Complex.exp (↑(-Real.pi * (2 * b) * ‖z‖ ^ 2 : ℝ) : ℂ)) =
      (↑(1 / (2 * b)) : ℂ) * Complex.exp (↑(-Real.pi * (2 / b) * ‖w‖ ^ 2 : ℝ) : ℂ) := by
  let c : ℝ := Real.pi * (2 * b)
  have hc : 0 < c := by dsimp [c]; positivity
  have h := fourier_gaussian_innerProductSpace (V := ℂ) (b := (c : ℂ))
    (by simpa using hc) ((2 : ℝ) • (conj w) : ℂ)
  rw [Real.fourier_eq'] at h
  convert h using 2
  · funext z
    rw [← real_inner_comm z, traceInnerComplex]
    simp [gaussianPhase, c, smul_eq_mul, mul_assoc]
  · rw [Complex.finrank_real_complex]
    norm_num
    dsimp [c]
    push_cast
    field_simp [Real.pi_ne_zero, hb.ne']
  · congr 1
    rw [norm_smul, Complex.norm_conj, Real.norm_eq_abs, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    dsimp [c]
    push_cast
    field_simp [Real.pi_ne_zero, hb.ne']

private theorem integrable_gaussianPhase {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    {c : ℝ} (hc : 0 < c) (w : V) :
    Integrable (fun x : V ↦ gaussianPhase ⟪w, x⟫ * Complex.exp (↑(-c * ‖x‖ ^ 2 : ℝ) : ℂ)) := by
  convert GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (V := V) (b := (c : ℂ))
    (by simpa using hc) (-2 * (Real.pi : ℂ) * Complex.I) w using 1
  funext x
  rw [gaussianPhase, ← Complex.exp_add]
  push_cast
  ring_nf

/-- The mixed Gaussian Fourier integral with the negative trace phase. Each complex
Lebesgue factor is `dx dy` (Mathlib's `Complex.volume_preserving_equiv_real_prod`),
not `2 dx dy`. Thus its prefactor is `(2 * b j)⁻¹`, not `(b j)⁻¹`. -/
public theorem mixedGaussian_fourier (a : R → ℝ) (b : C → ℝ)
    (ha : ∀ i, 0 < a i) (hb : ∀ j, 0 < b j) (w : (R → ℝ) × (C → ℂ)) :
    Integrable (fun x ↦ gaussianPhase (mixedTracePairing x w) * mixedGaussian a b x) ∧
    (∫ x, gaussianPhase (mixedTracePairing x w) * mixedGaussian a b x) =
      (∏ i, (↑(1 / Real.sqrt (a i)) : ℂ)) * (∏ j, (↑(1 / (2 * b j)) : ℂ)) *
        mixedGaussian (fun i ↦ (a i)⁻¹) (fun j ↦ (b j)⁻¹) w := by
  let f (i : R) (x : ℝ) := gaussianPhase (x * w.1 i) *
    Complex.exp (↑(-Real.pi * a i * x ^ 2 : ℝ) : ℂ)
  let g (j : C) (z : ℂ) := gaussianPhase (2 * (z * w.2 j).re) *
    Complex.exp (↑(-Real.pi * (2 * b j) * ‖z‖ ^ 2 : ℝ) : ℂ)
  have hf (i : R) : Integrable (f i) := by
    simpa only [f, neg_mul, Real.norm_eq_abs, sq_abs, Real.inner_apply, mul_comm (w.1 i)] using
      integrable_gaussianPhase (mul_pos Real.pi_pos (ha i)) (w.1 i)
  have hg (j : C) : Integrable (g j) := by
    simpa only [g, traceInnerComplex, neg_mul] using
      integrable_gaussianPhase (mul_pos Real.pi_pos (mul_pos zero_lt_two (hb j)))
        ((2 : ℝ) • conj (w.2 j) : ℂ)
  have hfactor : (fun x ↦ gaussianPhase (mixedTracePairing x w) * mixedGaussian a b x) =
      fun x ↦ (∏ i, f i (x.1 i)) * (∏ j, g j (x.2 j)) := by
    funext x
    simp only [mixedTracePairing, mixedGaussian, gaussianPhase_add, gaussianPhase_sum, f, g,
      Finset.prod_mul_distrib]
    ac_rfl
  rw [hfactor]
  refine ⟨(Integrable.fintype_prod hf).mul_prod (Integrable.fintype_prod hg), ?_⟩
  rw [show (∫ x : (R → ℝ) × (C → ℂ), (∏ i, f i (x.1 i)) * ∏ j, g j (x.2 j)) =
    (∫ x : R → ℝ, ∏ i, f i (x i)) * (∫ z : C → ℂ, ∏ j, g j (z j)) from
      integral_prod_mul (fun x : R → ℝ ↦ ∏ i, f i (x i)) (fun z : C → ℂ ↦ ∏ j, g j (z j)),
    integral_fintype_prod_volume_eq_prod (f := f),
    integral_fintype_prod_volume_eq_prod (f := g)]
  simp only [f, g, realGaussianIntegral _ _ (ha _), complexGaussianIntegral _ _ (hb _),
    Finset.prod_mul_distrib, mixedGaussian, div_eq_mul_inv]
  ac_rfl

/-- The mixed Gaussian is continuous in the product topology. -/
public theorem continuous_mixedGaussian (a : R → ℝ) (b : C → ℝ) :
    Continuous (mixedGaussian a b) := by
  unfold mixedGaussian
  fun_prop

/-- An isotropic Gaussian majorant for the mixed Gaussian, in the product sup norm. -/
public theorem norm_mixedGaussian_le_exp (a : R → ℝ) (b : C → ℝ)
    {c : ℝ} (hc : 0 < c) (ha : ∀ i, c ≤ Real.pi * a i)
    (hb : ∀ j, c ≤ Real.pi * (2 * b j)) (x : (R → ℝ) × (C → ℂ)) :
    ‖mixedGaussian a b x‖ ≤ Real.exp (-c * ‖x‖ ^ 2) := by
  let A := ∑ i, Real.pi * a i * (x.1 i) ^ 2
  let B := ∑ j, Real.pi * (2 * b j) * ‖x.2 j‖ ^ 2
  have hA : 0 ≤ A := Finset.sum_nonneg fun i _ ↦
    mul_nonneg (hc.le.trans (ha i)) (sq_nonneg _)
  have hB : 0 ≤ B := Finset.sum_nonneg fun j _ ↦
    mul_nonneg (hc.le.trans (hb j)) (sq_nonneg _)
  have hreal (i : R) : c * ‖x.1 i‖ ^ 2 ≤ A + B := calc
    c * ‖x.1 i‖ ^ 2 = c * (x.1 i) ^ 2 := by rw [Real.norm_eq_abs, sq_abs]
    _ ≤ Real.pi * a i * (x.1 i) ^ 2 := mul_le_mul_of_nonneg_right (ha i) (sq_nonneg _)
    _ ≤ A := Finset.single_le_sum (fun j _ ↦
      mul_nonneg (hc.le.trans (ha j)) (sq_nonneg _)) (Finset.mem_univ i)
    _ ≤ A + B := le_add_of_nonneg_right hB
  have hcomplex (j : C) : c * ‖x.2 j‖ ^ 2 ≤ A + B := calc
    c * ‖x.2 j‖ ^ 2 ≤ Real.pi * (2 * b j) * ‖x.2 j‖ ^ 2 :=
      mul_le_mul_of_nonneg_right (hb j) (sq_nonneg _)
    _ ≤ B := Finset.single_le_sum (fun i _ ↦
      mul_nonneg (hc.le.trans (hb i)) (sq_nonneg ‖x.2 i‖)) (Finset.mem_univ j)
    _ ≤ A + B := le_add_of_nonneg_left hA
  let r := Real.sqrt ((A + B) / c)
  have hr : r ^ 2 = (A + B) / c := Real.sq_sqrt (by positivity)
  have hcand (t : ℝ) (ht : 0 ≤ t) (h : c * t ^ 2 ≤ A + B) : t ≤ r := by
    apply le_of_not_gt
    intro hlt
    have hs : r ^ 2 < t ^ 2 := by
      exact pow_lt_pow_left₀ hlt (Real.sqrt_nonneg _) (by decide)
    rw [hr, div_lt_iff₀ hc] at hs
    linarith
  have hnorm : ‖x‖ ≤ r := by
    rw [Prod.norm_def, max_le_iff]
    exact ⟨(pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr
        (fun i ↦ hcand _ (norm_nonneg _) (hreal i)),
      (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr
        (fun j ↦ hcand _ (norm_nonneg _) (hcomplex j))⟩
  have hx : c * ‖x‖ ^ 2 ≤ A + B := by
    have hr' : ‖x‖ ^ 2 ≤ r ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hnorm 2
    rw [hr, le_div_iff₀ hc] at hr'
    simpa only [mul_comm] using hr'
  simp only [mixedGaussian, norm_mul, norm_prod, Complex.norm_exp_ofReal, ← Real.exp_sum,
    ← Real.exp_add, neg_mul]
  simp only [Finset.sum_neg_distrib]
  exact Real.exp_le_exp.mpr (by linarith only [hx] : -A + -B ≤ -(c * ‖x‖ ^ 2))

private theorem exists_pos_le_finite {ι : Type*} [Fintype ι] (f : ι → ℝ)
    (hf : ∀ i, 0 < f i) : ∃ c > 0, ∀ i, c ≤ f i := by
  classical
  let s := insert 1 (Finset.univ.image f)
  have hs : s.Nonempty := Finset.insert_nonempty _ _
  exact ⟨s.min' hs, by
    rcases Finset.mem_insert.mp (Finset.min'_mem s hs) with h | h
    · exact h.symm ▸ zero_lt_one
    · obtain ⟨i, _, hi⟩ := Finset.mem_image.mp h
      exact hi ▸ hf i,
    fun i ↦ Finset.min'_le _ _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _
      (Finset.mem_univ i)))⟩

/-- Positive coordinate scales give a global isotropic Gaussian majorant. -/
public theorem exists_norm_mixedGaussian_le_exp (a : R → ℝ) (b : C → ℝ)
    (ha : ∀ i, 0 < a i) (hb : ∀ j, 0 < b j) :
    ∃ c > 0, ∀ x, ‖mixedGaussian a b x‖ ≤ Real.exp (-c * ‖x‖ ^ 2) := by
  obtain ⟨u, hu, hua⟩ := exists_pos_le_finite (fun i ↦ Real.pi * a i)
    (fun i ↦ mul_pos Real.pi_pos (ha i))
  obtain ⟨v, hv, hvb⟩ := exists_pos_le_finite (fun j ↦ Real.pi * (2 * b j))
    (fun j ↦ mul_pos Real.pi_pos (mul_pos zero_lt_two (hb j)))
  exact ⟨min u v, lt_min hu hv, norm_mixedGaussian_le_exp a b (lt_min hu hv)
    (fun i ↦ (min_le_left _ _).trans (hua i)) (fun j ↦ (min_le_right _ _).trans (hvb j))⟩

private theorem pow_mul_gaussian_le {c t : ℝ} (hc : 0 < c) (ht : 0 ≤ t) (p : ℕ) :
    t ^ p * Real.exp (-c * t ^ 2) ≤ max 1 (p.factorial / c ^ p) := by
  by_cases h : t ≤ 1
  · have hpow : t ^ p ≤ 1 := pow_le_one₀ ht h
    have he : Real.exp (-c * t ^ 2) ≤ 1 :=
      Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hc.le) (sq_nonneg _))
    exact (mul_le_of_le_one_right (pow_nonneg ht _) he).trans (hpow.trans (le_max_left _ _))
  · have hpow : t ^ p ≤ (t ^ 2) ^ p := by
      apply pow_le_pow_left₀ ht
      nlinarith only [le_of_not_ge h, sq_nonneg (t - 1)]
    apply le_trans (mul_le_mul_of_nonneg_right hpow (Real.exp_nonneg _))
    apply le_trans _ (le_max_right _ _)
    have hexp := Real.pow_div_factorial_le_exp (x := c * t ^ 2) (by positivity) p
    rw [mul_pow, div_le_iff₀ (by positivity : (0 : ℝ) < p.factorial)] at hexp
    rw [neg_mul, Real.exp_neg, ← div_eq_mul_inv, div_le_div_iff₀ (by positivity) (by positivity)]
    simpa only [mul_comm (Real.exp _), mul_comm (c ^ p)] using hexp

/-- Every polynomial weight times the mixed Gaussian is bounded, including when either
set of coordinates is empty. The statement also applies to the reciprocal scales. -/
public theorem mixedGaussian_rapidDecay (a : R → ℝ) (b : C → ℝ)
    (ha : ∀ i, 0 < a i) (hb : ∀ j, 0 < b j) (p : ℕ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ x, ‖x‖ ^ p * ‖mixedGaussian a b x‖ ≤ A := by
  obtain ⟨c, hc, h⟩ := exists_norm_mixedGaussian_le_exp a b ha hb
  exact ⟨max 1 (p.factorial / c ^ p), by positivity, fun x ↦
    (mul_le_mul_of_nonneg_left (h x) (by positivity)).trans
      (pow_mul_gaussian_le hc (norm_nonneg _) p)⟩

/-- The mixed Gaussian is integrable for product Lebesgue measure. -/
public theorem integrable_mixedGaussian (a : R → ℝ) (b : C → ℝ)
    (ha : ∀ i, 0 < a i) (hb : ∀ j, 0 < b j) : Integrable (mixedGaussian a b) := by
  simpa [gaussianPhase, mixedTracePairing] using (mixedGaussian_fourier a b ha hb 0).1


/-- Rapid decay of the mixed Gaussian Fourier integral in the trace frequency. -/
public theorem mixedGaussian_fourier_rapidDecay (a : R → ℝ) (b : C → ℝ)
    (ha : ∀ i, 0 < a i) (hb : ∀ j, 0 < b j) (p : ℕ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ w,
      ‖w‖ ^ p * ‖∫ x, gaussianPhase (mixedTracePairing x w) * mixedGaussian a b x‖ ≤ A := by
  obtain ⟨A, hA, h⟩ := mixedGaussian_rapidDecay (fun i ↦ (a i)⁻¹) (fun j ↦ (b j)⁻¹)
    (fun i ↦ inv_pos.mpr (ha i)) (fun j ↦ inv_pos.mpr (hb j)) p
  let K : ℂ := (∏ i, (↑(1 / Real.sqrt (a i)) : ℂ)) * (∏ j, (↑(1 / (2 * b j)) : ℂ))
  refine ⟨‖K‖ * A, by positivity, fun w ↦ ?_⟩
  rw [(mixedGaussian_fourier a b ha hb w).2]
  change ‖w‖ ^ p * ‖K * mixedGaussian _ _ w‖ ≤ ‖K‖ * A
  rw [norm_mul, mul_left_comm]
  exact mul_le_mul_of_nonneg_left (h w) (norm_nonneg _)

end Mixed

/-- Rapid decay is preserved by precomposition with a continuous real-linear equivalence. -/
public theorem rapidDecay_comp_continuousLinearEquiv
    {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
    [NormedSpace ℝ F] [NormedAddCommGroup G] (e : E ≃L[ℝ] F) (f : F → G) (p : ℕ)
    (hf : ∃ A : ℝ, 0 ≤ A ∧ ∀ y, ‖y‖ ^ p * ‖f y‖ ≤ A) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ x, ‖x‖ ^ p * ‖f (e x)‖ ≤ A := by
  obtain ⟨A, hA, hf⟩ := hf
  let B := ‖(e.symm : F →L[ℝ] E)‖
  have hB : 0 ≤ B := norm_nonneg _
  refine ⟨B ^ p * A, by positivity, fun x ↦ ?_⟩
  have hx : ‖x‖ ≤ B * ‖e x‖ := by
    simpa only [ContinuousLinearEquiv.coe_coe, e.symm_apply_apply] using
      (e.symm : F →L[ℝ] E).le_opNorm (e x)
  calc
    ‖x‖ ^ p * ‖f (e x)‖ ≤ (B * ‖e x‖) ^ p * ‖f (e x)‖ :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hx p) (norm_nonneg _)
    _ = B ^ p * (‖e x‖ ^ p * ‖f (e x)‖) := by rw [mul_pow, mul_assoc]
    _ ≤ B ^ p * A := mul_le_mul_of_nonneg_left (hf (e x)) (pow_nonneg hB _)

end Masullo
