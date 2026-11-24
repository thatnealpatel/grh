module

import Lemmas.ConsecutiveHarmonicBudget
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Transferring the consecutive-harmonic budget to angular moments

Sources: `b825bc58:.godel/bob/noisy-sparse-harmonics.md:3–9` (the upper bound)
and `8fde6138:.godel/bob/initial-harmonic-budget.md:23–29` (the weighted height
transfer). The pointwise majorant and its absolute coefficient budget are
supplied by `8b66f606:Proofs/Lemmas/ConsecutiveHarmonicBudget.lean:428`.

We price the first `n - 1` moments of a probability law on angles, and the
unnormalized even cosine sums in the finite weighted application. No density,
sparse minimax lower bound, or arithmetic packet estimate is used or proved.

Owning check session: `01a20bcd-0340-73f5-9604-3b5724a0ee86`.
-/

open MeasureTheory
open scoped BigOperators

namespace Masullo.ConsecutiveHarmonicTransfer

/-- The constant term `C_n` of the attaining majorant. -/
@[expose] public noncomputable def majorantConstant (n : ℕ) : ℝ :=
  1 / ((n : ℝ) * Real.sin (Real.pi / (2 * (n : ℝ))))

/-- The absolute coefficient budget `L_n` of the same majorant. -/
@[expose] public noncomputable def coefficientBudget (n : ℕ) : ℝ :=
  (1 - 1 / (n : ℝ)) * majorantConstant n

private theorem sum_mul_le_of_abs_le {n : ℕ} {d m : ℕ → ℝ} {e : ℝ}
    (hm : ∀ j ∈ Finset.Ico 1 n, |m j| ≤ e) :
    (∑ j ∈ Finset.Ico 1 n, d j * m j) ≤ (∑ j ∈ Finset.Ico 1 n, |d j|) * e := by
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun j hj ↦ ?_
  calc
    d j * m j ≤ |d j * m j| := le_abs_self _
    _ = |d j| * |m j| := abs_mul _ _
    _ ≤ |d j| * e := mul_le_mul_of_nonneg_left (hm j hj) (abs_nonneg _)

/-- The first `n - 1` cosine expectations control the envelope of a measurable
real angle on any probability space. -/
public theorem integral_abs_sin_half_le_of_cosine_moments {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] {s : α → ℝ} (hs : Measurable s)
    {n : ℕ} (hn : 2 ≤ n) {e : ℝ}
    (hm : ∀ j ∈ Finset.Ico 1 n, |∫ x, Real.cos ((j : ℝ) * s x) ∂μ| ≤ e) :
    (∫ x, |Real.sin (s x / 2)| ∂μ) ≤ majorantConstant n + coefficientBudget n * e := by
  obtain ⟨d, hmajor, _, _, _, hbudget, _⟩ :=
    ConsecutiveHarmonicBudget.exists_majorant_with_budget hn
  change (∑ j ∈ Finset.Ico 1 n, |d j|) = coefficientBudget n at hbudget
  have hf : Integrable (fun x ↦ |Real.sin (s x / 2)|) μ := by
    have hf_meas : Measurable (fun x ↦ |Real.sin (s x / 2)|) :=
      continuous_abs.measurable.comp (hs.div_const 2).sin
    refine Integrable.of_bound hf_meas.aestronglyMeasurable 1 (ae_of_all _ ?_)
    intro x
    rw [Real.norm_of_nonneg (abs_nonneg _)]
    exact Real.abs_sin_le_one _
  have hcos (j : ℕ) : Integrable (fun x ↦ Real.cos ((j : ℝ) * s x)) μ :=
    Integrable.of_bound (measurable_const.mul hs).cos.aestronglyMeasurable 1
      (ae_of_all _ fun x ↦ Real.abs_cos_le_one ((j : ℝ) * s x))
  have hterm (j : ℕ) : Integrable (fun x ↦ d j * Real.cos ((j : ℝ) * s x)) μ :=
    (hcos j).const_mul (d j)
  have hsum : Integrable (fun x ↦ ∑ j ∈ Finset.Ico 1 n, d j * Real.cos ((j : ℝ) * s x)) μ :=
    integrable_finsetSum _ fun j _ ↦ hterm j
  calc
    _ ≤ ∫ x, (majorantConstant n + ∑ j ∈ Finset.Ico 1 n, d j * Real.cos ((j : ℝ) * s x)) ∂μ :=
      integral_mono hf ((integrable_const _).add hsum) fun x ↦ hmajor (s x)
    _ = majorantConstant n +
        ∑ j ∈ Finset.Ico 1 n, d j * (∫ x, Real.cos ((j : ℝ) * s x) ∂μ) := by
      rw [integral_add (integrable_const _) hsum, integral_finsetSum _ fun j _ ↦ hterm j]
      simp only [integral_const, measureReal_def, measure_univ, ENNReal.toReal_one, one_smul,
        integral_const_mul]
    _ ≤ _ := by
      rw [← hbudget]
      exact add_le_add_right (sum_mul_le_of_abs_le (d := d) hm) _

/-- The Fourier moment of the angle law, in the `exp(-i j s)` convention. -/
@[expose] public noncomputable def fourierMoment {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (s : α → ℝ) (j : ℕ) : ℂ :=
  ∫ x, Complex.exp (((-((j : ℝ) * s x) : ℝ) : ℂ) * Complex.I) ∂μ

private theorem integral_cos_eq_re_fourierMoment {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] {s : α → ℝ} (hs : Measurable s) (j : ℕ) :
    (∫ x, Real.cos ((j : ℝ) * s x) ∂μ) = (fourierMoment μ s j).re := by
  let g (x : α) : ℂ := Complex.exp (((-((j : ℝ) * s x) : ℝ) : ℂ) * Complex.I)
  have hg : Measurable g := Complex.continuous_exp.measurable.comp
    ((Complex.continuous_ofReal.measurable.comp (measurable_const.mul hs).neg).mul_const _)
  have hi : Integrable g μ :=
    Integrable.of_bound hg.aestronglyMeasurable 1
      (ae_of_all _ fun x ↦ (Complex.norm_exp_ofReal_mul_I (-((j : ℝ) * s x))).le)
  calc
    _ = ∫ x, RCLike.re (g x) ∂μ := by
      apply integral_congr_ae
      exact ae_of_all _ fun x ↦ by
        change Real.cos ((j : ℝ) * s x) = (g x).re
        dsimp only [g]
        rw [Complex.exp_ofReal_mul_I_re, Real.cos_neg]
    _ = _ := integral_re hi

/-- Complex Fourier bounds imply the same upper bound with no increase in the
moment tolerance. -/
public theorem integral_abs_sin_half_le_of_fourier_moments {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] {s : α → ℝ} (hs : Measurable s)
    {n : ℕ} (hn : 2 ≤ n) {e : ℝ}
    (hm : ∀ j ∈ Finset.Ico 1 n, ‖fourierMoment μ s j‖ ≤ e) :
    (∫ x, |Real.sin (s x / 2)| ∂μ) ≤ majorantConstant n + coefficientBudget n * e := by
  apply integral_abs_sin_half_le_of_cosine_moments μ hs hn
  intro j hj
  rw [integral_cos_eq_re_fourierMoment μ hs j]
  exact (Complex.abs_re_le_norm _).trans (hm j hj)

private theorem cos_shift (j : ℕ) (v : ℝ) : Real.cos ((j : ℝ) * (2 * v - Real.pi)) =
    (-1 : ℝ) ^ j * Real.cos (2 * (j : ℝ) * v) := by
  rw [show (j : ℝ) * (2 * v - Real.pi) = 2 * (j : ℝ) * v - (j : ℝ) * Real.pi by ring,
    Real.cos_sub, Real.cos_nat_mul_pi, Real.sin_nat_mul_pi, mul_zero, add_zero, mul_comm]

/-- Price `|cos v|` from the unnormalized even cosine sums, using `s = 2v - π`.
The constant term scales with the total weight; the moment tolerance is not
rescaled, and no positive-total-weight assumption is needed. -/
public theorem sum_weight_mul_abs_cos_le_of_even_cosine_sums {ι : Type*}
    (t : Finset ι) {w : ι → ℝ} (hw : ∀ i ∈ t, 0 ≤ w i) (v : ι → ℝ)
    {n : ℕ} (hn : 2 ≤ n) {E : ℝ}
    (hm : ∀ j ∈ Finset.Ico 1 n, |∑ i ∈ t, w i * Real.cos (2 * (j : ℝ) * v i)| ≤ E) :
    (∑ i ∈ t, w i * |Real.cos (v i)|) ≤
      majorantConstant n * (∑ i ∈ t, w i) + coefficientBudget n * E := by
  obtain ⟨d, hmajor, _, _, _, hbudget, _⟩ :=
    ConsecutiveHarmonicBudget.exists_majorant_with_budget hn
  change (∑ j ∈ Finset.Ico 1 n, |d j|) = coefficientBudget n at hbudget
  let s (i : ι) := 2 * v i - Real.pi
  have hs (i : ι) : |Real.sin (s i / 2)| = |Real.cos (v i)| := by
    rw [show s i / 2 = v i - Real.pi / 2 by dsimp only [s]; ring,
      Real.sin_sub_pi_div_two, abs_neg]
  have hm_shift j (hj : j ∈ Finset.Ico 1 n) :
      |∑ i ∈ t, w i * Real.cos ((j : ℝ) * s i)| ≤ E := by
    have h : (∑ i ∈ t, w i * Real.cos ((j : ℝ) * s i)) =
        (-1 : ℝ) ^ j * ∑ i ∈ t, w i * Real.cos (2 * (j : ℝ) * v i) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ ↦ by
        dsimp only [s]
        rw [cos_shift, mul_left_comm]
    simpa only [h, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul] using hm j hj
  calc
    _ ≤ ∑ i ∈ t, w i *
        (majorantConstant n + ∑ j ∈ Finset.Ico 1 n, d j * Real.cos ((j : ℝ) * s i)) :=
      Finset.sum_le_sum fun i hi ↦ mul_le_mul_of_nonneg_left (by rw [← hs i]; exact hmajor (s i)) (hw i hi)
    _ = majorantConstant n * (∑ i ∈ t, w i) +
        ∑ j ∈ Finset.Ico 1 n, d j * (∑ i ∈ t, w i * Real.cos ((j : ℝ) * s i)) := by
      simp_rw [mul_add]
      rw [Finset.sum_add_distrib]
      congr 1
      · rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ ↦ mul_comm _ _
      · simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun j _ ↦ Finset.sum_congr rfl fun i _ ↦ mul_left_comm _ _ _
    _ ≤ _ := by
      rw [← hbudget]
      exact add_le_add_right (sum_mul_le_of_abs_le (d := d) hm_shift) _

end Masullo.ConsecutiveHarmonicTransfer
