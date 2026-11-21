module

public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Integral.Prod
public import Lemmas.HalfLineMellinVector

/-! # A single half-plane Blaschke factor at a fixed position cutoff

This is the scalar rank-one calculation for the rational degree-zero, unit-band
Hardy model of the global projection. It is a project calculation, not the
local/global identification used on p. 520. The full operator construction and
its scope are explained in `.godel/obligations/trace-hardy-diagonal-q.md`.
-/

open Complex Filter MeasureTheory Set
open scoped ComplexConjugate Topology

namespace Masullo

/-- The scalar Haar diagonal integral of a positive delay `y` on the
rank-one complement of a single Blaschke factor, with sharp position window
`[0,R]`. The edge term is present before the position cutoff is removed. -/
public theorem halfLineMellinVector_sharpCutoff_overlap {a : ℂ} (ha : 0 < a.re)
    {y R : ℝ} (hy : 0 ≤ y) :
    (∫ x in Icc 0 R, halfLineMellinVector a (x - y) * conj (halfLineMellinVector a x)) =
      if y ≤ R then Complex.exp (-a * y) *
        (1 - Complex.exp (-(↑(2 * a.re) : ℂ) * ↑(R - y))) else 0 := by
  by_cases h : y ≤ R
  · rw [ite_eq_left h]
    let r : ℂ := ↑(2 * a.re)
    have hr : r ≠ 0 := by dsimp [r]; exact_mod_cast (show 2 * a.re ≠ 0 by positivity)
    let q : ℝ → ℂ := fun x ↦ Complex.exp (-a * y) * (r * Complex.exp (-r * ↑(x - y)))
    have hsub : Icc y R ⊆ Icc 0 R := fun _ hx ↦ ⟨hy.trans hx.1, hx.2⟩
    calc
      _ = ∫ x in Icc 0 R, (Icc y R).indicator q x := by
        apply setIntegral_congr_fun measurableSet_Icc
        intro x hx
        by_cases hyx : y ≤ x
        · rw [indicator_of_mem (show x ∈ Icc y R from ⟨hyx, hx.2⟩)]
          exact halfLineMellinVector_shift_mul_conj ha hy hyx
        · change halfLineMellinVector a (x - y) * conj (halfLineMellinVector a x) =
              (Icc y R).indicator q x
          rw [indicator_of_notMem (show x ∉ Icc y R from fun hmem ↦ hyx hmem.1),
            halfLineMellinVector_eq_zero_of_neg a (sub_neg.mpr (lt_of_not_ge hyx)), zero_mul]
      _ = ∫ x in Icc y R, q x := by
        rw [integral_indicator measurableSet_Icc, Measure.restrict_restrict measurableSet_Icc,
          inter_eq_left.mpr hsub]
      _ = _ := by
        rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le h]
        simp only [q, intervalIntegral.integral_const_mul]
        rw [intervalIntegral.integral_comp_sub_right (fun t : ℝ ↦ Complex.exp (-r * ↑t)) y,
          sub_self,
          integral_exp_mul_complex (neg_ne_zero.mpr hr), ofReal_zero, mul_zero, Complex.exp_zero]
        congr 1
        change r * ((Complex.exp (-r * ↑(R - y)) - 1) / -r) =
          1 - Complex.exp (-r * ↑(R - y))
        field_simp
        ring
  · rw [ite_eq_right h]
    calc
      _ = ∫ _ in Icc 0 R, (0 : ℂ) := by
        apply setIntegral_congr_fun measurableSet_Icc
        intro x hx
        change halfLineMellinVector a (x - y) * conj (halfLineMellinVector a x) = 0
        rw [halfLineMellinVector_eq_zero_of_neg a
          (sub_neg.mpr (hx.2.trans_lt (lt_of_not_ge h))), zero_mul]
      _ = 0 := by simp

/-- Causal convolution with a profile on `[0,D]`, paired against the single
Blaschke vector on `[0,R]`. The profile is understood to be zero off `[0,D]`.
This is the **positive** rank-one pairing; the complementary projection
contributes its negative when the ambient convolution has zero diagonal. -/
public theorem halfLineMellinVector_sharpCutoff_convolution {a : ℂ} (ha : 0 < a.re)
    {g : ℝ → ℂ} {D : ℝ} (hg : IntegrableOn g (Icc 0 D)) (R : ℝ) :
    (∫ x in Icc 0 R, (∫ y in Icc 0 D, g y * halfLineMellinVector a (x - y)) *
      conj (halfLineMellinVector a x)) =
    ∫ y in Icc 0 D, g y * (if y ≤ R then Complex.exp (-a * y) *
      (1 - Complex.exp (-(↑(2 * a.re) : ℂ) * ↑(R - y))) else 0) := by
  let u := halfLineMellinVector a
  let μ := volume.restrict (Icc (0 : ℝ) R)
  let ν := volume.restrict (Icc (0 : ℝ) D)
  have hu : StronglyMeasurable u := stronglyMeasurable_halfLineMellinVector a
  have hK : StronglyMeasurable (fun p : ℝ × ℝ ↦ u (p.1 - p.2) * conj (u p.1)) :=
    (hu.comp_measurable (measurable_fst.sub measurable_snd)).mul
      ((continuous_conj.stronglyMeasurable).comp_measurable hu.measurable).comp_fst
  have hg' : Integrable g ν := hg
  have hi : Integrable (Function.uncurry (fun x y ↦ g y * (u (x - y) * conj (u x))))
      (μ.prod ν) := by
    apply (hg'.comp_snd μ).mul_bdd (c := Real.sqrt (2 * a.re) * Real.sqrt (2 * a.re))
      hK.aestronglyMeasurable
    exact ae_of_all _ fun p ↦ by
      rw [norm_mul, Complex.norm_conj]
      exact mul_le_mul (norm_halfLineMellinVector_le ha _) (norm_halfLineMellinVector_le ha _)
        (norm_nonneg _) (Real.sqrt_nonneg _)
  calc
    _ = ∫ x in Icc 0 R, ∫ y in Icc 0 D, g y * (u (x - y) * conj (u x)) := by
      congr 1 with x
      rw [← integral_mul_const]
      simp only [mul_assoc, u]
    _ = ∫ y in Icc 0 D, ∫ x in Icc 0 R, g y * (u (x - y) * conj (u x)) :=
      integral_integral_swap hi
    _ = _ := by
      apply setIntegral_congr_fun measurableSet_Icc
      intro y hy
      dsimp only [u]
      rw [integral_const_mul, halfLineMellinVector_sharpCutoff_overlap ha hy.1]

/-- Removing the sharp position cutoff on the single-factor convolution
pairing gives the Laplace value at `a`. After the exponential coordinate
change, this is the reflected Mellin value at the corresponding zero. -/
public theorem tendsto_halfLineMellinVector_sharpCutoff_convolution {a : ℂ} (ha : 0 < a.re)
    {g : ℝ → ℂ} {D : ℝ} (hg : IntegrableOn g (Icc 0 D)) :
    Tendsto (fun R : ℝ ↦ ∫ x in Icc 0 R,
      (∫ y in Icc 0 D, g y * halfLineMellinVector a (x - y)) * conj (halfLineMellinVector a x))
      atTop (𝓝 (∫ y in Icc 0 D, g y * Complex.exp (-a * y))) := by
  let r := 2 * a.re
  let k : ℝ → ℂ := fun y ↦ g y * Complex.exp (-a * y)
  refine Tendsto.congr' (f₁ := fun R ↦ ∫ y in Icc 0 D,
    k y * (1 - Complex.exp (-(r : ℂ) * (↑(R - y) : ℂ)))) ?_ ?_
  · filter_upwards [eventually_ge_atTop D] with R hR
    have h := halfLineMellinVector_sharpCutoff_convolution ha hg R
    refine Eq.trans ?_ h.symm
    apply setIntegral_congr_fun measurableSet_Icc
    intro y hy
    dsimp only [k, r]
    rw [ite_eq_left (hy.2.trans hR), mul_assoc]
  · refine MeasureTheory.tendsto_integral_filter_of_dominated_convergence (fun y ↦ ‖g y‖)
      ?_ ?_ hg.norm ?_
    · exact Eventually.of_forall fun R ↦
        (hg.aestronglyMeasurable.mul (by fun_prop)).mul (by fun_prop)
    · filter_upwards [eventually_ge_atTop D] with R hR
      filter_upwards [ae_restrict_mem measurableSet_Icc] with y hy
      have he : 0 < Real.exp (-r * (R - y)) := Real.exp_pos _
      have he' : Real.exp (-r * (R - y)) ≤ 1 := Real.exp_le_one_iff.mpr (by
        exact mul_nonpos_of_nonpos_of_nonneg (by dsimp [r]; linarith) (sub_nonneg.mpr (hy.2.trans hR)))
      have h₁ : ‖Complex.exp (-a * (y : ℂ))‖ ≤ 1 := by
        rw [Complex.norm_exp, Real.exp_le_one_iff, Complex.mul_re, Complex.ofReal_re,
          Complex.ofReal_im, mul_zero, sub_zero, Complex.neg_re]
        exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ha.le) hy.1
      have h₂ : ‖1 - Complex.exp (-(r : ℂ) * (↑(R - y) : ℂ))‖ ≤ 1 := by
        rw [← Complex.ofReal_neg, ← Complex.ofReal_mul, ← Complex.ofReal_exp,
          ← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real,
          Real.norm_of_nonneg (sub_nonneg.mpr he')]
        linarith
      dsimp [k]
      rw [norm_mul, norm_mul, mul_assoc]
      exact mul_le_of_le_one_right (norm_nonneg _)
        ((mul_le_of_le_one_right (norm_nonneg _) h₂).trans h₁)
    · exact ae_of_all _ fun y ↦ by
        have ht : Tendsto (fun R : ℝ ↦ -r * (R - y)) atTop atBot :=
          (tendsto_atTop_add_const_right atTop (-y) tendsto_id).const_mul_atTop_of_neg (by
            change -(2 * a.re) < 0
            linarith)
        have he : Tendsto (fun R : ℝ ↦ Complex.exp (-(r : ℂ) * (↑(R - y) : ℂ))) atTop (𝓝 0) := by
          have h := Complex.continuous_ofReal.continuousAt.tendsto.comp (Real.tendsto_exp_atBot.comp ht)
          simpa only [Function.comp_def, Complex.ofReal_zero, Complex.ofReal_exp,
            Complex.ofReal_mul, Complex.ofReal_neg] using h
        simpa only [sub_zero, mul_one] using
          (tendsto_const_nhds (x := k y)).mul ((tendsto_const_nhds (x := (1 : ℂ))).sub he)

end Masullo
