module

public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Lemmas.HalfLineMellinVector

/-! # A single half-plane Blaschke factor at a fixed position cutoff

This is the scalar rank-one calculation for the rational degree-zero, unit-band
Hardy model of the global projection. It is a project calculation, not the
local/global identification used on p. 520. The full operator construction and
its scope are explained in `.godel/obligations/trace-hardy-diagonal-q.md`.
-/

open Complex MeasureTheory Set
open scoped ComplexConjugate

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

end Masullo
