module

public import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Order.Group.Unbundled.Int
import Mathlib.Algebra.Order.Ring.Cast
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.LinearCombination

/-!
# Primitive row uniqueness with two filters

Source: `42017cc84804:.godel/alice/global-pivot-row-price.md:39–98`, unchanged at
scan pin `7817ec43` and base `6467546b`. This is the boxed row uniqueness step
(lines 60–73). In the first row `f_h = 1`; its global count is used for the heavier
endpoint in the first-row heavy/light price (lines 83–98). This module does not
prove the index formula, recover column labels, or establish the counting price.

Owning check session: `01a20fda-fdc5-7fd5-bef7-0dc0da54e6c0`.
-/

namespace PrimitiveTwoFilterRow

private theorem filter_product_dvd_det {F q m₁ m₂ δ₁ δ₂ f_h f_N : ℤ}
    (hh₁ : f_h ∣ m₁) (hh₂ : f_h ∣ m₂)
    (hN₁ : f_N ∣ F * m₁ - q * δ₁) (hN₂ : f_N ∣ F * m₂ - q * δ₂)
    (hq : q.gcd f_N = 1) : f_h * f_N ∣ m₁ * δ₂ - m₂ * δ₁ := by
  obtain ⟨k₁, hk₁⟩ := hh₁
  obtain ⟨k₂, hk₂⟩ := hh₂
  obtain ⟨l₁, hl₁⟩ := hN₁
  obtain ⟨l₂, hl₂⟩ := hN₂
  rw [hk₁] at hl₁
  rw [hk₂] at hl₂
  -- Cancel `q` on the determinant of the scaled rows, before restoring `f_h`.
  have hqdet : f_N ∣ q * (k₁ * δ₂ - k₂ * δ₁) := by
    refine ⟨k₂ * l₁ - k₁ * l₂, ?_⟩
    linear_combination k₂ * hl₁ - k₁ * hl₂
  obtain ⟨l, hl⟩ := (Int.isCoprime_iff_gcd_eq_one.mpr hq).symm.dvd_of_dvd_mul_left hqdet
  refine ⟨l, ?_⟩
  linear_combination δ₂ * hk₁ - δ₁ * hk₂ + f_h * hl

private theorem box_abs_det_le {m₁ m₂ δ₁ δ₂ V H : ℝ}
    (hm₁ : 0 ≤ m₁) (hm₂ : 0 ≤ m₂) (hV₁ : m₁ ≤ V) (hV₂ : m₂ ≤ V)
    (hH₁ : |δ₁| ≤ H) (hH₂ : |δ₂| ≤ H) : |m₁ * δ₂ - m₂ * δ₁| ≤ 2 * V * H := by
  have hV : 0 ≤ V := hm₁.trans hV₁
  calc
    _ ≤ |m₁ * δ₂| + |m₂ * δ₁| := abs_sub _ _
    _ = m₁ * |δ₂| + m₂ * |δ₁| := by simp only [abs_mul, abs_of_nonneg hm₁, abs_of_nonneg hm₂]
    _ ≤ V * H + V * H := add_le_add
      (mul_le_mul hV₁ hH₂ (abs_nonneg _) hV) (mul_le_mul hV₂ hH₁ (abs_nonneg _) hV)
    _ = _ := by rw [← two_mul, mul_assoc]

private theorem primitive_row_eq_of_cross_eq {m₁ m₂ δ₁ δ₂ : ℤ}
    (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (hprim₁ : m₁.gcd δ₁ = 1) (hprim₂ : m₂.gcd δ₂ = 1)
    (hcross : m₁ * δ₂ = m₂ * δ₁) : (m₁, δ₁) = (m₂, δ₂) := by
  have h₁ : m₁ ∣ m₂ := (Int.isCoprime_iff_gcd_eq_one.mpr hprim₁).dvd_of_dvd_mul_right
    (hcross ▸ dvd_mul_right m₁ δ₂)
  have h₂ : m₂ ∣ m₁ := (Int.isCoprime_iff_gcd_eq_one.mpr hprim₂).dvd_of_dvd_mul_right
    (hcross.symm ▸ dvd_mul_right m₂ δ₁)
  have hm : m₁ = m₂ := Int.dvd_antisymm hm₁.le hm₂.le h₁ h₂
  have hδ : δ₂ = δ₁ := Int.eq_of_mul_eq_mul_left hm₁.ne' (by simpa only [← hm] using hcross)
  exact Prod.ext hm hδ.symm

/-- Two primitive integer rows in the same real box are equal if they satisfy the
same two filters and the product of the filters strictly exceeds `2 * V * H`.
Only `q` and `f_N` need to be coprime. The gaps are signed, and either filter may be `1`. -/
public theorem primitiveRow_eq_of_two_filters {F q m₁ m₂ δ₁ δ₂ f_h f_N : ℤ} {V H : ℝ}
    (hf_h : 0 < f_h) (hf_N : 0 < f_N) (hm₁ : 0 < m₁) (hm₂ : 0 < m₂)
    (hV₁ : (m₁ : ℝ) ≤ V) (hV₂ : (m₂ : ℝ) ≤ V)
    (hH₁ : |(δ₁ : ℝ)| ≤ H) (hH₂ : |(δ₂ : ℝ)| ≤ H)
    (hprim₁ : m₁.gcd δ₁ = 1) (hprim₂ : m₂.gcd δ₂ = 1)
    (hh₁ : f_h ∣ m₁) (hh₂ : f_h ∣ m₂)
    (hN₁ : f_N ∣ F * m₁ - q * δ₁) (hN₂ : f_N ∣ F * m₂ - q * δ₂)
    (hq : q.gcd f_N = 1) (hcutoff : 2 * V * H < (f_h : ℝ) * (f_N : ℝ)) :
    (m₁, δ₁) = (m₂, δ₂) := by
  have hdiv := filter_product_dvd_det hh₁ hh₂ hN₁ hN₂ hq
  have hm₁R : (0 : ℝ) ≤ m₁ := by exact_mod_cast hm₁.le
  have hm₂R : (0 : ℝ) ≤ m₂ := by exact_mod_cast hm₂.le
  have hbound := box_abs_det_le hm₁R hm₂R hV₁ hV₂ hH₁ hH₂
  have hsmall : |m₁ * δ₂ - m₂ * δ₁| < |f_h * f_N| := by
    rw [abs_of_pos (mul_pos hf_h hf_N)]
    exact_mod_cast hbound.trans_lt hcutoff
  simp only [Int.abs_eq_natAbs] at hsmall
  have hzero := Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hdiv (by exact_mod_cast hsmall)
  exact primitive_row_eq_of_cross_eq hm₁ hm₂ hprim₁ hprim₂ (sub_eq_zero.mp hzero)

end PrimitiveTwoFilterRow
