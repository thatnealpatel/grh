module

public import Mathlib.MeasureTheory.Group.Circle
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# One-coordinate Laurent moment on the unit circle

Source: `20ac2a9d:.godel/bob/signed-gap-cube-screen.md:58–62`, unchanged at `4c47eae3`.
Owning check session: `01a20c03-fe6f-73b3-a1bb-bf0df5b6ef1a`.

This is the one-coordinate input to the moment iteration following
`Lemmas.TriangularCubeCoefficients`. The same unit phase supplies the linear
and conjugate terms; the law is Haar probability on the complex unit circle.
No product moment or shell estimate is asserted here.
-/

open MeasureTheory TopologicalSpace
open scoped BigOperators ComplexConjugate

namespace Masullo.LaurentCircleMoment

/-- The uniform probability law on the complex unit circle. -/
@[expose] public noncomputable def uniformCircle : Measure Circle :=
  Measure.haarMeasure (⊤ : PositiveCompacts Circle)

public instance instIsProbabilityMeasureUniformCircle : IsProbabilityMeasure uniformCircle :=
  ⟨Measure.haarMeasure_self (K₀ := (⊤ : PositiveCompacts Circle))⟩

private instance : uniformCircle.IsMulLeftInvariant := by
  unfold uniformCircle
  infer_instance

private def tail (b c : ℂ) (z : Circle) : ℂ := b * (z : ℂ) + c * conj (z : ℂ)

private theorem continuous_tail (b c : ℂ) : Continuous (tail b c) := by
  have hc : Continuous (fun z : Circle ↦ (z : ℂ)) := continuous_subtype_val
  unfold tail
  fun_prop

private theorem tail_antipode (b c : ℂ) (z : Circle) :
    tail b c ((-1 : Circle) * z) = -tail b c z := by
  simp only [tail, Circle.coe_neg, neg_mul, one_mul, map_neg, mul_neg]
  abel

private theorem continuous_add_moment (a b c : ℂ) (m : ℕ) :
    Continuous (fun z : Circle ↦ ‖a + tail b c z‖ ^ (2 * m)) :=
  ((continuous_const.add (continuous_tail b c)).norm).pow _

private theorem continuous_sub_moment (a b c : ℂ) (m : ℕ) :
    Continuous (fun z : Circle ↦ ‖a - tail b c z‖ ^ (2 * m)) :=
  ((continuous_const.sub (continuous_tail b c)).norm).pow _

private theorem integral_eq_sign_average (a b c : ℂ) (m : ℕ) :
    (∫ z, ‖a + tail b c z‖ ^ (2 * m) ∂uniformCircle) =
      ∫ z, (‖a + tail b c z‖ ^ (2 * m) + ‖a - tail b c z‖ ^ (2 * m)) / 2 ∂uniformCircle := by
  have hneg : (∫ z, ‖a - tail b c z‖ ^ (2 * m) ∂uniformCircle) =
      ∫ z, ‖a + tail b c z‖ ^ (2 * m) ∂uniformCircle := by
    simpa only [tail_antipode, ← sub_eq_add_neg] using
      (integral_mul_left_eq_self (μ := uniformCircle)
        (fun z ↦ ‖a + tail b c z‖ ^ (2 * m)) (-1 : Circle))
  have hp := (continuous_add_moment a b c m).integrable_of_hasCompactSupport
    (μ := uniformCircle) (HasCompactSupport.of_compactSpace _)
  have hn := (continuous_sub_moment a b c m).integrable_of_hasCompactSupport
    (μ := uniformCircle) (HasCompactSupport.of_compactSpace _)
  rw [integral_div, integral_add hp hn, hneg]
  ring

/-- For an even exponent, retain the even indices after sign cancellation. -/
private theorem sum_range_even (n : ℕ) (f : ℕ → ℝ) :
    (∑ i ∈ Finset.range (2 * n + 1), if Even i then f i else 0) =
      ∑ j ∈ Finset.range (n + 1), f (2 * j) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have heven : Even (2 * (n + 1)) := ⟨n + 1, by omega⟩
    have hodd := Nat.not_even_two_mul_add_one n
    rw [show 2 * (n + 1) + 1 = (2 * n + 1) + 1 + 1 by omega,
      Finset.sum_range_succ, Finset.sum_range_succ, ih,
      Finset.sum_range_succ (fun j ↦ f (2 * j)) (n + 1)]
    simp only [hodd, heven, ite_false, ite_true, add_zero,
      show 2 * n + 1 + 1 = 2 * (n + 1) by omega]

private theorem sign_average_pow (u d : ℝ) (n : ℕ) :
    ((u + d) ^ n + (u - d) ^ n) / 2 =
      ∑ j ∈ Finset.range (n + 1),
        if Even j then d ^ j * u ^ (n - j) * (n.choose j : ℝ) else 0 := by
  rw [add_comm u d, show u - d = -d + u by ring, add_pow, add_pow,
    ← Finset.sum_add_distrib, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j _
  rcases Nat.even_or_odd j with hj | hj
  · rw [ite_eq_left hj, hj.neg_pow]
    ring
  · rw [ite_eq_right (Nat.not_even_iff_odd.mpr hj), hj.neg_pow]
    ring

private theorem sign_average_pow_le (u d e : ℝ) (n : ℕ) (hu : 0 ≤ u) (hde : |d| ≤ e) :
    ((u + d) ^ n + (u - d) ^ n) / 2 ≤ ((u + e) ^ n + (u - e) ^ n) / 2 := by
  rw [sign_average_pow u d, sign_average_pow u e]
  apply Finset.sum_le_sum
  intro j _
  split_ifs with hj
  · rw [← hj.pow_abs d]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg d) hde j) (pow_nonneg hu _))
      (Nat.cast_nonneg _)
  · rfl

private theorem choose_succ_real {n j : ℕ} (hj : j ≤ n) :
    (n.choose (j + 1) : ℝ) * ((j : ℝ) + 1) = (n.choose j : ℝ) * ((n : ℝ) - j) := by
  simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_sub hj] using
    congrArg (fun k : ℕ ↦ (k : ℝ)) (Nat.choose_succ_right_eq n j)

/-- Pair two adjacent binomial recurrences, then bound the remaining odd factor. -/
private theorem choose_even_le {m j : ℕ} (hm : 0 < m) (hj : j ≤ m) :
    ((2 * m).choose (2 * j) : ℝ) ≤ (m.choose j : ℝ) * (2 * (m : ℝ) - 1) ^ j := by
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hK : (0 : ℝ) ≤ 2 * (m : ℝ) - 1 := by linarith
  induction j with
  | zero => simp
  | succ j ih =>
    have hj' : j ≤ m := by omega
    have hjm : (j : ℝ) + 1 ≤ m := by exact_mod_cast hj
    have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg _
    have hdist : (0 : ℝ) ≤ (m : ℝ) - j := by linarith
    have hodd : (0 : ℝ) ≤ 2 * (m : ℝ) - 2 * j - 1 := by linarith
    have h₁ := choose_succ_real (n := 2 * m) (j := 2 * j) (by omega)
    have h₂ := choose_succ_real (n := 2 * m) (j := 2 * j + 1) (by omega)
    rw [show 2 * j + 1 + 1 = 2 * (j + 1) by omega] at h₂
    push_cast at h₁ h₂
    have hrec : ((2 * m).choose (2 * (j + 1)) : ℝ) * ((j : ℝ) + 1) * (2 * (j : ℝ) + 1) =
        ((2 * m).choose (2 * j) : ℝ) * ((m : ℝ) - j) * (2 * (m : ℝ) - 2 * j - 1) := by
      calc
        _ = (((2 * m).choose (2 * (j + 1)) : ℝ) * (2 * (j : ℝ) + 1 + 1)) *
            (2 * (j : ℝ) + 1) / 2 := by ring
        _ = (((2 * m).choose (2 * j + 1) : ℝ) * (2 * (j : ℝ) + 1)) *
            (2 * (m : ℝ) - 2 * j - 1) / 2 := by rw [h₂]; ring
        _ = _ := by rw [h₁]; ring
    apply le_of_mul_le_mul_right _ (show (0 : ℝ) < (j : ℝ) + 1 by positivity)
    calc
      _ ≤ ((2 * m).choose (2 * (j + 1)) : ℝ) * ((j : ℝ) + 1) * (2 * (j : ℝ) + 1) :=
        le_mul_of_one_le_right (by positivity) (by linarith only [hj0])
      _ = ((2 * m).choose (2 * j) : ℝ) * ((m : ℝ) - j) * (2 * (m : ℝ) - 2 * j - 1) := hrec
      _ ≤ ((m.choose j : ℝ) * (2 * (m : ℝ) - 1) ^ j) * ((m : ℝ) - j) * (2 * (m : ℝ) - 1) :=
        mul_le_mul (mul_le_mul_of_nonneg_right (ih hj') hdist) (by linarith only [hj0]) hodd
          (mul_nonneg (by positivity) hdist)
      _ = (m.choose j : ℝ) * ((m : ℝ) - j) * (2 * (m : ℝ) - 1) ^ (j + 1) := by
        rw [pow_succ]
        ring
      _ = _ := by rw [← choose_succ_real hj']; ring

private theorem real_sign_average_le {m : ℕ} (hm : 0 < m) (x y : ℝ) :
    ((x + y) ^ (2 * m) + (x - y) ^ (2 * m)) / 2 ≤
      (x ^ 2 + (2 * (m : ℝ) - 1) * y ^ 2) ^ m := by
  rw [sign_average_pow, sum_range_even, add_comm (x ^ 2), add_pow]
  apply Finset.sum_le_sum
  intro j hj
  have hjm : j ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  rw [show 2 * m - 2 * j = 2 * (m - j) by omega, pow_mul y 2 j, pow_mul x 2 (m - j), mul_pow]
  calc
    _ ≤ (y ^ 2) ^ j * (x ^ 2) ^ (m - j) * ((m.choose j : ℝ) * (2 * (m : ℝ) - 1) ^ j) :=
      mul_le_mul_of_nonneg_left (choose_even_le hm hjm) (by positivity)
    _ = _ := by ring

/-- At fixed moduli the sign average is bounded by that of aligned real arguments. -/
private theorem complex_sign_average_le {m : ℕ} (hm : 0 < m) (a w : ℂ) :
    (‖a + w‖ ^ (2 * m) + ‖a - w‖ ^ (2 * m)) / 2 ≤
      (‖a‖ ^ 2 + (2 * (m : ℝ) - 1) * ‖w‖ ^ 2) ^ m := by
  let u := ‖a‖ ^ 2 + ‖w‖ ^ 2
  let d := 2 * (a * conj w).re
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hp : ‖a + w‖ ^ 2 = u + d := by
    simp only [Complex.sq_norm, Complex.normSq_add, u, d]
  have hn : ‖a - w‖ ^ 2 = u - d := by
    rw [sub_eq_add_neg]
    simp only [Complex.sq_norm, Complex.normSq_add, Complex.normSq_neg, map_neg, mul_neg,
      Complex.neg_re, u, d]
    ring
  have hd : |d| ≤ 2 * ‖a‖ * ‖w‖ := by
    dsimp [d]
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), mul_assoc]
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    simpa only [norm_mul, Complex.norm_conj] using Complex.abs_re_le_norm (a * conj w)
  calc
    _ = ((u + d) ^ m + (u - d) ^ m) / 2 := by rw [pow_mul, pow_mul, hp, hn]
    _ ≤ ((u + 2 * ‖a‖ * ‖w‖) ^ m + (u - 2 * ‖a‖ * ‖w‖) ^ m) / 2 :=
      sign_average_pow_le u d _ m hu hd
    _ = ((‖a‖ + ‖w‖) ^ (2 * m) + (‖a‖ - ‖w‖) ^ (2 * m)) / 2 := by
      rw [show u + 2 * ‖a‖ * ‖w‖ = (‖a‖ + ‖w‖) ^ 2 by dsimp [u]; ring,
        show u - 2 * ‖a‖ * ‖w‖ = (‖a‖ - ‖w‖) ^ 2 by dsimp [u]; ring, ← pow_mul, ← pow_mul]
    _ ≤ _ := real_sign_average_le hm _ _

private theorem tail_sq_le (b c : ℂ) (z : Circle) :
    ‖tail b c z‖ ^ 2 ≤ 2 * (‖b‖ ^ 2 + ‖c‖ ^ 2) := by
  have ht : ‖tail b c z‖ ≤ ‖b‖ + ‖c‖ := by
    simpa only [tail, norm_mul, Circle.norm_coe, Complex.norm_conj, mul_one] using
      norm_add_le (b * (z : ℂ)) (c * conj (z : ℂ))
  calc
    _ ≤ (‖b‖ + ‖c‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) ht _
    _ ≤ _ := by nlinarith only [sq_nonneg (‖b‖ - ‖c‖)]

/-- The `2m`-th moment of a degree-one Laurent polynomial in a single uniform
unit phase. The three coefficients can vanish, and the conjugate uses the same phase. -/
public theorem integral_norm_laurent_pow_le (a b c : ℂ) {m : ℕ} (hm : 0 < m) :
    (∫ z : Circle, ‖a + b * (z : ℂ) + c * conj (z : ℂ)‖ ^ (2 * m) ∂uniformCircle) ≤
      (‖a‖ ^ 2 + (4 * (m : ℝ) - 2) * (‖b‖ ^ 2 + ‖c‖ ^ 2)) ^ m := by
  simp only [add_assoc a]
  change (∫ z, ‖a + tail b c z‖ ^ (2 * m) ∂uniformCircle) ≤ _
  rw [integral_eq_sign_average]
  let M := (‖a‖ ^ 2 + (4 * (m : ℝ) - 2) * (‖b‖ ^ 2 + ‖c‖ ^ 2)) ^ m
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hK : (0 : ℝ) ≤ 2 * (m : ℝ) - 1 := by linarith
  have hM (z : Circle) :
      (‖a + tail b c z‖ ^ (2 * m) + ‖a - tail b c z‖ ^ (2 * m)) / 2 ≤ M := by
    refine (complex_sign_average_le hm a (tail b c z)).trans (pow_le_pow_left₀ (by positivity) ?_ m)
    calc
      _ ≤ ‖a‖ ^ 2 + (2 * (m : ℝ) - 1) * (2 * (‖b‖ ^ 2 + ‖c‖ ^ 2)) :=
        add_le_add_right (mul_le_mul_of_nonneg_left (tail_sq_le b c z) hK) _
      _ = _ := by ring
  have hcont := ((continuous_add_moment a b c m).add (continuous_sub_moment a b c m)).div_const 2
  have hint := hcont.integrable_of_hasCompactSupport (μ := uniformCircle)
    (HasCompactSupport.of_compactSpace _)
  calc
    _ ≤ ∫ _ : Circle, M ∂uniformCircle := integral_mono hint (integrable_const M) hM
    _ = M := by simp

end Masullo.LaurentCircleMoment
