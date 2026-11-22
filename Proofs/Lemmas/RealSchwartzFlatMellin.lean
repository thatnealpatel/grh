module

public import Lemmas.LogMellinDerivative
public import Lemmas.RealSchwartzFlatTail
import Mathlib.Tactic.Linarith

/-! # The entire raw real Mellin pairing of a flat Schwartz test -/

open MeasureTheory
open scoped SchwartzMap

namespace Masullo

/-- The two signed rays folded using the real sign character of parity `ε`. -/
@[expose] public noncomputable def realSchwartzParityLogProfile (b : 𝓢(ℝ, ℂ)) (ε : ℕ) (t : ℝ) : ℂ :=
  b (Real.exp t) + (-1 : ℂ) ^ ε * b (-Real.exp t)

private theorem norm_realSchwartz_exp_ray_le (b : 𝓢(ℝ, ℂ)) (K : ℕ) (t y : ℝ)
    (hy : ‖y‖ = Real.exp t) :
    ‖b y‖ ≤ SchwartzMap.seminorm ℝ K 0 b * Real.exp (-(K : ℝ) * t) := by
  rw [neg_mul, Real.exp_neg, ← div_eq_mul_inv, le_div_iff₀ (Real.exp_pos _),
    Real.exp_nat_mul, mul_comm, ← hy]
  exact SchwartzMap.norm_pow_mul_le_seminorm ℝ b K y

/-- Flatness bounds the negative log tail and the Schwartz seminorm bounds the positive
log tail, so the raw weighted profile has an exponential majorant at every `z`. -/
public theorem exists_realSchwartzParityLog_mellin_bound (b : 𝓢(ℝ, ℂ))
    (hflat : ∀ j : ℕ, iteratedDeriv j (b : ℝ → ℂ) 0 = 0) (ε : ℕ) (z : ℂ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ,
      ‖realSchwartzParityLogProfile b ε t * Complex.exp (z * t)‖ ≤ C * Real.exp (-3 * |t|) := by
  obtain ⟨K, hK⟩ := exists_nat_ge (|z.re| + 3)
  have hKpos : 1 ≤ K := by
    exact_mod_cast (show (1 : ℝ) ≤ (K : ℝ) by linarith [abs_nonneg z.re])
  obtain ⟨A, hA, hneg⟩ := exists_realSchwartz_negLog_tail_bound b hflat K hKpos
  let B := SchwartzMap.seminorm ℝ K 0 b
  let M := max A B
  have hM : 0 ≤ M := hA.trans (le_max_left ..)
  refine ⟨2 * M, mul_nonneg (by norm_num) hM, fun t ↦ ?_⟩
  have weighted {a C : ℝ} (hC : C ≤ M)
      (hp : ‖b (Real.exp t)‖ ≤ C * Real.exp (a * t))
      (hm : ‖b (-Real.exp t)‖ ≤ C * Real.exp (a * t))
      (ha : (a + z.re) * t ≤ -3 * |t|) :
      ‖realSchwartzParityLogProfile b ε t * Complex.exp (z * t)‖ ≤
        2 * M * Real.exp (-3 * |t|) := by
    have hfold : ‖realSchwartzParityLogProfile b ε t‖ ≤ 2 * M * Real.exp (a * t) := by
      calc
        _ ≤ ‖b (Real.exp t)‖ + ‖b (-Real.exp t)‖ := by
          simpa only [realSchwartzParityLogProfile, norm_mul, norm_pow, norm_neg, norm_one,
            one_pow, one_mul] using norm_add_le (b (Real.exp t)) ((-1 : ℂ) ^ ε * b (-Real.exp t))
        _ ≤ C * Real.exp (a * t) + C * Real.exp (a * t) := add_le_add hp hm
        _ ≤ 2 * M * Real.exp (a * t) := by
          rw [← two_mul, ← mul_assoc]
          gcongr
    rw [norm_mul, Complex.norm_exp, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      mul_zero, sub_zero]
    calc
      _ ≤ 2 * M * Real.exp (a * t) * Real.exp (z.re * t) :=
        mul_le_mul_of_nonneg_right hfold (Real.exp_pos _).le
      _ = 2 * M * Real.exp ((a + z.re) * t) := by rw [add_mul, Real.exp_add, mul_assoc]
      _ ≤ _ := by gcongr
  by_cases ht : t ≤ 0
  · obtain ⟨hp, hm⟩ := hneg t ht
    apply weighted (le_max_left A B) hp hm
    have hrate : 3 ≤ (K : ℝ) + z.re := by linarith [neg_abs_le z.re]
    simpa only [abs_of_nonpos ht, mul_neg, neg_mul, neg_neg] using
      (mul_le_mul_of_nonpos_right hrate ht)
  · have hp := (Real.exp_pos t).le
    have hnorm : ‖Real.exp t‖ = Real.exp t := Real.norm_of_nonneg hp
    apply weighted (le_max_right A B) (norm_realSchwartz_exp_ray_le b K t _ hnorm)
      (norm_realSchwartz_exp_ray_le b K t _ ((norm_neg _).trans hnorm))
    have hrate : -(K : ℝ) + z.re ≤ -3 := by linarith [le_abs_self z.re]
    rw [abs_of_nonneg (le_of_not_ge ht)]
    exact mul_le_mul_of_nonneg_right hrate (le_of_not_ge ht)

/-- The folded real pairing and its first log moment are absolutely integrable everywhere,
and the moment is the complex derivative of the pairing. -/
public theorem hasDerivAt_realSchwartzParityLog_mellin (b : 𝓢(ℝ, ℂ))
    (hflat : ∀ j : ℕ, iteratedDeriv j (b : ℝ → ℂ) 0 = 0) (ε : ℕ) (z : ℂ) :
    Integrable (fun t : ℝ ↦ realSchwartzParityLogProfile b ε t * Complex.exp (z * t)) ∧
    Integrable (fun t : ℝ ↦ (t : ℂ) * (realSchwartzParityLogProfile b ε t * Complex.exp (z * t))) ∧
    HasDerivAt (fun w : ℂ ↦ ∫ t : ℝ, realSchwartzParityLogProfile b ε t * Complex.exp (w * t))
      (∫ t : ℝ, (t : ℂ) * (realSchwartzParityLogProfile b ε t * Complex.exp (z * t))) z := by
  obtain ⟨C, hC, h⟩ := exists_realSchwartzParityLog_mellin_bound b hflat ε z
  have hf : Continuous (realSchwartzParityLogProfile b ε) :=
    (b.continuous.comp Real.continuous_exp).add
      (continuous_const.mul (b.continuous.comp Real.continuous_exp.neg))
  exact hasDerivAt_logMellin_of_decay hf z (r := 1) one_pos hC
    (by simpa only [mul_one] using h)

/-- The raw real log-Mellin pairing of a flat Schwartz test is entire. -/
public theorem differentiable_realSchwartzParityLog_mellin (b : 𝓢(ℝ, ℂ))
    (hflat : ∀ j : ℕ, iteratedDeriv j (b : ℝ → ℂ) 0 = 0) (ε : ℕ) :
    Differentiable ℂ (fun z : ℂ ↦ ∫ t : ℝ, realSchwartzParityLogProfile b ε t * Complex.exp (z * t)) :=
  fun z ↦ (hasDerivAt_realSchwartzParityLog_mellin b hflat ε z).2.2.differentiableAt

end Masullo
