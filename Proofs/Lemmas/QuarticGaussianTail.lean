module

import Lemmas.QuarticThetaPoisson
import all Lemmas.CappedDyadicTail
public import Lemmas.PositiveLogBumpDecay
public import Lemmas.QuarticGaussianZeroCount
import all Lemmas.QuarticGaussianZeroCount

/-! # The normalized absolute tail of the quartic Gaussian zero sum

The sum is indexed by distinct real ordinates, retaining both signs and
excluding both cutoff endpoints. No finite-head or operator assertion is made.
-/

open Complex MeasureTheory

namespace Masullo

/-- The critical-line zeros above the truncation height, in absolute height. -/
public abbrev QuarticGaussianTailZero :=
  {t : ℝ // QuarticGaussianD (QuarticGaussianLine t) = 0 ∧ 8192 < |t|}

/-- Absolute contribution at one ordinate, with order capped at two and with
no norm-one Haar volume in the Fourier integral. -/
public noncomputable def quarticGaussianTailTerm (t : QuarticGaussianTailZero) : ℝ :=
  (QuarticGaussianCappedOrder t.val : ℝ) * ‖∫ x : ℝ, (PositiveLogBumpDecay.b x : ℂ) *
    Complex.exp (I * (t.val : ℂ) * (x : ℂ))‖

/-- The two stated Gaussian estimates suffice for the absolute-tail budget. -/
public theorem quarticGaussianTail_bound_of_decay
    (hB : ∀ x : ℝ, ‖QuarticGaussianB x‖ ≤ 234 * Real.exp (3 * |x| - Real.exp |x| / 2))
    (hc : (1 / 1000 : ℝ) ≤ ‖QuarticGaussianD 6‖) :
    Summable quarticGaussianTailTerm ∧
      (∑' t, quarticGaussianTailTerm t) ≤ (425984 : ℝ) / 10 ^ 12 ∧
      (425984 : ℝ) / 10 ^ 12 < 1 / 1000 := by
  classical
  apply cappedDyadicTail_bound (fun t : QuarticGaussianTailZero ↦ t.val)
    (fun t ↦ (QuarticGaussianCappedOrder t.val : ℝ))
    (fun t ↦ ‖∫ x : ℝ, (PositiveLogBumpDecay.b x : ℂ) *
      Complex.exp (I * (t.val : ℂ) * (x : ℂ))‖)
    (fun t ↦ t.property.2) (fun _ ↦ Nat.cast_nonneg _) (fun _ ↦ norm_nonneg _)
  · intro j A hA
    let e : QuarticGaussianTailZero ↪ ℝ := ⟨Subtype.val, Subtype.val_injective⟩
    have h := QuarticGaussian_sum_capped_band_le_of_decay hB hc j (A.map e) (by
      intro t ht
      obtain ⟨u, hu, rfl⟩ := Finset.mem_map.mp ht
      exact ⟨u.property.1, hA u hu⟩)
    rw [Finset.sum_map] at h
    exact_mod_cast h
  · intro j t ht
    exact PositiveLogBumpDecay.norm_integral_le j t.val (by simpa [mul_comm] using ht.1)

/-- The normalized zero tail, conditional only on the negative-log Poisson identity. -/
public theorem quarticGaussianTail_bound_of_poisson
    (hpoisson : ∀ x : ℝ, x < 0 → QuarticGaussianB x =
      (1 / 32 : ℂ) * (Real.exp (-3 * x) : ℂ) *
        ∑' a : ℤ × ℤ, QuarticGaussianLattice a ^ 4 *
          (Real.exp (-(Real.pi / 2 * Real.exp (-x) * ‖QuarticGaussianLattice a‖ ^ 2)) : ℂ)) :
    Summable quarticGaussianTailTerm ∧
      (∑' t, quarticGaussianTailTerm t) ≤ (425984 : ℝ) / 10 ^ 12 ∧
      (425984 : ℝ) / 10 ^ 12 < 1 / 1000 :=
  quarticGaussianTail_bound_of_decay (QuarticGaussianB_decay_of_poisson hpoisson)
    QuarticGaussianD_center_lower_bound

/-- Absolute tail bound for the quartic Gaussian singleton. -/
public theorem quarticGaussianTail_bound :
    Summable quarticGaussianTailTerm ∧
      (∑' t, quarticGaussianTailTerm t) ≤ (425984 : ℝ) / 10 ^ 12 ∧
      (425984 : ℝ) / 10 ^ 12 < 1 / 1000 := by
  apply quarticGaussianTail_bound_of_poisson
  intro x hx
  exact quarticTheta_poisson x hx

end Masullo
