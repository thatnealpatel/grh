module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.NumberTheory.Chebyshev
import Mathlib.Tactic

/-! # Real-cutoff replacement for the normalized von Mangoldt ramp

Source: `bbca37033019:.godel/bob/fixed-strip-endpoints.md`, lines 39–43
(higher prime powers: lines 29–34).
Consumer: `b3723e8a43ba:.godel/bob/twist-endpoint-packet.md`, lines 11–17.
Owning check session: `01a20f35-88fa-72a0-aedd-8c10c7068d1c`.

The all-von-Mangoldt mean in `Lemmas.SignedEndpointRamp` uses the strict
cutoff below. This file bounds the total variation upon changing its real
cutoff and the total mass discarded by restricting to primes. The estimates
are absolute; in particular they need no regularity in a bounded twist.
-/

open Real (log)
open scoped ArithmeticFunction.vonMangoldt

namespace Masullo

/-- Positive integers strictly below the real cutoff. -/
public noncomputable def primeRampSupport (X : ℝ) : Finset ℕ := Finset.Ico 1 ⌈X⌉₊

/-- The normalized logarithmic ramp, extended by zero off its strict support. -/
public noncomputable def vonMangoldtRampWeight (X : ℝ) (n : ℕ) : ℝ :=
  Λ n * max (log (X / n)) 0 / X

private noncomputable def rampNumerator (X : ℝ) (n : ℕ) : ℝ :=
  Λ n * max (log (X / n)) 0

private theorem rampNumerator_nonneg (X : ℝ) (n : ℕ) : 0 ≤ rampNumerator X n :=
  mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (le_max_right ..)

/-- Membership expresses the strict real inequality, not a floor cutoff. -/
public theorem mem_primeRampSupport {X : ℝ} {n : ℕ} :
    n ∈ primeRampSupport X ↔ 1 ≤ n ∧ (n : ℝ) < X := by
  rw [primeRampSupport, Finset.mem_Ico, Nat.lt_ceil]

private theorem primeRampSupport_mono {X Y : ℝ} (hXY : X ≤ Y) :
    primeRampSupport X ⊆ primeRampSupport Y := fun _ hn ↦
  let ⟨hn₁, hnX⟩ := mem_primeRampSupport.mp hn
  mem_primeRampSupport.mpr ⟨hn₁, hnX.trans_le hXY⟩

private theorem rampNumerator_eq_zero_off_support {X : ℝ} (hX : 0 < X) {n : ℕ}
    (hn : n ∉ primeRampSupport X) : rampNumerator X n = 0 := by
  by_cases hn₀ : n = 0
  · simp [rampNumerator, hn₀]
  have hn₁ : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn₀
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn₀
  have hXn : X ≤ (n : ℝ) := le_of_not_gt fun h ↦ hn (mem_primeRampSupport.mpr ⟨hn₁, h⟩)
  have hl : log (X / n) ≤ 0 := Real.log_nonpos (by positivity) ((div_le_one hnpos).mpr hXn)
  simp [rampNumerator, max_eq_right hl]

/-- In particular an integer exactly equal to the cutoff carries zero weight. -/
public theorem vonMangoldtRampWeight_eq_zero_off_support {X : ℝ} (hX : 0 < X) {n : ℕ}
    (hn : n ∉ primeRampSupport X) : vonMangoldtRampWeight X n = 0 := by
  change rampNumerator X n / X = 0
  rw [rampNumerator_eq_zero_off_support hX hn, zero_div]

/-- On the strict finite support this is the weight in the signed endpoint mean. -/
public theorem vonMangoldtRampWeight_eq_on_support {X : ℝ} {n : ℕ}
    (hn : n ∈ primeRampSupport X) : vonMangoldtRampWeight X n = Λ n * log (X / n) / X := by
  obtain ⟨hn₁, hnX⟩ := mem_primeRampSupport.mp hn
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (zero_lt_one.trans_le hn₁)
  have hl : 0 ≤ log (X / n) := Real.log_nonneg ((one_le_div hnpos).mpr hnX.le)
  simp only [vonMangoldtRampWeight, max_eq_left hl]

local notation "Kψ" => (log 4 + 4 : ℝ)

private theorem sum_vonMangoldt_le {X : ℝ} (hX : 0 ≤ X) :
    (∑ n ∈ primeRampSupport X, Λ n) ≤ Kψ * X := by
  refine le_trans ?_ (Chebyshev.psi_le_const_mul_self hX)
  rw [Chebyshev.psi_eq_sum_Icc]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro n hn
    obtain ⟨_, hnX⟩ := mem_primeRampSupport.mp hn
    exact Finset.mem_Icc.mpr ⟨Nat.zero_le n, Nat.le_floor hnX.le⟩
  · exact fun _ _ _ ↦ ArithmeticFunction.vonMangoldt_nonneg

private theorem rampNumerator_increment {X Y : ℝ} (hX : 0 < X) (hXY : X ≤ Y) {n : ℕ}
    (hn : 1 ≤ n) : 0 ≤ rampNumerator Y n - rampNumerator X n ∧
      rampNumerator Y n - rampNumerator X n ≤ Λ n * log (Y / X) := by
  have hY := hX.trans_le hXY
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (zero_lt_one.trans_le hn)
  have hd : 0 ≤ log (Y / X) := Real.log_nonneg ((one_le_div hX).mpr hXY)
  have hadd : log (Y / n) = log (X / n) + log (Y / X) := by
    rw [Real.log_div hY.ne' hnpos.ne', Real.log_div hX.ne' hnpos.ne', Real.log_div hY.ne' hX.ne']
    ring
  have hmono : max (log (X / n)) 0 ≤ max (log (Y / n)) 0 := by
    apply max_le_max _ le_rfl
    linarith
  have hup : max (log (Y / n)) 0 ≤ max (log (X / n)) 0 + log (Y / X) := by
    refine max_le ?_ (add_nonneg (le_max_right ..) hd)
    rw [hadd]
    exact add_le_add (le_max_left (log (X / n)) 0) le_rfl
  simp only [rampNumerator, ← mul_sub]
  exact ⟨mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (sub_nonneg.mpr hmono),
    mul_le_mul_of_nonneg_left (sub_le_iff_le_add.mpr (by simpa [add_comm] using hup))
      ArithmeticFunction.vonMangoldt_nonneg⟩

private theorem sum_rampNumerator_increment_le {X Y : ℝ} (hX : 0 < X) (hXY : X ≤ Y) :
    (∑ n ∈ primeRampSupport Y, (rampNumerator Y n - rampNumerator X n)) ≤
      Kψ * Y * log (Y / X) := calc
  _ ≤ ∑ n ∈ primeRampSupport Y, Λ n * log (Y / X) := by
    exact Finset.sum_le_sum fun _ hn ↦ (rampNumerator_increment hX hXY
      (mem_primeRampSupport.mp hn).1).2
  _ ≤ _ := by
    rw [← Finset.sum_mul]
    exact mul_le_mul_of_nonneg_right (sum_vonMangoldt_le (hX.le.trans hXY))
      (Real.log_nonneg ((one_le_div hX).mpr hXY))

private theorem sum_rampNumerator_eq_common {X Y : ℝ} (hX : 0 < X) (hXY : X ≤ Y) :
    (∑ n ∈ primeRampSupport X, rampNumerator X n) =
      ∑ n ∈ primeRampSupport Y, rampNumerator X n :=
  Finset.sum_subset (primeRampSupport_mono hXY) fun _ _ h ↦ rampNumerator_eq_zero_off_support hX h

private theorem sum_rampNumerator_le {X : ℝ} (hX : 1 ≤ X) :
    (∑ n ∈ primeRampSupport X, rampNumerator X n) ≤ 2 * Kψ * X := by
  -- Halving the cutoff costs at most `Kψ * Y * log 2` in unnormalized mass.
  have main (m : ℕ) (Y : ℝ) (hY : 1 ≤ Y) (hm : Y ≤ m) :
      (∑ n ∈ primeRampSupport Y, rampNumerator Y n) ≤ 2 * Kψ * Y := by
    induction m generalizing Y with
    | zero => simp at hm; linarith
    | succ m ih =>
      by_cases hY₂ : 2 ≤ Y
      · have hsmall : 1 ≤ Y / 2 := by linarith
        have hm' : Y / 2 ≤ (m : ℝ) := by push_cast at hm; linarith
        have hhalf : Y / 2 ≤ Y := by linarith
        have hpos : 0 < Y / 2 := by positivity
        have hratio : Y / (Y / 2) = 2 := by field_simp [hpos.ne']
        have hincr := sum_rampNumerator_increment_le hpos hhalf
        rw [Finset.sum_sub_distrib, ← sum_rampNumerator_eq_common hpos hhalf, hratio] at hincr
        have hlog : log 2 ≤ 1 := by
          have hl := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
          norm_num at hl
          exact hl
        have hcost : Kψ * Y * log 2 ≤ Kψ * Y := by
          simpa using mul_le_mul_of_nonneg_left hlog (show 0 ≤ Kψ * Y by positivity)
        linarith only [hincr, hcost, ih (Y / 2) hsmall hm']
      · have hz (n : ℕ) (hn : n ∈ primeRampSupport Y) : rampNumerator Y n = 0 := by
          obtain ⟨hn₁, hnY⟩ := mem_primeRampSupport.mp hn
          have hn₂ : n < 2 := by exact_mod_cast hnY.trans_le (le_of_not_ge hY₂)
          have hn_eq : n = 1 := by omega
          simp [rampNumerator, hn_eq, ArithmeticFunction.vonMangoldt_apply_one]
        rw [Finset.sum_eq_zero hz]
        positivity
  exact main ⌈X⌉₊ X hX (Nat.le_ceil X)

/-- Total absolute variation on the common support. The old ramp is extended
by zero up to the new cutoff. The constant is absolute. -/
public theorem vonMangoldtRamp_totalVariation_le {X Y : ℝ} (hX : 1 ≤ X) (hXY : X ≤ Y) :
    (∑ n ∈ primeRampSupport Y, |vonMangoldtRampWeight Y n - vonMangoldtRampWeight X n|) ≤
      3 * Kψ * log (Y / X) := by
  have hXp : 0 < X := zero_lt_one.trans_le hX
  have hYp := hXp.trans_le hXY
  have hnorm₀ : 0 ≤ 1 - X / Y := sub_nonneg.mpr ((div_le_one hYp).mpr hXY)
  have hnorm : 1 - X / Y ≤ log (Y / X) := by
    simpa only [inv_div] using Real.one_sub_inv_le_log_of_pos (div_pos hYp hXp)
  have hmass : (∑ n ∈ primeRampSupport Y, vonMangoldtRampWeight X n) ≤ 2 * Kψ := by
    change (∑ n ∈ primeRampSupport Y, rampNumerator X n / X) ≤ _
    rw [← Finset.sum_div, ← sum_rampNumerator_eq_common hXp hXY]
    exact (div_le_iff₀ hXp).mpr (sum_rampNumerator_le hX)
  calc
    _ ≤ ∑ n ∈ primeRampSupport Y, ((rampNumerator Y n - rampNumerator X n) / Y +
        (1 - X / Y) * vonMangoldtRampWeight X n) := by
      refine Finset.sum_le_sum fun n hn ↦ ?_
      have hsplit : vonMangoldtRampWeight Y n - vonMangoldtRampWeight X n =
          (rampNumerator Y n - rampNumerator X n) / Y - (1 - X / Y) * vonMangoldtRampWeight X n := by
        change rampNumerator Y n / Y - rampNumerator X n / X = _
        change _ = _ - (1 - X / Y) * (rampNumerator X n / X)
        field_simp [hXp.ne', hYp.ne']
        ring
      rw [hsplit]
      have hleft := div_nonneg (rampNumerator_increment hXp hXY
        (mem_primeRampSupport.mp hn).1).1 hYp.le
      have hright : 0 ≤ (1 - X / Y) * vonMangoldtRampWeight X n :=
        mul_nonneg hnorm₀ (div_nonneg (rampNumerator_nonneg X n) hXp.le)
      simpa only [← sub_eq_add_neg, abs_neg, abs_of_nonneg hleft, abs_of_nonneg hright] using
        abs_add_le ((rampNumerator Y n - rampNumerator X n) / Y)
          (-((1 - X / Y) * vonMangoldtRampWeight X n))
    _ ≤ Kψ * log (Y / X) + (2 * Kψ) * log (Y / X) := by
      rw [Finset.sum_add_distrib, ← Finset.sum_div, ← Finset.mul_sum]
      refine add_le_add ((div_le_iff₀ hYp).mpr ?_) ?_
      · rw [mul_right_comm]
        exact sum_rampNumerator_increment_le hXp hXY
      · calc
          _ ≤ (1 - X / Y) * (2 * Kψ) := mul_le_mul_of_nonneg_left hmass hnorm₀
          _ ≤ _ := by
            rw [mul_comm (1 - X / Y)]
            exact mul_le_mul_of_nonneg_left hnorm (show 0 ≤ 2 * Kψ by positivity)
    _ = _ := by ring

private theorem higherPower_card_le {X : ℝ} (hX : 1 ≤ X) (s : Finset ℕ)
    (hs : ∀ n ∈ s, n ∈ primeRampSupport X ∧ ¬ n.Prime ∧ IsPrimePow n) :
    (s.card : ℝ) ≤ √X * (log (2 * X) / log 2) := by
  have hlog2 : 0 < log 2 := Real.log_pos (by norm_num)
  have hL : 0 ≤ log (2 * X) / log 2 := by
    exact div_nonneg (Real.log_nonneg (by linarith)) hlog2.le
  let B := Finset.Icc 1 ⌊√X⌋₊ ×ˢ Finset.Icc 1 ⌊log (2 * X) / log 2⌋₊
  have hcover : s ⊆ B.image (fun pk : ℕ × ℕ ↦ pk.1 ^ pk.2) := by
    intro n hn
    obtain ⟨hnX, hnp, hpp⟩ := hs n hn
    obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff n).mp hpp
    have hk₂ : 2 ≤ k := by
      by_contra! h
      have hk₁ : k = 1 := by omega
      exact hnp (by simpa only [hk₁, pow_one] using hp)
    have hcut := (mem_primeRampSupport.mp hnX).2
    have hcut' : (p : ℝ) ^ k ≤ X := by exact_mod_cast hcut.le
    have hp_sq : (p : ℝ) ^ 2 ≤ X :=
      (show (p : ℝ) ^ 2 ≤ (p : ℝ) ^ k by
        exact_mod_cast Nat.pow_le_pow_right hp.pos hk₂).trans hcut'
    have hp_le : (p : ℝ) ≤ √X := Real.le_sqrt_of_sq_le hp_sq
    have h2k : (2 : ℝ) ^ k ≤ X :=
      (show (2 : ℝ) ^ k ≤ (p : ℝ) ^ k by
        exact_mod_cast Nat.pow_le_pow_left hp.two_le k).trans hcut'
    have hk_le : (k : ℝ) ≤ log (2 * X) / log 2 := by
      apply (le_div_iff₀ hlog2).mpr
      rw [← Real.log_pow]
      exact Real.log_le_log (by positivity) (h2k.trans (by linarith))
    refine Finset.mem_image.mpr ⟨(p, k), Finset.mem_product.mpr ⟨?_, ?_⟩, rfl⟩
    · exact Finset.mem_Icc.mpr ⟨hp.one_lt.le, Nat.le_floor hp_le⟩
    · exact Finset.mem_Icc.mpr ⟨hk, Nat.le_floor hk_le⟩
  have hcard : s.card ≤ B.card := (Finset.card_le_card hcover).trans Finset.card_image_le
  calc
    (s.card : ℝ) ≤ (B.card : ℝ) := by exact_mod_cast hcard
    _ = (⌊√X⌋₊ : ℕ) * (⌊log (2 * X) / log 2⌋₊ : ℕ) := by
      simp [B, Finset.card_product, Nat.card_Icc]
    _ ≤ _ := by
      exact mul_le_mul (Nat.floor_le (Real.sqrt_nonneg X)) (Nat.floor_le hL)
        (Nat.cast_nonneg _) (Real.sqrt_nonneg X)

private theorem abs_rampWeight_le {X : ℝ} (hX : 1 ≤ X) {n : ℕ}
    (hn : n ∈ primeRampSupport X) : |vonMangoldtRampWeight X n| ≤ log (2 * X) ^ 2 / X := by
  obtain ⟨hn₁, hnX⟩ := mem_primeRampSupport.mp hn
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (zero_lt_one.trans_le hn₁)
  have hnreal : (1 : ℝ) ≤ n := by exact_mod_cast hn₁
  have hXp := zero_lt_one.trans_le hX
  have hlog : 0 ≤ log (2 * X) := Real.log_nonneg (by linarith)
  have hΛ : Λ n ≤ log (2 * X) :=
    ArithmeticFunction.vonMangoldt_le_log.trans (Real.log_le_log hnpos (by linarith))
  have hramp : max (log (X / n)) 0 ≤ log (2 * X) := by
    refine max_le (Real.log_le_log (div_pos hXp hnpos) ?_) hlog
    exact (div_le_self hXp.le hnreal).trans (by linarith)
  have hw₀ : 0 ≤ vonMangoldtRampWeight X n :=
    div_nonneg (rampNumerator_nonneg X n) hXp.le
  rw [abs_of_nonneg hw₀, vonMangoldtRampWeight, pow_two]
  exact div_le_div_of_nonneg_right (mul_le_mul hΛ hramp (le_max_right ..) hlog) hXp.le

/-- The absolute mass discarded when restricting the ramp to primes. The
nonzero discarded terms are higher prime powers, counted by a finite cover. -/
public theorem vonMangoldtRamp_higherPowerMass_le {X : ℝ} (hX : 1 ≤ X) :
    (∑ n ∈ (primeRampSupport X).filter (fun n ↦ ¬ n.Prime), |vonMangoldtRampWeight X n|) ≤
      (log 2)⁻¹ * (X ^ (-(1 / 2) : ℝ) * log (2 * X) ^ 3) := by
  classical
  have hXp := zero_lt_one.trans_le hX
  let T := (primeRampSupport X).filter (fun n ↦ ¬ n.Prime)
  let S := T.filter (fun n ↦ Λ n ≠ 0)
  have hzero : (∑ n ∈ S, |vonMangoldtRampWeight X n|) = ∑ n ∈ T, |vonMangoldtRampWeight X n| := by
    refine Finset.sum_subset (Finset.filter_subset _ _) fun n hn hnS ↦ ?_
    have h : Λ n = 0 := by simpa [S, hn] using hnS
    simp [vonMangoldtRampWeight, h]
  have hmem (n : ℕ) (hn : n ∈ S) : n ∈ primeRampSupport X ∧ ¬ n.Prime ∧ IsPrimePow n := by
    obtain ⟨hnT, hnΛ⟩ := Finset.mem_filter.mp hn
    exact ⟨(Finset.mem_filter.mp hnT).1, (Finset.mem_filter.mp hnT).2,
      ArithmeticFunction.vonMangoldt_ne_zero_iff.mp hnΛ⟩
  change (∑ n ∈ T, |vonMangoldtRampWeight X n|) ≤ _
  rw [← hzero]
  calc
    _ ≤ ∑ _n ∈ S, log (2 * X) ^ 2 / X :=
      Finset.sum_le_sum fun n hn ↦ abs_rampWeight_le hX (hmem n hn).1
    _ = (S.card : ℝ) * (log (2 * X) ^ 2 / X) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (√X * (log (2 * X) / log 2)) * (log (2 * X) ^ 2 / X) :=
      mul_le_mul_of_nonneg_right (higherPower_card_le hX S hmem) (by positivity)
    _ = _ := by
      rw [show (-(1 / 2) : ℝ) = 1 / 2 - 1 by norm_num, Real.rpow_sub hXp, Real.rpow_one,
        ← Real.sqrt_eq_rpow]
      ring

/-- Taking real parts recovers exactly the all-von-Mangoldt mean in the
signed endpoint quotient, for its twist or any other complex coefficients. -/
public theorem vonMangoldtRamp_twist_re_eq (X : ℝ) (z : ℕ → ℂ) :
    (∑ n ∈ primeRampSupport X, (vonMangoldtRampWeight X n : ℂ) * z n).re =
      X⁻¹ * ∑ n ∈ primeRampSupport X, Λ n * (z n).re * log (X / n) := by
  rw [Complex.re_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun n hn ↦ ?_
  rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
    vonMangoldtRampWeight_eq_on_support hn]
  ring

private theorem norm_twisted_sum_le (s : Finset ℕ) (a : ℕ → ℝ) {z : ℕ → ℂ} {B : ℝ}
    (hz : ∀ n, ‖z n‖ ≤ B) :
    ‖∑ n ∈ s, (a n : ℂ) * z n‖ ≤ B * ∑ n ∈ s, |a n| := calc
  _ ≤ ∑ n ∈ s, ‖(a n : ℂ) * z n‖ := norm_sum_le _ _
  _ ≤ ∑ n ∈ s, B * |a n| := by
    refine Finset.sum_le_sum fun n _ ↦ ?_
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_comm B]
    exact mul_le_mul_of_nonneg_left (hz n) (abs_nonneg _)
  _ = _ := (Finset.mul_sum ..).symm

/-- The same bounded phase can be kept at the two cutoffs, with no regularity assumption. -/
public theorem vonMangoldtRamp_twist_cutoff_le {X Y B : ℝ} (hX : 1 ≤ X) (hXY : X ≤ Y)
    {z : ℕ → ℂ} (hz : ∀ n, ‖z n‖ ≤ B) :
    ‖(∑ n ∈ primeRampSupport Y, (vonMangoldtRampWeight Y n : ℂ) * z n) -
      ∑ n ∈ primeRampSupport X, (vonMangoldtRampWeight X n : ℂ) * z n‖ ≤
      B * (3 * Kψ * log (Y / X)) := by
  have hB := (norm_nonneg (z 1)).trans (hz 1)
  have hcommon : (∑ n ∈ primeRampSupport X, (vonMangoldtRampWeight X n : ℂ) * z n) =
      ∑ n ∈ primeRampSupport Y, (vonMangoldtRampWeight X n : ℂ) * z n := by
    refine Finset.sum_subset (primeRampSupport_mono hXY) fun n _ hn ↦ ?_
    simp [vonMangoldtRampWeight_eq_zero_off_support (zero_lt_one.trans_le hX) hn]
  rw [hcommon, ← Finset.sum_sub_distrib]
  simp only [← sub_mul, ← Complex.ofReal_sub]
  exact (norm_twisted_sum_le _ _ hz).trans
    (mul_le_mul_of_nonneg_left (vonMangoldtRamp_totalVariation_le hX hXY) hB)

/-- With any bounded phase, the normalized von Mangoldt mean differs from the
prime mean with weights `log p * log (X / p) / X` by at most the discarded mass
times the phase bound. -/
public theorem vonMangoldtRamp_twist_prime_le {X B : ℝ} (hX : 1 ≤ X) {z : ℕ → ℂ}
    (hz : ∀ n, ‖z n‖ ≤ B) :
    ‖(∑ n ∈ primeRampSupport X, (vonMangoldtRampWeight X n : ℂ) * z n) -
      ∑ p ∈ (primeRampSupport X).filter Nat.Prime,
        ((log (p : ℝ) * log (X / p) / X : ℝ) : ℂ) * z p‖ ≤
      B * ((log 2)⁻¹ * (X ^ (-(1 / 2) : ℝ) * log (2 * X) ^ 3)) := by
  have hB := (norm_nonneg (z 1)).trans (hz 1)
  have hprime : (∑ p ∈ (primeRampSupport X).filter Nat.Prime,
      (vonMangoldtRampWeight X p : ℂ) * z p) =
      ∑ p ∈ (primeRampSupport X).filter Nat.Prime,
        ((log (p : ℝ) * log (X / p) / X : ℝ) : ℂ) * z p := by
    refine Finset.sum_congr rfl fun p hp ↦ ?_
    obtain ⟨hpX, hpprime⟩ := Finset.mem_filter.mp hp
    rw [vonMangoldtRampWeight_eq_on_support hpX, ArithmeticFunction.vonMangoldt_apply_prime hpprime]
  rw [← hprime, ← Finset.sum_filter_add_sum_filter_not (primeRampSupport X) Nat.Prime
    (fun n ↦ (vonMangoldtRampWeight X n : ℂ) * z n), add_sub_cancel_left]
  exact (norm_twisted_sum_le _ _ hz).trans
    (mul_le_mul_of_nonneg_left (vonMangoldtRamp_higherPowerMass_le hX) hB)

end Masullo
