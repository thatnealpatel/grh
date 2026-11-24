module

public import Lemmas.PrimeRampReplacement
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.NumberTheory.AbelSummation
import Mathlib.Tactic

/-!
# Frozen Poisson attenuation of the finite prime ramp

Source: `4c47eae3387e:.godel/bob/uncut-poisson-transfer.md:17`, used in (1).
Consumer: `.godel/bob/uncut-census-window.md:49` at pin `52090c0259f5`.
Owning check session: `01a20f88-43d7-7049-9647-cb18c5a08d70`.

Scope: The finite arithmetic estimate with the cutoff and coefficients held
fixed. This does not prove a Poisson convolution identity or transfer the whole
screen.
-/

open MeasureTheory Set
open Real (log)

namespace Masullo

/-- The Poisson multiplier differs from its cutoff value by at most the
logarithmic distance to the cutoff times the width. -/
public theorem rpow_neg_sub_le_mul_log {p V h : ℝ} (hp : 1 ≤ p) (hpV : p ≤ V)
    (hh : 0 ≤ h) : 0 ≤ p ^ (-h) - V ^ (-h) ∧ p ^ (-h) - V ^ (-h) ≤ h * log (V / p) := by
  have hp₀ := zero_lt_one.trans_le hp
  have hV₀ := hp₀.trans_le hpV
  have hl : 0 ≤ log (V / p) := Real.log_nonneg ((one_le_div hp₀).mpr hpV)
  have hfact : p ^ (-h) - V ^ (-h) = p ^ (-h) * (1 - Real.exp (-(h * log (V / p)))) := by
    rw [Real.rpow_def_of_pos hp₀, Real.rpow_def_of_pos hV₀, mul_sub, mul_one, ← Real.exp_add,
      Real.log_div hV₀.ne' hp₀.ne']
    congr 2
    ring
  refine ⟨sub_nonneg.mpr (Real.rpow_le_rpow_of_nonpos hp₀ hpV (neg_nonpos.mpr hh)), ?_⟩
  calc
    _ = _ := hfact
    _ ≤ p ^ (-h) * (h * log (V / p)) := by
      apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hp₀.le _)
      linarith only [Real.add_one_le_exp (-(h * log (V / p)))]
    _ ≤ _ := mul_le_of_le_one_left (mul_nonneg hh hl)
      (Real.rpow_le_one_of_one_le_of_nonpos hp (neg_nonpos.mpr hh))

private noncomputable def primeLogCoeff (n : ℕ) : ℝ := if n.Prime then log n else 0

private theorem sum_primeLogCoeff_eq_theta (u : ℝ) :
    (∑ n ∈ Finset.Icc 0 ⌊u⌋₊, primeLogCoeff n) = Chebyshev.theta u := by
  rw [Chebyshev.theta_eq_sum_Icc, Finset.sum_filter]
  rfl

private theorem quadraticRamp_eq_floor_sum {V : ℝ} (hV : 1 ≤ V) :
    (∑ p ∈ (primeRampSupport V).filter Nat.Prime, log (p : ℝ) * log (V / p) ^ 2) =
      ∑ n ∈ Finset.Ioc 1 ⌊V⌋₊, (log V - log (n : ℝ)) ^ 2 * primeLogCoeff n := by
  have hV₀ := zero_lt_one.trans_le hV
  calc
    _ = ∑ n ∈ (primeRampSupport V).filter Nat.Prime,
        (log V - log (n : ℝ)) ^ 2 * primeLogCoeff n := by
      refine Finset.sum_congr rfl fun n hn ↦ ?_
      obtain ⟨hnV, hnP⟩ := Finset.mem_filter.mp hn
      have hn₀ : 0 < (n : ℝ) := by exact_mod_cast hnP.pos
      rw [Real.log_div hV₀.ne' hn₀.ne', primeLogCoeff, ite_eq_left hnP, mul_comm]
    _ = _ := by
      refine Finset.sum_subset (fun n hn ↦ ?_) fun n hn hn' ↦ ?_
      · obtain ⟨hnV, hnP⟩ := Finset.mem_filter.mp hn
        exact Finset.mem_Ioc.mpr ⟨hnP.one_lt, Nat.le_floor (mem_primeRampSupport.mp hnV).2.le⟩
      · by_cases hnP : n.Prime
        · have hnV : (n : ℝ) ≤ V :=
            (Nat.le_floor_iff hV₀.le).mp (Finset.mem_Ioc.mp hn).2
          have hVn : V ≤ (n : ℝ) := le_of_not_gt fun h ↦ hn'
            (Finset.mem_filter.mpr ⟨mem_primeRampSupport.mpr ⟨hnP.one_lt.le, h⟩, hnP⟩)
          -- The only possible additional prime is exactly at the cutoff.
          simp [le_antisymm hVn hnV]
        · simp [primeLogCoeff, hnP]

/-- The normalized quadratic log ramp costs at most `2 * K` under the
Chebyshev bound on the full interval from `1` to `V`. -/
public theorem primeRamp_quadratic_le {V K : ℝ} (hV : 1 ≤ V) (hK : 0 ≤ K)
    (hθ : ∀ u : ℝ, 1 ≤ u → u ≤ V → Chebyshev.theta u ≤ K * u) :
    (∑ p ∈ (primeRampSupport V).filter Nat.Prime, log (p : ℝ) * log (V / p) ^ 2 / V) ≤
      2 * K := by
  have hV₀ := zero_lt_one.trans_le hV
  let k (u : ℝ) := 2 * (log V - log u) / u
  have hu₀ (u : ℝ) (hu : u ∈ Icc 1 V) : 0 < u := zero_lt_one.trans_le hu.1
  have hcLog : ContinuousOn log (Icc 1 V) :=
    fun u hu ↦ (Real.hasDerivAt_log (hu₀ u hu).ne').continuousAt.continuousWithinAt
  have hcK : ContinuousOn k (Icc 1 V) :=
    (continuousOn_const.mul (continuousOn_const.sub hcLog)).div continuousOn_id
      (fun u hu ↦ (hu₀ u hu).ne')
  have hd (u : ℝ) (hu : u ∈ Icc 1 V) :
      HasDerivAt (fun t : ℝ ↦ (log V - log t) ^ 2) (-k u) u := by
    convert ((hasDerivAt_const u (log V)).sub (Real.hasDerivAt_log (hu₀ u hu).ne')).pow 2
      using 1
    simp only [k, div_eq_mul_inv, Pi.sub_apply]
    ring
  have hiDeriv : IntegrableOn (deriv (fun t : ℝ ↦ (log V - log t) ^ 2)) (Icc 1 V) :=
    (hcK.neg.integrableOn_compact isCompact_Icc).congr_fun
      (fun u hu ↦ (hd u hu).deriv.symm) measurableSet_Icc
  -- Abel summation gives the quadratic kernel against the inclusive prime-log mass.
  have hAbel := sum_mul_eq_sub_sub_integral_mul primeLogCoeff zero_le_one hV
    (fun u hu ↦ (hd u hu).differentiableAt) hiDeriv
  have hθ1 : Chebyshev.theta 1 = 0 := Chebyshev.theta_eq_zero_of_lt_two (by norm_num)
  rw [← sum_primeLogCoeff_eq_theta 1, Nat.floor_one] at hθ1
  rw [Nat.floor_one, sub_self, zero_pow (by decide : (2 : ℕ) ≠ 0), zero_mul,
    hθ1, mul_zero, sub_zero, zero_sub, ← intervalIntegral.integral_of_le hV,
    ← intervalIntegral.integral_neg] at hAbel
  have hrep : (∑ p ∈ (primeRampSupport V).filter Nat.Prime, log (p : ℝ) * log (V / p) ^ 2) =
      ∫ u in (1 : ℝ)..V, k u * Chebyshev.theta u := by
    rw [quadraticRamp_eq_floor_sum hV, hAbel]
    apply intervalIntegral.integral_congr
    rw [uIcc_of_le hV]
    intro u hu
    dsimp only
    rw [(hd u hu).deriv, neg_mul, neg_neg, sum_primeLogCoeff_eq_theta]
  have hiTheta : IntervalIntegrable (fun u ↦ k u * Chebyshev.theta u) volume 1 V := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hV]
    simpa only [sum_primeLogCoeff_eq_theta] using
      integrableOn_mul_sum_Icc (m := 0) primeLogCoeff zero_le_one
        (hcK.integrableOn_compact isCompact_Icc)
  have hiUpper : IntervalIntegrable (fun u : ℝ ↦ (2 * K) * (log V - log u)) volume 1 V :=
    (continuousOn_const.mul (continuousOn_const.sub hcLog)).intervalIntegrable_of_Icc hV
  have hbound : (∫ u in (1 : ℝ)..V, k u * Chebyshev.theta u) ≤
      ∫ u in (1 : ℝ)..V, (2 * K) * (log V - log u) := by
    refine intervalIntegral.integral_mono_on hV hiTheta hiUpper fun u hu ↦ ?_
    have hlog := sub_nonneg.mpr (Real.log_le_log (hu₀ u hu) hu.2)
    calc
      _ ≤ k u * (K * u) :=
        mul_le_mul_of_nonneg_left (hθ u hu.1 hu.2) (div_nonneg (by positivity) (hu₀ u hu).le)
      _ = _ := by dsimp [k]; field_simp [(hu₀ u hu).ne']
  have harea : (∫ u in (1 : ℝ)..V, (log V - log u)) = V - 1 - log V := by
    rw [intervalIntegral.integral_sub intervalIntegrable_const (hcLog.intervalIntegrable_of_Icc hV),
      intervalIntegral.integral_const, integral_log, Real.log_one, smul_eq_mul]
    ring
  rw [← Finset.sum_div, div_le_iff₀ hV₀, hrep]
  calc
    _ ≤ _ := hbound
    _ = (2 * K) * (V - 1 - log V) := by rw [intervalIntegral.integral_const_mul, harea]
    _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith only [Real.log_nonneg hV]) (by positivity)

/-- The complex finite prime ramp changes by at most `2 * K * h` when its
pointwise Poisson multiplier is replaced by the multiplier at the fixed cutoff. -/
public theorem primeRamp_attenuation_le {V h K : ℝ} (hV : 1 ≤ V) (hh : 0 ≤ h) (hK : 0 ≤ K)
    (hθ : ∀ u : ℝ, 1 ≤ u → u ≤ V → Chebyshev.theta u ≤ K * u)
    {a : ℕ → ℂ} (ha : ∀ p ∈ (primeRampSupport V).filter Nat.Prime, ‖a p‖ ≤ 1) :
    ‖(∑ p ∈ (primeRampSupport V).filter Nat.Prime,
        (↑(log (p : ℝ) * log (V / p) / V) : ℂ) * a p * ↑((p : ℝ) ^ (-h))) -
      ↑(V ^ (-h)) * (∑ p ∈ (primeRampSupport V).filter Nat.Prime,
        (↑(log (p : ℝ) * log (V / p) / V) : ℂ) * a p)‖ ≤ 2 * K * h := by
  let s := (primeRampSupport V).filter Nat.Prime
  let w (p : ℕ) := log (p : ℝ) * log (V / p) / V
  have hV₀ := zero_lt_one.trans_le hV
  change ‖(∑ p ∈ s, (w p : ℂ) * a p * ↑((p : ℝ) ^ (-h))) -
    ↑(V ^ (-h)) * (∑ p ∈ s, (w p : ℂ) * a p)‖ ≤ _
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine (norm_sum_le _ _).trans ?_
  calc
    _ ≤ ∑ p ∈ s, h * (log (p : ℝ) * log (V / p) ^ 2 / V) := by
      refine Finset.sum_le_sum fun p hp ↦ ?_
      obtain ⟨hp₁, hpV⟩ := mem_primeRampSupport.mp (Finset.mem_filter.mp hp).1
      have hp₁' : (1 : ℝ) ≤ p := by exact_mod_cast hp₁
      have hp₀ := zero_lt_one.trans_le hp₁'
      have hl : 0 ≤ log (V / p) := Real.log_nonneg ((one_le_div hp₀).mpr hpV.le)
      have hw : 0 ≤ w p := div_nonneg (mul_nonneg (Real.log_nonneg hp₁') hl) hV₀.le
      have hδ := rpow_neg_sub_le_mul_log hp₁' hpV.le hh
      have hsplit : (w p : ℂ) * a p * ↑((p : ℝ) ^ (-h)) - ↑(V ^ (-h)) * ((w p : ℂ) * a p) =
          (w p : ℂ) * a p * ↑((p : ℝ) ^ (-h) - V ^ (-h)) := by
        rw [Complex.ofReal_sub]
        ring
      rw [hsplit]
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hw, abs_of_nonneg hδ.1]
      calc
        _ ≤ w p * 1 * (h * log (V / p)) :=
          mul_le_mul (mul_le_mul_of_nonneg_left (ha p hp) hw) hδ.2 hδ.1 (mul_nonneg hw zero_le_one)
        _ = _ := by dsimp [w]; ring
    _ = h * ∑ p ∈ s, log (p : ℝ) * log (V / p) ^ 2 / V := (Finset.mul_sum ..).symm
    _ ≤ _ := by
      rw [mul_comm (2 * K) h]
      exact mul_le_mul_of_nonneg_left (primeRamp_quadratic_le hV hK hθ) hh

/-- Unconditional frozen prime-ramp attenuation with an explicit absolute
constant from Mathlib's Chebyshev bound. -/
public theorem primeRamp_attenuation_le_absolute {V h : ℝ} (hV : 1 ≤ V) (hh : 0 ≤ h)
    {a : ℕ → ℂ} (ha : ∀ p ∈ (primeRampSupport V).filter Nat.Prime, ‖a p‖ ≤ 1) :
    ‖(∑ p ∈ (primeRampSupport V).filter Nat.Prime,
        (↑(log (p : ℝ) * log (V / p) / V) : ℂ) * a p * ↑((p : ℝ) ^ (-h))) -
      ↑(V ^ (-h)) * (∑ p ∈ (primeRampSupport V).filter Nat.Prime,
        (↑(log (p : ℝ) * log (V / p) / V) : ℂ) * a p)‖ ≤ 2 * (log 4 + 4) * h := by
  refine primeRamp_attenuation_le hV hh (by positivity) (fun u hu _ ↦ ?_) ha
  exact (Chebyshev.theta_le_psi u).trans
    (Chebyshev.psi_le_const_mul_self (zero_lt_one.trans_le hu).le)

end Masullo
