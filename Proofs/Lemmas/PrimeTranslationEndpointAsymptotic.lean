module

public import Lemmas.PrimeTranslationEndpointSchur

import Mathlib.NumberTheory.AbelSummation
import Mathlib.NumberTheory.LSeries.WeakPNT

/-! # Asymptotic prime-translation endpoint bound

Source: `bdd74f2:.godel/adhoc/prime-translation-norm.md`, lines 28–38 and 52–60.
Used for the spatially cut high-frequency piece in
`85842a8:.godel/alice/prime-conductor-window.md`, lines 52–62.
Owning check session: `01a20d17-2b2a-7097-a6d0-937638b43d97`.

Scope: the upper Schur bound, uniform in the complex `L²` input, with leading
coefficient one. The PNT supplies the Chebyshev majorant and Abel summation
bounds the reciprocal contribution. This does not address the reverse norm
bound, modulation, leakage, or the conductor inequalities themselves.
-/

open Filter MeasureTheory
open Real (exp log sqrt)
open scoped ArithmeticFunction.vonMangoldt Topology

namespace Masullo

private theorem psi_eq_sum_Icc_one (y : ℝ) :
    Chebyshev.psi y = ∑ n ∈ Finset.Icc 1 ⌊y⌋₊, Λ n := by
  simp only [Chebyshev.psi, ← Finset.Icc_add_one_left_eq_Ioc, zero_add]

private theorem exists_psi_majorant {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y : ℝ, 1 ≤ y →
      (∑ n ∈ Finset.Icc 1 ⌊y⌋₊, Λ n) ≤ (1 + ε) * y + C := by
  have hnear : ∀ᶠ y in atTop, Chebyshev.psi y / y < 1 + ε :=
    Chebyshev.tendsto_psi_div_atTop.eventually_lt_const (by linarith)
  obtain ⟨Y, hY⟩ := eventually_atTop.mp hnear
  refine ⟨Chebyshev.psi Y, Chebyshev.psi_nonneg Y, ?_⟩
  intro y hy
  rw [← psi_eq_sum_Icc_one]
  by_cases h : Y ≤ y
  · exact ((div_lt_iff₀ (zero_lt_one.trans_le hy)).mp (hY y h)).le.trans
      (le_add_of_nonneg_right (Chebyshev.psi_nonneg Y))
  · exact (Chebyshev.psi_mono (le_of_not_ge h)).trans
      (le_add_of_nonneg_left (mul_nonneg (by positivity) (zero_le_one.trans hy)))

private theorem reciprocal_vonMangoldt_le {y : ℝ} (hy : 1 ≤ y) :
    (∑ n ∈ Finset.Icc 1 ⌊y⌋₊, Λ n / (n : ℝ)) ≤ (log 4 + 4) * (1 + log y) := by
  let K : ℝ := log 4 + 4
  change _ ≤ K * (1 + log y)
  have htpos (t : ℝ) (ht : t ∈ Set.Icc 1 y) : 0 < t := zero_lt_one.trans_le ht.1
  have hderiv (t : ℝ) (ht : t ∈ Set.Icc 1 y) :
      HasDerivAt (fun x : ℝ ↦ x⁻¹) (-(t ^ 2)⁻¹) t :=
    hasDerivAt_inv (htpos t ht).ne'
  have hinv : ContinuousOn (fun t : ℝ ↦ t⁻¹) (Set.Icc 1 y) :=
    continuous_id.continuousOn.inv₀ fun t ht ↦ (htpos t ht).ne'
  have hslope : ContinuousOn (fun t : ℝ ↦ deriv (fun x : ℝ ↦ x⁻¹) t) (Set.Icc 1 y) :=
    ((hinv.pow 2).neg).congr fun t ht ↦ by
      rw [(hderiv t ht).deriv]
      change -(t ^ 2)⁻¹ = -(t⁻¹ ^ 2)
      rw [inv_pow]
  have hab := sum_mul_eq_sub_integral_mul₀ (fun n ↦ Λ n) ArithmeticFunction.map_zero
    y (fun t ht ↦ (hderiv t ht).differentiableAt) hslope.integrableOn_Icc
  simp only [← Chebyshev.psi_eq_sum_Icc] at hab
  rw [Finset.Icc_eq_cons_Ioc (Nat.zero_le ⌊y⌋₊), Finset.sum_cons] at hab
  simp only [ArithmeticFunction.map_zero, mul_zero, ← Finset.Icc_add_one_left_eq_Ioc, zero_add,
    inv_mul_eq_div] at hab
  -- Chebyshev's global linear bound controls the reciprocal main term and integral.
  have hmain : Chebyshev.psi y / y ≤ K :=
    (div_le_iff₀ (zero_lt_one.trans_le hy)).mpr
      (Chebyshev.psi_le_const_mul_self (zero_le_one.trans hy))
  have hprod : IntervalIntegrable (fun t : ℝ ↦ deriv (fun x : ℝ ↦ x⁻¹) t * Chebyshev.psi t)
      volume 1 y := by
    apply (intervalIntegrable_iff_integrableOn_Icc_of_le hy).mpr
    simpa only [← Chebyshev.psi_eq_sum_Icc] using
      integrableOn_mul_sum_Icc (m := 0) (fun n ↦ Λ n) zero_le_one hslope.integrableOn_Icc
  have hzero : 0 ∉ Set.uIcc (1 : ℝ) y := by
    rw [Set.uIcc_of_le hy]
    exact fun h ↦ (not_le_of_gt zero_lt_one) h.1
  have hlog : (∫ t in (1 : ℝ)..y, t⁻¹) = log y := by rw [integral_inv hzero, div_one]
  have hlower : -K * log y ≤ ∫ t in Set.Ioc 1 y, deriv (fun x : ℝ ↦ x⁻¹) t * Chebyshev.psi t := by
    rw [← intervalIntegral.integral_of_le hy, ← hlog, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_mono_on hy
      ((intervalIntegrable_iff_integrableOn_Icc_of_le hy).mpr
        (continuousOn_const.mul hinv).integrableOn_Icc) hprod ?_
    intro t ht
    rw [(hderiv t ht).deriv]
    calc
      -K * t⁻¹ = -(t ^ 2)⁻¹ * (K * t) := by field_simp [(htpos t ht).ne']
      _ ≤ -(t ^ 2)⁻¹ * Chebyshev.psi t :=
        mul_le_mul_of_nonpos_left (Chebyshev.psi_le_const_mul_self (htpos t ht).le)
          (neg_nonpos.mpr (inv_nonneg.mpr (sq_nonneg t)))
  linarith only [hab, hmain, hlower]

private theorem eventually_affine_lt_exp (C K : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ D : ℝ in atTop, C + K * (1 + D) < δ * exp (D / 2) := by
  have hlin : Tendsto (fun t : ℝ ↦ t * exp (-t)) atTop (𝓝 0) := by
    simpa only [pow_one] using Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1
  have hsum : Tendsto (fun t : ℝ ↦ (C + K) * exp (-t) + (2 * K) * (t * exp (-t)))
      atTop (𝓝 0) := by
    simpa only [mul_zero, add_zero] using
      (Real.tendsto_exp_neg_atTop_nhds_zero.const_mul (C + K)).add (hlin.const_mul (2 * K))
  have hhalf : Tendsto (fun D : ℝ ↦ D / 2) atTop atTop :=
    Tendsto.atTop_div_const (by norm_num) tendsto_id
  filter_upwards [(hsum.comp hhalf).eventually_lt_const hδ] with D hD
  apply (div_lt_iff₀ (Real.exp_pos (D / 2))).mp
  calc
    (C + K * (1 + D)) / exp (D / 2) =
        (C + K) * exp (-(D / 2)) + (2 * K) * (D / 2 * exp (-(D / 2))) := by
      rw [div_eq_mul_inv, ← Real.exp_neg]
      ring
    _ < δ := hD

/-- For each `η > 0`, the endpoint Schur bound has cost at most
`(1 + η) * exp (D / 2)` for all sufficiently large real `D`, uniformly over
complex `L²` inputs supported almost everywhere on `[0,D]`. The prime-power
correlations retain the factor two and strict cutoff `n < exp D`. -/
public theorem primeTranslationEndpointAsymptotic {η : ℝ} (hη : 0 < η) :
    ∀ᶠ D : ℝ in atTop, ∀ {u : ℝ → ℂ}, MemLp u 2 volume →
      (∀ᵐ x ∂volume, x ∉ Set.Icc 0 D → u x = 0) →
      2 * (∑ n ∈ Finset.Ico 1 ⌈exp D⌉₊, Λ n / sqrt n *
        ∫ x : ℝ, ‖u x‖ * ‖u (x + log n)‖) ≤
        (1 + η) * exp (D / 2) * ∫ x : ℝ, ‖u x‖ ^ 2 := by
  let δ : ℝ := η / 2
  let K : ℝ := log 4 + 4
  have hδ : 0 < δ := half_pos hη
  have hK : 0 ≤ K := add_nonneg (Real.log_nonneg (by norm_num)) (by norm_num)
  obtain ⟨C, hC, hψ⟩ := exists_psi_majorant hδ
  filter_upwards [eventually_gt_atTop (0 : ℝ), eventually_affine_lt_exp C K hδ] with D hD herr
  intro u hu huzero
  have hB : 0 ≤ K * (1 + D) := mul_nonneg hK (by linarith)
  have hrec : (∑ n ∈ Finset.Icc 1 ⌊exp D⌋₊, Λ n / (n : ℝ)) ≤ K * (1 + D) := by
    simpa only [Real.log_exp] using reciprocal_vonMangoldt_le (Real.one_le_exp hD.le)
  have hschur := primeTranslationEndpointSchur hD hδ.le hC hB (fun y hy _ ↦ hψ y hy) hrec hu huzero
  refine hschur.trans ?_
  refine mul_le_mul_of_nonneg_right ?_ (integral_nonneg fun x ↦ sq_nonneg ‖u x‖)
  dsimp only [δ] at herr ⊢
  linarith only [herr]

end Masullo
