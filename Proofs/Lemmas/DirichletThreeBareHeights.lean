module

public import Theorems.PadicRamifiedThreeFourier
public import Mathlib.Analysis.Calculus.LogDeriv
public import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Lemmas.DirichletLFunctionGrowth
import Lemmas.NegFiveHorizontalInverse
import Mathlib.Analysis.Complex.Liouville

/-!
# Bare Dirichlet good heights for the quadratic character modulo three

The analytic disk bound supplies an upper edge for the bare `L`-function.
Real coefficients give the lower edge at the same height; Cauchy's estimate
then bounds the logarithmic derivative on both entire segments.
-/

open Complex Set
open Metric
open scoped ComplexConjugate

namespace Masullo

/-- For the bare Dirichlet `L`-function of the quadratic character modulo
three, one height in every indicated interval gives nonvanishing and a
uniform polynomial logarithmic-derivative bound on both closed segments. -/
public theorem padicRamifiedThree_bare_good_heights :
    ∃ (C : ℝ) (m : ℕ), 0 < C ∧ ∀ H : ℝ, 1 ≤ H → ∃ T ∈ Ioo H (H + 1),
      ∀ σ ∈ Icc (-1 / 2 : ℝ) (3 / 2), ∀ t : ℝ, |t| = T →
        let s := (σ : ℂ) + (t : ℂ) * I
        padicRamifiedThreeCharacter.LFunction s ≠ 0 ∧
          ‖logDeriv padicRamifiedThreeCharacter.LFunction s‖ ≤ C * (1 + T) ^ m := by
  let χ := padicRamifiedThreeCharacter
  let f := χ.LFunction
  have hχ : χ ≠ 1 := by
    intro h
    have hc := DirichletCharacter.eq_one_iff_conductor_eq_one.mp h
    have hp : χ.conductor = 3 ^ 1 := padicRamifiedThreeCharacter_isPrimitive
    rw [hp] at hc
    norm_num at hc
  have hf : Differentiable ℂ f := DirichletCharacter.differentiable_LFunction hχ
  have hconj (s : ℂ) : f (conj s) = conj (f s) :=
    dirichletLFunction_conj_of_real χ hχ (fun n ↦ padicRamifiedThreeCharacter_conj n) s
  obtain ⟨b, hb, hanchor⟩ := exists_dirichlet_anchor_at (show (1 : ℝ) < 2 by norm_num)
  obtain ⟨D, hD, hgrowth⟩ := exists_dirichlet_LFunction_growth_closed_halfPlane χ hχ
  have hcircle (H : ℝ) (hH : 1 ≤ H) (z : ℂ)
      (hz : z ∈ sphere (2 + ((H + 1 / 2 : ℝ) : ℂ) * I) 6) :
      ‖f z‖ ≤ (D * 16 ^ (6 : ℕ)) * H ^ (6 : ℕ) := by
    let c : ℂ := 2 + ((H + 1 / 2 : ℝ) : ℂ) * I
    have hd : ‖z - c‖ = 6 := by simpa only [mem_sphere, dist_eq_norm] using hz
    have hcr : c.re = 2 := by simp [c]
    have hci : c.im = H + 1 / 2 := by simp [c]
    have hre : -4 ≤ z.re := by
      have hr := Complex.abs_re_le_norm (z - c)
      rw [hd, sub_re, hcr] at hr
      linarith [(abs_le.mp hr).1]
    have hc : ‖c‖ ≤ H + 5 / 2 := by
      refine (norm_le_abs_re_add_abs_im c).trans ?_
      rw [hcr, hci, abs_of_nonneg (by linarith : 0 ≤ H + 1 / 2)]
      norm_num
      linarith
    have hz' : ‖z‖ + 6 ≤ 16 * H := by
      have hz'' : ‖z‖ ≤ ‖z - c‖ + ‖c‖ := by
        simpa only [sub_add_cancel] using norm_add_le (z - c) c
      linarith
    calc
      ‖f z‖ ≤ D * (‖z‖ + 6) ^ 6 := hgrowth z hre
      _ ≤ D * (16 * H) ^ 6 := by gcongr
      _ = _ := by rw [mul_pow, mul_assoc]
  obtain ⟨B, A, hB, -, hupper⟩ := analytic_good_heights_of_circle_growth
    (f := f) (fun z _ ↦ hf.analyticAt z) hb
    (one_le_mul_of_one_le_of_one_le hD (by norm_num)) (H₀ := 1) le_rfl
    (fun t ↦ hanchor χ (by simp)) hcircle
  let k := ⌈A⌉₊
  have hDpos : 0 < D := zero_lt_one.trans_le hD
  refine ⟨D * 9 ^ (6 : ℕ) * B, 6 + k, by positivity, fun H hH ↦ ?_⟩
  obtain ⟨T, hT, hseg⟩ := hupper H hH
  have hT₁ : 1 ≤ T := hH.trans hT.1.le
  have hT₀ : 0 ≤ T := zero_le_one.trans hT₁
  refine ⟨T, hT, fun σ hσ t ht ↦ ?_⟩
  let s : ℂ := (σ : ℂ) + (t : ℂ) * I
  let u : ℂ := (σ : ℂ) + (T : ℂ) * I
  change f s ≠ 0 ∧ ‖logDeriv f s‖ ≤ _
  have hσ' : σ ∈ Icc (-1 / 2 : ℝ) 2 := ⟨hσ.1, hσ.2.trans (by norm_num)⟩
  obtain ⟨hu, huinv⟩ := hseg σ hσ'
  change f u ≠ 0 at hu
  change ‖(f u)⁻¹‖ ≤ B * T ^ A at huinv
  have hs : f s ≠ 0 ∧ ‖(f s)⁻¹‖ ≤ B * T ^ A := by
    by_cases h : 0 ≤ t
    · rw [abs_of_nonneg h] at ht
      simpa only [s, u, ht] using And.intro hu huinv
    · rw [abs_of_nonpos (le_of_not_ge h), neg_eq_iff_eq_neg] at ht
      have hsu : s = conj u := by simp [s, u, ht, map_add, map_mul]
      rw [hsu, hconj]
      exact ⟨fun hz ↦ hu (by simpa using congrArg (starRingEnd ℂ) hz),
        by simpa only [norm_inv, norm_conj] using huinv⟩
  have hsr : s.re = σ := by simp [s]
  have hsi : s.im = t := by simp [s]
  have hs' : ‖s‖ ≤ 3 / 2 + T := by
    refine (norm_le_abs_re_add_abs_im s).trans ?_
    rw [hsr, hsi, ht]
    have habs : |σ| ≤ 3 / 2 := abs_le.mpr ⟨by linarith [hσ.1], hσ.2⟩
    linarith
  have hbd (w : ℂ) (hw : w ∈ sphere s 1) :
      ‖f w‖ ≤ (D * 9 ^ (6 : ℕ)) * (1 + T) ^ (6 : ℕ) := by
    have hd : ‖w - s‖ = 1 := by simpa only [mem_sphere, dist_eq_norm] using hw
    have hre : -4 ≤ w.re := by
      have hr := Complex.abs_re_le_norm (w - s)
      rw [hd, sub_re, hsr] at hr
      linarith [(abs_le.mp hr).1, hσ.1]
    have hw' : ‖w‖ + 6 ≤ 9 * (1 + T) := by
      have hw'' : ‖w‖ ≤ ‖w - s‖ + ‖s‖ := by
        simpa only [sub_add_cancel] using norm_add_le (w - s) s
      linarith
    calc
      ‖f w‖ ≤ D * (‖w‖ + 6) ^ 6 := hgrowth w hre
      _ ≤ D * (9 * (1 + T)) ^ 6 := by gcongr
      _ = _ := by rw [mul_pow, mul_assoc]
  have hderiv : ‖deriv f s‖ ≤ (D * 9 ^ (6 : ℕ)) * (1 + T) ^ (6 : ℕ) := by
    simpa only [div_one] using
      norm_deriv_le_of_forall_mem_sphere_norm_le (by norm_num : (0 : ℝ) < 1)
        hf.diffContOnCl hbd
  have hpow : T ^ A ≤ (1 + T) ^ k := calc
    T ^ A ≤ T ^ (k : ℝ) := Real.rpow_le_rpow_of_exponent_le hT₁ (Nat.le_ceil A)
    _ = T ^ k := Real.rpow_natCast T k
    _ ≤ (1 + T) ^ k := by gcongr; linarith
  refine ⟨hs.1, ?_⟩
  rw [logDeriv_apply, div_eq_mul_inv, norm_mul]
  calc
    _ ≤ ((D * 9 ^ (6 : ℕ)) * (1 + T) ^ (6 : ℕ)) * (B * (1 + T) ^ k) :=
      mul_le_mul hderiv (hs.2.trans (mul_le_mul_of_nonneg_left hpow hB.le))
        (norm_nonneg _) (by positivity)
    _ = _ := by rw [pow_add]; ring

end Masullo
