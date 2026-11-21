module

public import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic.Linarith

/-!
# Growth of the pole-subtracted completed zeta function

This project estimate prepares the multiplicity-weighted summability input to
`Masullo.weight_eq_zero_of_zero_mass_annihilation`. Masullo counts the zeros
with multiplicity in (B.4.2.2), p. 614; the estimate here uses the theta
construction in Mathlib independently of the manuscript's trace formulas.
-/

open Complex Filter HurwitzZeta MeasureTheory Set

namespace Masullo

private noncomputable def modifiedTheta : ℝ → ℂ := (hurwitzEvenFEPair 0).f_modif

-- Subtract the constant term at infinity, and use theta inversion below one.
private theorem modifiedTheta_nonneg {t : ℝ} (ht : 0 < t) :
    ∃ v : ℝ, 0 ≤ v ∧ modifiedTheta t = v := by
  have habove (x : ℝ) (hx : 1 < x) : ∃ v : ℝ, 0 ≤ v ∧ modifiedTheta x = v := by
    have hsum := hasSum_nat_cosKernel₀ 0 (zero_lt_one.trans hx)
    simp only [QuotientAddGroup.mk_zero, mul_zero, zero_mul, Real.cos_zero, mul_one] at hsum
    have hnonneg : 0 ≤ cosKernel 0 x - 1 := by
      rw [← hsum.tsum_eq]
      exact tsum_nonneg (fun _ ↦ by positivity)
    refine ⟨cosKernel 0 x - 1, hnonneg, ?_⟩
    simp [modifiedTheta, WeakFEPair.f_modif, hx, notMem_Ioo_of_ge hx.le,
      hurwitzEvenFEPair, evenKernel_eq_cosKernel_of_zero]
  rcases lt_trichotomy t 1 with hlt | rfl | hgt
  · have hx : 1 < 1 / t := by rwa [lt_div_iff₀ ht, one_mul]
    obtain ⟨v, hv, he⟩ := habove (1 / t) hx
    have hfe := (hurwitzEvenFEPair 0).hf_modif_FE (1 / t) (by positivity)
    change (hurwitzEvenFEPair 0).f_modif (1 / (1 / t)) =
      (1 * (↑((1 / t) ^ (1 / 2 : ℝ)) : ℂ)) • (hurwitzEvenFEPair 0).g_modif (1 / t) at hfe
    have hfg (x : ℝ) : (hurwitzEvenFEPair 0).g_modif x = modifiedTheta x := by
      simp [modifiedTheta, WeakFEPair.f_modif, WeakFEPair.g_modif, hurwitzEvenFEPair,
        evenKernel_eq_cosKernel_of_zero]
    rw [hfg, he, one_div_one_div, one_mul, smul_eq_mul, ← ofReal_mul] at hfe
    exact ⟨_, mul_nonneg (by positivity) hv, hfe⟩
  · exact ⟨0, le_rfl, by simp [modifiedTheta, WeakFEPair.f_modif]⟩
  · exact habove t hgt

private noncomputable def thetaIntegrand (s : ℂ) (t : ℝ) : ℂ :=
  (t : ℂ) ^ (s / 2 - 1) * modifiedTheta t

private theorem integrable_thetaIntegrand (s : ℂ) : IntegrableOn (thetaIntegrand s) (Ioi 0) := by
  exact ((hurwitzEvenFEPair 0).isStrongFEPair_toStrongFEPair.hasMellin (s / 2)).1

private theorem integral_thetaIntegrand (s : ℂ) :
    (∫ t in Ioi 0, thetaIntegrand s t) = 2 * completedRiemannZeta₀ s := by
  change (∫ t in Ioi 0, thetaIntegrand s t) =
    2 * ((hurwitzEvenFEPair 0).Λ₀ (s / 2) / 2)
  rw [← mul_div_assoc, mul_div_cancel_left₀ _ two_ne_zero]
  rfl

-- The two endpoint powers dominate the intervening powers, one on each side of t = 1.
private theorem completedZeta₀_le_endpoint {s : ℂ} {m : ℝ}
    (hl : 1 - m ≤ s.re) (hu : s.re ≤ m) :
    ‖completedRiemannZeta₀ s‖ ≤ 2 * ‖completedRiemannZeta₀ (m : ℂ)‖ := by
  let μ := (volume : Measure ℝ).restrict (Ioi 0)
  let a : ℂ := (m : ℂ)
  let b : ℂ := 1 - a
  have hle : ∀ t ∈ Ioi (0 : ℝ), ‖thetaIntegrand s t‖ ≤
      (thetaIntegrand a t).re + (thetaIntegrand b t).re := by
    intro t ht
    obtain ⟨v, hv, hv'⟩ := modifiedTheta_nonneg (mem_Ioi.mp ht)
    have hnorm : ‖thetaIntegrand s t‖ = t ^ (s.re / 2 - 1) * v := by
      simp [thetaIntegrand, hv', norm_real, abs_of_nonneg hv,
        norm_cpow_eq_rpow_re_of_pos (mem_Ioi.mp ht), div_ofNat_re]
    have hre (c : ℝ) : (thetaIntegrand (c : ℂ) t).re = t ^ (c / 2 - 1) * v := by
      simp only [thetaIntegrand, hv', ← ofReal_ofNat, ← ofReal_div, ← ofReal_one, ← ofReal_sub,
        ← ofReal_cpow (mem_Ioi.mp ht).le, ← ofReal_mul, ofReal_re]
    have hb : b = ((1 - m : ℝ) : ℂ) := by simp [b, a]
    rw [hnorm, hb, hre, hre]
    have ht' : 0 < t := ht
    by_cases h : 1 ≤ t
    · exact (mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le h (by linarith)) hv).trans
        (le_add_of_nonneg_right (by positivity))
    · exact (mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow_of_exponent_ge ht' (le_of_not_ge h) (by linarith)) hv).trans
        (le_add_of_nonneg_left (by positivity))
  have ha : Integrable (fun t ↦ (thetaIntegrand a t).re) μ := (integrable_thetaIntegrand a).re
  have hb : Integrable (fun t ↦ (thetaIntegrand b t).re) μ := (integrable_thetaIntegrand b).re
  have hm := setIntegral_mono_on (integrable_thetaIntegrand s).norm (ha.add hb) measurableSet_Ioi hle
  have hsum : (∫ t, (thetaIntegrand a t).re + (thetaIntegrand b t).re ∂μ) =
      (∫ t, (thetaIntegrand a t).re ∂μ) + (∫ t, (thetaIntegrand b t).re ∂μ) :=
    integral_add ha hb
  have hre (c : ℂ) : (∫ t, (thetaIntegrand c t).re ∂μ) =
      (2 * completedRiemannZeta₀ c).re :=
    (integral_re (integrable_thetaIntegrand c)).trans
      (congrArg Complex.re (integral_thetaIntegrand c))
  change (∫ t, ‖thetaIntegrand s t‖ ∂μ) ≤
    (∫ t, (thetaIntegrand a t).re + (thetaIntegrand b t).re ∂μ) at hm
  rw [hsum, hre, hre, show completedRiemannZeta₀ b = completedRiemannZeta₀ a from
    completedRiemannZeta₀_one_sub a] at hm
  have hn := (norm_integral_le_integral_norm (μ := μ) (thetaIntegrand s)).trans hm
  rw [show (∫ t, thetaIntegrand s t ∂μ) = 2 * completedRiemannZeta₀ s from
    integral_thetaIntegrand s, norm_mul] at hn
  norm_num [Complex.mul_re] at hn
  linarith [Complex.re_le_norm (completedRiemannZeta₀ a)]

private theorem completedZeta₀_at_even_nat_le (n : ℕ) :
    ‖completedRiemannZeta₀ ((2 * (n + 1 : ℕ) : ℕ) : ℂ)‖ ≤
      ((∑' k : ℕ, ((k : ℝ) ^ 2)⁻¹) + 2) * (n.factorial : ℝ) := by
  let m : ℕ := 2 * (n + 1)
  let s : ℂ := m
  have hm : 2 ≤ m := by dsimp [m]; omega
  have hs : (2 : ℝ) ≤ s.re := by
    change (2 : ℝ) ≤ ((m : ℂ)).re
    rw [natCast_re]
    exact_mod_cast hm
  have hs' : 1 < s.re := by linarith
  have hgamma : Gamma (s / 2) = n.factorial := by
    rw [show s / 2 = (n : ℂ) + 1 by push_cast [s, m]; ring, Gamma_nat_eq_factorial]
  have hpi : ‖(↑Real.pi : ℂ) ^ (-s / 2)‖ ≤ 1 := by
    rw [norm_cpow_eq_rpow_re_of_pos Real.pi_pos, ← Real.rpow_zero Real.pi]
    exact Real.rpow_le_rpow_of_exponent_le (by linarith [Real.pi_gt_three])
      (by simp [div_ofNat_re]; linarith)
  have hseries : ‖∑' k : ℕ, 1 / (k : ℂ) ^ s‖ ≤ ∑' k : ℕ, ((k : ℝ) ^ 2)⁻¹ := by
    have H : Summable (fun k : ℕ ↦ ((k : ℝ) ^ 2)⁻¹) := Real.summable_nat_pow_inv.mpr (by decide)
    apply tsum_of_norm_bounded H.hasSum
    intro k
    rcases eq_or_ne k 0 with rfl | hk
    · simp [zero_cpow (Complex.ne_zero_of_one_lt_re hs')]
    · have hk' : 0 < (k : ℝ) := by positivity
      rw [norm_div, norm_one, ← ofReal_natCast, norm_cpow_eq_rpow_re_of_pos hk', one_div,
        ← Real.rpow_natCast]
      exact inv_anti₀ (by positivity)
        (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hk) hs)
  have hΛ : ‖completedRiemannZeta s‖ ≤ (∑' k : ℕ, ((k : ℝ) ^ 2)⁻¹) * (n.factorial : ℝ) := by
    rw [completedZeta_eq_tsum_of_one_lt_re hs', hgamma, norm_mul, norm_mul, Complex.norm_natCast]
    calc
      _ ≤ (n.factorial : ℝ) * ‖∑' k : ℕ, 1 / (k : ℂ) ^ s‖ :=
        mul_le_mul_of_nonneg_right (mul_le_of_le_one_left (by positivity) hpi) (norm_nonneg _)
      _ ≤ _ := by rw [mul_comm]; gcongr
  have ht : ‖1 / s‖ ≤ 1 := by
    rw [norm_div, norm_one, div_le_one (norm_pos_iff.mpr (Complex.ne_zero_of_one_lt_re hs'))]
    exact (by linarith : 1 ≤ s.re).trans (re_le_norm s)
  have ht' : ‖1 / (1 - s)‖ ≤ 1 := by
    have h₁ : 1 ≤ (s - 1).re := by simp; linarith
    rw [show 1 - s = -(s - 1) by ring, norm_div, norm_one, norm_neg,
      div_le_one (by linarith [re_le_norm (s - 1)])]
    exact h₁.trans (re_le_norm (s - 1))
  have he : completedRiemannZeta₀ s = completedRiemannZeta s + 1 / s + 1 / (1 - s) := by
    rw [completedRiemannZeta_eq]; ring
  change ‖completedRiemannZeta₀ s‖ ≤ _
  rw [he]
  have hfac : 1 ≤ (n.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos n
  linarith [norm_add_le (completedRiemannZeta s + 1 / s) (1 / (1 - s)),
    norm_add_le (completedRiemannZeta s) (1 / s)]

/-- The modified completed zeta is bounded by a constant times `n!` uniformly
on `|Re s| ≤ n`. In particular, the estimate needs no bound on `Im s`. -/
public theorem completedZeta₀_factorial_growth :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (n : ℕ) (s : ℂ), |s.re| ≤ n →
      ‖completedRiemannZeta₀ s‖ ≤ C * (n.factorial : ℝ) := by
  refine ⟨2 * ((∑' k : ℕ, ((k : ℝ) ^ 2)⁻¹) + 2), ?_, ?_⟩
  · have hnonneg : 0 ≤ ∑' k : ℕ, ((k : ℝ) ^ 2)⁻¹ := tsum_nonneg (fun _ ↦ by positivity)
    linarith
  intro n s hs
  let m : ℕ := 2 * (n + 1)
  obtain ⟨hl, hu⟩ := abs_le.mp hs
  have h₁ : 1 - (m : ℝ) ≤ s.re := by push_cast [m]; linarith
  have h₂ : s.re ≤ (m : ℝ) := by push_cast [m]; linarith
  calc
    _ ≤ 2 * ‖completedRiemannZeta₀ (m : ℂ)‖ := by
      simpa using completedZeta₀_le_endpoint h₁ h₂
    _ ≤ _ := by
      rw [mul_assoc]; gcongr; exact completedZeta₀_at_even_nat_le n

end Masullo
