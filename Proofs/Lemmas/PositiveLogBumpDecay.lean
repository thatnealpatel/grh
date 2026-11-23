module

public import Lemmas.PositiveLogBumpCircle
public import Lemmas.PositiveLogBumpIBP
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Complex.RealDeriv

/-! # Explicit Fourier decay for the prescribed positive-log bump -/

open Complex Function MeasureTheory Set
open scoped ContDiff

namespace Masullo.PositiveLogBumpDecay

/-- The spatial scale in the prescribed log coordinate. -/
@[expose] public noncomputable def a : ℝ := Real.log 2 / 4

/-- The prescribed positive-log bump, supported between `a` and `3 * a`. -/
@[expose] public noncomputable def b (x : ℝ) : ℝ := profile (x / a - 2)

/-- The exact formula in the original coordinate `u = 4 * x / log 2 - 2`. -/
public theorem b_eq (x : ℝ) :
    b x = let u := 4 * x / Real.log 2 - 2
      if |u| < 1 then Real.exp (-1 / (1 - u ^ 2)) else 0 := by
  rw [b, profile_eq]
  have h : x / a = 4 * x / Real.log 2 := by
    unfold a
    ring
  rw [h]

private theorem a_bounds : 1 / 6 < a ∧ a < 1 / 4 := by
  unfold a
  exact ⟨by linarith [Real.log_two_gt_d9], by linarith [Real.log_two_lt_d9]⟩

private theorem a_pos : 0 < a := by linarith [a_bounds.1]

/-- The prescribed bump is smooth everywhere. -/
public theorem contDiff_b : ContDiff ℝ ∞ b :=
  contDiff_profile.comp ((contDiff_id.div_const a).sub contDiff_const)

private theorem iteratedDeriv_b (k : ℕ) (x : ℝ) :
    iteratedDeriv k b x = a⁻¹ ^ k * iteratedDeriv k profile (x / a - 2) := by
  let g (y : ℝ) := profile (y - 2)
  have hg : ContDiff ℝ k g :=
    (contDiff_profile.of_le (by simp)).comp (contDiff_id.sub contDiff_const)
  have hb : b = fun y ↦ g (a⁻¹ * y) := by
    ext y
    simp only [b, g, div_eq_mul_inv, mul_comm]
  rw [hb, iteratedDeriv_comp_const_mul hg]
  simp only [g, iteratedDeriv_comp_sub_const, show a⁻¹ * x = x / a by ring]

private theorem iteratedDeriv_ofReal {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (k : ℕ) (x : ℝ) :
    iteratedDeriv k (fun y ↦ (f y : ℂ)) x = Complex.ofReal (iteratedDeriv k f x) := by
  induction k generalizing x with
  | zero => simp
  | succ k ih =>
    have hD := hf.differentiable_iteratedDeriv k (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top k))
    rw [iteratedDeriv_succ, iteratedDeriv_succ, funext ih,
      ((hD x).hasDerivAt.ofReal_comp).deriv]

private theorem support_iteratedDeriv_b (k : ℕ) :
    support (iteratedDeriv k (fun x ↦ (b x : ℂ))) ⊆ Icc a (3 * a) := by
  intro x hx
  have hlt : |x / a - 2| < 1 := by
    by_contra! hl
    exact hx (by rw [iteratedDeriv_ofReal contDiff_b, iteratedDeriv_b,
      iteratedDeriv_profile_eq_zero k hl, mul_zero, Complex.ofReal_zero])
  obtain ⟨hl, hr⟩ := abs_lt.mp hlt
  refine ⟨?_, ?_⟩
  · simpa only [one_mul] using (le_div_iff₀ a_pos).mp (show 1 ≤ x / a by linarith)
  · exact (div_le_iff₀ a_pos).mp (show x / a ≤ 3 by linarith)

/-- The prescribed bump has compact support in the positive real line. -/
public theorem hasCompactSupport_b : HasCompactSupport b := by
  have hs : support b ⊆ Icc a (3 * a) := by
    intro x hx
    apply support_iteratedDeriv_b 0
    simpa only [iteratedDeriv_zero, mem_support, Complex.ofReal_ne_zero] using hx
  exact isCompact_Icc.of_isClosed_subset (isClosed_tsupport _)
    (closure_minimal hs isClosed_Icc)

/-- Integration by parts ten times with the scaled Cauchy bound for the exact cutoff. -/
public theorem norm_integral_le_tenth {t : ℝ} (ht : t ≠ 0) :
    ‖∫ x : ℝ, (b x : ℂ) * Complex.exp (I * (t : ℂ) * (x : ℂ))‖ ≤
      2 * a * (Nat.factorial 10 : ℝ) * (40 / (Real.exp 1 * a * |t|)) ^ 10 := by
  have hs := support_iteratedDeriv_b 0
  rw [iteratedDeriv_zero] at hs
  have hcompact : HasCompactSupport (fun x ↦ (b x : ℂ)) :=
    isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) (closure_minimal hs isClosed_Icc)
  have hC (x : ℝ) (_ : x ∈ Icc a (3 * a)) :
      ‖iteratedDeriv 10 (fun y ↦ (b y : ℂ)) x‖ ≤
        (Nat.factorial 10 : ℝ) * (40 / Real.exp 1) ^ 10 / a ^ 10 := by
    rw [iteratedDeriv_ofReal contDiff_b, Complex.norm_real, iteratedDeriv_b, norm_mul,
      norm_pow, norm_inv, Real.norm_eq_abs, abs_of_pos a_pos, inv_pow, ← div_eq_inv_mul]
    apply div_le_div_of_nonneg_right _ (by positivity)
    convert norm_iteratedDeriv_profile_le (k := 10) (by decide) (x / a - 2) using 1
    norm_num
  have h := norm_integral_exp_le_of_derivative_bound 10 ht (show a ≤ 3 * a by linarith [a_pos])
    (Complex.ofRealCLM.contDiff.comp contDiff_b) hcompact (support_iteratedDeriv_b 10) hC
  refine h.trans_eq ?_
  rw [show 3 * a - a = 2 * a by ring]
  rw [div_pow, div_pow, mul_pow (Real.exp 1 * a), mul_pow (Real.exp 1)]
  field_simp [a_pos.ne', (abs_pos.mpr ht).ne', (Real.exp_pos 1).ne']

/-- The Haar-normalized Fourier integral, with positive phase and no factor of `2π`,
decays by a factor of `1/1024` per dyadic band above `8192`. -/
public theorem norm_integral_le (j : ℕ) (t : ℝ) (ht : (2 : ℝ) ^ j * 8192 < |t|) :
    ‖∫ x : ℝ, (b x : ℂ) * Complex.exp (I * (t : ℂ) * (x : ℂ))‖ ≤
      (2 / 10 ^ 13 : ℝ) * (1 / 1024 : ℝ) ^ j := by
  have hj : 0 < (2 : ℝ) ^ j := by positivity
  have htpos : 0 < |t| := (by positivity : 0 < (2 : ℝ) ^ j * 8192).trans ht
  have he : 5 / 2 < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have hden : 3200 * (2 : ℝ) ^ j ≤ Real.exp 1 * a * |t| := calc
    _ ≤ ((5 / 2 : ℝ) * (1 / 6 : ℝ)) * (2 ^ j * 8192) := by linarith
    _ ≤ _ := by gcongr <;> first | positivity [a_pos] | linarith [a_bounds.1]
  have hratio : 40 / (Real.exp 1 * a * |t|) ≤ (1 / 80 : ℝ) / 2 ^ j := by
    refine (div_le_div_of_nonneg_left (by norm_num) (by positivity) hden).trans_eq ?_
    field_simp [hj.ne']; norm_num
  have ha : 2 * a ≤ 1 / 2 := by linarith [a_bounds.2]
  have hpow : ((1 / 80 : ℝ) / 2 ^ j) ^ 10 = (1 / 80 : ℝ) ^ 10 * (1 / 1024 : ℝ) ^ j := by
    rw [div_pow, div_eq_mul_inv, ← pow_mul, Nat.mul_comm j 10, pow_mul, ← inv_pow]
    norm_num
  calc
    _ ≤ 2 * a * (Nat.factorial 10 : ℝ) * (40 / (Real.exp 1 * a * |t|)) ^ 10 :=
      norm_integral_le_tenth (abs_pos.mp htpos)
    _ ≤ (1 / 2 : ℝ) * (Nat.factorial 10 : ℝ) * ((1 / 80 : ℝ) / 2 ^ j) ^ 10 := by
      have h := pow_le_pow_left₀ (by positivity [a_pos] : 0 ≤ 40 / (Real.exp 1 * a * |t|)) hratio 10
      gcongr
    _ = ((1 / 2 : ℝ) * (Nat.factorial 10 : ℝ) * (1 / 80 : ℝ) ^ 10) * (1 / 1024 : ℝ) ^ j := by
      rw [hpow]; ring
    _ ≤ _ := by
      gcongr
      norm_num [Nat.factorial]

end Masullo.PositiveLogBumpDecay
