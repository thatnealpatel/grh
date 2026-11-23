module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.RealDeriv

/-! # Cauchy bounds for the unscaled positive-log bump -/

open Complex Filter Metric Set
open scoped ContDiff Topology

namespace Masullo.PositiveLogBumpDecay

/-- The prescribed bump in its unscaled coordinate. -/
@[expose] public noncomputable def profile (u : ℝ) : ℝ := expNegInvGlue (1 - u ^ 2)

/-- The glue function gives exactly the prescribed cutoff, including the endpoints. -/
public theorem profile_eq (u : ℝ) :
    profile u = if |u| < 1 then Real.exp (-1 / (1 - u ^ 2)) else 0 := by
  have h : 0 < 1 - u ^ 2 ↔ |u| < 1 := by
    rw [sub_pos, ← sq_abs u]
    simpa only [one_pow] using (pow_lt_pow_iff_left₀ (abs_nonneg u)
      (zero_le_one : (0 : ℝ) ≤ 1) (by decide : (2 : ℕ) ≠ 0))
  by_cases hu : |u| < 1
  · simp [profile, expNegInvGlue, hu, not_le.mpr (h.mpr hu), div_eq_mul_inv]
  · simp [profile, expNegInvGlue, hu, le_of_not_gt (mt h.mp hu)]

/-- Mathlib's flat exponential glue makes this exact cutoff smooth across both endpoints. -/
public theorem contDiff_profile : ContDiff ℝ ∞ profile := by
  exact expNegInvGlue.contDiff.comp (contDiff_const.sub (contDiff_id.pow 2))

/-- Every derivative of the cutoff vanishes outside the open unit interval, endpoints included. -/
public theorem iteratedDeriv_profile_eq_zero (k : ℕ) {u : ℝ} (hu : 1 ≤ |u|) :
    iteratedDeriv k profile u = 0 := by
  have hc := contDiff_profile.continuous_iteratedDeriv k (by simp)
  have hstrict (v : ℝ) (hv : 1 < |v|) : iteratedDeriv k profile v = 0 := by
    have he : profile =ᶠ[𝓝 v] (fun _ ↦ 0) := by
      filter_upwards [continuous_abs.continuousAt.eventually (eventually_gt_nhds hv)] with w hw
      simp [profile_eq, not_lt_of_ge hw.le]
    simpa using (he.iteratedDeriv k).eq_of_nhds
  let S := {v : ℝ | iteratedDeriv k profile v = 0}
  have hS : IsClosed S := isClosed_eq hc continuous_const
  rcases le_abs.mp hu with hp | hn
  · exact closure_minimal (s := Ioi (1 : ℝ))
      (fun v hv ↦ hstrict v (hv.out.trans_le (le_abs_self _))) hS
      (by rw [closure_Ioi]; exact hp)
  · exact closure_minimal (s := Iio (-1 : ℝ)) (fun v hv ↦ hstrict v (by
      have h := hv.out
      linarith [neg_le_abs v])) hS (by rw [closure_Iio]; exact (show u ≤ -1 by linarith))

private noncomputable def extension (z : ℂ) : ℂ := Complex.exp (-1 / (1 - z ^ 2))

private theorem analyticAt_extension {z : ℂ} (hz : 1 - z ^ 2 ≠ 0) :
    AnalyticAt ℂ extension z := by
  have hOpen : IsOpen {w : ℂ | 1 - w ^ 2 ≠ 0} :=
    (isOpen_ne (x := (0 : ℂ))).preimage (by fun_prop)
  apply DifferentiableOn.analyticAt (s := {w : ℂ | 1 - w ^ 2 ≠ 0}) _ (hOpen.mem_nhds hz)
  intro w hw
  apply DifferentiableAt.differentiableWithinAt
  unfold extension
  exact Complex.differentiable_exp.differentiableAt.comp w
    ((differentiableAt_const (-1 : ℂ)).div
      ((differentiableAt_const (1 : ℂ)).sub (differentiableAt_id.pow 2)) hw)

private theorem sub_sq_ne_zero_of_norm_sub_le {u r : ℝ}
    (hr : r < 1 - |u|) {z : ℂ} (hz : ‖z - (u : ℂ)‖ ≤ r) : 1 - z ^ 2 ≠ 0 := by
  have hzn : ‖z‖ < 1 := calc
    ‖z‖ = ‖z - (u : ℂ) + (u : ℂ)‖ := by rw [sub_add_cancel]
    _ ≤ ‖z - (u : ℂ)‖ + ‖(u : ℂ)‖ := norm_add_le _ _
    _ < 1 := by rw [Complex.norm_real, Real.norm_eq_abs]; linarith
  intro h
  have hh := congrArg norm (sub_eq_zero.mp h)
  rw [norm_one, norm_pow] at hh
  nlinarith [norm_nonneg z]

/-- The real part of `(d + w)⁻¹` is at least `1 / (d + r)` on `‖w‖ ≤ r < d`. -/
private theorem re_inv_add_ge {d r : ℝ} {w : ℂ} (hr : 0 ≤ r) (hd : r < d) (hw : ‖w‖ ≤ r) :
    1 / (d + r) ≤ ((d : ℂ) + w)⁻¹.re := by
  have hre := (abs_le.mp ((Complex.abs_re_le_norm w).trans hw))
  have hpos : 0 < ((d : ℂ) + w).re := by simp only [add_re, ofReal_re]; linarith [hre.1]
  have hn : (d : ℂ) + w ≠ 0 := fun h ↦ by rw [h, zero_re] at hpos; exact lt_irrefl 0 hpos
  rw [Complex.inv_re, div_le_div_iff₀ (by linarith) (Complex.normSq_pos.mpr hn), one_mul]
  have hnorm : Complex.normSq w ≤ r ^ 2 := by
    rw [Complex.normSq_eq_norm_sq]
    exact pow_le_pow_left₀ (norm_nonneg _) hw 2
  have hprod := mul_le_mul_of_nonneg_left hre.2 (sub_nonneg.mpr hd.le)
  simp only [Complex.normSq_apply, add_re, add_im, ofReal_re, ofReal_im, zero_add] at hnorm ⊢
  nlinarith only [hnorm, hprod]

private theorem norm_extension_le {u r : ℝ} (hu : |u| < 1) (hr₀ : 0 ≤ r)
    (hr : r < 1 - |u|) {z : ℂ} (hz : ‖z - (u : ℂ)‖ ≤ r) :
    ‖extension z‖ ≤ Real.exp (-1 / (4 * (1 - |u|))) := by
  have hm : r < 1 - u := by linarith [le_abs_self u]
  have hp : r < 1 + u := by linarith [neg_le_abs u]
  have hminus := re_inv_add_ge hr₀ hm (w := -(z - (u : ℂ))) (by rwa [norm_neg])
  have hplus := re_inv_add_ge hr₀ hp hz
  rw [show ((↑(1 - u) : ℂ) + -(z - (u : ℂ))) = 1 - z by push_cast; ring] at hminus
  rw [show ((↑(1 + u) : ℂ) + (z - (u : ℂ))) = 1 + z by push_cast; ring] at hplus
  have hmpos : 0 < 1 - u + r := by linarith
  have hppos : 0 < 1 + u + r := by linarith
  have hl := (one_div_pos.mpr hmpos).le.trans hminus
  have hh := (one_div_pos.mpr hppos).le.trans hplus
  have h₁ : (1 - z) ≠ 0 := fun h ↦ by
    simp [h, hmpos.not_ge] at hminus
  have h₂ : (1 + z) ≠ 0 := fun h ↦ by
    simp [h, hppos.not_ge] at hplus
  have hpartial : (1 - z ^ 2)⁻¹ = ((1 - z)⁻¹ + (1 + z)⁻¹) / 2 := by
    rw [show 1 - z ^ 2 = (1 - z) * (1 + z) by ring]
    field_simp; ring
  rw [extension, Complex.norm_exp, div_eq_mul_inv, neg_one_mul, neg_re, neg_div,
    hpartial, div_eq_mul_inv, ← Complex.ofReal_ofNat, ← Complex.ofReal_inv, mul_re]
  simp only [add_re, ofReal_re, ofReal_im, mul_zero, sub_zero]
  apply Real.exp_le_exp.mpr
  have hnear : 1 / (2 * (1 - |u|)) ≤ 1 / (1 - |u| + r) :=
    one_div_le_one_div_of_le (by linarith) (by linarith)
  have hsum : 1 / (2 * (1 - |u|)) ≤ (1 - z)⁻¹.re + (1 + z)⁻¹.re := by
    rcases le_total 0 u with h | h
    · rw [abs_of_nonneg h] at hnear ⊢
      exact (hnear.trans hminus).trans (le_add_of_nonneg_right hh)
    · rw [abs_of_nonpos h, sub_neg_eq_add] at hnear ⊢
      exact (hnear.trans hplus).trans (le_add_of_nonneg_left hl)
  have he : -(1 / (4 * (1 - |u|))) = -(1 / (2 * (1 - |u|))) / 2 := by
    field_simp [show 1 - |u| ≠ 0 by linarith]; ring
  rw [he, show (2 : ℝ)⁻¹ = 1 / 2 by norm_num]
  linarith

private theorem iteratedDeriv_profile_eq_re (k : ℕ) {u : ℝ} (hu : |u| < 1) :
    iteratedDeriv k profile u = (iteratedDeriv k extension (u : ℂ)).re := by
  induction k generalizing u with
  | zero =>
    simp [profile_eq, hu, extension, ← Complex.ofReal_pow, ← Complex.ofReal_one,
      ← Complex.ofReal_sub, ← Complex.ofReal_neg, ← Complex.ofReal_div, ← Complex.ofReal_exp]
  | succ k ih =>
    have hs : iteratedDeriv k profile =ᶠ[𝓝 u]
        (fun v : ℝ ↦ (iteratedDeriv k extension (v : ℂ)).re) := by
      filter_upwards [continuous_abs.continuousAt.eventually (eventually_lt_nhds hu)] with v hv
      exact ih hv
    have hA := AnalyticAt.iterated_deriv (analyticAt_extension
      (sub_sq_ne_zero_of_norm_sub_le (r := 0) (by linarith) (by simp : ‖(u : ℂ) - ↑u‖ ≤ 0))) k
    rw [← iteratedDeriv_eq_iterate] at hA
    rw [iteratedDeriv_succ, iteratedDeriv_succ, hs.deriv_eq,
      hA.differentiableAt.hasDerivAt.real_of_complex.deriv]

/-- Cauchy's estimate with the radius taken up to the nearer endpoint. -/
public theorem norm_iteratedDeriv_profile_le_boundary (k : ℕ) {u : ℝ} (hu : |u| < 1) :
    ‖iteratedDeriv k profile u‖ ≤ (k.factorial : ℝ) * Real.exp (-1 / (4 * (1 - |u|))) /
      (1 - |u|) ^ k := by
  let d := 1 - |u|
  have hd : 0 < d := sub_pos.mpr hu
  have hradius (r : ℝ) (hr : r ∈ Ioo 0 d) :
      ‖iteratedDeriv k profile u‖ * r ^ k ≤ (k.factorial : ℝ) * Real.exp (-1 / (4 * d)) := by
    have hF : DiffContOnCl ℂ extension (ball (u : ℂ) r) := by
      apply DifferentiableOn.diffContOnCl
      intro z hz
      have hz' := mem_closedBall.mp (closure_ball_subset_closedBall hz)
      exact (analyticAt_extension (sub_sq_ne_zero_of_norm_sub_le hr.2
        (by simpa only [dist_eq_norm] using hz'))).differentiableAt.differentiableWithinAt
    have hC := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le k hr.1 hF
      (fun z hz ↦ norm_extension_le hu hr.1.le hr.2 (mem_sphere_iff_norm.mp hz).le)
    have hreal := Complex.abs_re_le_norm (iteratedDeriv k extension (u : ℂ))
    rw [← iteratedDeriv_profile_eq_re k hu, ← Real.norm_eq_abs] at hreal
    exact (le_div_iff₀ (pow_pos hr.1 k)).mp (hreal.trans hC)
  have hclosed : IsClosed {r : ℝ | ‖iteratedDeriv k profile u‖ * r ^ k ≤
      (k.factorial : ℝ) * Real.exp (-1 / (4 * d))} :=
    isClosed_le (by fun_prop) continuous_const
  exact (le_div_iff₀ (pow_pos hd k)).mpr (closure_minimal (s := Ioo 0 d)
    (fun r hr ↦ hradius r hr) hclosed
    (by rw [closure_Ioo hd.ne]; exact right_mem_Icc.mpr hd.le))

private theorem pow_mul_exp_neg_le {k : ℕ} (hk : 0 < k) {y : ℝ} (hy : 0 < y) :
    y ^ k * Real.exp (-y) ≤ ((k : ℝ) / Real.exp 1) ^ k := by
  have hk' : 0 < (k : ℝ) := Nat.cast_pos.mpr hk
  have h : y / (k : ℝ) ≤ Real.exp (y / (k : ℝ) - 1) := by
    linarith [Real.add_one_le_exp (y / (k : ℝ) - 1)]
  have hpow := pow_le_pow_left₀ (div_nonneg hy.le hk'.le) h k
  rw [← Real.exp_nat_mul, show (k : ℝ) * (y / (k : ℝ) - 1) = y - (k : ℝ) by
    field_simp] at hpow
  calc
    y ^ k * Real.exp (-y) = (k : ℝ) ^ k * ((y / (k : ℝ)) ^ k * Real.exp (-y)) := by
      rw [div_pow]; field_simp
    _ ≤ (k : ℝ) ^ k * (Real.exp (y - (k : ℝ)) * Real.exp (-y)) := by gcongr
    _ = ((k : ℝ) / Real.exp 1) ^ k := by
      rw [← Real.exp_add, div_pow, ← Real.exp_nat_mul, mul_one, div_eq_mul_inv, ← Real.exp_neg]
      congr 2
      ring

/-- Uniform Cauchy bound, including the zero derivatives beyond the support. -/
public theorem norm_iteratedDeriv_profile_le {k : ℕ} (hk : 0 < k) (u : ℝ) :
    ‖iteratedDeriv k profile u‖ ≤ (k.factorial : ℝ) * (4 * (k : ℝ) / Real.exp 1) ^ k := by
  by_cases hu : |u| < 1
  · let d := 1 - |u|
    have hd : 0 < d := sub_pos.mpr hu
    have hy : 0 < 1 / (4 * d) := by positivity
    calc
      _ ≤ (k.factorial : ℝ) * Real.exp (-1 / (4 * d)) / d ^ k :=
        norm_iteratedDeriv_profile_le_boundary k hu
      _ = (k.factorial : ℝ) * 4 ^ k * ((1 / (4 * d)) ^ k * Real.exp (-(1 / (4 * d)))) := by
        rw [neg_div, div_pow, mul_pow, one_pow]
        field_simp
      _ ≤ (k.factorial : ℝ) * 4 ^ k * (((k : ℝ) / Real.exp 1) ^ k) := by
        gcongr
        exact pow_mul_exp_neg_le hk hy
      _ = _ := by rw [mul_div_assoc, mul_pow]; ring
  · rw [iteratedDeriv_profile_eq_zero k (le_of_not_gt hu), norm_zero]
    positivity

end Masullo.PositiveLogBumpDecay
