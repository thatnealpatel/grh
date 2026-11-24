module

public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Algebra.Group.ForwardDiff
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# The unsmoothed long-cutoff spline

Source: `874eb9a:.godel/bob/long-cutoff-moments.md`, lines 14–37 and 45–50.
Application: `daee96a:.godel/bob/endpoint-convolution-lift.md`, lines 28–44.
Discovery pin: `50cd94de`. Owning check session: `01a20e58-ec66-7c2b-94b4-741e4461cd8a`.

The finite difference gives the support and the bilateral transform. The
half-line transform also gives the angular carrier in the endpoint-convolution
normalization, with Fourier kernel `exp (-i x r)`.
-/

open Complex Filter Function MeasureTheory Set
open scoped BigOperators Nat Topology

namespace Masullo

noncomputable section

/-- The truncated polynomial `h_j`, with real argument and natural order. -/
@[expose] public def longCutoffProfile (j : ℕ) (r : ℝ) : ℝ :=
  if r < 0 then 0 else
    ∑ l ∈ Finset.range j, (-1 : ℝ) ^ l * ((j - 1).choose l : ℝ) *
      (r ^ (j - l) / ((j - l)! : ℝ))

/-- The whole unsmoothed difference `B_j`, taking `j - k` in `ℝ`, not `ℕ`. -/
@[expose] public def longCutoffSpline (j : ℕ) (D y : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (j + 2), (-1 : ℝ) ^ k * ((j + 1).choose k : ℝ) *
    longCutoffProfile j (((j : ℝ) - (k : ℝ)) * D - y)

private theorem longCutoffProfile_zero_of_neg (j : ℕ) {r : ℝ} (hr : r < 0) :
    longCutoffProfile j r = 0 := ite_eq_left hr

private theorem continuous_longCutoffProfile (j : ℕ) : Continuous (longCutoffProfile j) := by
  have heq : longCutoffProfile j = fun r ↦
      ∑ l ∈ Finset.range j, (-1 : ℝ) ^ l * ((j - 1).choose l : ℝ) *
        (max r 0 ^ (j - l) / ((j - l)! : ℝ)) := by
    funext r
    by_cases hr : r < 0
    · rw [longCutoffProfile_zero_of_neg j hr, max_eq_right hr.le]
      symm
      exact Finset.sum_eq_zero fun l hl ↦ by
        have hm : j - l ≠ 0 := Nat.sub_ne_zero_of_lt (Finset.mem_range.mp hl)
        simp [zero_pow hm]
    · rw [longCutoffProfile, ite_eq_right hr, max_eq_left (le_of_not_gt hr)]
  rw [heq]
  exact continuous_finsetSum _ fun l _ ↦ by fun_prop

private theorem longCutoffSpline_zero_right (j : ℕ) {D y : ℝ} (hD : 0 < D)
    (hy : (j : ℝ) * D < y) : longCutoffSpline j D y = 0 := by
  refine Finset.sum_eq_zero fun k _ ↦ ?_
  rw [longCutoffProfile_zero_of_neg, mul_zero]
  exact sub_neg.mpr ((mul_le_mul_of_nonneg_right (sub_le_self _ (by positivity)) hD.le).trans_lt hy)

private theorem longCutoffSpline_zero_left (j : ℕ) {D y : ℝ} (hD : 0 < D)
    (hy : y < -D) : longCutoffSpline j D y = 0 := by
  let c (l : ℕ) : ℝ := (-1 : ℝ) ^ l * ((j - 1).choose l : ℝ) / ((j - l)! : ℝ)
  let p : ℝ → ℝ := ∑ l ∈ Finset.range j, (c l * D ^ (j - l)) • (fun r ↦ r ^ (j - l))
  have hp (r : ℝ) (hr : 0 ≤ D * r) : longCutoffProfile j (D * r) = p r := by
    rw [longCutoffProfile, ite_eq_right (not_lt.mpr hr)]
    simp only [p, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, c]
    exact Finset.sum_congr rfl fun l _ ↦ by rw [mul_pow]; ring
  have hdiff : (fwdDiff (1 : ℝ))^[j + 1] p = 0 := by
    rw [show p = _ from rfl, fwdDiff_iter_finsetSum]
    exact Finset.sum_eq_zero fun l _ ↦ by
      rw [fwdDiff_iter_const_smul, fwdDiff_iter_pow_eq_zero_of_lt
        ((Nat.sub_le j l).trans_lt (Nat.lt_succ_self j)), smul_zero]
  let a := (-D - y) / D
  calc
    longCutoffSpline j D y = ∑ k ∈ Finset.range (j + 2),
        (-1 : ℝ) ^ (j + 1 - k) * ((j + 1).choose (j + 1 - k) : ℝ) *
          longCutoffProfile j (((j : ℝ) - ((j + 1 - k : ℕ) : ℝ)) * D - y) := by
      exact (Finset.sum_range_reflect _ (j + 2)).symm
    _ = (fwdDiff (1 : ℝ))^[j + 1] p a := by
      rw [fwdDiff_iter_eq_sum_shift]
      refine Finset.sum_congr rfl fun k hk ↦ ?_
      have hk' : k ≤ j + 1 := by have := Finset.mem_range.mp hk; omega
      have ha : ((j : ℝ) - ((j + 1 - k : ℕ) : ℝ)) * D - y = D * (a + (k : ℝ)) := by
        rw [Nat.cast_sub hk', Nat.cast_add, Nat.cast_one]
        dsimp [a]
        field_simp
        ring
      have hnon : 0 ≤ D * (a + (k : ℝ)) := by
        change 0 ≤ D * (((-D - y) / D) + (k : ℝ))
        rw [mul_add, show D * ((-D - y) / D) = -D - y by field_simp]
        exact add_nonneg (sub_nonneg.mpr hy.le) (mul_nonneg hD.le (Nat.cast_nonneg k))
      rw [ha, hp _ hnon, Nat.choose_symm hk']
      simp [zsmul_eq_mul, nsmul_eq_mul]
    _ = 0 := by rw [hdiff]; rfl

/-- The closed support of the spline is contained in the signed cutoff interval. -/
public theorem tsupport_longCutoffSpline_subset {j : ℕ} (_hj : 1 ≤ j) {D : ℝ} (hD : 0 < D) :
    tsupport (longCutoffSpline j D) ⊆ Icc (-D) ((j : ℝ) * D) := by
  apply closure_minimal _ isClosed_Icc
  refine support_subset_iff'.mpr fun y hy ↦ ?_
  by_cases hl : y < -D
  · exact longCutoffSpline_zero_left j hD hl
  · exact longCutoffSpline_zero_right j hD (lt_of_not_ge fun hr ↦ hy ⟨le_of_not_gt hl, hr⟩)

private theorem norm_pow_mul_decay (w : ℂ) (n : ℕ) {r : ℝ} (hr : 0 ≤ r) :
    ‖(r : ℂ) ^ n * exp (-w * (r : ℂ))‖ = r ^ n * Real.exp (-w.re * r) := by
  simp [Complex.norm_exp, Real.norm_of_nonneg hr, Complex.mul_re]

private theorem integrableOn_pow_mul_decay {w : ℂ} (hw : 0 < w.re) (n : ℕ) :
    IntegrableOn (fun r : ℝ ↦ (r : ℂ) ^ n * exp (-w * (r : ℂ))) (Ioi 0) := by
  have hc : Continuous (fun r : ℝ ↦ (r : ℂ) ^ n * exp (-w * (r : ℂ))) := by fun_prop
  apply (integrable_norm_iff hc.aestronglyMeasurable).mp
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow (s := (n : ℝ)) (p := 1)
    ((by norm_num : (-1 : ℝ) < 0).trans_le (Nat.cast_nonneg n)) zero_lt_one hw
  refine (by simpa only [Real.rpow_natCast, Real.rpow_one] using h :
    IntegrableOn (fun r : ℝ ↦ r ^ n * Real.exp (-w.re * r)) (Ioi 0)).congr_fun
    (fun _ hr ↦ (norm_pow_mul_decay w n (le_of_lt hr)).symm) measurableSet_Ioi

private theorem integral_pow_mul_decay {w : ℂ} (hw : 0 < w.re) (n : ℕ) :
    (∫ r : ℝ in Ioi 0, (r : ℂ) ^ n * exp (-w * (r : ℂ))) = (n ! : ℂ) / w ^ (n + 1) := by
  have hw₀ : w ≠ 0 := by rintro rfl; simp at hw
  induction n with
  | zero =>
    simpa [div_neg, neg_div, one_div] using
      integral_exp_mul_complex_Ioi (a := -w) (by simpa using hw) 0
  | succ n ih =>
    let u (r : ℝ) := (r : ℂ) ^ (n + 1)
    let u' (r : ℝ) := ((n : ℂ) + 1) * (r : ℂ) ^ n
    let v (r : ℝ) := exp (-w * (r : ℂ))
    let v' (r : ℝ) := -w * v r
    have hdu (r : ℝ) (_ : r ∈ Ioi (0 : ℝ)) : HasDerivAt u (u' r) r := by
      simpa [u, u'] using ((hasDerivAt_id (r : ℂ)).pow (n + 1)).comp_ofReal
    have hdv (r : ℝ) (_ : r ∈ Ioi (0 : ℝ)) : HasDerivAt v (v' r) r := by
      simpa [v, v', mul_comm] using
        ((hasDerivAt_const_mul (x := (r : ℂ)) (-w)).cexp).comp_ofReal
    have hleft (r : ℝ) : u r * v' r = -w * (u r * v r) := by dsimp [v']; ring
    have huv' : IntegrableOn (u * v') (Ioi 0) := by
      simp_rw [Pi.mul_def, hleft]
      exact (integrableOn_pow_mul_decay hw (n + 1)).const_mul (-w)
    have hu'v : IntegrableOn (u' * v) (Ioi 0) := by
      simpa only [IntegrableOn, Pi.mul_def, u', v, mul_assoc] using
        (integrableOn_pow_mul_decay hw n).const_mul ((n : ℂ) + 1)
    have hzero : Tendsto (u * v) (𝓝[>] 0) (𝓝 0) := by
      have hc : Continuous (u * v) := by dsimp [u, v]; fun_prop
      have hz : (u * v) 0 = 0 := by simp [u]
      rw [← hz]
      exact hc.continuousWithinAt.tendsto
    have hinfty : Tendsto (u * v) atTop (𝓝 0) := by
      apply tendsto_zero_iff_norm_tendsto_zero.mpr
      have h := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero ((n + 1 : ℕ) : ℝ) w.re hw
      refine h.congr' ?_
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with r hr
      change r ^ ((n + 1 : ℕ) : ℝ) * Real.exp (-w.re * r) =
        ‖(r : ℂ) ^ (n + 1) * exp (-w * (r : ℂ))‖
      rw [Real.rpow_natCast, norm_pow_mul_decay w (n + 1) hr]
    have hibp := integral_Ioi_mul_deriv_eq_deriv_mul hdu hdv huv' hu'v hzero hinfty
    simp_rw [hleft, integral_const_mul] at hibp
    simp only [u, u', v, mul_assoc, integral_const_mul, sub_self, zero_sub, ih] at hibp
    apply (mul_left_cancel₀ (neg_ne_zero.mpr hw₀))
    rw [hibp, Nat.factorial_succ, Nat.cast_mul, Nat.cast_succ, pow_succ w (n + 1)]
    field_simp

private def longCutoffDecayTerm (j l : ℕ) (w : ℂ) (r : ℝ) : ℂ :=
  ((-1 : ℂ) ^ l * ((j - 1).choose l : ℂ) / ((j - l)! : ℂ)) *
    ((r : ℂ) ^ (j - l) * exp (-w * (r : ℂ)))

private theorem longCutoffProfile_decay_eq_sum (j : ℕ) (w : ℂ) {r : ℝ} (hr : 0 ≤ r) :
    exp (-w * (r : ℂ)) * (longCutoffProfile j r : ℂ) =
      ∑ l ∈ Finset.range j, longCutoffDecayTerm j l w r := by
  rw [longCutoffProfile, ite_eq_right (not_lt.mpr hr), Complex.ofReal_sum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun l _ ↦ by
    push_cast
    dsimp [longCutoffDecayTerm]
    ring

private theorem integrableOn_longCutoffDecayTerm {w : ℂ} (hw : 0 < w.re) (j l : ℕ) :
    IntegrableOn (longCutoffDecayTerm j l w) (Ioi 0) := by
  change IntegrableOn (fun r ↦ longCutoffDecayTerm j l w r) (Ioi 0)
  simpa only [IntegrableOn, longCutoffDecayTerm] using
    (integrableOn_pow_mul_decay hw (j - l)).const_mul
      ((-1 : ℂ) ^ l * ((j - 1).choose l : ℂ) / ((j - l)! : ℂ))

private theorem integrableOn_longCutoffProfile_decay {w : ℂ} (hw : 0 < w.re) (j : ℕ) :
    IntegrableOn (fun r : ℝ ↦ exp (-w * (r : ℂ)) * (longCutoffProfile j r : ℂ)) (Ici 0) := by
  rw [integrableOn_Ici_iff_integrableOn_Ioi]
  have hs : IntegrableOn (fun r : ℝ ↦ ∑ l ∈ Finset.range j, longCutoffDecayTerm j l w r)
      (Ioi 0) :=
    integrable_finsetSum _ fun l _ ↦ integrableOn_longCutoffDecayTerm hw j l
  exact hs.congr_fun (fun _ hr ↦ (longCutoffProfile_decay_eq_sum j w (le_of_lt hr)).symm)
    measurableSet_Ioi

private theorem longCutoffProfile_decay_indicator (j : ℕ) (w : ℂ) (r : ℝ) :
    (Ici (0 : ℝ)).indicator (fun u : ℝ ↦ exp (-w * (u : ℂ)) * (longCutoffProfile j u : ℂ)) r =
      exp (-w * (r : ℂ)) * (longCutoffProfile j r : ℂ) := by
  by_cases hr : r ∈ Ici (0 : ℝ)
  · exact indicator_of_mem hr _
  · have hr' : r < 0 := lt_of_not_ge fun h ↦ hr (mem_Ici.mpr h)
    simp [indicator_of_notMem hr, longCutoffProfile_zero_of_neg j hr']

/-- The profile is absolutely integrable against the decaying exponential on the right half-plane. -/
public theorem integrable_longCutoffProfile_decay (j : ℕ) {w : ℂ} (hw : 0 < w.re) :
    Integrable (fun r : ℝ ↦ exp (-w * (r : ℂ)) * (longCutoffProfile j r : ℂ)) :=
  ((integrableOn_longCutoffProfile_decay hw j).integrable_indicator measurableSet_Ici).congr
    (ae_of_all _ (longCutoffProfile_decay_indicator j w))

/-- The one-sided Laplace transform of `h_j`, with parameter in the open right half-plane. -/
public theorem integral_longCutoffProfile_Ici {j : ℕ} (hj : 1 ≤ j) {w : ℂ} (hw : 0 < w.re) :
    (∫ r : ℝ in Ici 0, exp (-w * (r : ℂ)) * (longCutoffProfile j r : ℂ)) =
      (1 - w) ^ (j - 1) / w ^ (j + 1) := by
  have hw₀ : w ≠ 0 := by rintro rfl; simp at hw
  rw [integral_Ici_eq_integral_Ioi,
    setIntegral_congr_fun measurableSet_Ioi (fun _ hr ↦ longCutoffProfile_decay_eq_sum j w hr.le),
    integral_finsetSum _ (fun l _ ↦ integrableOn_longCutoffDecayTerm hw j l)]
  calc
    (∑ l ∈ Finset.range j, ∫ r : ℝ in Ioi 0, longCutoffDecayTerm j l w r) =
        ∑ l ∈ Finset.range j, (-1 : ℂ) ^ l * ((j - 1).choose l : ℂ) / w ^ (j - l + 1) := by
      refine Finset.sum_congr rfl fun l _ ↦ ?_
      simp only [longCutoffDecayTerm, integral_const_mul, integral_pow_mul_decay hw]
      have hf : ((j - l)! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
      field_simp
    _ = (∑ l ∈ Finset.range j, (-w) ^ l * 1 ^ (j - 1 - l) * ((j - 1).choose l : ℂ)) /
        w ^ (j + 1) := by
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl fun l hl ↦ ?_
      have hdeg : l + (j - l + 1) = j + 1 := by have := Finset.mem_range.mp hl; omega
      rw [one_pow, mul_one, neg_pow w l, ← hdeg, pow_add]
      field_simp
      rw [pow_add, pow_succ w (j - l)]
      ring
    _ = _ := by
      rw [show Finset.range j = Finset.range (j - 1 + 1) by congr 1; omega, ← add_pow]
      rw [neg_add_eq_sub]

private theorem integral_longCutoffProfile_decay {j : ℕ} (hj : 1 ≤ j) {w : ℂ} (hw : 0 < w.re) :
    (∫ r : ℝ, exp (-w * (r : ℂ)) * (longCutoffProfile j r : ℂ)) =
      (1 - w) ^ (j - 1) / w ^ (j + 1) := by
  rw [← integral_longCutoffProfile_Ici hj hw, ← integral_indicator measurableSet_Ici]
  exact integral_congr_ae (ae_of_all _ fun r ↦ (longCutoffProfile_decay_indicator j w r).symm)

private theorem longCutoffProfile_reflect_weight (j : ℕ) (w : ℂ) (a y : ℝ) :
    exp (w * (y : ℂ)) * (longCutoffProfile j (a - y) : ℂ) =
      exp (w * (a : ℂ)) * (exp (-w * ((a - y : ℝ) : ℂ)) * (longCutoffProfile j (a - y) : ℂ)) := by
  rw [← mul_assoc, ← exp_add, Complex.ofReal_sub]
  congr 2
  ring

private theorem integrable_longCutoffProfile_reflect (j : ℕ) {w : ℂ} (hw : 0 < w.re) (a : ℝ) :
    Integrable (fun y : ℝ ↦ exp (w * (y : ℂ)) * (longCutoffProfile j (a - y) : ℂ)) := by
  simp_rw [longCutoffProfile_reflect_weight j w a]
  simpa only [sub_eq_add_neg, add_comm a] using
    (((integrable_longCutoffProfile_decay j hw).comp_add_right a).comp_neg.const_mul
      (exp (w * (a : ℂ))))

private theorem integral_longCutoffProfile_reflect {j : ℕ} (hj : 1 ≤ j)
    {w : ℂ} (hw : 0 < w.re) (a : ℝ) :
    (∫ y : ℝ, exp (w * (y : ℂ)) * (longCutoffProfile j (a - y) : ℂ)) =
      exp (w * (a : ℂ)) * ((1 - w) ^ (j - 1) / w ^ (j + 1)) := by
  let f (r : ℝ) := exp (-w * (r : ℂ)) * (longCutoffProfile j r : ℂ)
  simp_rw [longCutoffProfile_reflect_weight j w a, integral_const_mul]
  change exp (w * (a : ℂ)) * (∫ y : ℝ, f (a - y)) = _
  have hshift : (∫ y : ℝ, f (a - y)) = ∫ r : ℝ, f r := by
    simp only [sub_eq_add_neg, add_comm a]
    rw [integral_neg_eq_self (fun r : ℝ ↦ f (r + a)), integral_add_right_eq_self]
  rw [hshift, integral_longCutoffProfile_decay hj hw]

/-- The spline has an absolutely convergent bilateral integral, even away from the right half-plane. -/
public theorem integrable_longCutoffSpline (j : ℕ) (hj : 1 ≤ j) {D : ℝ} (hD : 0 < D) (w : ℂ) :
    Integrable (fun y : ℝ ↦ exp (w * (y : ℂ)) * (longCutoffSpline j D y : ℂ)) := by
  have hc : Continuous (longCutoffSpline j D) := by
    refine continuous_finsetSum _ fun k _ ↦ ?_
    exact continuous_const.mul
      ((continuous_longCutoffProfile j).comp (continuous_const.sub continuous_id))
  have hs : HasCompactSupport (longCutoffSpline j D) :=
    isCompact_Icc.of_isClosed_subset isClosed_closure (tsupport_longCutoffSpline_subset hj hD)
  have hco : HasCompactSupport (fun y : ℝ ↦ (longCutoffSpline j D y : ℂ)) :=
    hs.comp_left Complex.ofReal_zero
  exact ((by fun_prop : Continuous (fun y : ℝ ↦ exp (w * (y : ℂ)))).mul
    (continuous_ofReal.comp hc)).integrable_of_hasCompactSupport hco.mul_left

/-- The bilateral Laplace transform of `B_j`, with the positive sign in the exponent. -/
public theorem integral_longCutoffSpline {j : ℕ} (hj : 1 ≤ j) {D : ℝ} (_hD : 0 < D)
    {w : ℂ} (hw : 0 < w.re) :
    (∫ y : ℝ, exp (w * (y : ℂ)) * (longCutoffSpline j D y : ℂ)) =
      exp ((j : ℂ) * (D : ℂ) * w) * (1 - exp (-(D : ℂ) * w)) ^ (j + 1) *
        ((1 - w) ^ (j - 1) / w ^ (j + 1)) := by
  let a (k : ℕ) : ℝ := ((j : ℝ) - (k : ℝ)) * D
  let c (k : ℕ) : ℂ := (-1 : ℂ) ^ k * ((j + 1).choose k : ℂ)
  let F (k : ℕ) (y : ℝ) : ℂ := c k * (exp (w * (y : ℂ)) * (longCutoffProfile j (a k - y) : ℂ))
  have hside (y : ℝ) : exp (w * (y : ℂ)) * (longCutoffSpline j D y : ℂ) =
      ∑ k ∈ Finset.range (j + 2), F k y := by
    rw [longCutoffSpline, Complex.ofReal_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    push_cast
    dsimp [F, c, a]
    ring
  simp_rw [hside]
  rw [integral_finsetSum _ (fun k _ ↦ (integrable_longCutoffProfile_reflect j hw (a k)).const_mul (c k))]
  let A := exp ((j : ℂ) * (D : ℂ) * w)
  let q := exp (-(D : ℂ) * w)
  let M := (1 - w) ^ (j - 1) / w ^ (j + 1)
  have hexp (k : ℕ) : exp (w * (a k : ℂ)) = A * q ^ k := by
    dsimp [a, A, q]
    rw [← exp_nat_mul, ← exp_add]
    congr 1
    push_cast
    ring
  calc
    (∑ k ∈ Finset.range (j + 2), ∫ y : ℝ, F k y) =
        A * (∑ k ∈ Finset.range (j + 2), (-q) ^ k * 1 ^ (j + 1 - k) *
          ((j + 1).choose k : ℂ)) * M := by
      rw [Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun k _ ↦ ?_
      simp only [F, integral_const_mul, integral_longCutoffProfile_reflect hj hw, hexp, one_pow,
        mul_one, neg_pow q k]
      change c k * (A * q ^ k * M) = _
      dsimp [c]
      ring
    _ = _ := by rw [← add_pow, neg_add_eq_sub]

/-- On `Re w = 1/2`, the rational multiplier has a common weight `|w|⁻²` at every order. -/
public theorem longCutoffSpline_carrier {j : ℕ} (hj : 1 ≤ j) {w : ℂ} (hw : w.re = 1 / 2) :
    (1 - w) ^ (j - 1) / w ^ (j + 1) =
      (((‖w‖ ^ 2)⁻¹ : ℝ) : ℂ) * ((starRingEnd ℂ) w / w) ^ j := by
  have hw₀ : w ≠ 0 := by rintro rfl; norm_num at hw
  have hconj : 1 - w = (starRingEnd ℂ) w := by
    apply Complex.ext
    · norm_num [hw]
    · simp
  have hn : (↑(‖w‖ ^ 2 : ℝ) : ℂ) = (starRingEnd ℂ) w * w := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_eq_conj_mul_self]
  have hc₀ : (starRingEnd ℂ) w ≠ 0 := by simpa using hw₀
  cases j with
  | zero => omega
  | succ n =>
    rw [Nat.succ_sub_one, hconj, Complex.ofReal_inv, hn, div_pow,
      pow_succ w (n + 1), pow_succ _ n]
    field_simp
    exact (pow_succ _ _).symm

/-- The Fourier transform of the half-tilted endpoint profile, with kernel `exp (-i x r)`. -/
public theorem integral_longCutoffProfile_halfTilt {j : ℕ} (hj : 1 ≤ j) (x : ℝ) :
    let w : ℂ := 1 / 2 + (x : ℂ) * I
    (∫ r : ℝ, exp (-(x : ℂ) * I * (r : ℂ)) *
      ((Real.exp (-r / 2) * longCutoffProfile j r : ℝ) : ℂ)) =
        (((‖w‖ ^ 2)⁻¹ : ℝ) : ℂ) * ((starRingEnd ℂ) w / w) ^ j := by
  intro w
  have hw : w.re = 1 / 2 := by simp [w, Complex.mul_re]
  rw [← longCutoffSpline_carrier hj hw, ← integral_longCutoffProfile_decay hj (hw ▸ (by norm_num))]
  apply integral_congr_ae
  refine ae_of_all _ fun r ↦ ?_
  dsimp only
  rw [Complex.ofReal_mul, Complex.ofReal_exp, ← mul_assoc, ← exp_add]
  congr 2
  push_cast
  dsimp [w]
  ring

end

end Masullo
