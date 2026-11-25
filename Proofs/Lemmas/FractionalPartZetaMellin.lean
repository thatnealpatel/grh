module

public import Mathlib.NumberTheory.LSeries.RiemannZeta
import Lemmas.BoundedMellinTail
import Mathlib.Analysis.PSeriesComplex
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.NumberTheory.AbelSummation
import Mathlib.NumberTheory.Harmonic.ZetaAsymp

/-! # The Mellin transform of the fractional part

Abel summation identifies the tail above `1` with a regularization of the zeta function
on `1 < s.re`. Holomorphy of the bounded Mellin tail then continues this equation to
`0 < s.re`. On the strip `0 < s.re < 1` the contribution below `1` cancels the pole term.
-/

open Complex Filter MeasureTheory Set
open scoped Topology

namespace Masullo

private noncomputable abbrev fractC (x : ℝ) : ℂ := Complex.ofReal (Int.fract x)

private noncomputable abbrev fractKernel (s : ℂ) (x : ℝ) : ℂ :=
  fractC x * (x : ℂ) ^ (-s - 1)

private noncomputable abbrev fractTail (s : ℂ) : ℂ := ∫ x in Ioi (1 : ℝ), fractKernel s x

private theorem measurable_fractC : Measurable fractC :=
  Complex.continuous_ofReal.measurable.comp measurable_fract

private theorem norm_fractC_le_one (x : ℝ) : ‖fractC x‖ ≤ 1 := by
  rw [fractC, Complex.norm_real, Real.norm_of_nonneg (Int.fract_nonneg x)]
  exact (Int.fract_lt_one x).le

private theorem integrableOn_fractKernel_tail {s : ℂ} (hs : 0 < s.re) :
    IntegrableOn (fractKernel s) (Ioi 1) := by
  have hk : ContinuousOn (fun x : ℝ ↦ (x : ℂ) ^ (-s - 1)) (Ioi 1) :=
    continuousOn_of_forall_continuousAt fun x hx ↦
      Complex.continuousAt_ofReal_cpow_const _ _ (Or.inr (zero_lt_one.trans hx).ne')
  have hi : IntegrableOn (fun x : ℝ ↦ x ^ (-s.re - 1)) (Ioi 1) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one
  refine hi.mono' (measurable_fractC.aestronglyMeasurable.mul
    (hk.aestronglyMeasurable measurableSet_Ioi)) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  have hx0 : 0 < x := zero_lt_one.trans hx
  rw [fractKernel, norm_mul, norm_cpow_eq_rpow_re_of_pos hx0, sub_re, neg_re, one_re]
  exact mul_le_of_le_one_left (Real.rpow_nonneg hx0.le _) (norm_fractC_le_one x)

private theorem ofReal_mul_cpow_kernel {x : ℝ} (hx : 0 < x) (s : ℂ) :
    (x : ℂ) * (x : ℂ) ^ (-s - 1) = (x : ℂ) ^ (-s) := by
  nth_rw 1 [← cpow_one (x : ℂ)]
  rw [← cpow_add _ _ (ofReal_ne_zero.mpr hx.ne'), show 1 + (-s - 1) = -s by ring]

private theorem fractKernel_eq_cpow_on_Ioo (s : ℂ) :
    EqOn (fractKernel s) (fun x : ℝ ↦ (x : ℂ) ^ (-s)) (Ioo 0 1) := by
  intro x hx
  rw [fractKernel, fractC, Int.fract_eq_self.mpr ⟨hx.1.le, hx.2⟩, ofReal_mul_cpow_kernel hx.1]

private theorem integrableOn_fractKernel_head {s : ℂ} (hs : s.re < 1) :
    IntegrableOn (fractKernel s) (Ioc 0 1) := by
  rw [IntegrableOn, ← Measure.restrict_congr_set Ioo_ae_eq_Ioc, ← IntegrableOn]
  refine (IntegrableOn.congr_fun ?_ (fractKernel_eq_cpow_on_Ioo s).symm measurableSet_Ioo)
  exact (intervalIntegral.integrableOn_Ioo_cpow_iff zero_lt_one).mpr (by rw [neg_re]; linarith)

/-- The fractional-part Mellin kernel is absolutely integrable on the open critical strip. -/
public theorem integrableOn_fract_mul_cpow {s : ℂ} (hs₀ : 0 < s.re) (hs₁ : s.re < 1) :
    IntegrableOn (fun x : ℝ ↦ Complex.ofReal (Int.fract x) * (x : ℂ) ^ (-s - 1)) (Ioi 0) := by
  rw [← Ioc_union_Ioi_eq_Ioi (zero_le_one : (0 : ℝ) ≤ 1)]
  exact (integrableOn_fractKernel_head hs₁).union (integrableOn_fractKernel_tail hs₀)

private theorem integral_fractKernel_head {s : ℂ} (hs : s.re < 1) :
    (∫ x in Ioc (0 : ℝ) 1, fractKernel s x) = 1 / (1 - s) := by
  rw [setIntegral_congr_set Ioo_ae_eq_Ioc.symm,
    setIntegral_congr_fun measurableSet_Ioo (fractKernel_eq_cpow_on_Ioo s),
    setIntegral_congr_set Ioo_ae_eq_Ioc, ← intervalIntegral.integral_of_le zero_le_one,
    integral_cpow (Or.inl (by rw [neg_re]; linarith))]
  have h : -s + 1 = 1 - s := by ring
  have hne : 1 - s ≠ 0 := by
    intro hz
    have := congrArg Complex.re hz
    simp only [sub_re, one_re, zero_re] at this
    linarith
  simp [h, zero_cpow hne]

private theorem differentiableOn_fractTail : DifferentiableOn ℂ fractTail {s | 0 < s.re} := by
  have heq (s : ℂ) : fractTail s = boundedMellinTail fractC s := by
    simp only [fractTail, fractKernel, boundedMellinTail, neg_add_rev, sub_eq_add_neg]
    rw [add_comm (-s) (-1)]
  rw [funext heq]
  exact boundedMellinTail_differentiableOn measurable_fractC zero_le_one
    (fun x _ ↦ norm_fractC_le_one x)

private def abelCoeff (n : ℕ) : ℂ := if n = 0 then 0 else 1

private theorem sum_abelCoeff (n : ℕ) : ∑ k ∈ Finset.Icc 0 n, abelCoeff k = (n : ℂ) := by
  rw [Finset.Icc_eq_cons_Ioc (Nat.zero_le n), Finset.sum_cons]
  have heq : (∑ k ∈ Finset.Ioc 0 n, abelCoeff k) = ∑ _k ∈ Finset.Ioc 0 n, (1 : ℂ) :=
    Finset.sum_congr rfl fun k hk ↦ by simp [abelCoeff, (Finset.mem_Ioc.mp hk).1.ne']
  rw [heq]
  simp [abelCoeff]

private theorem deriv_cpow_neg {s : ℂ} (hs : s ≠ 0) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun y : ℝ ↦ (y : ℂ) ^ (-s)) (-s * (x : ℂ) ^ (-s - 1)) x :=
  hasDerivAt_ofReal_cpow_const hx.ne' (neg_ne_zero.mpr hs)

private theorem abelFractKernel {s : ℂ} (hs : s ≠ 0) (n : ℕ) :
    (∑ k ∈ Finset.range (n + 1), 1 / (k : ℂ) ^ s) = (n : ℂ) ^ (-s) * n -
      ∫ x in Ioc (1 : ℝ) n, -s * ((x : ℂ) ^ (-s) - fractKernel s x) := by
  have hder (x : ℝ) (hx : x ∈ Icc (1 : ℝ) n) := deriv_cpow_neg hs (zero_lt_one.trans_le hx.1)
  have hint : IntegrableOn (deriv (fun x : ℝ ↦ (x : ℂ) ^ (-s))) (Icc (1 : ℝ) n) := by
    refine (ContinuousOn.integrableOn_Icc (f := fun x : ℝ ↦ -s * (x : ℂ) ^ (-s - 1)) ?_).congr_fun
      (fun x hx ↦ (hder x hx).deriv.symm) measurableSet_Icc
    exact continuousOn_const.mul (continuousOn_of_forall_continuousAt fun x hx ↦
      Complex.continuousAt_ofReal_cpow_const _ _ (Or.inr (zero_lt_one.trans_le hx.1).ne'))
  have hab := sum_mul_eq_sub_integral_mul₀' abelCoeff (by simp [abelCoeff]) n
    (fun x hx ↦ (hder x hx).differentiableAt) hint
  simp only [sum_abelCoeff, ofReal_natCast] at hab
  calc
    _ = ∑ k ∈ Finset.Icc 0 n, (k : ℂ) ^ (-s) * abelCoeff k := by
      rw [Nat.range_succ_eq_Icc_zero]
      refine Finset.sum_congr rfl fun k _ ↦ ?_
      by_cases hk : k = 0 <;> simp [abelCoeff, hk, cpow_neg, one_div, hs]
    _ = _ := by
      rw [hab]
      congr 1
      refine setIntegral_congr_fun measurableSet_Ioc fun x hx ↦ ?_
      have hx0 : 0 < x := zero_lt_one.trans hx.1
      rw [(hder x ⟨hx.1.le, hx.2⟩).deriv, ← ofReal_natCast,
        natCast_floor_eq_intCast_floor hx0.le, fractKernel, fractC,
        ← ofReal_mul_cpow_kernel hx0 s, ← sub_mul, ← ofReal_sub, Int.fract, sub_sub_cancel, mul_assoc]
      exact congrArg (-s * ·) (mul_comm _ _)

private theorem tendsto_abelBoundary {s : ℂ} (hs : 1 < s.re) :
    Tendsto (fun n : ℕ ↦ (n : ℂ) ^ (-s) * n) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have h := (tendsto_rpow_neg_atTop (show 0 < s.re - 1 by linarith)).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  have hn' : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  change (n : ℝ) ^ (-(s.re - 1)) = ‖(n : ℂ) ^ (-s) * n‖
  have he : ((n : ℝ) : ℂ) ^ (-s) * ((n : ℝ) : ℂ) = ((n : ℝ) : ℂ) ^ (-(s - 1)) := by
    rw [mul_comm, ← ofReal_mul_cpow_kernel hn' (s - 1), show -(s - 1) - 1 = -s by ring]
  rw [← ofReal_natCast, he, norm_cpow_eq_rpow_re_of_pos hn', neg_re, sub_re, one_re]

private theorem fractTail_eq_of_one_lt_re {s : ℂ} (hs : 1 < s.re) :
    fractTail s = 1 / (s - 1) - riemannZeta s / s := by
  have hs₀ : s ≠ 0 := Complex.ne_zero_of_one_lt_re hs
  have hpow : IntegrableOn (fun x : ℝ ↦ (x : ℂ) ^ (-s)) (Ioi 1) :=
    integrableOn_Ioi_cpow_of_lt (by rw [neg_re]; linarith) zero_lt_one
  have hfr := integrableOn_fractKernel_tail (zero_lt_one.trans hs)
  have hint : IntegrableOn (fun x : ℝ ↦ -s * ((x : ℂ) ^ (-s) - fractKernel s x)) (Ioi 1) :=
    (hpow.sub hfr).const_mul _
  have hlim := intervalIntegral_tendsto_integral_Ioi 1 hint
    (tendsto_natCast_atTop_atTop (R := ℝ))
  have hlim' : Tendsto (fun n : ℕ ↦ ∫ x in Ioc (1 : ℝ) n, -s * ((x : ℂ) ^ (-s) - fractKernel s x))
      atTop (𝓝 (∫ x in Ioi (1 : ℝ), -s * ((x : ℂ) ^ (-s) - fractKernel s x))) := by
    refine hlim.congr' ?_
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    exact intervalIntegral.integral_of_le (by exact_mod_cast hn)
  -- Both the Dirichlet series and the Abel expression have limits along natural endpoints.
  have hab := ((tendsto_abelBoundary hs).sub hlim').congr (fun n ↦ (abelFractKernel hs₀ n).symm)
  have hsum := ((Complex.summable_one_div_nat_cpow.mpr hs).hasSum.tendsto_sum_nat).comp
    (tendsto_add_atTop_nat 1)
  have heq := tendsto_nhds_unique hsum hab
  rw [← zeta_eq_tsum_one_div_nat_cpow hs, integral_const_mul, integral_sub hpow hfr,
    integral_Ioi_cpow_of_lt (by rw [neg_re]; linarith) (zero_lt_one : (0 : ℝ) < 1),
    ofReal_one, one_cpow, show -s + 1 = -(s - 1) by ring, neg_div_neg_eq, zero_sub] at heq
  change riemannZeta s = -(-s * (1 / (s - 1) - fractTail s)) at heq
  have h := congrArg (fun z : ℂ ↦ z / s) heq
  rw [neg_mul, neg_neg, mul_div_cancel_left₀ _ hs₀] at h
  rw [h]
  ring

private theorem ne_zero_of_re_pos {s : ℂ} (hs : 0 < s.re) : s ≠ 0 := by
  intro h
  simp [h] at hs

/-- After removing the pole, the tail above `1` equals `1 - riemannZeta₀ s` when
multiplied by `s`. Both sides are holomorphic throughout the right half-plane. -/
private theorem mul_fractTail_eq {s : ℂ} (hs : 0 < s.re) :
    s * fractTail s = 1 - riemannZeta₀ s := by
  let U : Set ℂ := {z | 0 < z.re}
  have hU : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hUc : IsPreconnected U :=
    ((convex_Ioi (0 : ℝ)).linear_preimage Complex.reLm).isPreconnected
  have hleft : AnalyticOnNhd ℂ (fun z ↦ z * fractTail z) U :=
    (differentiableOn_id.mul differentiableOn_fractTail).analyticOnNhd hU
  have hright : AnalyticOnNhd ℂ (fun z ↦ 1 - riemannZeta₀ z) U :=
    ((differentiable_const (1 : ℂ)).sub differentiable_riemannZeta₀).differentiableOn.analyticOnNhd hU
  refine hleft.eqOn_of_preconnected_of_eventuallyEq hright hUc
    (by norm_num [U] : (2 : ℂ) ∈ U) ?_ (show s ∈ U from hs)
  filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
    (show (2 : ℂ) ∈ {z : ℂ | 1 < z.re} by norm_num)] with z hz
  have hz' : 1 < z.re := hz
  have hn : z ≠ 1 := by
    intro he
    simp [he] at hz'
  change z * fractTail z = 1 - riemannZeta₀ z
  rw [fractTail_eq_of_one_lt_re hz', riemannZeta_eq_inv_sub_add hn]
  field_simp [sub_ne_zero.mpr hn, Complex.ne_zero_of_one_lt_re hz']
  ring

/-- The fractional-part Mellin tail on the right half-plane, away from `s = 1`. -/
public theorem integral_fract_mul_cpow_Ioi_one {s : ℂ} (hs : 0 < s.re) (hs₁ : s ≠ 1) :
    (∫ x in Ioi (1 : ℝ), Complex.ofReal (Int.fract x) * (x : ℂ) ^ (-s - 1)) =
      1 / (s - 1) - riemannZeta s / s := by
  have hz := mul_fractTail_eq hs
  rw [riemannZeta_eq_inv_sub_add hs₁]
  change fractTail s = _
  apply (mul_right_inj' (ne_zero_of_re_pos hs)).mp
  rw [hz]
  field_simp [sub_ne_zero.mpr hs₁, ne_zero_of_re_pos hs]
  ring

/-- The Mellin transform of the real fractional part, cast to `ℂ`, equals `-ζ(s) / s`
on `0 < s.re < 1`. Powers use the positive real base embedded in `ℂ`. -/
public theorem integral_fract_mul_cpow {s : ℂ} (hs₀ : 0 < s.re) (hs₁ : s.re < 1) :
    (∫ x in Ioi (0 : ℝ), Complex.ofReal (Int.fract x) * (x : ℂ) ^ (-s - 1)) = -riemannZeta s / s := by
  have hsne : s ≠ 1 := by
    intro h
    simp [h] at hs₁
  have hhead : IntervalIntegrable (fractKernel s) volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mpr
      (integrableOn_fractKernel_head hs₁)
  change (∫ x in Ioi (0 : ℝ), fractKernel s x) = _
  rw [← intervalIntegral.integral_interval_add_Ioi' hhead (integrableOn_fractKernel_tail hs₀),
    intervalIntegral.integral_of_le zero_le_one, integral_fractKernel_head hs₁]
  change 1 / (1 - s) + (∫ x in Ioi (1 : ℝ), Complex.ofReal (Int.fract x) * (x : ℂ) ^ (-s - 1)) = _
  rw [integral_fract_mul_cpow_Ioi_one hs₀ hsne, show 1 - s = -(s - 1) by ring, div_neg, neg_div]
  ring

end Masullo
