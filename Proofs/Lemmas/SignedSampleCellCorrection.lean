module

public import Mathlib.Analysis.Complex.LocallyUniformLimit
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Topology.Algebra.InfiniteSum.TsumUniformlyOn
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.PSeries

/-!
# Unit-cell correction for signed samples

Source: `c321e4c8:.godel/conjectures/closed/fixed-baseline-signed-full-zero-divisor.md:71–100`
(unchanged from scan `fa7259d` to the writer base).
Owning session: `01a20eab-a304-7e57-9eec-1f7fc75e3637`.

Scope: the exact unit-cell difference, its absolute tail with the scale factor `B`, the
Dirichlet-series comparison, and the normally convergent holomorphic sum of the weighted
corrections under the first moment. No assertions about poles or recovery are included.
-/

open Filter MeasureTheory Set
open scoped Interval Topology

namespace SignedSampleCellCorrection

/-- The sample at the left endpoint minus the integral over its unit cell. -/
@[expose] public noncomputable def cell (n : ℝ) (w : ℂ) : ℂ :=
  (n : ℂ) ^ (-w) - ∫ x : ℝ in n..n + 1, (x : ℂ) ^ (-w)

private theorem cpow_intervalIntegrable {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (z : ℂ) :
    IntervalIntegrable (fun x : ℝ => (x : ℂ) ^ z) volume a b := by
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le hab]
  exact fun x hx => (Complex.continuousAt_ofReal_cpow_const x z
    (Or.inr (ha.trans_le hx.1).ne')).continuousWithinAt

private theorem hasDerivAt_cpow {x : ℝ} (hx : 0 < x) (z : ℂ) :
    HasDerivAt (fun y : ℝ => (y : ℂ) ^ z) (z * (x : ℂ) ^ (z - 1)) x := by
  by_cases hz : z = 0
  · simp [hz, hasDerivAt_const]
  · exact hasDerivAt_ofReal_cpow_const hx.ne' hz

/-- Exact unit-cell difference; the identity has no restriction on the exponent. -/
public theorem cell_eq_integral {n : ℝ} (hn : 0 < n) (w : ℂ) :
    cell n w = w * ∫ x : ℝ in n..n + 1, ((n + 1 - x : ℝ) : ℂ) * (x : ℂ) ^ (-w - 1) := by
  have hab : n ≤ n + 1 := by linarith
  let g := fun x : ℝ => ((n + 1 - x : ℝ) : ℂ) * (x : ℂ) ^ (-w - 1)
  have hg : IntervalIntegrable g volume n (n + 1) := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hab]
    refine (by fun_prop : Continuous (fun x : ℝ => ((n + 1 - x : ℝ) : ℂ))).continuousOn.mul ?_
    exact fun x hx => (Complex.continuousAt_ofReal_cpow_const x _
      (Or.inr (hn.trans_le hx.1).ne')).continuousWithinAt
  have hd (x : ℝ) (hx : x ∈ [[n, n + 1]]) :
      HasDerivAt (fun y : ℝ => ((y - (n + 1) : ℝ) : ℂ) * (y : ℂ) ^ (-w))
        ((x : ℂ) ^ (-w) + w * g x) x := by
    rw [uIcc_of_le hab] at hx
    have hlin : HasDerivAt (fun y : ℝ => ((y - (n + 1) : ℝ) : ℂ)) 1 x := by
      simpa only [id_eq, Complex.ofReal_one] using
        ((hasDerivAt_id x).sub_const (n + 1)).ofReal_comp
    have hp := hlin.mul (hasDerivAt_cpow (hn.trans_le hx.1) (-w))
    change HasDerivAt (fun y : ℝ => ((y - (n + 1) : ℝ) : ℂ) * (y : ℂ) ^ (-w)) _ x at hp
    convert hp using 1
    simp only [g, Complex.ofReal_sub, one_mul]
    ring
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    ((cpow_intervalIntegrable hn hab (-w)).add (hg.const_mul w))
  rw [intervalIntegral.integral_add (cpow_intervalIntegrable hn hab (-w)) (hg.const_mul w),
    intervalIntegral.integral_const_mul] at h
  simp only [sub_self, Complex.ofReal_zero, zero_mul, show n - (n + 1) = -1 by ring,
    Complex.ofReal_neg, Complex.ofReal_one, neg_one_mul, sub_neg_eq_add, zero_add] at h
  change (n : ℂ) ^ (-w) - (∫ x : ℝ in n..n + 1, (x : ℂ) ^ (-w)) = w * _
  rw [← h]
  ring

/-- A single cell is bounded by the integral of the absolute derivative, without
replacing the latter by a value at an integer endpoint. -/
public theorem norm_cell_le_integral {n : ℝ} (hn : 0 < n) (w : ℂ) :
    ‖cell n w‖ ≤ ‖w‖ * ∫ x : ℝ in n..n + 1, x ^ (-w.re - 1) := by
  have hab : n ≤ n + 1 := by linarith
  rw [cell_eq_integral hn, norm_mul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  apply intervalIntegral.norm_integral_le_of_norm_le hab
  · refine Eventually.of_forall fun x hx => ?_
    have hx0 : 0 < x := hn.trans hx.1
    have hd : 0 ≤ n + 1 - x := sub_nonneg.mpr hx.2
    rw [norm_mul, Complex.norm_of_nonneg hd, Complex.norm_cpow_eq_rpow_re_of_pos hx0,
      Complex.sub_re, Complex.neg_re, Complex.one_re]
    exact mul_le_of_le_one_left (Real.rpow_nonneg hx0.le _) (by linarith [hx.1])
  · apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hab]
    exact fun x hx => (Real.continuousAt_rpow_const x _
      (Or.inl (hn.trans_le hx.1).ne')).continuousWithinAt

private theorem rpow_intervalIntegrable {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (p : ℝ) :
    IntervalIntegrable (fun x : ℝ => x ^ p) volume a b := by
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le hab]
  exact fun x hx => (Real.continuousAt_rpow_const x p
    (Or.inl (ha.trans_le hx.1).ne')).continuousWithinAt

/-- The scaled finite absolute tail is bounded uniformly in the number of cells. -/
public theorem sum_range_norm_cell_le (B L N : ℕ) (hL : 1 ≤ L) {w : ℂ} (hw : 0 < w.re) :
    ∑ j ∈ Finset.range N, (B : ℝ) * ‖cell (↑(L + j) : ℝ) w‖ ≤
      (B : ℝ) * ‖w‖ * (L : ℝ) ^ (-w.re) / w.re := by
  let p := -w.re - 1
  have hp : p < -1 := by dsimp [p]; linarith
  have hL0 : 0 < (L : ℝ) := by exact_mod_cast (by omega : 0 < L)
  have hpos (j : ℕ) : 0 < (L : ℝ) + (j : ℝ) := by positivity
  have hstep (j : ℕ) : (L : ℝ) + (j : ℝ) ≤ (L : ℝ) + ((j + 1 : ℕ) : ℝ) := by
    simp [Nat.cast_add]
  have hsum :
      (∑ j ∈ Finset.range N, ∫ x : ℝ in (↑(L + j) : ℝ)..(↑(L + j) : ℝ) + 1, x ^ p) =
        ∫ x : ℝ in (L : ℝ)..(L : ℝ) + (N : ℝ), x ^ p := by
    simpa [Nat.cast_add, add_assoc] using
      (intervalIntegral.sum_integral_adjacent_intervals
        (a := fun j : ℕ => (L : ℝ) + (j : ℝ)) (n := N)
        (fun j _ => rpow_intervalIntegrable (hpos j) (hstep j) p))
  have hint : (∫ x : ℝ in (L : ℝ)..(L : ℝ) + (N : ℝ), x ^ p) ≤
      ∫ x : ℝ in Ioi (L : ℝ), x ^ p := by
    rw [intervalIntegral.integral_of_le (le_add_of_nonneg_right (Nat.cast_nonneg N))]
    refine setIntegral_mono_set (integrableOn_Ioi_rpow_of_lt hp hL0) ?_
      (Ioc_subset_Ioi_self.eventuallySubset)
    exact (ae_restrict_mem measurableSet_Ioi).mono fun x hx => Real.rpow_nonneg
      (hL0.trans (show (L : ℝ) < x from hx)).le _
  have heval : (∫ x : ℝ in Ioi (L : ℝ), x ^ p) = (L : ℝ) ^ (-w.re) / w.re := by
    rw [integral_Ioi_rpow_of_lt hp hL0, show p + 1 = -w.re by dsimp [p]; ring, div_neg, neg_div,
      neg_neg]
  calc
    _ ≤ ∑ j ∈ Finset.range N, (B : ℝ) *
        (‖w‖ * ∫ x : ℝ in (↑(L + j) : ℝ)..(↑(L + j) : ℝ) + 1, x ^ p) := by
      apply Finset.sum_le_sum
      intro j _
      exact mul_le_mul_of_nonneg_left (norm_cell_le_integral (by
        simpa [Nat.cast_add] using hpos j) w) (Nat.cast_nonneg B)
    _ = (B : ℝ) * ‖w‖ * (∫ x : ℝ in (L : ℝ)..(L : ℝ) + (N : ℝ), x ^ p) := by
      simp_rw [← mul_assoc, ← Finset.mul_sum, hsum]
    _ ≤ (B : ℝ) * ‖w‖ * (∫ x : ℝ in Ioi (L : ℝ), x ^ p) :=
      mul_le_mul_of_nonneg_left hint (by positivity)
    _ = _ := by rw [heval, mul_div_assoc]

/-- Absolute summability of the tail from cell `L`, with the full scaled bound. -/
public theorem absolute_tail (B L : ℕ) (hL : 1 ≤ L) {w : ℂ} (hw : 0 < w.re) :
    Summable (fun j : ℕ => (B : ℝ) * ‖cell (↑(L + j) : ℝ) w‖) ∧
      (∑' j : ℕ, (B : ℝ) * ‖cell (↑(L + j) : ℝ) w‖) ≤
        (B : ℝ) * ‖w‖ * (L : ℝ) ^ (-w.re) / w.re := by
  have h := summable_of_sum_range_le (fun _ => mul_nonneg (Nat.cast_nonneg B) (norm_nonneg _))
    fun N => sum_range_norm_cell_le B L N hL hw
  exact ⟨h, h.tsum_le_of_sum_range_le fun N => sum_range_norm_cell_le B L N hL hw⟩

/-- The exponent attached to a sample scale `B` and center `ρ`. -/
@[expose] public def exponent (B : ℕ) (ρ s : ℂ) : ℂ := 1 + (B : ℂ) * (s - ρ)

/-- The unweighted correction for one center; the first cell has index `1`. -/
@[expose] public noncomputable def correction (B : ℕ) (ρ s : ℂ) : ℂ :=
  (B : ℂ) * ∑' j : ℕ, cell (↑(1 + j) : ℝ) (exponent B ρ s)

private theorem re_exponent (B : ℕ) (ρ s : ℂ) :
    (exponent B ρ s).re = 1 + (B : ℝ) * (s.re - ρ.re) := by
  simp [exponent, Complex.add_re, Complex.mul_re, Complex.sub_re]

private theorem norm_correction_le {B : ℕ} {ρ s : ℂ} (hw : 0 < (exponent B ρ s).re) :
    ‖correction B ρ s‖ ≤ (B : ℝ) * ‖exponent B ρ s‖ / (exponent B ρ s).re := by
  have ha := absolute_tail B 1 le_rfl hw
  have h1 : Summable (fun j : ℕ => ‖cell (↑(1 + j) : ℝ) (exponent B ρ s)‖) := by
    simpa using (absolute_tail 1 1 le_rfl hw).1
  rw [correction, norm_mul, Complex.norm_natCast]
  refine (mul_le_mul_of_nonneg_left (norm_tsum_le_tsum_norm h1) (Nat.cast_nonneg B)).trans ?_
  simpa only [tsum_mul_left, Nat.cast_one, Real.one_rpow, mul_one] using ha.2

private theorem summable_shift_rpow {p : ℝ} (hp : p < -1) :
    Summable (fun j : ℕ => (↑(1 + j) : ℝ) ^ p) := by
  simpa only [Nat.add_comm 1] using (summable_nat_add_iff 1).2 (Real.summable_nat_rpow.mpr hp)

private theorem tsum_cell_eq_sub_integral {w : ℂ} (hw : 1 < w.re) :
    (∑' j : ℕ, cell (↑(1 + j) : ℝ) w) =
      (∑' j : ℕ, (↑(1 + j) : ℂ) ^ (-w)) - 1 / (w - 1) := by
  let p := fun j : ℕ => ((↑(1 + j) : ℝ) : ℂ) ^ (-w)
  let d := fun j : ℕ => cell (↑(1 + j) : ℝ) w
  have hpos (j : ℕ) : 0 < (↑(1 + j) : ℝ) := by positivity
  have hstep (j : ℕ) : (↑(1 + j) : ℝ) ≤ (↑(1 + (j + 1)) : ℝ) := by
    simp [Nat.cast_add]
  have hps : Summable p := by
    refine (summable_shift_rpow (p := -w.re) (by linarith)).of_norm_bounded fun j => ?_
    simpa only [p, Complex.norm_cpow_eq_rpow_re_of_pos (hpos j), Complex.neg_re] using
      (le_rfl : (↑(1 + j) : ℝ) ^ (-w.re) ≤ (↑(1 + j) : ℝ) ^ (-w.re))
  have hdabs : Summable (fun j => ‖d j‖) := by
    simpa only [d, Nat.cast_one, one_mul] using
      (absolute_tail 1 1 le_rfl (by linarith : 0 < w.re)).1
  have hds : Summable d := hdabs.of_norm_bounded fun _ => le_rfl
  have hfinite (N : ℕ) :
      (∑ j ∈ Finset.range N, p j) - (∑ j ∈ Finset.range N, d j) =
        ∫ x : ℝ in (1 : ℝ)..(↑(1 + N) : ℝ), (x : ℂ) ^ (-w) := by
    simp_rw [← Finset.sum_sub_distrib, p, d, cell, sub_sub_cancel]
    simpa only [Nat.add_zero, Nat.cast_one, Nat.cast_add, add_assoc] using
      (intervalIntegral.sum_integral_adjacent_intervals
        (a := fun j : ℕ => (↑(1 + j) : ℝ)) (n := N)
        (fun j _ => cpow_intervalIntegrable (hpos j) (hstep j) (-w)))
  have hinf : Tendsto (fun N : ℕ => (↑(1 + N) : ℝ)) atTop atTop := by
    simpa only [Function.comp_def, Nat.add_comm 1] using
      (tendsto_natCast_atTop_atTop (R := ℝ)).comp (tendsto_add_atTop_nat 1)
  have hw' : (-w).re < -1 := by rw [Complex.neg_re]; linarith
  have lim := intervalIntegral_tendsto_integral_Ioi 1
    (integrableOn_Ioi_cpow_of_lt hw' zero_lt_one) hinf
  have heval : (∫ x : ℝ in Ioi (1 : ℝ), (x : ℂ) ^ (-w)) = 1 / (w - 1) := by
    rw [integral_Ioi_cpow_of_lt hw' zero_lt_one, Complex.ofReal_one, Complex.one_cpow,
      show -w + 1 = -(w - 1) by ring, div_neg, neg_div, neg_neg]
  have heq := tendsto_nhds_unique
    (hps.hasSum.tendsto_sum_nat.sub hds.hasSum.tendsto_sum_nat)
    (lim.congr' (Eventually.of_forall fun N => (hfinite N).symm))
  have hsub : (∑' j, d j) = (∑' j, p j) - 1 / (w - 1) := by
    rw [← heq.trans heval, sub_sub_cancel]
  simpa only [d, p, Complex.ofReal_natCast] using hsub

/-- On `Re w > 1`, the subtracted integral is exactly `1 / (s - ρ)` after scaling. -/
public theorem correction_eq_dirichlet_sub {B : ℕ} (hB : 1 ≤ B) {ρ s : ℂ}
    (hw : 1 < (exponent B ρ s).re) :
    correction B ρ s =
      (B : ℂ) * (∑' j : ℕ, (↑(1 + j) : ℂ) ^ (-exponent B ρ s)) - 1 / (s - ρ) := by
  have hB0 : (B : ℂ) ≠ 0 := by exact_mod_cast (by omega : B ≠ 0)
  have hdiff : s - ρ ≠ 0 := by
    intro h
    simp [exponent, h] at hw
  have hcancel : (B : ℂ) * (1 / (exponent B ρ s - 1)) = 1 / (s - ρ) := by
    rw [show exponent B ρ s - 1 = (B : ℂ) * (s - ρ) by unfold exponent; ring]
    field_simp
  rw [correction, tsum_cell_eq_sub_integral hw, mul_sub, hcancel]

private theorem differentiable_cpow_exponent (x : ℝ) (hx : 0 < x) :
    Differentiable ℂ (fun w : ℂ => (x : ℂ) ^ (-w)) := by
  simp_rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hx.ne')]
  fun_prop

private theorem differentiable_cellIntegral {n : ℝ} (hn : 0 < n) :
    Differentiable ℂ (fun w : ℂ => ∫ x : ℝ in n..n + 1, (x : ℂ) ^ (-w)) := by
  let l := fun x : ℝ => (Real.log x : ℂ)
  let F := fun w : ℂ => fun x : ℝ => Complex.exp (l x * (-w))
  let F' := fun w : ℂ => fun x : ℝ => F w x * (-l x)
  have hF (w : ℂ) (x : ℝ) : HasDerivAt (F · x) (F' w x) w := by
    have hid : HasDerivAt (fun v : ℂ => v) 1 w := hasDerivAt_id w
    have harg : HasDerivAt (fun v : ℂ => l x * (-v)) (-(l x)) w := by
      simpa only [Pi.neg_apply, mul_neg, mul_one] using hid.neg.const_mul (l x)
    exact (Complex.hasDerivAt_exp (l x * (-w))).comp w harg
  let U := (univ : Set ℂ) ×ˢ [[n, n + 1]]
  have hpos {x : ℝ} (hx : x ∈ [[n, n + 1]]) : 0 < x := by
    rw [uIcc_of_le (by linarith : n ≤ n + 1)] at hx
    exact hn.trans_le hx.1
  have hl : ContinuousOn (fun z : ℂ × ℝ => l z.2) U := by
    refine Complex.continuous_ofReal.comp_continuousOn ?_
    exact fun z hz => ((Real.continuousAt_log (hpos hz.2).ne').comp
      continuous_snd.continuousAt).continuousWithinAt
  have hFc : ContinuousOn (Function.uncurry F) U :=
    (hl.mul continuous_fst.neg.continuousOn).cexp
  have hF'c : ContinuousOn (fun z : ℂ × ℝ => F' z.1 z.2) U := hFc.mul hl.neg
  have hfd (z : ℂ × ℝ) : fderiv ℂ (F · z.2) z.1 =
      ContinuousLinearMap.smulRightL ℂ ℂ ℂ (ContinuousLinearMap.id ℂ ℂ) (F' z.1 z.2) :=
    (hF z.1 z.2).hasFDerivAt.fderiv
  have hcont : ContinuousOn (fun z : ℂ × ℝ => fderiv ℂ (F · z.2) z.1) U :=
    ((ContinuousLinearMap.smulRightL ℂ ℂ ℂ
      (ContinuousLinearMap.id ℂ ℂ)).continuous.comp_continuousOn hF'c).congr (fun z _ => hfd z)
  have hdiff (w : ℂ) : DifferentiableAt ℂ (fun z => ∫ x : ℝ in n..n + 1, F z x) w :=
    (intervalIntegral.hasFDerivAt_integral_of_continuousOn_fderiv (μ := volume)
      (x₀ := w) univ_mem hFc (fun x _ z _ => (hF z x).differentiableAt.differentiableWithinAt)
      hcont).differentiableAt
  have heq (w : ℂ) : (∫ x : ℝ in n..n + 1, (x : ℂ) ^ (-w)) =
      ∫ x : ℝ in n..n + 1, F w x := by
    refine intervalIntegral.integral_congr fun x hx => ?_
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (hpos hx).ne')]
    dsimp only [F, l]
    rw [Complex.ofReal_log (hpos hx).le]
  simpa only [heq] using (show Differentiable ℂ (fun z => ∫ x : ℝ in n..n + 1, F z x) from hdiff)

/-- Every unit-cell difference is entire in the exponent, including at `w = 1`. -/
public theorem differentiable_cell {n : ℝ} (hn : 0 < n) : Differentiable ℂ (cell n) :=
  (differentiable_cpow_exponent n hn).sub (differentiable_cellIntegral hn)

private theorem differentiableOn_tsum_of_locallyUniform {ι : Type*} {F : ι → ℂ → ℂ}
    {U : Set ℂ} (hU : IsOpen U) (hF : ∀ i, DifferentiableOn ℂ (F i) U)
    (h : SummableLocallyUniformlyOn F U) :
    DifferentiableOn ℂ (fun s => ∑' i, F i s) U := by
  obtain ⟨g, hg⟩ := h
  have hlim := hasSumLocallyUniformlyOn_iff_tendstoLocallyUniformlyOn.mp hg
  exact (hlim.congr_right hg.tsum_eqOn.symm).differentiableOn
    (Eventually.of_forall fun T => DifferentiableOn.fun_sum fun i (_ : i ∈ T) => hF i) hU

private theorem norm_cell_le_rpow {n δ : ℝ} (hn : 1 ≤ n) (hδ : 0 < δ) {w : ℂ}
    (hw : δ ≤ w.re) : ‖cell n w‖ ≤ ‖w‖ * n ^ (-δ - 1) := by
  have hpos : 0 < n := zero_lt_one.trans_le hn
  have hstep : n ≤ n + 1 := by linarith
  refine (norm_cell_le_integral hpos w).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
  have h := intervalIntegral.integral_mono_on hstep (rpow_intervalIntegrable hpos hstep _)
    (f := fun x : ℝ => x ^ (-w.re - 1)) (g := fun _ => n ^ (-δ - 1)) intervalIntegrable_const
    (fun x hx => (Real.rpow_le_rpow_of_exponent_le (hn.trans hx.1) (by linarith)).trans
      (Real.rpow_le_rpow_of_nonpos hpos hx.1 (by linarith)))
  rwa [intervalIntegral.integral_const, show n + 1 - n = 1 by ring, one_smul] at h

private theorem isOpen_positiveRe : IsOpen {w : ℂ | 0 < w.re} :=
  isOpen_lt continuous_const Complex.continuous_re

private theorem differentiableOn_cellSum :
    DifferentiableOn ℂ (fun w => ∑' j : ℕ, cell (↑(1 + j) : ℝ) w) {w : ℂ | 0 < w.re} := by
  apply differentiableOn_tsum_of_locallyUniform isOpen_positiveRe
  · exact fun j => (differentiable_cell (by positivity : (0 : ℝ) < (↑(1 + j) : ℝ))).differentiableOn
  apply SummableLocallyUniformlyOn_of_locally_bounded isOpen_positiveRe
  intro K hKU hK
  by_cases hne : K.Nonempty
  · obtain ⟨z, hz, hmin⟩ := hK.exists_isMinOn hne Complex.continuous_re.continuousOn
    obtain ⟨y, _, hmax⟩ := hK.exists_isMaxOn hne (continuous_norm (E := ℂ)).continuousOn
    have hz0 : 0 < z.re := hKU hz
    refine ⟨fun j => ‖y‖ * (↑(1 + j) : ℝ) ^ (-z.re - 1),
      (summable_shift_rpow (p := -z.re - 1) (by linarith)).mul_left _, ?_⟩
    intro j w hw
    exact (norm_cell_le_rpow (by exact_mod_cast (by omega : 1 ≤ 1 + j)) hz0 (hmin hw)).trans
      (mul_le_mul_of_nonneg_right (hmax hw) (Real.rpow_nonneg (by positivity) _))
  · refine ⟨fun _ => 0, summable_zero, fun _ w hw => ?_⟩
    exact (hne ⟨w, hw⟩).elim

/-- The correction constructed from the unit cells is holomorphic whenever `Re w > 0`. -/
public theorem correction_holomorphic (B : ℕ) (ρ : ℂ) :
    AnalyticOnNhd ℂ (correction B ρ) {s : ℂ | 0 < (exponent B ρ s).re} := by
  have hdiff : Differentiable ℂ (exponent B ρ) := by unfold exponent; fun_prop
  have hopen : IsOpen {s : ℂ | 0 < (exponent B ρ s).re} :=
    isOpen_positiveRe.preimage hdiff.continuous
  apply DifferentiableOn.analyticOnNhd _ hopen
  exact (differentiableOn_cellSum.comp hdiff.differentiableOn (fun _ h => h)).const_mul _

/-- The common half-plane for the weighted sum of corrections. -/
@[expose] public def halfPlane (B : ℕ) (a : ℝ) : Set ℂ :=
  {s | max (1 / 2) (a - 1 / (B : ℝ)) < s.re}

private theorem isOpen_halfPlane (B : ℕ) (a : ℝ) : IsOpen (halfPlane B a) :=
  isOpen_lt continuous_const Complex.continuous_re

private theorem positive_margin {B : ℕ} (hB : 1 ≤ B) {a : ℝ} {s : ℂ}
    (hs : s ∈ halfPlane B a) : 0 < 1 + (B : ℝ) * (s.re - a) := by
  have hB0 : 0 < (B : ℝ) := by exact_mod_cast (by omega : 0 < B)
  have hs' : a - 1 / (B : ℝ) < s.re := (le_max_right _ _).trans_lt hs
  have h := (lt_div_iff₀ hB0).mp (show a - s.re < 1 / (B : ℝ) by linarith)
  linarith only [h, show (B : ℝ) * (s.re - a) = -((a - s.re) * (B : ℝ)) by ring]

private theorem margin_le_re_exponent (B : ℕ) {ρ s : ℂ} {a : ℝ} (hρ : ρ.re ≤ a) :
    1 + (B : ℝ) * (s.re - a) ≤ (exponent B ρ s).re := by
  rw [re_exponent]
  exact add_le_add le_rfl (mul_le_mul_of_nonneg_left (sub_le_sub_left hρ _) (Nat.cast_nonneg B))

private theorem norm_exponent_le (B : ℕ) (ρ s : ℂ) :
    ‖exponent B ρ s‖ ≤ 1 + (B : ℝ) * (‖s‖ + ‖ρ‖) := by
  unfold exponent
  calc
    _ ≤ ‖(1 : ℂ)‖ + ‖(B : ℂ) * (s - ρ)‖ := norm_add_le _ _
    _ = 1 + (B : ℝ) * ‖s - ρ‖ := by rw [norm_one, norm_mul, Complex.norm_natCast]
    _ ≤ _ := add_le_add le_rfl (mul_le_mul_of_nonneg_left (norm_sub_le s ρ) (Nat.cast_nonneg B))

/-- On compact subsets of the common half-plane the individual corrections are bounded
by a constant times `1 + ‖ρ‖`, uniformly over centers with `Re ρ ≤ a`. -/
public theorem correction_compact_bound {B : ℕ} (hB : 1 ≤ B) {a : ℝ} {K : Set ℂ}
    (hK : K ⊆ halfPlane B a) (hKc : IsCompact K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ρ : ℂ, ρ.re ≤ a → ∀ s ∈ K,
      ‖correction B ρ s‖ ≤ C * (1 + ‖ρ‖) := by
  by_cases hne : K.Nonempty
  · obtain ⟨z, hz, hmin⟩ := hKc.exists_isMinOn hne Complex.continuous_re.continuousOn
    obtain ⟨y, _, hmax⟩ := hKc.exists_isMaxOn hne (continuous_norm (E := ℂ)).continuousOn
    let δ := 1 + (B : ℝ) * (z.re - a)
    have hδ : 0 < δ := positive_margin hB (hK hz)
    let M := 1 + (B : ℝ) * (‖y‖ + 1)
    have hM : 0 ≤ M := by dsimp [M]; positivity
    have hBM : (B : ℝ) ≤ M := by
      have hy : 0 ≤ (B : ℝ) * ‖y‖ := by positivity
      dsimp [M]
      rw [mul_add, mul_one]
      linarith
    refine ⟨(B : ℝ) * M / δ, by positivity, fun ρ hρ s hs => ?_⟩
    have hre : δ ≤ (exponent B ρ s).re := by
      refine le_trans ?_ (margin_le_re_exponent B hρ)
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_left (sub_le_sub_right (hmin hs) a)
        (Nat.cast_nonneg B))
    have hnw : ‖exponent B ρ s‖ ≤ M * (1 + ‖ρ‖) := by
      refine (norm_exponent_le B ρ s).trans ?_
      calc
        _ ≤ 1 + (B : ℝ) * (‖y‖ + ‖ρ‖) := add_le_add le_rfl
          (mul_le_mul_of_nonneg_left (add_le_add (hmax hs) le_rfl) (Nat.cast_nonneg B))
        _ = 1 + (B : ℝ) * ‖y‖ + (B : ℝ) * ‖ρ‖ := by ring
        _ ≤ M + M * ‖ρ‖ := by
          refine add_le_add ?_ (mul_le_mul_of_nonneg_right hBM (norm_nonneg _))
          dsimp [M]
          rw [mul_add, mul_one]
          linarith [Nat.cast_nonneg (α := ℝ) B]
        _ = _ := by ring
    calc
      _ ≤ (B : ℝ) * ‖exponent B ρ s‖ / (exponent B ρ s).re :=
        norm_correction_le (hδ.trans_le hre)
      _ ≤ (B : ℝ) * ‖exponent B ρ s‖ / δ :=
        div_le_div_of_nonneg_left (by positivity) hδ hre
      _ ≤ (B : ℝ) * (M * (1 + ‖ρ‖)) / δ :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hnw (Nat.cast_nonneg B)) hδ.le
      _ = _ := by rw [← mul_assoc, div_mul_eq_mul_div]
  · exact ⟨0, le_rfl, fun _ _ s hs => (hne ⟨s, hs⟩).elim⟩

/-- The first moment gives a summable absolute majorant on every compact subset. -/
public theorem weighted_corrections_compact_majorant {ι : Type*} {B : ℕ} (hB : 1 ≤ B) {a : ℝ}
    (ρ c : ι → ℂ) (hρ : ∀ i, (ρ i).re ≤ a)
    (hm : Summable (fun i => ‖c i‖ * (1 + ‖ρ i‖))) {K : Set ℂ}
    (hK : K ⊆ halfPlane B a) (hKc : IsCompact K) :
    ∃ u : ι → ℝ, Summable u ∧ ∀ i s, s ∈ K → ‖c i * correction B (ρ i) s‖ ≤ u i := by
  obtain ⟨C, _, hC⟩ := correction_compact_bound hB hK hKc
  refine ⟨fun i => C * (‖c i‖ * (1 + ‖ρ i‖)), hm.mul_left C, fun i s hs => ?_⟩
  dsimp only
  rw [norm_mul, mul_left_comm C]
  exact mul_le_mul_of_nonneg_left (hC (ρ i) (hρ i) s hs) (norm_nonneg _)

/-- The weighted corrections converge normally and their sum is holomorphic on
`Re s > max(1/2, a - 1/B)` under the first moment. -/
public theorem weighted_corrections_normal_and_holomorphic {ι : Type*} {B : ℕ} (hB : 1 ≤ B)
    {a : ℝ} (ρ c : ι → ℂ) (hρ : ∀ i, (ρ i).re ≤ a)
    (hm : Summable (fun i => ‖c i‖ * (1 + ‖ρ i‖))) :
    SummableLocallyUniformlyOn (fun i s => c i * correction B (ρ i) s) (halfPlane B a) ∧
      AnalyticOnNhd ℂ (fun s => ∑' i, c i * correction B (ρ i) s) (halfPlane B a) := by
  have hopen := isOpen_halfPlane B a
  have hnormal := SummableLocallyUniformlyOn_of_locally_bounded hopen
    (fun _ hK hKc => weighted_corrections_compact_majorant hB ρ c hρ hm hK hKc)
  refine ⟨hnormal, (differentiableOn_tsum_of_locallyUniform hopen ?_ hnormal).analyticOnNhd hopen⟩
  intro i
  refine ((correction_holomorphic B (ρ i)).differentiableOn.mono (fun s hs => ?_)).const_mul _
  exact (positive_margin hB hs).trans_le (margin_le_re_exponent B (hρ i))

end SignedSampleCellCorrection
