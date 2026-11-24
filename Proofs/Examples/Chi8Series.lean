module

public import Mathlib.NumberTheory.LSeries.DirichletContinuation
public import Mathlib.NumberTheory.LegendreSymbol.ZModChar
import Lemmas.DirichletPeriodicPrimitives
import Mathlib.NumberTheory.LSeries.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# The endpoint Dirichlet series of χ₈

Abel summation gives locally uniform convergence near `s = 1`. On the part
of that neighborhood to the right of `1`, the limit is mathlib's `LFunction`.
The identity theorem and convergence of holomorphic derivatives then give
both endpoint statements for the original (ungrouped) partial sums.
-/

open Filter Finset Set
open scoped Topology

namespace Masullo

/-- The complex Dirichlet character attached to the discriminant `8`. -/
@[expose] public def chi8Complex : DirichletCharacter ℂ 8 :=
  ZMod.χ₈.ringHomComp (Int.castRingHom ℂ)

private theorem chi8Complex_ne_one : chi8Complex ≠ 1 := by
  intro h
  have h3 : ZMod.χ₈ (3 : ZMod 8) = -1 := by decide
  have hu : IsUnit (3 : ZMod 8) := isUnit_iff_exists_inv.mpr ⟨3, by decide⟩
  have he := congrArg (fun χ : DirichletCharacter ℂ 8 ↦ χ (3 : ZMod 8)) h
  change (Int.castRingHom ℂ) (ZMod.χ₈ (3 : ZMod 8)) = _ at he
  rw [h3, MulChar.one_apply hu] at he
  norm_num at he

private noncomputable def chi8Partial (N : ℕ) (s : ℂ) : ℂ :=
  ∑ n ∈ Icc 1 N, LSeries.term (fun k : ℕ ↦ chi8Complex (k : ZMod 8)) s n

private theorem chi8Partial_hasDerivAt (N : ℕ) (s : ℂ) :
    HasDerivAt (chi8Partial N)
      (∑ n ∈ Icc 1 N, -(LSeries.term
        (LSeries.logMul fun k : ℕ ↦ chi8Complex (k : ZMod 8)) s n)) s :=
  HasDerivAt.fun_sum fun n _ ↦ LSeries.hasDerivAt_term _ n s

private theorem chi8Partial_one (N : ℕ) :
    chi8Partial N 1 = ∑ n ∈ Icc 1 N, chi8Complex (n : ZMod 8) / (n : ℂ) := by
  apply sum_congr rfl
  intro n hn
  rw [LSeries.term_of_ne_zero (by have := (Finset.mem_Icc.mp hn).1; omega), Complex.cpow_one]

private theorem chi8Partial_deriv_one (N : ℕ) :
    deriv (chi8Partial N) 1 =
      ∑ n ∈ Icc 1 N, -chi8Complex (n : ZMod 8) * (Real.log (n : ℝ) : ℂ) / (n : ℂ) := by
  rw [(chi8Partial_hasDerivAt N 1).deriv]
  apply sum_congr rfl
  intro n hn
  rw [LSeries.term_of_ne_zero (by have := (Finset.mem_Icc.mp hn).1; omega), Complex.cpow_one]
  unfold LSeries.logMul
  rw [Complex.natCast_log, ← neg_div, neg_mul, mul_comm (Complex.log (n : ℂ))]

private theorem chi8Partial_differentiableOn (N : ℕ) (U : Set ℂ) :
    DifferentiableOn ℂ (chi8Partial N) U :=
  fun s _ ↦ (chi8Partial_hasDerivAt N s).differentiableAt.differentiableWithinAt

private noncomputable def chi8Disk : Set ℂ := Metric.ball 1 (1 / 2)

private theorem chi8Disk_re_norm {s : ℂ} (hs : s ∈ chi8Disk) :
    1 / 2 < s.re ∧ ‖s‖ ≤ 2 := by
  have hb : ‖s - 1‖ < 1 / 2 := by
    simpa only [chi8Disk, Metric.mem_ball, dist_eq_norm] using hs
  have hre := (Complex.abs_re_le_norm (s - 1)).trans_lt hb
  rw [Complex.sub_re, Complex.one_re, abs_lt] at hre
  have hnorm := norm_add_le (s - 1) (1 : ℂ)
  rw [sub_add_cancel, norm_one] at hnorm
  constructor <;> linarith [hre.1]

private noncomputable def chi8Weight (x : ℝ) (s : ℂ) : ℂ := (x : ℂ) ^ (-s)

private theorem chi8Weight_norm {x : ℝ} (hx : 1 ≤ x) {s : ℂ} (hs : s ∈ chi8Disk) :
    ‖chi8Weight x s‖ ≤ x ^ (-(1 / 2) : ℝ) := by
  rw [chi8Weight, Complex.norm_cpow_eq_rpow_re_of_pos (zero_lt_one.trans_le hx), Complex.neg_re]
  exact Real.rpow_le_rpow_of_exponent_le hx (neg_le_neg (chi8Disk_re_norm hs).1.le)

private theorem chi8Weight_sub_norm {x : ℝ} (hx : 1 ≤ x) {s : ℂ} (hs : s ∈ chi8Disk) :
    ‖chi8Weight x s - chi8Weight (x + 1) s‖ ≤ 2 * x ^ (-(3 / 2) : ℝ) := by
  have hpos {t : ℝ} (ht : x ≤ t) : 0 < t := zero_lt_one.trans_le (hx.trans ht)
  have hderiv (t : ℝ) (ht : t ∈ Set.Icc x (x + 1)) :
      HasDerivWithinAt (chi8Weight · s) (-s * (t : ℂ) ^ (-s - 1)) (Set.Icc x (x + 1)) t := by
    have hn : -s ≠ 0 := by
      have h := (chi8Disk_re_norm hs).1
      intro he
      have hz : s = 0 := neg_eq_zero.mp he
      norm_num [hz] at h
    exact (hasDerivAt_ofReal_cpow_const (hpos ht.1).ne' hn).hasDerivWithinAt
  have hbound (t : ℝ) (ht : t ∈ Set.Ico x (x + 1)) :
      ‖-s * (t : ℂ) ^ (-s - 1)‖ ≤ 2 * x ^ (-(3 / 2) : ℝ) := by
    rw [norm_mul, norm_neg, Complex.norm_cpow_eq_rpow_re_of_pos (hpos ht.1),
      Complex.sub_re, Complex.neg_re, Complex.one_re]
    have hr := (chi8Disk_re_norm hs).1
    refine mul_le_mul (chi8Disk_re_norm hs).2 ?_ (Real.rpow_nonneg (hpos ht.1).le _) (by norm_num)
    exact (Real.rpow_le_rpow_of_exponent_le (hx.trans ht.1) (by linarith : -s.re - 1 ≤ -(3 / 2)))
      |>.trans (Real.rpow_le_rpow_of_nonpos (zero_lt_one.trans_le hx) ht.1 (by norm_num))
  have h := norm_image_sub_le_of_norm_deriv_le_segment' hderiv hbound (x + 1)
    (Set.right_mem_Icc.mpr (by linarith))
  rw [add_sub_cancel_left, mul_one, norm_sub_rev] at h
  exact h

private noncomputable def chi8Prefix (N : ℕ) : ℂ :=
  ∑ n ∈ Icc 1 N, chi8Complex (n : ZMod 8)

private theorem chi8Prefix_bounded : ∃ B : ℝ, 0 ≤ B ∧ ∀ N : ℕ, ‖chi8Prefix N‖ ≤ B := by
  obtain ⟨B, hB, hb⟩ := (dirichletPartialSum_data chi8Complex chi8Complex_ne_one).bounded
  refine ⟨B, hB, fun N ↦ ?_⟩
  cases N with
  | zero => simpa [chi8Prefix] using hB
  | succ N =>
    simpa only [chi8Prefix, dirichletPartialSum, Nat.floor_natCast] using
      hb ((N.succ : ℕ) : ℝ) (by exact_mod_cast Nat.succ_pos N)

private noncomputable def chi8AbelTerm (n : ℕ) (s : ℂ) : ℂ :=
  chi8Prefix (n + 1) * (chi8Weight ((n : ℝ) + 1) s - chi8Weight (((n : ℝ) + 1) + 1) s)

private theorem chi8Partial_eq_abel (N : ℕ) (s : ℂ) :
    chi8Partial N s = (∑ n ∈ range N, chi8AbelTerm n s) +
      chi8Prefix N * chi8Weight ((N : ℝ) + 1) s := by
  induction N with
  | zero => simp [chi8Partial, chi8Prefix]
  | succ N ih =>
    have hp : chi8Prefix (N + 1) = chi8Prefix N + chi8Complex ((N + 1 : ℕ) : ZMod 8) :=
      sum_Icc_succ_top (by omega) _
    have ht := sum_Icc_succ_top (a := 1) (b := N) (by omega)
      (LSeries.term (fun k : ℕ ↦ chi8Complex (k : ZMod 8)) s)
    change chi8Partial (N + 1) s = chi8Partial N s + _ at ht
    rw [ht, ih, sum_range_succ, chi8AbelTerm, hp, Nat.cast_succ]
    rw [LSeries.term_of_ne_zero (by omega : N + 1 ≠ 0), div_eq_mul_inv, ← Complex.cpow_neg]
    simp only [chi8Weight, Complex.ofReal_add, Complex.ofReal_natCast, Complex.ofReal_one,
      Nat.cast_add, Nat.cast_one]
    ring

private theorem chi8Partial_uniform_limit :
    TendstoUniformlyOn chi8Partial (fun s ↦ ∑' n : ℕ, chi8AbelTerm n s) atTop chi8Disk := by
  obtain ⟨B, hB, hb⟩ := chi8Prefix_bounded
  have hsum : Summable (fun n : ℕ ↦ B * (2 * ((n : ℝ) + 1) ^ (-(3 / 2) : ℝ))) := by
    have hr := Real.summable_nat_rpow.mpr (by norm_num : (-(3 / 2) : ℝ) < -1)
    simpa only [Nat.cast_add, Nat.cast_one] using
      ((summable_nat_add_iff 1).mpr hr |>.mul_left (2 : ℝ)).mul_left B
  have hu := tendstoUniformlyOn_tsum_nat hsum (s := chi8Disk) (f := chi8AbelTerm) (by
    intro n s hs
    rw [chi8AbelTerm, norm_mul]
    exact mul_le_mul (hb _) (chi8Weight_sub_norm (le_add_of_nonneg_left (Nat.cast_nonneg n)) hs)
      (norm_nonneg _) hB)
  have hrem : TendstoUniformlyOn (fun (N : ℕ) s ↦ chi8Prefix N * chi8Weight ((N : ℝ) + 1) s)
      (fun _ ↦ 0) atTop chi8Disk := by
    have hpow : Tendsto (fun N : ℕ ↦ ((N : ℝ) + 1) ^ (-(1 / 2) : ℝ)) atTop (𝓝 0) := by
      exact (tendsto_rpow_neg_atTop (by norm_num)).comp
        (tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_natCast_atTop_atTop)
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    have hh : Tendsto (fun N : ℕ ↦ B * ((N : ℝ) + 1) ^ (-(1 / 2) : ℝ)) atTop (𝓝 0) := by
      simpa only [mul_zero] using hpow.const_mul B
    filter_upwards [hh.eventually (gt_mem_nhds hε)] with N hN s hs
    rw [dist_zero_left, norm_mul]
    exact (mul_le_mul (hb _) (chi8Weight_norm (le_add_of_nonneg_left (Nat.cast_nonneg N)) hs)
      (norm_nonneg _) hB).trans_lt hN
  have h := hu.add hrem
  simp only [Pi.add_def, add_zero] at h
  exact h.congr (Eventually.of_forall fun N s _ ↦ (chi8Partial_eq_abel N s).symm)

private theorem chi8Partial_tendsto_of_one_lt_re {s : ℂ} (hs : 1 < s.re) :
    Tendsto (fun N ↦ chi8Partial N s) atTop (𝓝 (chi8Complex.LFunction s)) := by
  rw [chi8Complex.LFunction_eq_LSeries hs]
  have h : HasSum (LSeries.term (fun k : ℕ ↦ chi8Complex (k : ZMod 8)) s)
      (LSeries (fun k : ℕ ↦ chi8Complex (k : ZMod 8)) s) :=
    (chi8Complex.LSeriesSummable_of_one_lt_re hs).LSeriesHasSum
  have hshift := (hasSum_nat_add_iff' 1).mpr h
  simp only [sum_range_one, LSeries.term_zero, sub_zero] at hshift
  refine hshift.tendsto_sum_nat.congr fun N ↦ ?_
  simp only [chi8Partial, ← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range,
    Nat.add_sub_cancel, Nat.add_comm 1]

private theorem chi8Partial_uniform :
    TendstoUniformlyOn chi8Partial chi8Complex.LFunction atTop chi8Disk := by
  let g : ℂ → ℂ := fun s ↦ ∑' n : ℕ, chi8AbelTerm n s
  have h : TendstoUniformlyOn chi8Partial g atTop chi8Disk := chi8Partial_uniform_limit
  have hopen : IsOpen chi8Disk := Metric.isOpen_ball
  have hd : DifferentiableOn ℂ g chi8Disk := h.tendstoLocallyUniformlyOn.differentiableOn
    (Eventually.of_forall fun N ↦ chi8Partial_differentiableOn N chi8Disk) hopen
  have hz : (5 / 4 : ℂ) ∈ chi8Disk := by
    rw [chi8Disk, Metric.mem_ball, dist_eq_norm, show (5 / 4 : ℂ) - 1 = (1 / 4 : ℝ) by norm_num,
      Complex.norm_real, Real.norm_of_nonneg (by norm_num)]
    norm_num
  have hzre : (5 / 4 : ℂ) ∈ {s : ℂ | 1 < s.re} := by
    change 1 < (5 / 4 : ℂ).re
    have he : (5 / 4 : ℂ) = ((5 / 4 : ℝ) : ℂ) := by norm_num
    rw [he, Complex.ofReal_re]
    norm_num
  have heq : g =ᶠ[𝓝 (5 / 4 : ℂ)] chi8Complex.LFunction := by
    filter_upwards [hopen.mem_nhds hz, (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hzre]
      with s hs hsr
    exact tendsto_nhds_unique (h.tendstoLocallyUniformlyOn.tendsto_at hs)
      (chi8Partial_tendsto_of_one_lt_re hsr)
  exact h.congr_right ((hd.analyticOnNhd hopen).eqOn_of_preconnected_of_eventuallyEq
    ((DirichletCharacter.differentiable_LFunction chi8Complex_ne_one).differentiableOn.analyticOnNhd
      hopen) (convex_ball (1 : ℂ) (1 / 2)).isPreconnected hz heq)

private theorem one_mem_chi8Disk : (1 : ℂ) ∈ chi8Disk :=
  Metric.mem_ball_self (by norm_num)

/-- The positive-index Dirichlet partial sums converge to the continued `LFunction` at `1`. -/
public theorem tendsto_chi8_series_one :
    Tendsto (fun N : ℕ ↦ ∑ n ∈ Icc 1 N, chi8Complex (n : ZMod 8) / (n : ℂ))
      atTop (𝓝 (chi8Complex.LFunction 1)) :=
  (chi8Partial_uniform.tendstoLocallyUniformlyOn.tendsto_at one_mem_chi8Disk).congr chi8Partial_one

/-- The partial sums with the negative logarithmic weight converge to the complex derivative
of the continued `LFunction` at `1`. -/
public theorem tendsto_chi8_deriv_series_one :
    Tendsto (fun N : ℕ ↦ ∑ n ∈ Icc 1 N,
      -chi8Complex (n : ZMod 8) * (Real.log (n : ℝ) : ℂ) / (n : ℂ))
      atTop (𝓝 (deriv chi8Complex.LFunction 1)) := by
  have h := chi8Partial_uniform.tendstoLocallyUniformlyOn.deriv
    (Eventually.of_forall fun N ↦ chi8Partial_differentiableOn N chi8Disk) Metric.isOpen_ball
  exact (h.tendsto_at one_mem_chi8Disk).congr chi8Partial_deriv_one

/-- Real-coefficient form of `tendsto_chi8_series_one`. -/
public theorem tendsto_chi8_series_one_re :
    Tendsto (fun N : ℕ ↦ ∑ n ∈ Icc 1 N, (ZMod.χ₈ (n : ZMod 8) : ℝ) / (n : ℝ))
      atTop (𝓝 (chi8Complex.LFunction 1).re) := by
  refine (Complex.continuous_re.continuousAt.tendsto.comp tendsto_chi8_series_one).congr fun N ↦ ?_
  change (∑ n ∈ Icc 1 N, chi8Complex (n : ZMod 8) / (n : ℂ)).re = _
  have h : Complex.ofReal (∑ n ∈ Icc 1 N, (ZMod.χ₈ (n : ZMod 8) : ℝ) / (n : ℝ)) =
      ∑ n ∈ Icc 1 N, chi8Complex (n : ZMod 8) / (n : ℂ) := by
    simp only [Complex.ofReal_sum, Complex.ofReal_div, Complex.ofReal_intCast,
      Complex.ofReal_natCast, chi8Complex, MulChar.ringHomComp_apply, Int.coe_castRingHom]
  rw [← h, Complex.ofReal_re]

/-- Real-coefficient form of `tendsto_chi8_deriv_series_one`. -/
public theorem tendsto_chi8_deriv_series_one_re :
    Tendsto (fun N : ℕ ↦ ∑ n ∈ Icc 1 N, -(ZMod.χ₈ (n : ZMod 8) : ℝ) * Real.log n / (n : ℝ))
      atTop (𝓝 (deriv chi8Complex.LFunction 1).re) := by
  refine (Complex.continuous_re.continuousAt.tendsto.comp tendsto_chi8_deriv_series_one).congr fun N ↦ ?_
  change (∑ n ∈ Icc 1 N, -chi8Complex (n : ZMod 8) * (Real.log (n : ℝ) : ℂ) / (n : ℂ)).re = _
  have h : Complex.ofReal (∑ n ∈ Icc 1 N, -(ZMod.χ₈ (n : ZMod 8) : ℝ) * Real.log n / (n : ℝ)) =
      ∑ n ∈ Icc 1 N, -chi8Complex (n : ZMod 8) * (Real.log (n : ℝ) : ℂ) / (n : ℂ) := by
    simp only [Complex.ofReal_sum, Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_neg,
      Complex.ofReal_intCast, Complex.ofReal_natCast, chi8Complex, MulChar.ringHomComp_apply,
      Int.coe_castRingHom]
  rw [← h, Complex.ofReal_re]

end Masullo
