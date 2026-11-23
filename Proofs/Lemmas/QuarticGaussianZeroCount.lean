module

public import Mathlib.Analysis.Complex.JensenFormula
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.PSeries
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.SpecificLimits.Normed
import Lemmas.LogMellinDerivative

/-!
# Jensen counting for the quartic Gaussian Mellin integral

The coordinates `(a,b)` enumerate `ℤ[i]` without quotienting by its units.
The zero lattice point contributes zero to the theta series. The Mellin integral
is taken over the whole real log coordinate, without a normalizing factor of four.
-/

open Complex MeasureTheory MeromorphicOn Metric Set
open scoped BigOperators

namespace Masullo

/-- The quartic Gaussian on the complex plane. -/
public noncomputable def QuarticGaussianTest (z : ℂ) : ℂ :=
  z ^ 4 * (Real.exp (-(2 * Real.pi * ‖z‖ ^ 2)) : ℂ)

/-- The Gaussian integer corresponding to its two integer coordinates. -/
public noncomputable def QuarticGaussianLattice (a : ℤ × ℤ) : ℂ :=
  (a.1 : ℂ) + (a.2 : ℂ) * I

/-- The concrete quartic Gaussian theta profile in the log coordinate. -/
public noncomputable def QuarticGaussianB (x : ℝ) : ℂ :=
  ∑' a : ℤ × ℤ, QuarticGaussianTest ((Real.exp (x / 2) : ℂ) * QuarticGaussianLattice a)

/-- The concrete unnormalized quartic Gaussian Mellin transform. -/
public noncomputable def QuarticGaussianD (w : ℂ) : ℂ :=
  ∫ x : ℝ, QuarticGaussianB x * Complex.exp (w * (x : ℂ))

/-- The point of the critical line with ordinate `t`. -/
public noncomputable def QuarticGaussianLine (t : ℝ) : ℂ := (1 / 2 : ℂ) + (t : ℂ) * I

private theorem QuarticGaussianLine_injective : Function.Injective QuarticGaussianLine := by
  intro t u h
  simpa [QuarticGaussianLine, Complex.add_im, Complex.mul_im] using congrArg Complex.im h

/-- Both signs of the ordinate are counted, excluding the lower cutoff and including the upper. -/
public def QuarticGaussianBandZeros (j : ℕ) : Set ℝ :=
  {t | QuarticGaussianD (QuarticGaussianLine t) = 0 ∧
    (8192 : ℝ) * 2 ^ j < |t| ∧ |t| ≤ 8192 * 2 ^ (j + 1)}

/-- The weight of a line zero, capped at two. The order is taken after complexifying
    the ordinate; the affine change of coordinate has nonzero slope. -/
public noncomputable def QuarticGaussianCappedOrder (t : ℝ) : ℕ :=
  min (analyticOrderNatAt QuarticGaussianD (QuarticGaussianLine t)) 2

/-- The cap computed in the `w` coordinate is the cap for the holomorphic extension
    of the real-ordinate function `t ↦ D(1/2 + it)`. -/
public theorem QuarticGaussianCappedOrder_eq_ordinate (t : ℝ) :
    QuarticGaussianCappedOrder t = min
      (analyticOrderNatAt (fun z : ℂ ↦ QuarticGaussianD (1 / 2 + z * I)) (t : ℂ)) 2 := by
  let g : ℂ → ℂ := fun z ↦ 1 / 2 + z * I
  have hg : AnalyticAt ℂ g (t : ℂ) := by dsimp [g]; fun_prop
  have hderiv : HasDerivAt g I (t : ℂ) := by
    simpa only [g, id, one_mul] using
      ((hasDerivAt_id (t : ℂ)).mul_const I).const_add (1 / 2 : ℂ)
  have h := analyticOrderAt_comp_of_deriv_ne_zero (f := QuarticGaussianD) hg
    (by rw [hderiv.deriv]; exact I_ne_zero)
  change analyticOrderAt (fun z : ℂ ↦ QuarticGaussianD (1 / 2 + z * I)) (t : ℂ) =
    analyticOrderAt QuarticGaussianD (QuarticGaussianLine t) at h
  unfold QuarticGaussianCappedOrder analyticOrderNatAt
  rw [h]

private theorem QuarticGaussianLine_mem_disk {T t : ℝ} (ht : |t| ≤ T) :
    QuarticGaussianLine t ∈ closedBall (6 : ℂ) (T + 6) := by
  rw [mem_closedBall, dist_eq_norm]
  have hnorm : ‖QuarticGaussianLine t - 6‖ ≤ 11 / 2 + |t| := by
    have heq : QuarticGaussianLine t - 6 = (-11 / 2 : ℝ) + (t : ℂ) * I := by
      unfold QuarticGaussianLine
      push_cast
      ring
    rw [heq]
    simpa [norm_mul, Real.norm_eq_abs] using
      norm_add_le ((-11 / 2 : ℝ) : ℂ) ((t : ℂ) * I)
  linarith

private theorem QuarticGaussian_divisor_eq_order {F : ℂ → ℂ} (hF : Differentiable ℂ F)
    {r : ℝ} (hz : z ∈ closedBall (6 : ℂ) r) :
    divisor F (closedBall (6 : ℂ) r) z = (analyticOrderNatAt F z : ℤ) := by
  have h : AnalyticOnNhd ℂ F (closedBall (6 : ℂ) r) := fun w _ ↦ hF.analyticAt w
  rw [h.divisor_apply hz]
  unfold analyticOrderNatAt
  generalize analyticOrderAt F z = n
  induction n with
  | top => simp
  | coe n => simp

private theorem QuarticGaussian_order_ne_top {F : ℂ → ℂ} (hF : Differentiable ℂ F)
    (hc : F 6 ≠ 0) (z : ℂ) : analyticOrderAt F z ≠ ⊤ := by
  have h : AnalyticOnNhd ℂ F univ := fun w _ ↦ hF.analyticAt w
  apply h.analyticOrderAt_ne_top_of_isPreconnected isPreconnected_univ
    (mem_univ (6 : ℂ)) (mem_univ z)
  rw [(hF.analyticAt 6).analyticOrderAt_eq_zero.mpr hc]
  simp

private theorem QuarticGaussian_sum_capped_le_divisor {F : ℂ → ℂ}
    (hF : Differentiable ℂ F) {T : ℝ} (A : Finset ℝ) (hA : ∀ t ∈ A, |t| ≤ T) :
    ((∑ t ∈ A, min (analyticOrderNatAt F (QuarticGaussianLine t)) 2 : ℕ) : ℝ) ≤
      ((∑ᶠ z, divisor F (closedBall (6 : ℂ) (T + 6)) z : ℤ) : ℝ) := by
  classical
  let B := A.map ⟨QuarticGaussianLine, QuarticGaussianLine_injective⟩
  let E := divisor F (closedBall (6 : ℂ) (T + 6))
  have hs := E.finiteSupport (isCompact_closedBall _ _)
  let U := B ∪ hs.toFinset
  have hsum : ∑ᶠ z, E z = ∑ z ∈ U, E z :=
    finsum_eq_sum_of_support_subset _ fun _ hz ↦
      Finset.subset_union_right (hs.mem_toFinset.mpr hz)
  have hE : 0 ≤ E :=
    (show AnalyticOnNhd ℂ F (closedBall (6 : ℂ) (T + 6)) from
      fun z _ ↦ hF.analyticAt z).divisor_nonneg
  have hcount : (∑ t ∈ A, ((min (analyticOrderNatAt F (QuarticGaussianLine t)) 2 : ℕ) : ℤ)) ≤
      ∑ᶠ z, E z := by
    calc
      _ ≤ ∑ z ∈ B, E z := by
        dsimp only [B]
        rw [Finset.sum_map]
        apply Finset.sum_le_sum
        intro t ht
        change (↑(min (analyticOrderNatAt F (QuarticGaussianLine t)) 2) : ℤ) ≤ E (QuarticGaussianLine t)
        rw [QuarticGaussian_divisor_eq_order hF (QuarticGaussianLine_mem_disk (hA t ht))]
        exact_mod_cast (min_le_left (analyticOrderNatAt F (QuarticGaussianLine t)) 2)
      _ ≤ ∑ z ∈ U, E z :=
        Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left fun z _ _ ↦ hE z
      _ = _ := hsum.symm
  exact_mod_cast hcount

private theorem QuarticGaussian_sum_capped_le_jensen {F : ℂ → ℂ}
    (hF : Differentiable ℂ F) (hc : 0 < ‖F 6‖) {T M : ℝ} (hT : 0 ≤ T) (hM : 1 ≤ M)
    (hbound : ∀ z ∈ sphere (6 : ℂ) (2 * (T + 6)), ‖F z‖ ≤ M)
    (A : Finset ℝ) (hA : ∀ t ∈ A, |t| ≤ T) :
    ((∑ t ∈ A, min (analyticOrderNatAt F (QuarticGaussianLine t)) 2 : ℕ) : ℝ) ≤
      Real.log (M / ‖F 6‖) / Real.log 2 := by
  let r := T + 6
  have hr : 0 < r := by dsimp [r]; linarith
  have hR : 0 < 2 * r := by positivity
  have hs := AnalyticOnNhd.sum_divisor_le (f := F) (c := 6) (r := r) (R := 2 * r)
    (by simpa [abs_of_pos hr] using hr)
    (by rw [abs_of_pos hr, abs_of_pos hR]; linarith) hM (fun z _ ↦ hF.analyticAt z)
    (norm_pos_iff.mp hc) (by simpa [abs_of_pos hR, r] using hbound)
  rw [abs_of_pos hr, mul_div_cancel_right₀ _ hr.ne'] at hs
  exact (QuarticGaussian_sum_capped_le_divisor hF A hA).trans hs

private theorem QuarticGaussian_log_jensen_budget {T : ℕ} (hT : 8192 ≤ T) :
    let p : ℕ := 2 * (T + 6) + 9
    Real.log ((468000 : ℝ) * (2 * (p : ℝ)) ^ p) / Real.log 2 ≤
      10 * T * Real.log (6 * T) := by
  intro p
  have hT' : (8192 : ℝ) ≤ T := by exact_mod_cast hT
  have hp : (p : ℝ) = 2 * (T : ℝ) + 21 := by dsimp [p]; push_cast; ring
  have hp₀ : 0 < (p : ℝ) := by linarith
  have hlog₂ : 1 / 2 < Real.log 2 := lt_trans (by norm_num) Real.log_two_gt_d9
  have hlog₀ : 0 < Real.log 2 := by linarith
  have hlog : Real.log 468000 ≤ 14 := by
    rw [← Real.log_exp 14]
    apply Real.log_le_log (by norm_num)
    have he : (8 / 3 : ℝ) ≤ Real.exp 1 := le_of_lt (lt_trans (by norm_num) Real.exp_one_gt_d9)
    calc
      _ ≤ (8 / 3 : ℝ) ^ (14 : ℕ) := by norm_num
      _ ≤ Real.exp 1 ^ (14 : ℕ) := by gcongr
      _ = _ := by rw [← Real.exp_nat_mul]; norm_num
  have hlogT : 1 ≤ Real.log (6 * (T : ℝ)) := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos _) (by linarith [Real.exp_one_lt_three])
  have hle : Real.log (2 * (p : ℝ)) ≤ Real.log (6 * (T : ℝ)) :=
    Real.log_le_log (by positivity) (by linarith)
  rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow, div_le_iff₀ hlog₀]
  calc
    _ ≤ 14 + (p : ℝ) * Real.log (6 * (T : ℝ)) := by gcongr
    _ ≤ 5 * (T : ℝ) * Real.log (6 * (T : ℝ)) := by
      have hprod := mul_le_mul_of_nonneg_right (show (p : ℝ) + 14 ≤ 5 * (T : ℝ) by linarith)
        (show 0 ≤ Real.log (6 * (T : ℝ)) by linarith)
      nlinarith
    _ ≤ _ := by
      have h := mul_le_mul_of_nonneg_left hlog₂.le
        (show 0 ≤ 10 * (T : ℝ) * Real.log (6 * (T : ℝ)) by positivity)
      linarith

private theorem QuarticGaussian_dyadic_budget (j : ℕ) :
    10 * ((8192 * 2 ^ (j + 1) : ℕ) : ℝ) * Real.log (6 * ((8192 * 2 ^ (j + 1) : ℕ) : ℝ)) ≤
      ((163840 * 2 ^ j * (12 + j) : ℕ) : ℝ) := by
  push_cast
  rw [pow_succ]
  have heq : (6 : ℝ) * (8192 * (2 ^ j * 2)) = 98304 * 2 ^ j := by ring
  rw [heq, Real.log_mul (by norm_num) (by positivity), Real.log_pow]
  have hlog : Real.log 98304 ≤ 12 := by
    calc
      _ ≤ Real.log ((2 : ℝ) ^ (17 : ℕ)) := Real.log_le_log (by norm_num) (by norm_num)
      _ ≤ 12 := by rw [Real.log_pow]; norm_num; linarith [Real.log_two_lt_d9]
  have hlog₂ : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
  have hcast : 0 ≤ (j : ℝ) := by positivity
  have hj : (j : ℝ) * Real.log 2 ≤ (j : ℝ) * 1 := mul_le_mul_of_nonneg_left hlog₂ hcast
  rw [show (10 : ℝ) * (8192 * (2 ^ j * 2)) = 163840 * 2 ^ j by ring]
  exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)

/-- Jensen reduces the count through integer height `T` to the center lower bound and
    an explicit sphere envelope, with `p = 2(T+6)+9`. The capped count is of actual
    complex vanishing orders of the same Mellin transform, not of a proxy divisor. -/
public theorem QuarticGaussian_sum_capped_le_of_disk_bound
    (hD : Differentiable ℂ QuarticGaussianD) (hc : (1 / 1000 : ℝ) ≤ ‖QuarticGaussianD 6‖)
    {T : ℕ} (hT : 8192 ≤ T)
    (hbound : let p : ℕ := 2 * (T + 6) + 9
      ∀ w ∈ sphere (6 : ℂ) (2 * ((T : ℝ) + 6)),
        ‖QuarticGaussianD w‖ ≤ 468 * (2 * (p : ℝ)) ^ p)
    (A : Finset ℝ) (hA : ∀ t ∈ A, |t| ≤ (T : ℝ)) :
    ((∑ t ∈ A, QuarticGaussianCappedOrder t : ℕ) : ℝ) ≤ 10 * T * Real.log (6 * T) := by
  let p : ℕ := 2 * (T + 6) + 9
  let M : ℝ := 468 * (2 * (p : ℝ)) ^ p
  have hp : (1 : ℝ) ≤ p := by exact_mod_cast (show 1 ≤ p by dsimp [p]; omega)
  have hM : 1 ≤ M := by
    apply one_le_mul_of_one_le_of_one_le (by norm_num)
    exact one_le_pow₀ (by linarith)
  have hc' : 0 < ‖QuarticGaussianD 6‖ := lt_of_lt_of_le (by norm_num) hc
  have hj := QuarticGaussian_sum_capped_le_jensen hD hc' (Nat.cast_nonneg T) hM hbound A hA
  have hlog : Real.log (M / ‖QuarticGaussianD 6‖) ≤ Real.log (468000 * (2 * (p : ℝ)) ^ p) := by
    apply Real.log_le_log (by positivity)
    rw [div_le_iff₀ hc']
    calc
      M = (468000 * (2 * (p : ℝ)) ^ p) * (1 / 1000) := by dsimp [M]; ring
      _ ≤ _ := by gcongr
  calc
    _ ≤ Real.log (M / ‖QuarticGaussianD 6‖) / Real.log 2 := hj
    _ ≤ Real.log (468000 * (2 * (p : ℝ)) ^ p) / Real.log 2 :=
      div_le_div_of_nonneg_right hlog (Real.log_nonneg (by norm_num))
    _ ≤ _ := QuarticGaussian_log_jensen_budget hT

private noncomputable def QuarticGaussianQ (a : ℤ × ℤ) : ℝ := ‖QuarticGaussianLattice a‖ ^ 2

private theorem QuarticGaussianQ_eq (a : ℤ × ℤ) :
    QuarticGaussianQ a = (a.1 : ℝ) ^ 2 + (a.2 : ℝ) ^ 2 := by
  rw [QuarticGaussianQ, Complex.sq_norm, Complex.normSq_apply]
  simp [QuarticGaussianLattice, Complex.mul_re, Complex.mul_im, pow_two]

private theorem QuarticGaussianQ_ge_natAbs (a : ℤ × ℤ) :
    (a.1.natAbs : ℝ) + (a.2.natAbs : ℝ) ≤ QuarticGaussianQ a := by
  rw [QuarticGaussianQ_eq]
  have h (n : ℤ) : (n.natAbs : ℝ) ≤ (n : ℝ) ^ 2 := by
    rw [← sq_abs (n : ℝ), ← Int.cast_abs]
    have habs : (|n| : ℤ) = (n.natAbs : ℤ) := (Nat.cast_natAbs (α := ℤ) n).symm
    rw [habs]
    calc
      (n.natAbs : ℝ) ≤ ((n.natAbs ^ 2 : ℕ) : ℝ) := Nat.cast_le.mpr (by
        rw [pow_two]; exact Nat.le_mul_self _)
      _ = (↑(n.natAbs : ℤ) : ℝ) ^ 2 := by simp
  exact add_le_add (h a.1) (h a.2)

private theorem QuarticGaussianQ_ge_one {a : ℤ × ℤ} (ha : a ≠ (0, 0)) :
    1 ≤ QuarticGaussianQ a := by
  have hn : 1 ≤ a.1.natAbs + a.2.natAbs := by
    obtain ⟨m, n⟩ := a
    by_contra! hn
    apply ha
    simp only [Prod.mk.injEq]
    have hm : m.natAbs = 0 := by omega
    have hn' : n.natAbs = 0 := by omega
    exact ⟨Int.natAbs_eq_zero.mp hm, Int.natAbs_eq_zero.mp hn'⟩
  exact (by exact_mod_cast hn : (1 : ℝ) ≤ (a.1.natAbs : ℝ) + (a.2.natAbs : ℝ)).trans
    (QuarticGaussianQ_ge_natAbs a)

private theorem QuarticGaussian_geometric_int : HasSum (fun n : ℤ ↦ (2 / 3 : ℝ) ^ n.natAbs) 5 := by
  let q : ℝ := 2 / 3
  let f : ℤ → ℝ := fun n ↦ q ^ n.natAbs
  have hs : Summable f := Summable.of_nat_of_neg
    (by simpa [f] using summable_geometric_of_lt_one (by norm_num : 0 ≤ q) (by norm_num : q < 1))
    (by simpa [f] using summable_geometric_of_lt_one (by norm_num : 0 ≤ q) (by norm_num : q < 1))
  have hts : (∑' n : ℤ, f n) = 5 := by
    rw [tsum_int_eq_zero_add_two_mul_tsum_pnat (show f.Even by intro n; simp [f]) hs]
    change f 0 + 2 • (∑' n : ℕ+, (fun m : ℕ ↦ q ^ m) (n : ℕ)) = 5
    rw [tsum_pnat_eq_tsum_succ]
    simp only [f, Int.natAbs_zero, pow_zero, pow_succ]
    rw [tsum_mul_right, tsum_geometric_of_lt_one (by norm_num : 0 ≤ q) (by norm_num : q < 1)]
    norm_num [q]
  exact hts ▸ hs.hasSum

private theorem QuarticGaussian_gaussian_sum_bound {c v : ℝ} (hc : 3 / 2 ≤ c) (hv : 0 ≤ v) :
    let f : ℤ × ℤ → ℂ := fun a ↦ (QuarticGaussianLattice a) ^ 4 *
      (Real.exp (-(c * Real.exp v * QuarticGaussianQ a)) : ℂ)
    Summable (fun a ↦ ‖f a‖) ∧ ‖∑' a, f a‖ ≤ 200 * Real.exp (-(Real.exp v / 2)) := by
  intro f
  let k := Real.exp v
  have hk : 1 ≤ k := Real.one_le_exp_iff.mpr hv
  let q : ℤ → ℝ := fun n ↦ (2 / 3 : ℝ) ^ n.natAbs
  have hg := QuarticGaussian_geometric_int
  have hg' : HasSum (fun a : ℤ × ℤ ↦ q a.1 * q a.2) (5 * 5) :=
    hg.mul hg (hg.summable.mul_of_nonneg hg.summable (fun _ ↦ by positivity) (fun _ ↦ by positivity))
  have hmajor := hg'.mul_left (8 * Real.exp (-(k / 2)))
  have hle (a : ℤ × ℤ) : ‖f a‖ ≤ 8 * Real.exp (-(k / 2)) * (q a.1 * q a.2) := by
    by_cases ha : a = (0, 0)
    · subst a; simp [f, QuarticGaussianLattice, q]; positivity
    let n := QuarticGaussianQ a
    let m := a.1.natAbs + a.2.natAbs
    have hm : (m : ℝ) ≤ n := by simpa [m, n] using QuarticGaussianQ_ge_natAbs a
    have hn : 1 ≤ n := QuarticGaussianQ_ge_one ha
    have hprod : k / 2 + n ≤ c * k * n := by
      have h₁ : n ≤ k * n := le_mul_of_one_le_left (by positivity) hk
      have h₂ : k ≤ k * n := le_mul_of_one_le_right (by positivity) hn
      have h₃ : (3 / 2 : ℝ) * (k * n) ≤ c * (k * n) := by gcongr
      linarith
    have hsq : n ^ 2 ≤ 8 * Real.exp (n / 2) := by
      have he := Real.pow_div_factorial_le_exp (n / 2) (by positivity) 2
      norm_num at he
      linarith
    have hq : Real.exp (-(1 / 2 : ℝ)) ≤ 2 / 3 := by
      rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by norm_num)]
      linarith [Real.add_one_le_exp (1 / 2 : ℝ)]
    dsimp only [f]
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, Real.abs_exp,
      ← show (‖QuarticGaussianLattice a‖ ^ 2) ^ 2 = ‖QuarticGaussianLattice a‖ ^ 4 by
        rw [← pow_mul]]
    change n ^ 2 * Real.exp (-(c * k * n)) ≤ _
    calc
      _ ≤ (8 * Real.exp (n / 2)) * Real.exp (-(k / 2 + n)) := by
        gcongr
      _ = 8 * Real.exp (-(k / 2)) * Real.exp (-(n / 2)) := by
        rw [mul_assoc, ← Real.exp_add, mul_assoc, ← Real.exp_add]
        ring_nf
      _ ≤ 8 * Real.exp (-(k / 2)) * (q a.1 * q a.2) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        calc
          _ ≤ Real.exp ((m : ℝ) * -(1 / 2 : ℝ)) := Real.exp_le_exp.mpr (by linarith)
          _ = Real.exp (-(1 / 2 : ℝ)) ^ m := Real.exp_nat_mul ..
          _ ≤ (2 / 3 : ℝ) ^ m := pow_le_pow_left₀ (Real.exp_nonneg _) hq _
          _ = _ := pow_add ..
  refine ⟨hmajor.summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) hle, ?_⟩
  convert tsum_of_norm_bounded hmajor hle using 1
  simp only [k]
  ring

private theorem QuarticGaussianB_direct (x : ℝ) :
    QuarticGaussianB x = (Real.exp (2 * x) : ℂ) *
      ∑' a : ℤ × ℤ, QuarticGaussianLattice a ^ 4 *
        (Real.exp (-(2 * Real.pi * Real.exp x * QuarticGaussianQ a)) : ℂ) := by
  unfold QuarticGaussianB
  rw [← tsum_mul_left]
  congr 1
  funext a
  rw [QuarticGaussianTest, mul_pow, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    Real.abs_exp, mul_pow, ← Real.exp_nat_mul]
  norm_cast
  rw [← Real.exp_nat_mul]
  norm_num only [Nat.cast_ofNat]
  simp only [QuarticGaussianQ]
  rw [show (4 : ℝ) * (x / 2) = 2 * x by ring, show (2 : ℝ) * (x / 2) = x by ring]
  calc
    (Real.exp (2 * x) : ℂ) * QuarticGaussianLattice a ^ 4 *
        (Real.exp (-(2 * Real.pi * (Real.exp x * ‖QuarticGaussianLattice a‖ ^ 2))) : ℂ) =
      (Real.exp (2 * x) : ℂ) * QuarticGaussianLattice a ^ 4 *
        (Real.exp (-(2 * Real.pi * Real.exp x * ‖QuarticGaussianLattice a‖ ^ 2)) : ℂ) := by
      rw [mul_assoc (2 * Real.pi)]
    _ = _ := mul_assoc ..

/-- The defining lattice series supplies the positive-log theta estimate. -/
public theorem QuarticGaussianB_pos_decay {x : ℝ} (hx : 0 ≤ x) :
    ‖QuarticGaussianB x‖ ≤ 234 * Real.exp (3 * |x| - Real.exp |x| / 2) := by
  have h := (QuarticGaussian_gaussian_sum_bound (v := x) (c := 2 * Real.pi)
    (by linarith [Real.pi_gt_three]) hx).2
  rw [QuarticGaussianB_direct, norm_mul, Complex.norm_real, Real.norm_eq_abs, Real.abs_exp,
    abs_of_nonneg hx]
  calc
    _ ≤ Real.exp (2 * x) * (200 * Real.exp (-(Real.exp x / 2))) := by gcongr
    _ = 200 * Real.exp (2 * x - Real.exp x / 2) := by
      rw [mul_left_comm, ← Real.exp_add]; ring_nf
    _ ≤ _ := by
      apply mul_le_mul (by norm_num) (Real.exp_le_exp.mpr (by linarith))
        (Real.exp_nonneg _) (by norm_num)

/-- The precise Poisson-side representation for negative log coordinate implies the
    two-sided quantitative theta bound. The representation itself is a separate input. -/
public theorem QuarticGaussianB_decay_of_poisson
    (hpoisson : ∀ x : ℝ, x < 0 → QuarticGaussianB x =
      (1 / 32 : ℂ) * (Real.exp (-3 * x) : ℂ) *
        ∑' a : ℤ × ℤ, QuarticGaussianLattice a ^ 4 *
          (Real.exp (-(Real.pi / 2 * Real.exp (-x) * ‖QuarticGaussianLattice a‖ ^ 2)) : ℂ))
    (x : ℝ) : ‖QuarticGaussianB x‖ ≤ 234 * Real.exp (3 * |x| - Real.exp |x| / 2) := by
  rcases le_or_gt 0 x with hx | hx
  · exact QuarticGaussianB_pos_decay hx
  have h := (QuarticGaussian_gaussian_sum_bound (v := -x) (c := Real.pi / 2)
    (by linarith [Real.pi_gt_three]) (by linarith)).2
  rw [hpoisson x hx, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    Real.abs_exp, norm_div, norm_one, abs_of_neg hx, show ‖(32 : ℂ)‖ = 32 by norm_num,
    one_div, neg_mul]
  calc
    _ ≤ (32 : ℝ)⁻¹ * Real.exp (-(3 * x)) * (200 * Real.exp (-(Real.exp (-x) / 2))) :=
      mul_le_mul_of_nonneg_left h (by positivity)
    _ = (200 / 32 : ℝ) * Real.exp (-(3 * x) - Real.exp (-x) / 2) := by
      rw [mul_assoc, mul_left_comm (Real.exp _), ← mul_assoc, ← Real.exp_add]
      ring_nf
    _ ≤ 234 * Real.exp (3 * -x - Real.exp (-x) / 2) := by
      rw [show 3 * -x = -(3 * x) by ring]
      exact mul_le_mul_of_nonneg_right (by norm_num) (Real.exp_nonneg _)

private theorem QuarticGaussianB_measurable : Measurable QuarticGaussianB := by
  unfold QuarticGaussianB QuarticGaussianTest
  apply Measurable.tsum
  intro a
  fun_prop

private theorem QuarticGaussian_weighted_le (hB : ∀ x : ℝ,
    ‖QuarticGaussianB x‖ ≤ 234 * Real.exp (3 * |x| - Real.exp |x| / 2))
    (w : ℂ) (x : ℝ) :
    ‖QuarticGaussianB x * Complex.exp (w * (x : ℂ))‖ ≤
      234 * Real.exp ((3 + |w.re|) * |x| - Real.exp |x| / 2) := by
  rw [norm_mul, Complex.norm_exp, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, sub_zero]
  calc
    _ ≤ (234 * Real.exp (3 * |x| - Real.exp |x| / 2)) *
        Real.exp (|w.re| * |x|) := by
      exact mul_le_mul (hB x) (Real.exp_le_exp.mpr (by
        rw [← abs_mul]; exact le_abs_self _)) (Real.exp_nonneg _) (by positivity)
    _ = _ := by rw [mul_assoc, ← Real.exp_add]; ring_nf

/-- The recorded two-sided theta estimate implies entireness of the concrete integral. -/
public theorem QuarticGaussianD_differentiable_of_decay
    (hB : ∀ x : ℝ, ‖QuarticGaussianB x‖ ≤ 234 * Real.exp (3 * |x| - Real.exp |x| / 2)) :
    Differentiable ℂ QuarticGaussianD := by
  intro w
  let a := 6 + |w.re|
  apply (hasDerivAt_logMellin_of_measurable_decay QuarticGaussianB_measurable w
    (r := 1) (C := 234 * Real.exp (a ^ 2)) (by norm_num) (by positivity) ?_).2.2.differentiableAt
  intro x
  apply (QuarticGaussian_weighted_le hB w x).trans
  rw [mul_assoc, ← Real.exp_add]
  gcongr
  have hv := abs_nonneg x
  generalize |x| = v at hv ⊢
  have he := Real.pow_div_factorial_le_exp v hv 2
  norm_num at he ⊢
  dsimp only [a]
  nlinarith [sq_nonneg (v / 2 - (6 + |w.re|))]

-- Substitute first `y = exp x`, then `u = a*y`, in the complete log integral.
private theorem QuarticGaussian_logGamma (n : ℕ) {a : ℝ} (ha : 0 < a) :
    Integrable (fun x : ℝ ↦ Real.exp (((n : ℝ) + 1) * x - a * Real.exp x)) ∧
    (∫ x : ℝ, Real.exp (((n : ℝ) + 1) * x - a * Real.exp x)) =
      (a ^ (n + 1))⁻¹ * (n.factorial : ℝ) := by
  let g : ℝ → ℝ := fun y ↦ Real.exp (-y) * y ^ n
  have hg₁ : IntegrableOn g (Ioi 0) := by
    simpa [g, Real.rpow_natCast] using Real.GammaIntegral_convergent
      (show 0 < (n : ℝ) + 1 by positivity)
  have hg₂ : (∫ y in Ioi (0 : ℝ), g y) = (n.factorial : ℝ) := by
    rw [← Real.Gamma_nat_eq_factorial]
    rw [Real.Gamma_eq_integral (by positivity : (0 : ℝ) < (n : ℝ) + 1)]
    simp [g, Real.rpow_natCast]
  let G : ℝ → ℝ := fun y ↦ (a ^ n)⁻¹ * g (a * y)
  have hG : IntegrableOn (fun y ↦ g (a * y)) (Ioi (0 : ℝ)) :=
    (integrableOn_Ioi_comp_mul_left_iff g 0 ha).2 (by simpa using hg₁)
  have heq (x : ℝ) : Real.exp (((n : ℝ) + 1) * x - a * Real.exp x) =
      Real.exp x • G (Real.exp x) := by
    rw [show ((n : ℝ) + 1) * x - a * Real.exp x = x + ((n : ℝ) * x) + -(a * Real.exp x) by ring,
      Real.exp_add, Real.exp_add, Real.exp_nat_mul]
    simp only [G, g, mul_pow, smul_eq_mul]
    field_simp
  simp_rw [heq]
  refine ⟨(integrable_comp_exp G).2 (hG.const_mul _), ?_⟩
  rw [integral_comp_exp, show (∫ y in Ioi (0 : ℝ), G y) =
    (a ^ n)⁻¹ * ∫ y in Ioi (0 : ℝ), g (a * y) from integral_const_mul ..,
    integral_comp_mul_left_Ioi g 0 ha, mul_zero, hg₂, smul_eq_mul, pow_succ, mul_inv]
  ring

private noncomputable def QuarticGaussian_invSq (n : ℤ) : ℝ := ((n : ℝ) ^ 2)⁻¹

private theorem QuarticGaussian_invSq_summable : Summable QuarticGaussian_invSq := by
  exact Summable.of_nat_of_neg (by simp [QuarticGaussian_invSq])
    (by simp [QuarticGaussian_invSq])

private theorem QuarticGaussian_invSq_tsum_le : ∑' n : ℤ, QuarticGaussian_invSq n ≤ 4 := by
  have hz : QuarticGaussian_invSq 0 = 0 := by simp [QuarticGaussian_invSq]
  have he : QuarticGaussian_invSq.Even := by intro n; simp [QuarticGaussian_invSq]
  rw [tsum_int_eq_zero_add_two_mul_tsum_pnat he QuarticGaussian_invSq_summable, hz, zero_add]
  change 2 • (∑' i : ℕ+, (fun n : ℕ ↦ ((n : ℝ) ^ 2)⁻¹) (i : ℕ)) ≤ 4
  rw [tsum_pnat_eq_tsum_succ (f := fun n : ℕ ↦ ((n : ℝ) ^ 2)⁻¹), two_nsmul]
  suffices h : (∑' i : ℕ, (((i + 1 : ℕ) : ℝ) ^ 2)⁻¹) ≤ 2 by linarith
  apply Real.tsum_le_of_sum_range_le (fun _ ↦ by positivity)
  intro n
  have heq : Finset.Ioo 0 (n + 1) = (Finset.range n).map ⟨(· + 1), by
      intro a b h; exact Nat.add_right_cancel h⟩ := by
    ext i; simp only [Finset.mem_Ioo, Finset.mem_map, Finset.mem_range]
    change (0 < i ∧ i < n + 1) ↔ ∃ a, a < n ∧ a + 1 = i
    constructor
    · intro hi; exact ⟨i - 1, by omega, by omega⟩
    · rintro ⟨a, ha, rfl⟩; omega
  have h := sum_Ioo_inv_sq_le (α := ℝ) 0 (n + 1)
  rw [heq, Finset.sum_map] at h
  change (∑ i ∈ Finset.range n, (((i + 1 : ℕ) : ℝ) ^ 2)⁻¹) ≤ _ at h
  simpa using h

private noncomputable def QuarticGaussian_centerTerm (a : ℤ × ℤ) : ℂ :=
  QuarticGaussianLattice a ^ 4 * ((QuarticGaussianQ a ^ 8)⁻¹ : ℝ)

private theorem QuarticGaussian_centerTerm_norm (a : ℤ × ℤ) :
    ‖QuarticGaussian_centerTerm a‖ = (QuarticGaussianQ a ^ 6)⁻¹ := by
  have hn : 0 ≤ QuarticGaussianQ a := by rw [QuarticGaussianQ]; positivity
  rw [QuarticGaussian_centerTerm, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (by positivity), ← show QuarticGaussianQ a ^ 2 = ‖QuarticGaussianLattice a‖ ^ 4 by
      rw [QuarticGaussianQ, ← pow_mul]]
  by_cases h : QuarticGaussianQ a = 0
  · simp [h]
  · field_simp

private theorem QuarticGaussian_offaxis_bound (a : ℤ × ℤ) (h₁ : a.1 ≠ 0) (h₂ : a.2 ≠ 0) :
    ‖QuarticGaussian_centerTerm a‖ ≤ (1 / 64 : ℝ) *
      (QuarticGaussian_invSq a.1 * QuarticGaussian_invSq a.2) := by
  rw [QuarticGaussian_centerTerm_norm, QuarticGaussian_invSq, QuarticGaussian_invSq]
  let m := |(a.1 : ℝ)|
  let n := |(a.2 : ℝ)|
  have hm : 1 ≤ m := by dsimp [m]; rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs h₁
  have hn : 1 ≤ n := by dsimp [n]; rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs h₂
  have hq : QuarticGaussianQ a = m ^ 2 + n ^ 2 := by
    simp [QuarticGaussianQ_eq, m, n, sq_abs]
  rw [← sq_abs (a.1 : ℝ), ← sq_abs (a.2 : ℝ)]
  change (QuarticGaussianQ a ^ 6)⁻¹ ≤ 1 / 64 * ((m ^ 2)⁻¹ * (n ^ 2)⁻¹)
  have hmn : 1 ≤ m * n := one_le_mul_of_one_le_of_one_le hm hn
  have h₃ : 2 * (m * n) ≤ QuarticGaussianQ a := by rw [hq]; nlinarith [sq_nonneg (m - n)]
  have h₄ : (m * n) ^ 2 ≤ (m * n) ^ 6 := pow_le_pow_right₀ hmn (by decide)
  have h₅ : 64 * (m ^ 2 * n ^ 2) ≤ QuarticGaussianQ a ^ 6 := by
    calc
      _ ≤ (2 * (m * n)) ^ 6 := by rw [mul_pow, mul_pow] at *; norm_num; gcongr
      _ ≤ _ := pow_le_pow_left₀ (by positivity) h₃ _
  convert inv_anti₀ (show 0 < 64 * (m ^ 2 * n ^ 2) by positivity) h₅ using 1
  rw [mul_inv, mul_inv, one_div]

private theorem QuarticGaussian_axis_term (n : ℤ) :
    QuarticGaussian_centerTerm (n, 0) = (QuarticGaussian_invSq n ^ 6 : ℝ) ∧
    QuarticGaussian_centerTerm (0, n) = (QuarticGaussian_invSq n ^ 6 : ℝ) := by
  have hI : I ^ 4 = 1 := by rw [show (4 : ℕ) = 2 * 2 by decide, pow_mul, I_sq]; norm_num
  unfold QuarticGaussian_centerTerm QuarticGaussian_invSq
  simp only [QuarticGaussianQ_eq, QuarticGaussianLattice, Int.cast_zero, zero_mul,
    add_zero, zero_add, zero_pow (by decide : 2 ≠ 0), mul_pow, hI, mul_one]
  push_cast
  by_cases h : (n : ℂ) = 0
  · simp [h]
  · constructor <;> field_simp

private theorem QuarticGaussian_centerTerm_summable :
    Summable (fun a ↦ ‖QuarticGaussian_centerTerm a‖) := by
  let g := QuarticGaussian_invSq
  let δ : ℤ → ℝ := fun n ↦ if n = 0 then 1 else 0
  have hg (n : ℤ) : 0 ≤ g n := by exact inv_nonneg.mpr (sq_nonneg _)
  have hd (n : ℤ) : 0 ≤ δ n := by dsimp [δ]; split <;> positivity
  have hs : Summable δ := summable_of_ne_finset_zero (s := {0}) (by simp [δ])
  have hg' := QuarticGaussian_invSq_summable
  have hmajor := ((hg'.mul_of_nonneg hs hg hd).add (hs.mul_of_nonneg hg' hd hg)).add
    ((hg'.mul_of_nonneg hg' hg hg).mul_left (1 / 64))
  apply hmajor.of_nonneg_of_le (fun _ ↦ norm_nonneg _)
  have hgle (n : ℤ) : g n ^ 6 ≤ g n := by
    by_cases hn : n = 0
    · simp [hn, g, QuarticGaussian_invSq]
    have h : 1 ≤ |(n : ℝ)| := by rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hn
    have hg1 : g n ≤ 1 := inv_le_one_of_one_le₀ (by
      rw [← sq_abs]; nlinarith)
    calc
      g n ^ 6 = g n ^ 5 * g n := pow_succ ..
      _ ≤ 1 * g n := mul_le_mul_of_nonneg_right (pow_le_one₀ (hg n) hg1) (hg n)
      _ = g n := one_mul _
  rintro ⟨m, n⟩
  rcases eq_or_ne n 0 with rfl | hn
  · simpa [QuarticGaussian_axis_term, δ, g, QuarticGaussian_invSq, abs_of_nonneg (by positivity :
        0 ≤ (((m : ℝ) ^ 2)⁻¹) ^ 6)] using hgle m
  rcases eq_or_ne m 0 with rfl | hm
  · simpa [QuarticGaussian_axis_term, δ, g, QuarticGaussian_invSq, abs_of_nonneg (by positivity :
        0 ≤ (((n : ℝ) ^ 2)⁻¹) ^ 6)] using hgle n
  simpa [δ, hm, hn, g] using QuarticGaussian_offaxis_bound (m, n) hm hn

private theorem QuarticGaussian_centerTerm_re_tsum :
    3 ≤ (∑' a : ℤ × ℤ, QuarticGaussian_centerTerm a).re := by
  classical
  let U : Finset (ℤ × ℤ) := {(1, 0), (-1, 0), (0, 1), (0, -1)}
  let u : ℤ × ℤ → ℝ := fun a ↦ if a ∈ U then 1 else 0
  let g := QuarticGaussian_invSq
  let e : ℤ × ℤ → ℝ := fun a ↦ (1 / 64 : ℝ) * (g a.1 * g a.2)
  have hg (n : ℤ) : 0 ≤ g n := by exact inv_nonneg.mpr (sq_nonneg _)
  have hs := QuarticGaussian_invSq_summable
  have hep := hs.mul_of_nonneg hs hg hg
  have he : Summable e := hep.mul_left _
  have hU : Summable u := summable_of_ne_finset_zero (s := U) (by simp [u])
  have hsumU : (∑' a, u a) = 4 := by
    rw [tsum_eq_sum (s := U) (by simp [u])]
    have hh : (∑ a ∈ U, u a) = ∑ _a ∈ U, (1 : ℝ) :=
      Finset.sum_congr rfl (fun a ha ↦ by simp [u, ha])
    rw [hh, Finset.sum_const, nsmul_eq_mul, mul_one]
    have hcard : U.card = 4 := by decide
    rw [hcard]; norm_num
  have hsume : (∑' a, e a) ≤ 1 / 4 := by
    rw [show (∑' a, e a) = (1 / 64 : ℝ) * (∑' n, g n) ^ 2 by
      rw [tsum_mul_left, pow_two]; exact congrArg _ (hs.hasSum.mul hs.hasSum hep).tsum_eq]
    have h := QuarticGaussian_invSq_tsum_le
    have h₀ : 0 ≤ ∑' n, g n := tsum_nonneg hg
    calc
      _ ≤ (1 / 64 : ℝ) * (4 : ℝ) ^ 2 := by gcongr
      _ = _ := by norm_num
  have hle (a : ℤ × ℤ) : u a - e a ≤ (QuarticGaussian_centerTerm a).re := by
    obtain ⟨m, n⟩ := a
    by_cases hu : (m, n) ∈ U
    · have h' : m = 1 ∧ n = 0 ∨ m = -1 ∧ n = 0 ∨ m = 0 ∧ n = 1 ∨ m = 0 ∧ n = -1 := by
        simpa [U] using hu
      have hv : QuarticGaussian_centerTerm (m, n) = 1 := by
        rcases h' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
          norm_num [QuarticGaussian_axis_term, QuarticGaussian_invSq]
      simp only [u, hu, ite_true, hv, one_re, sub_le_self_iff]
      exact mul_nonneg (by norm_num) (mul_nonneg (hg m) (hg n))
    simp only [u, hu, ite_false, zero_sub]
    rcases eq_or_ne n 0 with rfl | hn
    · rw [(QuarticGaussian_axis_term m).1, ofReal_re]
      exact (neg_nonpos.mpr (mul_nonneg (by norm_num) (mul_nonneg (hg m) (hg 0)))).trans (by positivity)
    rcases eq_or_ne m 0 with rfl | hm
    · rw [(QuarticGaussian_axis_term n).2, ofReal_re]
      exact (neg_nonpos.mpr (mul_nonneg (by norm_num) (mul_nonneg (hg 0) (hg n)))).trans (by positivity)
    exact (neg_le_neg (QuarticGaussian_offaxis_bound (m, n) hm hn)).trans
      (neg_le_of_abs_le (Complex.abs_re_le_norm _))
  have hS := QuarticGaussian_centerTerm_summable.of_norm
  rw [Complex.re_tsum hS]
  have hsum := (hU.sub he).tsum_le_tsum hle (Complex.reCLM.summable hS)
  rw [hU.tsum_sub he, hsumU] at hsum
  linarith

private theorem QuarticGaussian_center_integral : QuarticGaussianD 6 =
    (((((2 * Real.pi) ^ 8)⁻¹ * (Nat.factorial 7 : ℝ)) : ℝ) : ℂ) *
      ∑' a, QuarticGaussian_centerTerm a := by
  let F : (ℤ × ℤ) → ℝ → ℂ := fun a x ↦ QuarticGaussianLattice a ^ 4 *
    (Real.exp (8 * x - 2 * Real.pi * QuarticGaussianQ a * Real.exp x) : ℂ)
  let C : ℝ := ((2 * Real.pi) ^ 8)⁻¹ * (Nat.factorial 7 : ℝ)
  have hF (a : ℤ × ℤ) : Integrable (F a) ∧
      (∫ x, F a x) = (C : ℂ) * QuarticGaussian_centerTerm a ∧
      (∫ x, ‖F a x‖) = C * ‖QuarticGaussian_centerTerm a‖ := by
    by_cases ha : a = (0, 0)
    · subst a; simp [F, QuarticGaussian_centerTerm, QuarticGaussianLattice]
    have h := QuarticGaussian_logGamma 7 (a := 2 * Real.pi * QuarticGaussianQ a)
      (mul_pos (by positivity) (lt_of_lt_of_le zero_lt_one (QuarticGaussianQ_ge_one ha)))
    norm_num only [Nat.cast_ofNat] at h
    let f := fun x : ℝ ↦ Real.exp (8 * x - 2 * Real.pi * QuarticGaussianQ a * Real.exp x)
    have hf : Integrable f ∧ (∫ x, f x) = ((2 * Real.pi * QuarticGaussianQ a) ^ 8)⁻¹ * (Nat.factorial 7 : ℝ) := by
      convert h using 1; norm_num [f]
    refine ⟨hf.1.ofReal.const_mul _, ?_, ?_⟩
    · change (∫ x, QuarticGaussianLattice a ^ 4 * (f x : ℂ)) = _
      rw [integral_const_mul, integral_complex_ofReal (f := f), hf.2,
        QuarticGaussian_centerTerm, mul_pow, mul_inv]
      dsimp [C]
      push_cast
      ring
    · have hnorm (x : ℝ) : ‖F a x‖ = ‖QuarticGaussianLattice a ^ 4‖ * f x := by
        dsimp [F, f]; rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Real.abs_exp]
      simp_rw [hnorm]
      rw [integral_const_mul, hf.2, QuarticGaussian_centerTerm, norm_mul, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (by rw [QuarticGaussianQ]; positivity)),
        mul_pow, mul_inv]
      dsimp [C]
      ring
  have hpoint (x : ℝ) : QuarticGaussianB x * Complex.exp ((6 : ℂ) * (x : ℂ)) = ∑' a, F a x := by
    rw [QuarticGaussianB_direct, mul_right_comm, ← tsum_mul_left]
    congr 1
    funext a
    rw [← Complex.ofReal_ofNat 6, ← Complex.ofReal_mul, ← Complex.ofReal_exp]
    dsimp [F]
    calc
      _ = QuarticGaussianLattice a ^ 4 *
          ((Real.exp (2 * x) : ℂ) * (Real.exp (6 * x) : ℂ) *
            (Real.exp (-(2 * Real.pi * Real.exp x * QuarticGaussianQ a)) : ℂ)) := by ring
      _ = _ := by
        rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, ← Real.exp_add, ← Real.exp_add]
        congr 3
        ring
  unfold QuarticGaussianD
  simp_rw [hpoint]
  rw [← integral_tsum_of_summable_integral_norm (fun a ↦ (hF a).1) (by
    simp_rw [fun a ↦ (hF a).2.2]
    exact QuarticGaussian_centerTerm_summable.mul_left C)]
  change _ = (C : ℂ) * ∑' a, QuarticGaussian_centerTerm a
  simp_rw [fun a ↦ (hF a).2.1, tsum_mul_left]

/-- The value at the Jensen center is bounded away from zero by the four unit
    contributions. The other axis contributions are nonnegative, and the off-axis
    contributions are absolutely bounded using the product of two inverse-square series. -/
public theorem QuarticGaussianD_center_lower_bound : (1 / 1000 : ℝ) ≤ ‖QuarticGaussianD 6‖ := by
  rw [QuarticGaussian_center_integral, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (by positivity)]
  have h₇ : 2 * Real.pi ≤ 7 := by linarith [Real.pi_lt_d2]
  have hC : ((7 : ℝ) ^ 8)⁻¹ * (Nat.factorial 7 : ℝ) ≤
      ((2 * Real.pi) ^ 8)⁻¹ * (Nat.factorial 7 : ℝ) := by gcongr
  calc
    _ ≤ ((7 : ℝ) ^ 8)⁻¹ * (Nat.factorial 7 : ℝ) * 3 := by norm_num [Nat.factorial]
    _ ≤ _ := mul_le_mul hC (QuarticGaussian_centerTerm_re_tsum.trans (Complex.re_le_norm _))
      (by norm_num) (by positivity)

/-- The two-sided theta bound gives the explicit Jensen growth envelope on every
    disk centered at six with nonnegative integer radius. -/
public theorem QuarticGaussianD_disk_bound_of_decay
    (hB : ∀ x : ℝ, ‖QuarticGaussianB x‖ ≤ 234 * Real.exp (3 * |x| - Real.exp |x| / 2))
    (R : ℕ) {w : ℂ} (hw : w ∈ closedBall (6 : ℂ) R) :
    let p : ℕ := R + 9
    ‖QuarticGaussianD w‖ ≤ 468 * (2 * (p : ℝ)) ^ p := by
  intro p
  let n := R + 8
  have hpn : p = n + 1 := by rfl
  have hp : (p : ℝ) = (R : ℝ) + 9 := by simp [p]
  have hdist : ‖w - 6‖ ≤ (R : ℝ) := by simpa [dist_eq_norm] using hw
  have hre := (Complex.abs_re_le_norm (w - 6)).trans hdist
  have hre' : |w.re| ≤ (R : ℝ) + 6 := by
    simpa using (by
      calc
        |w.re| = |(w - 6).re + (6 : ℂ).re| := by simp
        _ ≤ |(w - 6).re| + |(6 : ℂ).re| := abs_add_le ..
        _ ≤ (R : ℝ) + 6 := by simpa using add_le_add_right hre 6)
  let f : ℝ → ℝ := fun x ↦ Real.exp ((p : ℝ) * x - Real.exp x / 2)
  have hf : Integrable f ∧ (∫ x, f x) = (2 : ℝ) ^ p * (n.factorial : ℝ) := by
    have h := QuarticGaussian_logGamma n (by norm_num : (0 : ℝ) < 1 / 2)
    rw [hpn, Nat.cast_add, Nat.cast_one] at hp
    have heq (x : ℝ) : f x = Real.exp (((n : ℝ) + 1) * x - (1 / 2) * Real.exp x) := by
      dsimp [f]
      rw [hpn, Nat.cast_add, Nat.cast_one]
      congr 1
      ring
    rw [show f = _ from funext heq]
    simpa [hpn, inv_pow] using h
  have hm := Measure.measurePreserving_neg (volume : Measure ℝ)
  have hfi : Integrable (fun x : ℝ ↦ f (-x)) := hm.integrable_comp_of_integrable hf.1
  have hfn : (∫ x, f (-x)) = ∫ x, f x :=
    hm.integral_comp (Homeomorph.neg ℝ).measurableEmbedding f
  have hb (x : ℝ) : ‖QuarticGaussianB x * Complex.exp (w * (x : ℂ))‖ ≤
      234 * (f x + f (-x)) := by
    apply (QuarticGaussian_weighted_le hB w x).trans
    calc
      _ ≤ 234 * f |x| := by dsimp [f]; gcongr; linarith
      _ ≤ _ := by
        gcongr
        by_cases hx : 0 ≤ x
        · rw [abs_of_nonneg hx]; exact le_add_of_nonneg_right (Real.exp_nonneg _)
        · rw [abs_of_nonpos (le_of_not_ge hx)]; exact le_add_of_nonneg_left (Real.exp_nonneg _)
  have hfactorial : n.factorial ≤ p ^ p := by
    calc
      n.factorial ≤ n ^ n := Nat.factorial_le_pow n
      _ ≤ p ^ n := Nat.pow_le_pow_left (by omega) n
      _ ≤ p ^ p := Nat.pow_le_pow_right (by omega) (by omega)
  calc
    ‖QuarticGaussianD w‖ ≤ ∫ x, 234 * (f x + f (-x)) :=
      norm_integral_le_of_norm_le ((hf.1.add hfi).const_mul _) (ae_of_all _ hb)
    _ = 468 * ((2 : ℝ) ^ p * (n.factorial : ℝ)) := by
      rw [integral_const_mul, integral_add hf.1 hfi, hfn, hf.2]; ring
    _ ≤ 468 * (2 * (p : ℝ)) ^ p := by
      rw [mul_pow]
      gcongr
      exact_mod_cast hfactorial

/-- The band set of distinct real ordinates is finite once entireness and nonvanishing
    at the Jensen center have been established. -/
public theorem QuarticGaussianBandZeros_finite (hD : Differentiable ℂ QuarticGaussianD)
    (hc : QuarticGaussianD 6 ≠ 0) (j : ℕ) : (QuarticGaussianBandZeros j).Finite := by
  let T : ℝ := 8192 * 2 ^ (j + 1)
  let E := divisor QuarticGaussianD (closedBall (6 : ℂ) (T + 6))
  refine (E.finiteSupport (isCompact_closedBall _ _)).of_injOn ?_
    QuarticGaussianLine_injective.injOn
  intro t ht
  rw [Function.mem_support]
  have hz := QuarticGaussian_order_ne_top hD hc (QuarticGaussianLine t)
  rw [QuarticGaussian_divisor_eq_order hD (QuarticGaussianLine_mem_disk ht.2.2)]
  have hord := (hD.analyticAt _).analyticOrderAt_ne_zero.mpr ht.1
  exact_mod_cast (show analyticOrderNatAt QuarticGaussianD (QuarticGaussianLine t) ≠ 0 by
    intro h
    apply hord
    rw [← Nat.cast_analyticOrderNatAt hz, h, Nat.cast_zero])

/-- The precise dyadic count reduces to the two concrete estimates on the theta profile
    and on the value of its Mellin transform at six. `A` may be the whole band or any
    finite subset of its distinct real ordinates. -/
public theorem QuarticGaussian_sum_capped_band_le_of_decay
    (hB : ∀ x : ℝ, ‖QuarticGaussianB x‖ ≤ 234 * Real.exp (3 * |x| - Real.exp |x| / 2))
    (hc : (1 / 1000 : ℝ) ≤ ‖QuarticGaussianD 6‖)
    (j : ℕ) (A : Finset ℝ) (hA : ∀ t ∈ A, t ∈ QuarticGaussianBandZeros j) :
    (∑ t ∈ A, QuarticGaussianCappedOrder t) ≤ 163840 * 2 ^ j * (12 + j) := by
  let T : ℕ := 8192 * 2 ^ (j + 1)
  have hT : 8192 ≤ T := Nat.le_mul_of_pos_right _ (by positivity)
  have hupper (t : ℝ) (ht : t ∈ A) : |t| ≤ (T : ℝ) := by
    simpa [T] using (hA t ht).2.2
  have hs := QuarticGaussian_sum_capped_le_of_disk_bound
    (QuarticGaussianD_differentiable_of_decay hB) hc hT (fun w hw ↦ ?_) A hupper
  · exact_mod_cast hs.trans (QuarticGaussian_dyadic_budget j)
  · have hR : ((2 * (T + 6) : ℕ) : ℝ) = 2 * ((T : ℝ) + 6) := by push_cast; rfl
    exact QuarticGaussianD_disk_bound_of_decay hB (2 * (T + 6))
      (sphere_subset_closedBall (hR.symm ▸ hw))

/-- The band bound with only the negative-log Poisson identity as input. -/
public theorem QuarticGaussian_sum_capped_band_le_of_poisson
    (hpoisson : ∀ x : ℝ, x < 0 → QuarticGaussianB x =
      (1 / 32 : ℂ) * (Real.exp (-3 * x) : ℂ) *
        ∑' a : ℤ × ℤ, QuarticGaussianLattice a ^ 4 *
          (Real.exp (-(Real.pi / 2 * Real.exp (-x) * ‖QuarticGaussianLattice a‖ ^ 2)) : ℂ))
    (j : ℕ) (A : Finset ℝ) (hA : ∀ t ∈ A, t ∈ QuarticGaussianBandZeros j) :
    (∑ t ∈ A, QuarticGaussianCappedOrder t) ≤ 163840 * 2 ^ j * (12 + j) :=
  QuarticGaussian_sum_capped_band_le_of_decay (QuarticGaussianB_decay_of_poisson hpoisson)
    QuarticGaussianD_center_lower_bound j A hA

end Masullo
