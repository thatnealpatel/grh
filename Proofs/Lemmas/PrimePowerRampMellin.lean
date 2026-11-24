module

public import Mathlib.NumberTheory.LSeries.Dirichlet
import all Lemmas.LogRampAbel -- unfold the ramp to compare cutoffs
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # Mellin transform of the von Mangoldt logarithmic ramp

Equation (2) of `5f22f5a60aef:.godel/bob/unsigned-edge-rh.md:13–30`, on the
half-plane `1 < s.re`. This is the initial integral identity, not its analytic
continuation or the subsequent Landau argument.

Owning check session: `01a20f88-43d7-7049-9647-cb18c5a08d70`.
-/

open Complex Filter MeasureTheory Set
open scoped Topology

namespace PrimeSquareRamp

private theorem logRatio_mul_rpow_le {c x : ℝ} (hc : 0 < c) (hx : c ≤ x) (r : ℝ) :
    Real.log (x / c) * x ^ r ≤ x ^ (1 + r) / c := by
  have hx₀ := hc.trans_le hx
  calc
    _ ≤ (x / c) * x ^ r :=
      mul_le_mul_of_nonneg_right
        ((Real.log_le_sub_one_of_pos (div_pos hx₀ hc)).trans (sub_le_self _ zero_le_one))
        (Real.rpow_nonneg hx₀.le _)
    _ = (x ^ (1 : ℝ) * x ^ r) / c := by rw [Real.rpow_one, div_mul_eq_mul_div]
    _ = _ := by rw [Real.rpow_add hx₀]

private theorem ofReal_mul_cpow_pred {x : ℝ} (hx : x ≠ 0) (z : ℂ) :
    (x : ℂ) * (x : ℂ) ^ (z - 1) = (x : ℂ) ^ z := by
  conv_lhs => lhs; rw [← Complex.cpow_one (x : ℂ)]
  rw [← Complex.cpow_add _ _ (ofReal_ne_zero.mpr hx), show 1 + (z - 1) = z by ring]

private theorem logKernel_mellin {c : ℝ} (hc : 0 < c) {s : ℂ} (hs : 1 < s.re) :
    IntegrableOn (fun x : ℝ ↦ (Real.log (x / c) : ℂ) * (x : ℂ) ^ (-(s + 1))) (Ioi c) ∧
    (∫ x : ℝ in Ioi c, (Real.log (x / c) : ℂ) * (x : ℂ) ^ (-(s + 1))) =
      (c : ℂ) ^ (-s) / s ^ 2 := by
  let u (x : ℝ) : ℂ := Real.log (x / c)
  let u' (x : ℝ) : ℂ := (x⁻¹ : ℝ)
  let v (x : ℝ) : ℂ := (x : ℂ) ^ (-s) / (-s)
  let v' (x : ℝ) : ℂ := (x : ℂ) ^ (-(s + 1))
  have hs₀ : s ≠ 0 := by rintro rfl; norm_num at hs
  have hu (x : ℝ) (hx : 0 < x) : HasDerivAt u (u' x) x := by
    apply HasDerivAt.ofReal_comp
    refine ((Real.hasDerivAt_log hx.ne').sub_const (Real.log c)).congr_of_eventuallyEq ?_
    filter_upwards [eventually_ne_nhds hx.ne'] with y hy
    exact Real.log_div hy hc.ne'
  have hr : (-(s + 1)).re < -1 := by simp; linarith
  have hr₁ : -(s + 1) + 1 = -s := by ring
  have hv (x : ℝ) (hx : 0 < x) : HasDerivAt v (v' x) x := by
    have hne : -(s + 1) ≠ -1 := by
      intro h
      rw [h] at hr
      simp at hr
    simpa only [hr₁] using hasDerivAt_ofReal_cpow_const' hx.ne' hne
  have hvc (x : ℝ) (hx : 0 < x) : ContinuousAt v' x :=
    continuousAt_ofReal_cpow_const x _ (Or.inr hx.ne')
  have hg : IntegrableOn (fun x : ℝ ↦ x ^ (-s.re) / c) (Ioi c) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith) hc).div_const c
  have hi : IntegrableOn (u * v') (Ioi c) := by
    apply hg.mono' ((show ContinuousOn (u * v') (Ioi c) from fun x hx ↦
      ((hu x (hc.trans hx)).continuousAt.mul (hvc x (hc.trans hx))).continuousWithinAt
      ).aestronglyMeasurable measurableSet_Ioi)
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with x hx
    have hx₀ := hc.trans hx
    have hlog : 0 ≤ Real.log (x / c) := Real.log_nonneg ((le_div_iff₀ hc).2 (by simpa using hx.le))
    change ‖(Real.log (x / c) : ℂ) * (x : ℂ) ^ (-(s + 1))‖ ≤ _
    rw [norm_mul, Complex.norm_of_nonneg hlog, norm_cpow_eq_rpow_re_of_pos hx₀]
    simpa only [neg_re, add_re, one_re, show 1 + -(s.re + 1) = -s.re by ring] using
      logRatio_mul_rpow_le hc hx.le (-(s.re + 1))
  have hvprod : EqOn (u' * v) (fun x ↦ v' x / (-s)) (Ioi c) := by
    intro x hx
    have hx₀ := hc.trans hx
    change ((x⁻¹ : ℝ) : ℂ) * ((x : ℂ) ^ (-s) / (-s)) = (x : ℂ) ^ (-(s + 1)) / (-s)
    rw [Complex.ofReal_inv, ← mul_div_assoc, ← Complex.cpow_neg_one,
      ← Complex.cpow_add _ _ (ofReal_ne_zero.mpr hx₀.ne'), show -1 + -s = -(s + 1) by ring]
  have hj : IntegrableOn (u' * v) (Ioi c) :=
    IntegrableOn.congr_fun ((integrableOn_Ioi_cpow_of_lt hr hc).div_const (-s))
      hvprod.symm measurableSet_Ioi
  have hl : Tendsto (u * v) (𝓝[>] c) (𝓝 (0 : ℂ)) := by
    have h := (hu c hc).continuousAt.mul (hv c hc).continuousAt
    have hz : (u * v) c = 0 := by simp [u, hc.ne']
    rw [ContinuousAt, hz] at h
    exact h.mono_left nhdsWithin_le_nhds
  have ht : Tendsto (u * v) atTop (𝓝 (0 : ℂ)) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    refine squeeze_zero' (g := fun x : ℝ ↦ (x ^ (1 + -s.re) / c) / ‖-s‖)
      (Eventually.of_forall fun _ ↦ norm_nonneg _) ?_ ?_
    · filter_upwards [eventually_ge_atTop c] with x hx
      have hx₀ := hc.trans_le hx
      have hlog : 0 ≤ Real.log (x / c) := Real.log_nonneg ((le_div_iff₀ hc).2 (by simpa using hx))
      change ‖(Real.log (x / c) : ℂ) * ((x : ℂ) ^ (-s) / (-s))‖ ≤
        (x ^ (1 + -s.re) / c) / ‖-s‖
      rw [norm_mul, norm_div, Complex.norm_of_nonneg hlog, norm_cpow_eq_rpow_re_of_pos hx₀,
        neg_re, ← mul_div_assoc]
      exact div_le_div_of_nonneg_right (logRatio_mul_rpow_le hc hx (-s.re)) (norm_nonneg _)
    · simpa only [show 1 + -s.re = -(s.re - 1) by ring, zero_div] using
        ((tendsto_rpow_neg_atTop (sub_pos.mpr hs)).div_const c |>.div_const ‖-s‖)
  refine ⟨hi, ?_⟩
  change (∫ x in Ioi c, u x * v' x) = _
  rw [integral_Ioi_mul_deriv_eq_deriv_mul (fun x hx ↦ hu x (hc.trans hx))
      (fun x hx ↦ hv x (hc.trans hx)) hi hj hl ht, sub_zero, zero_sub]
  change -(∫ x in Ioi c, (u' * v) x) = _
  rw [setIntegral_congr_fun measurableSet_Ioi hvprod, integral_div,
    integral_Ioi_cpow_of_lt hr hc, hr₁]
  field_simp [hs₀]

private theorem linear_mellin {s : ℂ} (hs : 1 < s.re) :
    IntegrableOn (fun x : ℝ ↦ (x : ℂ) * (x : ℂ) ^ (-(s + 1))) (Ioi 1) ∧
    (∫ x : ℝ in Ioi 1, (x : ℂ) * (x : ℂ) ^ (-(s + 1))) = 1 / (s - 1) := by
  have heq : EqOn (fun x : ℝ ↦ (x : ℂ) * (x : ℂ) ^ (-(s + 1)))
      (fun x : ℝ ↦ (x : ℂ) ^ (-s)) (Ioi 1) := by
    intro x hx
    rw [show -(s + 1) = -s - 1 by ring]
    exact ofReal_mul_cpow_pred ((zero_lt_one.trans hx).ne') _
  have hre : (-s).re < -1 := by simp; linarith
  refine ⟨(integrableOn_Ioi_cpow_of_lt hre zero_lt_one).congr_fun heq.symm measurableSet_Ioi, ?_⟩
  rw [setIntegral_congr_fun measurableSet_Ioi heq, integral_Ioi_cpow_of_lt hre zero_lt_one,
    ofReal_one, one_cpow, show -s + 1 = -(s - 1) by ring, div_neg, neg_div, neg_neg]

local notation "Λ" => ArithmeticFunction.vonMangoldt

private noncomputable def mangoldtLogTerm (s : ℂ) (n : ℕ) (x : ℝ) : ℂ :=
  (Ici (n : ℝ)).indicator
    (fun y : ℝ ↦ (Λ n : ℂ) * ((Real.log (y / n) : ℂ) * (y : ℂ) ^ (-(s + 1)))) x

private theorem mangoldtLogTerm_mellin {s : ℂ} (hs : 1 < s.re) (n : ℕ) :
    Integrable (mangoldtLogTerm s n) ∧
      (∫ x, mangoldtLogTerm s n x) = LSeries.term (fun k ↦ (Λ k : ℂ)) s n / s ^ 2 := by
  rcases eq_or_ne n 0 with rfl | hn
  · have hz : mangoldtLogTerm s 0 = 0 := by funext x; simp [mangoldtLogTerm]
    simp [hz]
  have hn₀ : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
  obtain ⟨hi, hI⟩ := logKernel_mellin hn₀ hs
  have hic : IntegrableOn (fun x : ℝ ↦ (Λ n : ℂ) *
      ((Real.log (x / n) : ℂ) * (x : ℂ) ^ (-(s + 1)))) (Ici (n : ℝ)) := by
    rw [integrableOn_Ici_iff_integrableOn_Ioi]
    exact hi.const_mul _
  refine ⟨hic.integrable_indicator measurableSet_Ici, ?_⟩
  unfold mangoldtLogTerm
  rw [integral_indicator measurableSet_Ici, integral_Ici_eq_integral_Ioi,
    integral_const_mul, hI, LSeries.term_of_ne_zero hn, Complex.ofReal_natCast, cpow_neg,
    div_eq_mul_inv ((Λ n : ℝ) : ℂ), mul_div_assoc]

-- On a positive base, the complex power has the same modulus as the power at `s.re`.
private theorem norm_mangoldtLogTerm (s : ℂ) (n : ℕ) (x : ℝ) :
    ‖mangoldtLogTerm s n x‖ = (mangoldtLogTerm (s.re : ℂ) n x).re := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [mangoldtLogTerm]
  by_cases hx : x ∈ Ici (n : ℝ)
  · have hn₀ : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
    have hx₀ : 0 < x := hn₀.trans_le hx
    have hlog : 0 ≤ Real.log (x / n) := Real.log_nonneg ((le_div_iff₀ hn₀).2
      (by simpa using hx))
    have h_exp : -((s.re : ℂ) + 1) = ((-(s.re + 1) : ℝ) : ℂ) := by push_cast; rfl
    simp only [mangoldtLogTerm, indicator_of_mem hx, norm_mul,
      Complex.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg, Complex.norm_of_nonneg hlog,
      norm_cpow_eq_rpow_re_of_pos hx₀, neg_re, add_re, one_re]
    rw [h_exp, ← Complex.ofReal_cpow hx₀.le, ← Complex.ofReal_mul, ← Complex.ofReal_mul, ofReal_re]
  · simp [mangoldtLogTerm, indicator_of_notMem hx]

private theorem term_re_eq_norm (s : ℂ) (n : ℕ) :
    LSeries.term (fun k ↦ (Λ k : ℂ)) (s.re : ℂ) n =
      (‖LSeries.term (fun k ↦ (Λ k : ℂ)) s n‖ : ℂ) := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  rw [LSeries.term_of_ne_zero hn, LSeries.norm_term_eq, ite_eq_right hn,
    Complex.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg, Complex.ofReal_div,
    Complex.ofReal_cpow (Nat.cast_nonneg n), Complex.ofReal_natCast]

private theorem summable_integral_norm_mangoldtLogTerm {s : ℂ} (hs : 1 < s.re) :
    Summable fun n ↦ ∫ x, ‖mangoldtLogTerm s n x‖ := by
  have hsr : 1 < ((s.re : ℂ)).re := by simpa only [ofReal_re] using hs
  have hnorm (n : ℕ) : (∫ x, ‖mangoldtLogTerm s n x‖) =
      ‖LSeries.term (fun k ↦ (Λ k : ℂ)) s n‖ / s.re ^ 2 := by
    obtain ⟨hi, hI⟩ := mangoldtLogTerm_mellin hsr n
    calc
      _ = (∫ x, (mangoldtLogTerm (s.re : ℂ) n x).re) :=
        integral_congr_ae (Eventually.of_forall (norm_mangoldtLogTerm s n))
      _ = (∫ x, mangoldtLogTerm (s.re : ℂ) n x).re := integral_re hi
      _ = _ := by rw [hI, term_re_eq_norm, ← Complex.ofReal_pow, ← Complex.ofReal_div, ofReal_re]
  simp_rw [hnorm]
  exact (ArithmeticFunction.LSeriesSummable_vonMangoldt hs).norm.div_const _

private theorem mangoldtLogTerm_eq_zero_of_le_one {s : ℂ} {x : ℝ} (hx : x ≤ 1) (n : ℕ) :
    mangoldtLogTerm s n x = 0 := by
  rcases n with _ | _ | n
  · simp [mangoldtLogTerm]
  · simp [mangoldtLogTerm]
  · have hn : (1 : ℝ) < (n + 2 : ℕ) := by exact_mod_cast Nat.succ_lt_succ (Nat.zero_lt_succ n)
    have hnot : x ∉ Ici ((n + 2 : ℕ) : ℝ) := not_le.mpr (hx.trans_lt hn)
    exact indicator_of_notMem hnot _

private theorem tsum_mangoldtLogTerm_eq {s : ℂ} {x : ℝ} (hx : 1 < x) :
    (∑' n, mangoldtLogTerm s n x) = (logRamp Λ x : ℂ) * (x : ℂ) ^ (-(s + 1)) := by
  have hx₀ := zero_lt_one.trans hx
  rw [tsum_eq_sum (s := Finset.Ioc 1 ⌊x⌋₊), logRamp, Complex.ofReal_sum, Finset.sum_mul]
  · apply Finset.sum_congr rfl
    intro n hn
    have hn' : (n : ℝ) ≤ x := (Nat.cast_le.mpr (Finset.mem_Ioc.mp hn).2).trans (Nat.floor_le hx₀.le)
    rw [mangoldtLogTerm, indicator_of_mem (show x ∈ Ici (n : ℝ) from hn'), Complex.ofReal_mul]
    ring
  · intro n hn
    rcases le_or_gt n 1 with hn₁ | hn₁
    · rcases n with _ | _ | n
      · simp [mangoldtLogTerm]
      · simp [mangoldtLogTerm]
      · omega
    · have hn' : ⌊x⌋₊ < n := lt_of_not_ge (fun h ↦ hn (Finset.mem_Ioc.mpr ⟨hn₁, h⟩))
      exact indicator_of_notMem (show x ∉ Ici (n : ℝ) from not_le.mpr ((Nat.floor_lt hx₀.le).1 hn')) _

private theorem logRamp_eq_mangoldt_sum {x : ℝ} (hx : 1 ≤ x) :
    logRamp Λ x = ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, Λ n * Real.log (x / n) := by
  have hf : 1 ≤ ⌊x⌋₊ := Nat.le_floor (by simpa only [Nat.cast_one] using hx)
  rw [logRamp, Finset.Icc_eq_cons_Ioc hf, Finset.sum_cons]
  simp only [ArithmeticFunction.vonMangoldt_apply_one, zero_mul, zero_add, mul_comm]

/-- The complex Mellin transform of `B(X) - X` on `Re s > 1`, with `B` the von Mangoldt
logarithmic ramp summed over all natural indices `1 ≤ n ≤ X`. -/
public theorem vonMangoldt_logRamp_mellin {s : ℂ} (hs : 1 < s.re) :
    let B (x : ℝ) := ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, Λ n * Real.log (x / n)
    IntegrableOn (fun x : ℝ ↦ ((B x : ℂ) - (x : ℂ)) * (x : ℂ) ^ (-(s + 1))) (Ici 1) ∧
    (∫ x : ℝ in Ici 1, ((B x : ℂ) - (x : ℂ)) * (x : ℂ) ^ (-(s + 1))) =
      -logDeriv riemannZeta s / s ^ 2 - 1 / (s - 1) := by
  intro B
  rw [integrableOn_Ici_iff_integrableOn_Ioi, integral_Ici_eq_integral_Ioi]
  let f := mangoldtLogTerm s
  have hfi (n : ℕ) : Integrable (f n) := (mangoldtLogTerm_mellin hs n).1
  have habs : (∑' n, ∫⁻ x, ‖f n x‖ₑ) ≠ ⊤ := by
    have hnorm (n : ℕ) : ‖(∫ x, ‖f n x‖)‖ₑ = ∫⁻ x, ‖f n x‖ₑ := by
      rw [← ofReal_integral_norm_eq_lintegral_eNorm (hfi n), Real.eNorm_of_nonneg]
      exact integral_nonneg (fun _ ↦ norm_nonneg _)
    simp_rw [← hnorm]
    apply tsum_eNorm_ne_top_iff_summable_norm.mpr
    have hnonneg (n : ℕ) : 0 ≤ ∫ x, ‖f n x‖ := integral_nonneg (fun _ ↦ norm_nonneg _)
    simpa only [Real.norm_of_nonneg (hnonneg _)] using summable_integral_norm_mangoldtLogTerm hs
  have hfm (n : ℕ) := (hfi n).aestronglyMeasurable
  have hti : Integrable (fun x ↦ ∑' n, f n x) := by
    refine ⟨(AEMeasurable.tsum fun n ↦ (hfm n).aemeasurable).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_eNorm]
    calc
      _ ≤ ∫⁻ x, ∑' n, ‖f n x‖ₑ := lintegral_mono (fun _ ↦ eNorm_tsum_le_tsum_eNorm)
      _ = _ := lintegral_tsum (fun n ↦ (hfm n).aemeasurable.eNorm)
      _ < ⊤ := lt_top_iff_ne_top.mpr habs
  have heq : EqOn (fun x ↦ ∑' n, f n x) (fun x : ℝ ↦ (B x : ℂ) * (x : ℂ) ^ (-(s + 1))) (Ioi 1) := by
    intro x (hx : 1 < x)
    have hB : logRamp Λ x = B x := logRamp_eq_mangoldt_sum hx.le
    simpa only [hB] using tsum_mangoldtLogTerm_eq (s := s) hx
  have hBi := hti.integrableOn.congr_fun heq measurableSet_Ioi
  obtain ⟨hXi, hX⟩ := linear_mellin hs
  simp only [sub_mul]
  refine ⟨hBi.sub hXi, ?_⟩
  rw [integral_sub hBi hXi, hX, ← setIntegral_congr_fun measurableSet_Ioi heq,
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx ↦ by
      have hx' : x ≤ 1 := le_of_not_gt hx
      simp only [f, mangoldtLogTerm_eq_zero_of_le_one hx', tsum_zero]),
    integral_tsum hfm habs]
  dsimp only [f]
  simp_rw [(mangoldtLogTerm_mellin hs _).2]
  rw [tsum_div_const, ← LSeries, ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs,
    logDeriv_apply, neg_div]

end PrimeSquareRamp
