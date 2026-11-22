module

public import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
public import Mathlib.Topology.Algebra.InfiniteSum.UniformOn
import Mathlib.Algebra.Field.Periodic
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Algebra.InfiniteSum.TsumUniformlyOn
import Mathlib.Topology.Instances.Int

/-! # Monogenic periodization in logarithmic coordinates

Masullo §1.2.8, printed pp. 16–17, takes `γ > 1` and defines the averaging
operator `Φγ(ϕ)(x) := ∑ k ∈ ℤ, ϕ(γ^k x)` for `x > 0`. We use `u = log x`
and represent a smooth quotient function by its smooth `log γ`-periodic lift.
In these coordinates, the multiplier `t^a` from Definition D.3.2.1 and Lemma
D.3.2.3(6) (p. 801) acts by `exp (a * u)`, using the Schwartz–Bruhat change
of variables (p. 593).

We prove local uniform convergence of the series and all its derivatives,
and the normalized cutoff construction of a right inverse (Lemma 4.2.1.5(1)
and the surjectivity part of (2), pp. 165–167). This file does not bundle
these spaces with their locally convex topologies or prove topological exactness.
-/

open Set Function Filter
open scoped ContDiff SchwartzMap Topology

namespace Masullo

noncomputable section

/-- The weighted Schwartz condition on a logarithmic profile. -/
@[expose] public def LogWeightedSchwartz (f : ℝ → ℂ) : Prop :=
  ∀ a : ℝ, ∃ b : 𝓢(ℝ, ℂ), ∀ u : ℝ, b u = (Real.exp (a * u) : ℂ) * f u

/-- Real log coordinates for the series in §1.2.8. -/
@[expose] public def logPeriodization (T : ℝ) (f : ℝ → ℂ) (u : ℝ) : ℂ :=
  ∑' k : ℤ, f (u + (k : ℝ) * T)

/-- The printed series at a positive `x` is exactly the log periodization lifted back along
`exp`, with no factor of `log γ`. This identity does not assert convergence. -/
public theorem logPeriodization_eq_monogenic {γ x : ℝ} (hγ : 0 < γ) (hx : 0 < x)
    (f : ℝ → ℂ) : logPeriodization (Real.log γ) f (Real.log x) =
      ∑' k : ℤ, f (Real.log (γ ^ k * x)) := by
  simp only [logPeriodization, Real.log_mul (zpow_ne_zero _ hγ.ne') hx.ne',
    Real.log_zpow, add_comm (Real.log x)]

private theorem logWeightedSchwartz_of_hasCompactSupport {f : ℝ → ℂ}
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) : LogWeightedSchwartz f := by
  intro a
  let e : ℝ → ℂ := fun x ↦ Real.exp (a * x)
  have he : ContDiff ℝ ∞ e := Complex.ofRealCLM.contDiff.comp
    (Real.contDiff_exp.comp (contDiff_const.mul contDiff_id))
  exact ⟨(hc.mul_left (f := e)).toSchwartzMap (he.mul hf), fun _ ↦ rfl⟩

private theorem locallyFinite_bump_translates {T : ℝ} (hT : 0 < T)
    (b : ContDiffBump (0 : ℝ)) : LocallyFinite (fun k : ℤ ↦
      support (fun u : ℝ ↦ b (u + (k : ℝ) * T))) := by
  intro x
  refine ⟨Metric.ball x 1, Metric.ball_mem_nhds _ zero_lt_one, ?_⟩
  refine (isCompact_iff_finite.mp (isCompact_closedBall (0 : ℤ)
    ((b.rOut + (|x| + 1)) / T))).subset ?_
  rintro k ⟨u, huk, hux⟩
  change b (u + (k : ℝ) * T) ≠ 0 at huk
  have hb : |u + (k : ℝ) * T| < b.rOut := by
    have hmem : u + (k : ℝ) * T ∈ support (b : ℝ → ℝ) := huk
    simpa [b.support_eq, Metric.mem_ball, Real.dist_eq] using hmem
  have hx : |u - x| < 1 := by simpa [Metric.mem_ball, Real.dist_eq] using hux
  have hu : |u| ≤ |x| + 1 := by
    have h := abs_sub_le u x 0
    rw [sub_zero, sub_zero] at h
    linarith
  rw [Metric.mem_closedBall, Int.dist_eq, Int.cast_zero, sub_zero, le_div_iff₀ hT]
  have h := abs_sub_le (u + (k : ℝ) * T) 0 u
  rw [sub_zero, zero_sub, abs_neg, add_sub_cancel_left, abs_mul, abs_of_pos hT] at h
  linarith

private theorem periodic_sum_translates {F : Type*} [AddCommMonoid F] [TopologicalSpace F]
    (T : ℝ) (b : ℝ → F) :
    Periodic (fun u ↦ ∑' k : ℤ, b (u + (k : ℝ) * T)) T := by
  intro u
  have h := (Equiv.addLeft (1 : ℤ)).tsum_eq (fun k : ℤ ↦ b (u + (k : ℝ) * T))
  change (∑' k : ℤ, b (u + ((1 + k : ℤ) : ℝ) * T)) = _ at h
  simpa only [Int.cast_add, Int.cast_one, add_mul, one_mul, ← add_assoc] using h

private theorem exists_normalized_periodization_cutoff {T : ℝ} (hT : 0 < T) :
    ∃ w : ℝ → ℝ, ContDiff ℝ ∞ w ∧ HasCompactSupport w ∧
      ∀ u : ℝ, HasSum (fun k : ℤ ↦ w (u + (k : ℝ) * T)) 1 := by
  let b : ContDiffBump (0 : ℝ) := ⟨T, 2 * T, hT, by linarith⟩
  let d : ℝ → ℝ := fun u ↦ ∑' k : ℤ, b (u + (k : ℝ) * T)
  have hfin := locallyFinite_bump_translates hT b
  have hsum (u : ℝ) : Summable (fun k : ℤ ↦ b (u + (k : ℝ) * T)) := by
    obtain ⟨s, hs⟩ := hfin.exists_finset_support u
    exact summable_of_ne_finset_zero (fun k hk ↦ notMem_support.mp
      (fun hn ↦ hk (hs.self_of_nhds hn)))
  have hd : ContDiff ℝ ∞ d := by
    rw [contDiff_iff_contDiffAt]
    intro u
    obtain ⟨s, hs⟩ := hfin.exists_finset_support u
    have hsmooth : ContDiff ℝ ∞ (fun x ↦ ∑ k ∈ s, b (x + (k : ℝ) * T)) :=
      ContDiff.sum (fun _ _ ↦ b.contDiff.comp (contDiff_id.add contDiff_const))
    apply hsmooth.contDiffAt.congr_of_eventuallyEq
    filter_upwards [hs] with x hx
    exact tsum_eq_sum (fun k hk ↦ notMem_support.mp (fun hn ↦ hk (hx hn)))
  have hp : Periodic d T := periodic_sum_translates T b
  have hpos (u : ℝ) : 0 < d u := by
    obtain ⟨v, hv, huv⟩ := hp.exists_mem_Ico₀ hT u
    rw [huv]
    have hb : b v = 1 := b.one_of_mem_closedBall (by
      simpa [b, Metric.mem_closedBall, Real.dist_eq, abs_of_nonneg hv.1] using hv.2.le)
    have h := (hsum v).le_tsum 0 (fun _ _ ↦ b.nonneg)
    simp only [Int.cast_zero, zero_mul, add_zero, hb] at h
    exact zero_lt_one.trans_le h
  let w : ℝ → ℝ := fun u ↦ b u / d u
  refine ⟨w, b.contDiff.div hd (fun u ↦ (hpos u).ne'), ?_, ?_⟩
  · exact HasCompactSupport.of_support_subset_isCompact b.hasCompactSupport
      (fun u hu ↦ subset_closure (show u ∈ support (b : ℝ → ℝ) from
        fun hn ↦ hu (show b u / d u = 0 by rw [hn, zero_div])))
  · intro u
    have h := (hsum u).hasSum.div_const (d u)
    rw [show (∑' k : ℤ, b (u + (k : ℝ) * T)) / d u = 1 from div_self (hpos u).ne'] at h
    convert h using 1
    funext k
    simp only [w, hp.int_mul k u]

/-- The cutoff section of the printed averaging operator. A single smooth compactly supported
real cutoff in log coordinates works for every smooth periodic target. The equation is stated
as `HasSum` with exactly the integer-power samples in the manuscript, not a totalized sum. -/
public theorem monogenicPeriodization_cutoff_section {γ : ℝ} (hγ : 1 < γ) :
    ∃ w : ℝ → ℝ, ContDiff ℝ ∞ w ∧ HasCompactSupport w ∧
      ∀ g : ℝ → ℂ, ContDiff ℝ ∞ g → Periodic g (Real.log γ) →
        LogWeightedSchwartz (fun u ↦ (w u : ℂ) * g u) ∧
          ∀ x : ℝ, 0 < x →
            HasSum (fun k : ℤ ↦ (w (Real.log (γ ^ k * x)) : ℂ) * g (Real.log (γ ^ k * x)))
              (g (Real.log x)) := by
  have hγ₀ : 0 < γ := zero_lt_one.trans hγ
  obtain ⟨w, hw, hc, hs⟩ := exists_normalized_periodization_cutoff (Real.log_pos hγ)
  refine ⟨w, hw, hc, fun g hg hp ↦ ⟨?_, ?_⟩⟩
  · have hwc : HasCompactSupport (fun u ↦ (w u : ℂ)) :=
      HasCompactSupport.of_support_subset_isCompact hc (fun u hu ↦
        subset_closure (show u ∈ support w from fun hn ↦ hu (by simp [hn])))
    exact logWeightedSchwartz_of_hasCompactSupport
      ((Complex.ofRealCLM.contDiff.comp hw).mul hg) hwc.mul_right
  · intro x hx
    have h := ((hs (Real.log x)).mapL Complex.ofRealCLM).mul_right (g (Real.log x))
    simp only [Complex.ofRealCLM_apply, Complex.ofReal_one, one_mul] at h
    convert h using 1
    funext k
    rw [Real.log_mul (zpow_ne_zero _ hγ₀.ne') hx.ne', Real.log_zpow, add_comm,
      hp.int_mul k (Real.log x)]

private theorem LogWeightedSchwartz.smooth {f : ℝ → ℂ} (hf : LogWeightedSchwartz f) :
    ContDiff ℝ ∞ f := by
  obtain ⟨b, hb⟩ := hf 0
  have he : (⇑b : ℝ → ℂ) = f := by funext u; simpa using hb u
  rw [← he]
  exact b.smooth ⊤

private theorem LogWeightedSchwartz.deriv_mem {f : ℝ → ℂ} (hf : LogWeightedSchwartz f) :
    LogWeightedSchwartz (deriv f) := by
  intro a
  obtain ⟨b, hb⟩ := hf a
  refine ⟨SchwartzMap.derivCLM ℂ ℂ b - (a : ℂ) • b, fun u ↦ ?_⟩
  have he : HasDerivAt (fun v : ℝ ↦ (Real.exp (a * v) : ℂ))
      ((Real.exp (a * u) : ℂ) * (a : ℂ)) u := by
    simpa only [id_eq, mul_one, Complex.ofReal_mul] using
      ((hasDerivAt_id u).const_mul a).exp.ofReal_comp
  have hd := he.fun_mul (hf.smooth.differentiable (by simp) u).hasDerivAt
  have hdb := hd.congr_of_eventuallyEq (Filter.Eventually.of_forall hb)
  rw [sub_apply, SchwartzMap.derivCLM_apply, hdb.deriv, smul_apply,
    smul_eq_mul, hb]
  ring

private theorem LogWeightedSchwartz.iteratedDeriv_mem {f : ℝ → ℂ}
    (hf : LogWeightedSchwartz f) (m : ℕ) : LogWeightedSchwartz (iteratedDeriv m f) := by
  induction m with
  | zero => simpa using hf
  | succ m ih => rw [iteratedDeriv_succ]; exact ih.deriv_mem

private theorem summable_exp_neg_int_abs {T : ℝ} (hT : 0 < T) :
    Summable (fun k : ℤ ↦ Real.exp (-(|(k : ℝ)| * T))) := by
  have h := summable_geometric_of_lt_one (Real.exp_pos (-T)).le
    (show Real.exp (-T) < 1 by rw [← Real.exp_zero, Real.exp_lt_exp]; linarith)
  exact summable_int_iff_summable_nat_and_neg.mpr
    ⟨by simpa [abs_of_nonneg, ← Real.exp_nat_mul, mul_neg] using h,
     by simpa [abs_of_nonneg, ← Real.exp_nat_mul, mul_neg] using h⟩

private theorem LogWeightedSchwartz.norm_le_exp_decay {f : ℝ → ℂ} (hf : LogWeightedSchwartz f) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : ℝ, ‖f u‖ ≤ C * Real.exp (-|u|) := by
  obtain ⟨bp, hbp⟩ := hf 1
  obtain ⟨bm, hbm⟩ := hf (-1)
  let p := SchwartzMap.seminorm ℂ (E := ℝ) (F := ℂ) 0 0
  refine ⟨p bp + p bm, by positivity, fun u ↦ ?_⟩
  have hp : Real.exp u * ‖f u‖ ≤ p bp := by
    simpa [p, hbp, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)] using SchwartzMap.le_seminorm' ℂ 0 0 bp u
  have hm : Real.exp (-u) * ‖f u‖ ≤ p bm := by
    simpa only [p, iteratedDeriv_zero, hbm, pow_zero, one_mul, neg_mul, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using SchwartzMap.le_seminorm' ℂ 0 0 bm u
  rw [Real.exp_neg, ← div_eq_mul_inv, le_div_iff₀ (Real.exp_pos _), mul_comm]
  rcases le_total 0 u with hu | hu
  · rw [abs_of_nonneg hu]
    exact hp.trans (le_add_of_nonneg_right (apply_nonneg p bm))
  · rw [abs_of_nonpos hu]
    exact hm.trans (le_add_of_nonneg_left (apply_nonneg p bp))

private theorem LogWeightedSchwartz.locallyUniformlySummable_translates {T : ℝ} (hT : 0 < T)
    {f : ℝ → ℂ} (hf : LogWeightedSchwartz f) :
    SummableLocallyUniformlyOn (fun (k : ℤ) (u : ℝ) ↦ f (u + (k : ℝ) * T)) univ := by
  obtain ⟨C, hC, hdecay⟩ := hf.norm_le_exp_decay
  apply SummableLocallyUniformlyOn_of_locally_bounded isOpen_univ
  intro K _ hK
  obtain ⟨R, hR⟩ := hK.bddAbove_image (continuous_abs.continuousOn (s := K))
  refine ⟨fun k ↦ (C * Real.exp R) * Real.exp (-(|(k : ℝ)| * T)),
    (summable_exp_neg_int_abs hT).mul_left _, fun k u hu ↦ ?_⟩
  have hRu : |u| ≤ R := hR (mem_image_of_mem _ hu)
  have habs := abs_sub_le (u + (k : ℝ) * T) 0 u
  rw [sub_zero, zero_sub, abs_neg, add_sub_cancel_left, abs_mul, abs_of_pos hT] at habs
  calc
    ‖f (u + (k : ℝ) * T)‖ ≤ C * Real.exp (-|u + (k : ℝ) * T|) := hdecay _
    _ ≤ C * Real.exp (R + -(|(k : ℝ)| * T)) := by
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) hC
    _ = _ := by simp only [Real.exp_add, mul_assoc]

/-- Smooth well-definedness for all weighted Schwartz inputs. The iterated derivatives of the
periodization are obtained by summing the translated input derivatives locally uniformly.
The proof uses a two-sided exponential majorant instead of the one-sided tail estimate
(4.2.1.9) in the manuscript. -/
public theorem logPeriodization_smooth {T : ℝ} (hT : 0 < T) {f : ℝ → ℂ}
    (hf : LogWeightedSchwartz f) :
    ContDiff ℝ ∞ (logPeriodization T f) ∧ Periodic (logPeriodization T f) T ∧
      ∀ m : ℕ, HasSumLocallyUniformlyOn (fun (k : ℤ) (u : ℝ) ↦
        iteratedDeriv m f (u + (k : ℝ) * T)) (iteratedDeriv m (logPeriodization T f)) univ := by
  have hsum (m : ℕ) : HasSumLocallyUniformlyOn
      (fun (k : ℤ) (u : ℝ) ↦ iteratedDeriv m f (u + (k : ℝ) * T))
      (logPeriodization T (iteratedDeriv m f)) univ := by
    obtain ⟨g, hg⟩ := (hf.iteratedDeriv_mem m).locallyUniformlySummable_translates hT
    apply hasSumLocallyUniformlyOn_iff_tendstoLocallyUniformlyOn.mpr
    exact (hasSumLocallyUniformlyOn_iff_tendstoLocallyUniformlyOn.mp hg).congr_right
      (fun u hu ↦ (hg.tsum_eqOn hu).symm)
  have hd (m : ℕ) (u : ℝ) : HasDerivAt (logPeriodization T (iteratedDeriv m f))
      (logPeriodization T (iteratedDeriv (m + 1) f) u) u := by
    refine hasDerivAt_of_tendstoLocallyUniformlyOn isOpen_univ
      (hasSumLocallyUniformlyOn_iff_tendstoLocallyUniformlyOn.mp (hsum (m + 1))) ?_
      (fun v hv ↦ (hsum m).hasSum hv) (mem_univ u)
    exact Filter.Eventually.of_forall (fun s v _ ↦ HasDerivAt.fun_sum (fun k _ ↦ by
      have hk : HasDerivAt (iteratedDeriv m f) (iteratedDeriv (m + 1) f (v + (k : ℝ) * T))
          (v + (k : ℝ) * T) := by
        rw [iteratedDeriv_succ]
        exact ((hf.iteratedDeriv_mem m).smooth.differentiable (by simp) _).hasDerivAt
      simpa only [Function.comp_def, one_smul, id_eq] using
        hk.scomp v ((hasDerivAt_id v).add_const ((k : ℝ) * T))))
  have heq (m : ℕ) : iteratedDeriv m (logPeriodization T f) =
        logPeriodization T (iteratedDeriv m f) := by
    induction m with
    | zero => simp
    | succ m ih => rw [iteratedDeriv_succ, ih]; exact funext (fun u ↦ (hd m u).deriv)
  refine ⟨contDiff_of_differentiable_iteratedDeriv (fun m _ ↦ ?_),
    periodic_sum_translates T f, fun m ↦ heq m ▸ hsum m⟩
  rw [heq m]
  exact fun u ↦ (hd m u).differentiableAt

end
end Masullo
