module

public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! # Landau's lemma for a nonnegative Mellin tail

Source: `2a477e0bed19:.godel/conjectures/closed/order-two-prime-index-violation-phase.md:72–120`.
Scope: the finite real convergence abscissa obstruction, and the sign of a simple pole there;
not the subsequent prime-index phase argument. Owning check session:
`01a20f35-88fa-72a0-aedd-8c10c7068d1c`.
The open tail `Ioi A` has the same Lebesgue integral and integrability as `[A, ∞)`.
-/

open Filter MeasureTheory Set
open scoped ENNReal NNReal Topology

namespace Masullo

/-- The actual Mellin tail, in the normalization `x ^ (-s - 1)`. -/
@[expose] public noncomputable def nonnegativeMellinTail (g : ℝ → ℝ) (A : ℝ) (s : ℂ) : ℂ :=
  ∫ x in Ioi A, (g x : ℂ) * (x : ℂ) ^ (-(s + 1))

/-- Absolute convergence of the real Mellin tail, not a condition on its totalized integral. -/
@[expose] public def MellinTailConverges (g : ℝ → ℝ) (A r : ℝ) : Prop :=
  IntegrableOn (fun x : ℝ ↦ g x * x ^ (-(r + 1))) (Ioi A)

private noncomputable def realKernel (g : ℝ → ℝ) (r x : ℝ) : ℝ :=
  g x * x ^ (-(r + 1))

private noncomputable def logMoment (g : ℝ → ℝ) (r : ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  realKernel g r x * (Real.log x ^ n / n.factorial)

private theorem realKernel_aemeasurable {g : ℝ → ℝ} {μ : Measure ℝ}
    (hg : AEMeasurable g μ) (r : ℝ) : AEMeasurable (realKernel g r) μ :=
  hg.mul (measurable_id.pow_const _).aemeasurable

private theorem logMoment_aemeasurable {g : ℝ → ℝ} {μ : Measure ℝ}
    (hg : AEMeasurable g μ) (r : ℝ) (n : ℕ) : AEMeasurable (logMoment g r n) μ :=
  (realKernel_aemeasurable hg r).mul ((Real.measurable_log.pow_const n).div_const _).aemeasurable

private theorem logMoment_nonneg {g : ℝ → ℝ} {r x : ℝ} (hx : 1 ≤ x) (hg : 0 ≤ g x)
    (n : ℕ) : 0 ≤ logMoment g r n x :=
  mul_nonneg (mul_nonneg hg (Real.rpow_nonneg (zero_le_one.trans hx) _))
    (div_nonneg (pow_nonneg (Real.log_nonneg hx) _) (Nat.cast_nonneg _))

private theorem complexKernel_ofReal {g : ℝ → ℝ} {x : ℝ} (hx : 0 ≤ x) (r : ℝ) :
    (g x : ℂ) * (x : ℂ) ^ (-((r : ℂ) + 1)) = (realKernel g r x : ℂ) := by
  rw [realKernel, Complex.ofReal_mul, Complex.ofReal_cpow hx]
  push_cast
  rfl

private theorem hasSum_logMoment_complex {g : ℝ → ℝ} {x : ℝ} (hx : 0 < x) (r : ℝ) (w : ℂ) :
    HasSum (fun n ↦ (logMoment g r n x : ℂ) * w ^ n)
      ((g x : ℂ) * (x : ℂ) ^ (-((r : ℂ) - w + 1))) := by
  have h := (NormedSpace.expSeries_div_hasSum_exp ((Real.log x : ℂ) * w)).mul_left
    (realKernel g r x : ℂ)
  rw [← Complex.exp_eq_exp_ℂ] at h
  have hterm (n : ℕ) : (realKernel g r x : ℂ) * (((Real.log x : ℂ) * w) ^ n / n.factorial) =
      (logMoment g r n x : ℂ) * w ^ n := by
    rw [logMoment, Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_pow,
      Complex.ofReal_natCast, mul_pow]
    ring
  simp_rw [hterm] at h
  convert h using 1
  rw [← complexKernel_ofReal hx.le, Complex.cpow_def_of_ne_zero (by exact_mod_cast hx.ne'),
    Complex.cpow_def_of_ne_zero (by exact_mod_cast hx.ne'), ← Complex.ofReal_log hx.le,
    mul_assoc, ← Complex.exp_add]
  congr 2
  ring

private theorem hasSum_logMoment_real {g : ℝ → ℝ} {x : ℝ} (hx : 0 < x) (r t : ℝ) :
    HasSum (fun n ↦ logMoment g r n x * t ^ n) (realKernel g (r - t) x) := by
  have h := hasSum_logMoment_complex (g := g) hx r (t : ℂ)
  rw [← Complex.ofReal_sub, complexKernel_ofReal hx.le] at h
  simpa only [Complex.reCLM_apply, ← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.ofReal_re]
    using Complex.reCLM.hasSum h

private theorem ae_one_le {A : ℝ} (hA : 2 ≤ A) : ∀ᵐ x ∂volume.restrict (Ioi A), 1 ≤ x :=
  (ae_restrict_mem measurableSet_Ioi).mono fun _ hx ↦ (by linarith [show A < _ from hx])

-- A positive leftward step still within the half-plane dominates the series on its closed disk.
private theorem hasSum_integral_logMoment {g : ℝ → ℝ} {A r T : ℝ} {w : ℂ}
    (hA : 2 ≤ A) (hg : AEMeasurable g (volume.restrict (Ioi A)))
    (hg₀ : ∀ᵐ x ∂volume.restrict (Ioi A), 0 ≤ g x)
    (hT : MellinTailConverges g A (r - T)) (hw : ‖w‖ ≤ T) :
    HasSum (fun n ↦ ((∫ x in Ioi A, logMoment g r n x : ℝ) : ℂ) * w ^ n)
      (nonnegativeMellinTail g A ((r : ℂ) - w)) := by
  let μ := volume.restrict (Ioi A)
  let B (n : ℕ) (x : ℝ) := logMoment g r n x * T ^ n
  have hx : ∀ᵐ x ∂μ, 1 ≤ x := ae_one_le hA
  have hsum : ∀ᵐ x ∂μ, HasSum (fun n ↦ B n x) (realKernel g (r - T) x) :=
    hx.mono fun _ hx ↦ hasSum_logMoment_real (zero_lt_one.trans_le hx) r T
  have hB : Integrable (fun x ↦ ∑' n, B n x) μ :=
    (show Integrable (realKernel g (r - T)) μ from hT).congr (hsum.mono fun _ h ↦ h.tsum_eq.symm)
  have h := hasSum_integral_of_dominated_convergence (μ := μ)
    (F := fun n x ↦ (logMoment g r n x : ℂ) * w ^ n) B
    (fun n ↦ ((Complex.continuous_ofReal.measurable.comp_aemeasurable
      (logMoment_aemeasurable hg r n)).mul_const _).aestronglyMeasurable)
    (fun n ↦ (hx.and hg₀).mono fun x ⟨hx, hgx⟩ ↦ by
      rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg (logMoment_nonneg hx hgx n)]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hw _) (logMoment_nonneg hx hgx n))
    (hsum.mono fun _ h ↦ h.summable) hB
    (hx.mono fun _ hx ↦ hasSum_logMoment_complex (zero_lt_one.trans_le hx) r w)
  simpa only [integral_mul_const, integral_complex_ofReal, nonnegativeMellinTail, μ] using h

private theorem integrable_logMoment {g : ℝ → ℝ} {A r T : ℝ}
    (hA : 2 ≤ A) (hg : AEMeasurable g (volume.restrict (Ioi A)))
    (hg₀ : ∀ᵐ x ∂volume.restrict (Ioi A), 0 ≤ g x)
    (hT₀ : 0 < T) (hT : MellinTailConverges g A (r - T)) (n : ℕ) :
    IntegrableOn (logMoment g r n) (Ioi A) := by
  have hT' : IntegrableOn (realKernel g (r - T)) (Ioi A) := hT
  refine (hT'.div_const (T ^ n)).mono'
    (logMoment_aemeasurable hg r n).aestronglyMeasurable ?_
  filter_upwards [ae_one_le hA, hg₀] with x hx hgx
  rw [Real.norm_of_nonneg (logMoment_nonneg hx hgx n), le_div_iff₀ (pow_pos hT₀ _)]
  have h := hasSum_logMoment_real (g := g) (zero_lt_one.trans_le hx) r T
  rw [← h.tsum_eq]
  exact h.summable.le_tsum n fun j _ ↦
    mul_nonneg (logMoment_nonneg hx hgx j) (pow_nonneg hT₀.le _)

-- For a larger real step, use the extended integral first: no integrability to its left is assumed.
private theorem converges_of_summable_logMoment {g : ℝ → ℝ} {A r t : ℝ}
    (hA : 2 ≤ A) (hg : AEMeasurable g (volume.restrict (Ioi A)))
    (hg₀ : ∀ᵐ x ∂volume.restrict (Ioi A), 0 ≤ g x) (ht : 0 ≤ t)
    (hint : ∀ n, IntegrableOn (logMoment g r n) (Ioi A))
    (hs : Summable (fun n ↦ (∫ x in Ioi A, logMoment g r n x) * t ^ n)) :
    MellinTailConverges g A (r - t) := by
  let μ := volume.restrict (Ioi A)
  let B (n : ℕ) (x : ℝ) := logMoment g r n x * t ^ n
  have hpos : ∀ᵐ x ∂μ, 1 ≤ x ∧ 0 ≤ g x := (ae_one_le hA).and hg₀
  have hB₀ (n : ℕ) : 0 ≤ᵐ[μ] B n := hpos.mono fun _ ⟨hx, hgx⟩ ↦
    mul_nonneg (logMoment_nonneg hx hgx n) (pow_nonneg ht _)
  refine ⟨(realKernel_aemeasurable hg _).aestronglyMeasurable, hasFiniteIntegral_iff_eNorm.mpr ?_⟩
  change (∫⁻ x, ‖realKernel g (r - t) x‖ₑ ∂μ) < ∞
  calc
    (∫⁻ x, ‖realKernel g (r - t) x‖ₑ ∂μ) = ∫⁻ x, ∑' n, ENNReal.ofReal (B n x) ∂μ := by
      apply lintegral_congr_ae
      filter_upwards [hpos] with x hx
      have h := hasSum_logMoment_real (g := g) (zero_lt_one.trans_le hx.1) r t
      have hx₀ : 0 ≤ realKernel g (r - t) x :=
        mul_nonneg hx.2 (Real.rpow_nonneg (zero_le_one.trans hx.1) _)
      rw [Real.eNorm_eq_ofReal hx₀, ← h.tsum_eq]
      exact ENNReal.ofReal_tsum_of_nonneg
        (fun n ↦ mul_nonneg (logMoment_nonneg hx.1 hx.2 n) (pow_nonneg ht _)) h.summable
    _ = ∑' n, ∫⁻ x, ENNReal.ofReal (B n x) ∂μ :=
      lintegral_tsum fun n ↦ ENNReal.measurable_ofReal.comp_aemeasurable
        ((logMoment_aemeasurable hg r n).mul_const _)
    _ = ∑' n, ENNReal.ofReal ((∫ x in Ioi A, logMoment g r n x) * t ^ n) := by
      apply tsum_congr
      intro n
      rw [← ofReal_integral_eq_lintegral_ofReal ((hint n).mul_const _) (hB₀ n)]
      simp only [integral_mul_const]
    _ < ∞ := hs.tsum_ofReal_lt_top

private theorem summable_real_of_hasSum {a : ℕ → ℝ} {t : ℝ} {z : ℂ}
    (h : HasSum (fun n ↦ (a n : ℂ) * (t : ℂ) ^ n) z) :
    Summable (fun n ↦ a n * t ^ n) := by
  simpa only [Complex.reCLM_apply, ← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.ofReal_re]
    using (Complex.reCLM.hasSum h).summable

private theorem hasFPowerSeriesOnBall_mellinCentered {g : ℝ → ℝ} {A r : ℝ} {T : ℝ≥0}
    (hA : 2 ≤ A) (hg : AEMeasurable g (volume.restrict (Ioi A)))
    (hg₀ : ∀ᵐ x ∂volume.restrict (Ioi A), 0 ≤ g x)
    (hT₀ : 0 < T) (hT : MellinTailConverges g A (r - T)) :
    HasFPowerSeriesOnBall (fun w ↦ nonnegativeMellinTail g A ((r : ℂ) - w))
      (FormalMultilinearSeries.ofScalars ℂ (fun n ↦ ((∫ x in Ioi A, logMoment g r n x : ℝ) : ℂ)))
      0 T := by
  have hpos (n : ℕ) : 0 ≤ ∫ x in Ioi A, logMoment g r n x :=
    integral_nonneg_of_ae ((ae_one_le hA).and hg₀ |>.mono fun _ ⟨hx, hgx⟩ ↦
      logMoment_nonneg hx hgx n)
  have hsum := hasSum_integral_logMoment (w := ((T : ℝ) : ℂ)) hA hg hg₀ hT (by simp)
  refine ⟨FormalMultilinearSeries.le_radius_of_summable _ ?_, by exact_mod_cast hT₀, ?_⟩
  · simpa only [FormalMultilinearSeries.ofScalars_norm, Complex.norm_real,
      Real.norm_of_nonneg (hpos _)] using summable_real_of_hasSum hsum
  · intro w hw
    have hw' : ‖w‖ < (T : ℝ) := by
      simpa only [Metric.eball_coe, Metric.mem_ball, dist_zero_right] using hw
    simpa only [FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul, zero_add] using
      hasSum_integral_logMoment hA hg hg₀ hT hw'.le

/-- Landau's lemma at a finite absolute convergence abscissa. A locally analytic `F` at `α`
  cannot agree on the convergent side with the actual Mellin integral of `g`. No convergence
  at `α` itself is required. -/
public theorem nonnegativeMellinTail_no_analytic_extension {g : ℝ → ℝ} {A α : ℝ}
    (hA : 2 ≤ A) (hg : AEMeasurable g (volume.restrict (Ioi A)))
    (hg₀ : ∀ᵐ x ∂volume.restrict (Ioi A), 0 ≤ g x)
    (hright : ∀ r > α, MellinTailConverges g A r)
    (hleft : ∀ r < α, ¬ MellinTailConverges g A r)
    {F : ℂ → ℂ} (hF : AnalyticAt ℂ F (α : ℂ))
    (hagree : ∀ᶠ s : ℂ in 𝓝 (α : ℂ), α < s.re → F s = nonnegativeMellinTail g A s) :
    False := by
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp (hF.eventually_analyticAt.and hagree)
  let r : ℝ := α + ε / 4
  let T : ℝ≥0 := ⟨ε / 8, by positivity⟩
  let R : ℝ≥0 := ⟨ε / 2, by positivity⟩
  let t : ℝ := 3 * ε / 8
  let G (w : ℂ) := F ((r : ℂ) - w)
  have hshift {w : ℂ} (hw : ‖w‖ ≤ (R : ℝ)) : dist ((r : ℂ) - w) (α : ℂ) < ε := by
    rw [dist_eq_norm, show (r : ℂ) - w - (α : ℂ) = ((r - α : ℝ) : ℂ) - w by
      push_cast; ring]
    refine (norm_sub_le ..).trans_lt ?_
    rw [Complex.norm_real, Real.norm_of_nonneg (by dsimp [r]; linarith)]
    change ‖w‖ ≤ ε / 2 at hw
    change α + ε / 4 - α + ‖w‖ < ε
    linarith
  have hd : DifferentiableOn ℂ G (Metric.closedBall 0 (R : ℝ)) := by
    intro w hw
    have hw' : ‖w‖ ≤ (R : ℝ) := by simpa only [Metric.mem_closedBall, dist_zero_right] using hw
    exact ((hball (hshift hw')).1.differentiableAt.comp w
      (differentiableAt_id.const_sub (r : ℂ))).differentiableWithinAt
  have hlong := hd.hasFPowerSeriesOnBall (R := R) (by change 0 < ε / 2; positivity)
  have hT₀ : 0 < T := by change 0 < ε / 8; positivity
  have hT : MellinTailConverges g A (r - (T : ℝ)) :=
    hright _ (by change α < α + ε / 4 - ε / 8; linarith)
  have hlocal := (hasFPowerSeriesOnBall_mellinCentered hA hg hg₀ hT₀ hT).congr
    (g := G) (fun w hw ↦ by
      have hw' : ‖w‖ < (T : ℝ) := by
        simpa only [Metric.eball_coe, Metric.mem_ball, dist_zero_right] using hw
      change ‖w‖ < ε / 8 at hw'
      have hwR : ‖w‖ ≤ (R : ℝ) := by change ‖w‖ ≤ ε / 2; linarith
      apply ((hball (hshift hwR)).2 ?_).symm
      have hre := (le_abs_self w.re).trans (Complex.abs_re_le_norm w)
      rw [Complex.sub_re, Complex.ofReal_re]
      change α < α + ε / 4 - w.re
      linarith)
  have hcoeff := hlong.hasFPowerSeriesAt.eq_formalMultilinearSeries hlocal.hasFPowerSeriesAt
  -- The extension's Taylor series reaches `r - t < α`, beyond the original half-plane.
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have htw : (t : ℂ) ∈ Metric.eball (0 : ℂ) (R : ℝ≥0∞) := by
    rw [Metric.eball_coe, Metric.mem_ball, dist_zero_right, Complex.norm_real, Real.norm_of_nonneg ht]
    change 3 * ε / 8 < ε / 2
    linarith
  have hs := hlong.hasSum htw
  rw [hcoeff] at hs
  simp only [FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul] at hs
  exact hleft (r - t) (by dsimp [r, t]; linarith) <|
    converges_of_summable_logMoment hA hg hg₀ ht
      (integrable_logMoment hA hg hg₀ (by exact_mod_cast hT₀) hT) (summable_real_of_hasSum hs)

private theorem mellinTail_re_nonneg {g : ℝ → ℝ} {A r : ℝ} (hA : 2 ≤ A)
    (hg₀ : ∀ᵐ x ∂volume.restrict (Ioi A), 0 ≤ g x) (hr : MellinTailConverges g A r) :
    0 ≤ (nonnegativeMellinTail g A r).re := by
  have hpos := ae_one_le hA
  have heq : (fun x : ℝ ↦ (g x : ℂ) * (x : ℂ) ^ (-((r : ℂ) + 1))) =ᵐ[volume.restrict (Ioi A)]
      (fun x ↦ (realKernel g r x : ℂ)) := hpos.mono fun _ hx ↦ complexKernel_ofReal (zero_le_one.trans hx) r
  have hint : Integrable (fun x : ℝ ↦ (g x : ℂ) * (x : ℂ) ^ (-((r : ℂ) + 1)))
      (volume.restrict (Ioi A)) :=
    (show Integrable (realKernel g r) (volume.restrict (Ioi A)) from hr).ofReal.congr heq.symm
  rw [nonnegativeMellinTail, ← Complex.reCLM_apply, ← Complex.reCLM.integral_comp_comm hint]
  apply integral_nonneg_of_ae
  filter_upwards [heq, hpos, hg₀] with x hx hx₁ hgx
  rw [Complex.reCLM_apply, hx, Complex.ofReal_re]
  exact mul_nonneg hgx (Real.rpow_nonneg (zero_le_one.trans hx₁) _)

/-- A real residue of a simple pole at `α` cannot be negative. The local principal-part formula
  needs to agree with the Mellin tail only on the real convergent side. -/
public theorem nonnegativeMellinTail_residue_nonneg {g : ℝ → ℝ} {A α ρ : ℝ}
    (hA : 2 ≤ A) (hg₀ : ∀ᵐ x ∂volume.restrict (Ioi A), 0 ≤ g x)
    (hright : ∀ r > α, MellinTailConverges g A r)
    {F : ℂ → ℂ} (hF : AnalyticAt ℂ F (α : ℂ))
    (hpole : ∀ᶠ r : ℝ in 𝓝[>] α,
      nonnegativeMellinTail g A r = (ρ : ℂ) / ((r : ℂ) - (α : ℂ)) + F r) :
    0 ≤ ρ := by
  have hreg : ContinuousAt (fun r : ℝ ↦ F (r : ℂ)) α :=
    hF.continuousAt.comp Complex.continuous_ofReal.continuousAt
  have hlim : Tendsto (fun r : ℝ ↦ ((r : ℂ) - (α : ℂ)) * nonnegativeMellinTail g A r)
      (𝓝[>] α) (𝓝 (ρ : ℂ)) := by
    have hcont : ContinuousAt (fun r : ℝ ↦ (ρ : ℂ) + ((r : ℂ) - (α : ℂ)) * F r) α :=
      continuousAt_const.add ((Complex.continuous_ofReal.continuousAt.sub continuousAt_const).mul hreg)
    have h := tendsto_nhdsWithin_of_tendsto_nhds (s := Ioi α) hcont.tendsto
    simp only [sub_self, zero_mul, add_zero] at h
    apply h.congr'
    filter_upwards [eventually_mem_nhdsWithin, hpole] with r hr hrp
    have hr' : α < r := hr
    have hn : (r : ℂ) - (α : ℂ) ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hr'.ne')
    rw [hrp, mul_add, mul_div_cancel₀ _ hn]
  have hre := Complex.continuous_re.continuousAt.tendsto.comp hlim
  apply (isClosed_Ici (a := (0 : ℝ))).mem_of_tendsto (by simpa only [Complex.ofReal_re] using hre)
  filter_upwards [eventually_mem_nhdsWithin (s := Ioi α)] with r hr
  have hr' : α < r := hr
  change 0 ≤ (((r : ℂ) - (α : ℂ)) * nonnegativeMellinTail g A r).re
  rw [← Complex.ofReal_sub, Complex.mul_re]
  simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  exact mul_nonneg (sub_nonneg.mpr hr'.le) (mellinTail_re_nonneg hA hg₀ (hright r hr'))

end Masullo
