module

public import Theorems.RadialWeightedSchwartzStage
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Theorems.RealMultiplicativeMeasure
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Function.LpSpace.Complete

/-! # The closed-interval radial Hardy–Sobolev norm

Masullo §1.1.3 (p. 11), in the identity-module case `G = ℝ₊ˣ`. In the
coordinate `x = log t`, the normalized measure `dt/t` of (9.2.2.4) (p. 412)
is `volume` on `ℝ`. The maximum of the two exponential weights is retained,
as is the real exponent `s / 2` on `1 + x²`.
-/

open Filter MeasureTheory Set
open scoped ContDiff ENNReal NNReal SchwartzMap Topology

namespace Masullo

/-- The density of the radial squared Hardy–Sobolev norm against `dx`. -/
@[expose] public noncomputable def logSobolevWeight (a b s x : ℝ) : ℝ :=
  max (Real.exp (2 * a * x)) (Real.exp (2 * b * x)) * (1 + x ^ 2) ^ (s / 2)

private theorem logSobolevWeight_pos (a b s x : ℝ) : 0 < logSobolevWeight a b s x := by
  unfold logSobolevWeight
  exact mul_pos ((Real.exp_pos _).trans_le (le_max_left ..)) (Real.rpow_pos_of_pos (by positivity) _)

private theorem continuous_logSobolevWeight (a b s : ℝ) : Continuous (logSobolevWeight a b s) :=
  (Continuous.max (by fun_prop) (by fun_prop)).mul
    ((show Continuous (fun x : ℝ ↦ 1 + x ^ 2) by fun_prop).rpow_const
      (fun x ↦ Or.inl ((show 0 < 1 + (x : ℝ) ^ 2 by positivity).ne')))

private theorem integrable_schwartz_norm_sq_mul_logPower (g : 𝓢(ℝ, ℂ)) (s : ℝ) :
    Integrable (fun x : ℝ ↦ ‖g x‖ ^ 2 * (1 + x ^ 2) ^ (s / 2)) := by
  obtain ⟨m, hm⟩ := exists_nat_ge (s / 2)
  let C := SchwartzMap.seminorm ℝ 0 0 g
  have hint : Integrable (fun x : ℝ ↦ C * 2 ^ (m - 1) * (‖g x‖ + ‖x‖ ^ (2 * m) * ‖g x‖)) :=
    (g.integrable.norm.add (g.integrable_pow_mul volume (2 * m))).const_mul _
  refine hint.mono' ?_ (ae_of_all _ fun x ↦ ?_)
  · exact ((g.continuous.norm.pow 2).mul
      ((show Continuous (fun x : ℝ ↦ 1 + x ^ 2) by fun_prop).rpow_const
        (fun x ↦ Or.inl ((show 0 < 1 + (x : ℝ) ^ 2 by positivity).ne')))).aestronglyMeasurable
  · rw [Real.norm_of_nonneg (by positivity)]
    have hw : (1 + x ^ 2) ^ (s / 2) ≤ 2 ^ (m - 1) * (1 + ‖x‖ ^ (2 * m)) := by
      calc
        _ ≤ (1 + x ^ 2) ^ (m : ℝ) := Real.rpow_le_rpow_of_exponent_le (le_add_of_nonneg_right (sq_nonneg x)) hm
        _ ≤ _ := by
          rw [Real.rpow_natCast, pow_mul, Real.norm_eq_abs, sq_abs]
          simpa only [one_pow] using (add_pow_le (zero_le_one : (0 : ℝ) ≤ 1) (sq_nonneg x) m)
    calc
      ‖g x‖ ^ 2 * (1 + x ^ 2) ^ (s / 2) ≤ (C * ‖g x‖) * (2 ^ (m - 1) * (1 + ‖x‖ ^ (2 * m))) := by
        rw [pow_two]
        gcongr
        exact SchwartzMap.norm_le_seminorm ℝ g x
      _ = _ := by ring

private theorem norm_sq_weighted_profile (a x : ℝ) (z : ℂ) :
    ‖logStageWeight a x * z‖ ^ 2 = Real.exp (2 * a * x) * ‖z‖ ^ 2 := by
  rw [norm_mul, mul_pow, logStageWeight, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _), ← Real.exp_nat_mul]
  push_cast
  ring_nf

/-- The exact squared norm is integrable using just the two endpoint Schwartz
profiles. There is no spare exponential decay assumption and `s` may be negative. -/
public theorem integrable_logSobolevWeight_mul_norm_sq {a b s : ℝ} (hab : a ≤ b)
    {f : ℝ → ℂ} (hf : f ∈ logWeightedProfiles (Icc a b)) :
    Integrable (fun x : ℝ ↦ logSobolevWeight a b s x * ‖f x‖ ^ 2) := by
  obtain ⟨g, hg⟩ := hf.2 ⟨a, le_rfl, hab⟩
  obtain ⟨h, hh⟩ := hf.2 ⟨b, hab, le_rfl⟩
  refine ((integrable_schwartz_norm_sq_mul_logPower g s).add
    (integrable_schwartz_norm_sq_mul_logPower h s)).mono'
    ((continuous_logSobolevWeight a b s).mul (hf.1.continuous.norm.pow 2)).aestronglyMeasurable
    (ae_of_all _ fun x ↦ ?_)
  rw [Real.norm_of_nonneg (mul_nonneg (logSobolevWeight_pos a b s x).le (sq_nonneg _))]
  simp only [Pi.add_apply, hg x, hh x, norm_sq_weighted_profile, logSobolevWeight]
  rw [mul_right_comm, ← add_mul, ← add_mul]
  gcongr
  exact max_le_add_of_nonneg (Real.exp_pos _).le (Real.exp_pos _).le

/-- Lebesgue measure in `x = log t`, weighted by the exact squared-norm density. -/
@[expose] public noncomputable def logSobolevMeasure (a b s : ℝ) : Measure ℝ :=
  volume.withDensity (fun x ↦ ((logSobolevWeight a b s x).toNNReal : ℝ≥0∞))

private theorem measurable_logSobolevDensity (a b s : ℝ) :
    Measurable (fun x ↦ (logSobolevWeight a b s x).toNNReal) :=
  (continuous_logSobolevWeight a b s).measurable.real_toNNReal

/-- Closed-interval radial profiles belong to the weighted `L²` space. -/
public theorem memLp_logSobolevMeasure {a b s : ℝ} (hab : a ≤ b)
    {f : ℝ → ℂ} (hf : f ∈ logWeightedProfiles (Icc a b)) :
    MemLp f 2 (logSobolevMeasure a b s) := by
  rw [memLp_two_iff_integrable_sq_norm hf.1.continuous.aestronglyMeasurable,
    logSobolevMeasure,
    integrable_withDensity_iff_integrable_coe_smul (measurable_logSobolevDensity a b s)]
  simpa only [smul_eq_mul, Real.coe_toNNReal _ (logSobolevWeight_pos a b s _).le] using
    integrable_logSobolevWeight_mul_norm_sq (s := s) hab hf

/-- The pointwise profile viewed as an a.e. class in the normalized weighted `L²` space. -/
public noncomputable def logSobolevToLp {a b : ℝ} (hab : a ≤ b) (s : ℝ) :
    logWeightedProfiles (Icc a b) →ₗ[ℂ] Lp ℂ 2 (logSobolevMeasure a b s) where
  toFun f := (memLp_logSobolevMeasure hab f.property).toLp f.1
  map_add' f g := (memLp_logSobolevMeasure hab f.property).toLp_add
    (memLp_logSobolevMeasure hab g.property)
  map_smul' c f := (memLp_logSobolevMeasure hab f.property).toLp_const_smul c

/-- The image in `L²` has the original profile as a representative. -/
public theorem logSobolevToLp_ae_eq {a b : ℝ} (hab : a ≤ b) (s : ℝ)
    (f : logWeightedProfiles (Icc a b)) :
    (logSobolevToLp hab s f : ℝ → ℂ) =ᵐ[logSobolevMeasure a b s] f.1 :=
  (memLp_logSobolevMeasure hab f.property).coeFn_toLp

/-- Distinct smooth profiles are not identified by the weighted a.e. quotient. -/
public theorem logSobolevToLp_injective {a b : ℝ} (hab : a ≤ b) (s : ℝ) :
    Function.Injective (logSobolevToLp hab s) := by
  intro f g h
  apply Subtype.ext
  apply Measure.eq_of_ae_eq (μ := (volume : Measure ℝ)) _
    f.property.1.continuous g.property.1.continuous
  apply (withDensity_ae_eq (measurable_logSobolevDensity a b s).coe_nnreal_ennreal.aemeasurable
    (ae_of_all _ fun x ↦ by simp [(logSobolevWeight_pos a b s x)])).mp
  exact (logSobolevToLp_ae_eq hab s f).symm.trans (h ▸ logSobolevToLp_ae_eq hab s g)

/-- The norm of the embedded profile is the printed weighted integral, with
`dt/t` normalized to `dx` and with the integrability established above. -/
public theorem norm_logSobolevToLp {a b : ℝ} (hab : a ≤ b) (s : ℝ)
    (f : logWeightedProfiles (Icc a b)) :
    ‖logSobolevToLp hab s f‖ =
      Real.sqrt (∫ x : ℝ, logSobolevWeight a b s x * ‖f.1 x‖ ^ 2) := by
  change ‖(memLp_logSobolevMeasure hab f.property).toLp f.1‖ = _
  rw [Lp.norm_toLp, (memLp_logSobolevMeasure hab f.property).eLpNorm_eq_integral_rpow_norm
    (by norm_num) (by simp), ENNReal.toReal_ofReal (by positivity)]
  norm_num only [ENNReal.toReal_ofNat, ← Real.rpow_natCast _ 2, Nat.cast_ofNat]
  rw [Real.sqrt_eq_rpow, one_div]
  congr 1
  rw [logSobolevMeasure, integral_withDensity_eq_integral_smul (measurable_logSobolevDensity a b s)]
  simp only [NNReal.smul_def, smul_eq_mul, Real.coe_toNNReal _ (logSobolevWeight_pos a b s _).le]

/-- The change of variables takes the literal positive-real weight and `dt/t`
back to the integrable norm expression in `x = log t`. The measure on the
right is the positive restriction of `dt/|t|` on the ambient real line. -/
public theorem logSobolevToLp_positiveIntegral {a b : ℝ} (hab : a ≤ b) (s : ℝ)
    (f : logWeightedProfiles (Icc a b)) :
    let μ := (((volume : Measure ℝ).restrict ({0}ᶜ)).withDensity
      (fun t ↦ ENNReal.ofReal |t|⁻¹)).restrict (Ioi 0)
    let F := fun t : ℝ ↦ max (t ^ (2 * a)) (t ^ (2 * b)) *
      (1 + |Real.log t| ^ 2) ^ (s / 2) * ‖f.1 (Real.log t)‖ ^ 2
    Integrable F μ ∧ ‖logSobolevToLp hab s f‖ = Real.sqrt (∫ t, F t ∂μ) := by
  dsimp only
  rw [← map_volume_exp_eq_restrict_realMultiplicative]
  let F := fun t : ℝ ↦ max (t ^ (2 * a)) (t ^ (2 * b)) *
    (1 + |Real.log t| ^ 2) ^ (s / 2) * ‖f.1 (Real.log t)‖ ^ 2
  change Integrable F (volume.map Real.exp) ∧
    ‖logSobolevToLp hab s f‖ = Real.sqrt (∫ t, F t ∂(volume.map Real.exp))
  have hexp : Measurable Real.exp := Real.continuous_exp.measurable
  have hlog : Measurable Real.log := Real.measurable_log
  have hf : Continuous f.1 := f.property.1.continuous
  have hF : Measurable F := by
    dsimp [F]
    fun_prop
  have hcomp : F ∘ Real.exp = fun x ↦ logSobolevWeight a b s x * ‖f.1 x‖ ^ 2 := by
    funext x
    simp only [Function.comp_apply, F, logSobolevWeight, Real.log_exp, sq_abs]
    rw [mul_comm (2 * a) x, mul_comm (2 * b) x, Real.exp_mul, Real.exp_mul]
  refine ⟨(integrable_map_measure hF.aestronglyMeasurable hexp.aemeasurable).2
    (hcomp.symm ▸ integrable_logSobolevWeight_mul_norm_sq (s := s) hab f.property), ?_⟩
  rw [norm_logSobolevToLp, integral_map hexp.aemeasurable hF.aestronglyMeasurable, ← hcomp]
  rfl

/-- The same weighted `L²` map on all-weight profiles, via their natural inclusion. -/
public noncomputable def logSobolevAllToLp {a b : ℝ} (hab : a ≤ b) (s : ℝ) :
    logWeightedProfiles univ →ₗ[ℂ] Lp ℂ 2 (logSobolevMeasure a b s) :=
  (logSobolevToLp hab s).comp (Submodule.inclusion (fun _ hf ↦ ⟨hf.1,
    fun w ↦ hf.2 ⟨w, mem_univ _⟩⟩))

/-- The all-weight map also has the original profile as its representative. -/
public theorem logSobolevAllToLp_ae_eq {a b : ℝ} (hab : a ≤ b) (s : ℝ)
    (f : logWeightedProfiles univ) :
    (logSobolevAllToLp hab s f : ℝ → ℂ) =ᵐ[logSobolevMeasure a b s] f.1 :=
  logSobolevToLp_ae_eq hab s _

private theorem smooth_logStageWeight (a : ℝ) : ContDiff ℝ ∞ (logStageWeight a) :=
  Complex.ofRealCLM.contDiff.comp (Real.contDiff_exp.comp (contDiff_const.mul contDiff_id))

private theorem mem_logWeightedProfiles_univ_of_compact {f : ℝ → ℂ}
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) : f ∈ logWeightedProfiles univ := by
  refine ⟨hf, fun a ↦ ?_⟩
  have hcs : HasCompactSupport (fun x ↦ logStageWeight a x * f x) := hc.mul_left
  exact ⟨hcs.toSchwartzMap ((smooth_logStageWeight a).mul hf), fun _ ↦ rfl⟩

private noncomputable def sobolevCutoff (n : ℕ) (x : ℝ) : ℝ :=
  (⟨1, 2, one_pos, one_lt_two⟩ : ContDiffBump (0 : ℝ)) (((n : ℝ) + 1)⁻¹ • x)

private theorem sobolevCutoff_smooth (n : ℕ) : ContDiff ℝ ∞ (sobolevCutoff n) :=
  ContDiffBump.contDiff _ |>.comp (contDiff_const_smul _)

private theorem sobolevCutoff_compact (n : ℕ) : HasCompactSupport (sobolevCutoff n) :=
  ContDiffBump.hasCompactSupport _ |>.comp_smul (inv_ne_zero (by positivity))

private theorem sobolevCutoff_eventually_one (x : ℝ) : ∀ᶠ n in atTop, sobolevCutoff n x = 1 := by
  obtain ⟨N, hN⟩ := exists_nat_ge ‖x‖
  filter_upwards [eventually_ge_atTop N] with n hn
  apply ContDiffBump.one_of_mem_closedBall
  rw [mem_closedBall_zero_iff, norm_smul, Real.norm_of_nonneg (by positivity),
    inv_mul_eq_div]
  change ‖x‖ / ((n : ℝ) + 1) ≤ 1
  rw [div_le_one (by positivity)]
  exact hN.trans ((Nat.cast_le.mpr hn).trans (le_add_of_nonneg_right zero_le_one))

/-- Compactly supported, all-weight profiles approximate each closed-interval profile
in the printed norm. The proof uses domination by the squared norm integrand, not
convergence in the Schwartz–Bruhat LF topology. -/
public theorem exists_logSobolevAllToLp_tendsto {a b : ℝ} (hab : a ≤ b) (s : ℝ)
    (f : logWeightedProfiles (Icc a b)) :
    ∃ u : ℕ → logWeightedProfiles univ, (∀ n, HasCompactSupport (u n).1) ∧
      Tendsto (fun n ↦ logSobolevAllToLp hab s (u n)) atTop (𝓝 (logSobolevToLp hab s f)) := by
  let v (n : ℕ) (x : ℝ) := sobolevCutoff n x • f.1 x
  have hv (n : ℕ) : ContDiff ℝ ∞ (v n) := (sobolevCutoff_smooth n).smul f.property.1
  have hvc (n : ℕ) : HasCompactSupport (v n) := (sobolevCutoff_compact n).smul_right
  let u (n : ℕ) : logWeightedProfiles univ :=
    ⟨v n, mem_logWeightedProfiles_univ_of_compact (hv n) (hvc n)⟩
  refine ⟨u, hvc, tendsto_iff_norm_sub_tendsto_zero.2 ?_⟩
  let F (n : ℕ) (x : ℝ) := logSobolevWeight a b s x * ‖v n x - f.1 x‖ ^ 2
  have hDCT : Tendsto (fun n ↦ ∫ x, F n x) atTop (𝓝 0) := by
    have h := tendsto_integral_of_dominated_convergence (f := fun _ ↦ (0 : ℝ))
      (F := F) (fun x ↦ logSobolevWeight a b s x * ‖f.1 x‖ ^ 2)
      (fun n ↦ ((continuous_logSobolevWeight a b s).mul
        (((hv n).continuous.sub f.property.1.continuous).norm.pow 2)).aestronglyMeasurable)
      (integrable_logSobolevWeight_mul_norm_sq hab f.property)
    suffices H : Tendsto (fun n ↦ ∫ x, F n x) atTop (𝓝 (∫ _ : ℝ, (0 : ℝ))) by
      simpa using H
    apply h
    · intro n
      refine ae_of_all _ fun x ↦ ?_
      change ‖logSobolevWeight a b s x * ‖sobolevCutoff n x • f.1 x - f.1 x‖ ^ 2‖ ≤ _
      have he : sobolevCutoff n x • f.1 x - f.1 x = (sobolevCutoff n x - 1) • f.1 x := by
        rw [sub_smul, one_smul]
      rw [Real.norm_of_nonneg (mul_nonneg (logSobolevWeight_pos a b s x).le (sq_nonneg _)),
        he, norm_smul, Real.norm_eq_abs]
      have h₀ : 0 ≤ sobolevCutoff n x := ContDiffBump.nonneg _
      have h₁ : sobolevCutoff n x ≤ 1 := ContDiffBump.le_one _
      rw [abs_of_nonpos (sub_nonpos.mpr h₁)]
      apply mul_le_mul_of_nonneg_left _ (logSobolevWeight_pos a b s x).le
      apply pow_le_pow_left₀ (mul_nonneg (neg_nonneg.mpr (sub_nonpos.mpr h₁)) (norm_nonneg _)) _ 2
      exact mul_le_of_le_one_left (norm_nonneg _) (by linarith)
    · refine ae_of_all _ fun x ↦ tendsto_const_nhds.congr' ?_
      filter_upwards [sobolevCutoff_eventually_one x] with n hn
      simp [F, v, hn]
  have h := Real.continuous_sqrt.continuousAt.tendsto.comp hDCT
  rw [Real.sqrt_zero] at h
  convert h using 1
  funext n
  change ‖logSobolevToLp hab s _ - logSobolevToLp hab s f‖ = Real.sqrt (∫ x, F n x)
  rw [← map_sub, norm_logSobolevToLp]
  rfl

/-- The natural inclusions of the all-weight and closed-interval profiles have the
same complete closure in weighted `L²`. Via the faithful norm formula, this is a
common isometric completion, using the maps on the original pointwise profiles. -/
public theorem logSobolev_commonCompletion {a b : ℝ} (hab : a ≤ b) (s : ℝ) :
    closure (range (logSobolevAllToLp hab s)) = closure (range (logSobolevToLp hab s)) ∧
      IsComplete (closure (range (logSobolevToLp hab s))) := by
  refine ⟨le_antisymm (closure_mono ?_) (closure_minimal ?_ isClosed_closure),
    isClosed_closure.isComplete⟩
  · rintro _ ⟨f, rfl⟩
    exact ⟨_, rfl⟩
  · rintro _ ⟨f, rfl⟩
    obtain ⟨u, _, hu⟩ := exists_logSobolevAllToLp_tendsto hab s f
    exact mem_closure_of_tendsto hu (Eventually.of_forall fun n ↦ mem_range_self (u n))

end Masullo
