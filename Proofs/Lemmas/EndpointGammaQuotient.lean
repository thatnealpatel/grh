module

public import Lemmas.SignedEndpointProfile
public import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Lemmas.DigammaExponential
import Mathlib.Analysis.Fourier.LpSpace
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Tactic

/-! # Archimedean energy of the signed endpoint profile

Selection pin: `b6b5fe8c`. Source: `6ffb987a:.godel/bob/endpoint-arithmetic-test.md`,
lines 5–28. Consumer: `b3723e8:.godel/bob/twist-endpoint-packet.md`, lines 11–17.
Owning check session: `01a20efe-657a-74fc-9a09-f6e32d4cc146`.

We integrate the true modulated zero extension, keeping the boundary terms in
its Fourier transform, and normalize with angular Plancherel (`dξ/(2π)`). The
Gauss integral compared with the logarithmic integral bounds the parity symbols;
the translated Fourier density then controls the centered logarithmic moment.
The result is the archimedean contribution alone, not the conductor term,
prime-side asymptotics, or the signed zero-charge bound in the consumer.
-/

open MeasureTheory Set
open scoped FourierTransform SchwartzMap RealInnerProductSpace

namespace Masullo

section Fourier

/-- The angular transform with kernel `exp (-I * ξ * x)` of the modulated
zero extension from `SignedEndpointProfile`. -/
@[expose] public noncomputable def signedEndpointAngularFourier (D y ξ : ℝ) : ℂ :=
  ∫ x : ℝ, primeWindowPhase (-ξ) x *
    (primeWindowPhase y x * (signedEndpointProfile D x : ℂ))

/-- Modulation translates angular frequency by `y`, not by `2πy`. -/
public theorem signedEndpointAngularFourier_shift (D y ξ : ℝ) :
    signedEndpointAngularFourier D y ξ = signedEndpointAngularFourier D 0 (ξ - y) := by
  unfold signedEndpointAngularFourier
  congr 1
  funext x
  simp only [primeWindowPhase, Complex.ofReal_zero, mul_zero, zero_mul, Complex.exp_zero, one_mul,
    ← mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  ring

private theorem signedEndpointAngularFourier_interval {D : ℝ} (hD : 0 ≤ D) (ξ : ℝ) :
    signedEndpointAngularFourier D 0 ξ =
      (∫ x in (0 : ℝ)..D, Complex.exp (((-1 / 2 : ℂ) - Complex.I * ξ) * (x : ℂ))) +
        (Real.exp (-D / 2) : ℂ) *
          (∫ x in (0 : ℝ)..D, Complex.exp (((1 / 2 : ℂ) - Complex.I * ξ) * (x : ℂ))) := by
  let f (x : ℝ) := primeWindowPhase (-ξ) x * (signedEndpointProfile D x : ℂ)
  have hf : ∀ x ∉ Icc 0 D, f x = 0 := by
    intro x hx
    simp [f, signedEndpointProfile, hx]
  have h : signedEndpointAngularFourier D 0 ξ = ∫ x in Icc 0 D, f x := by
    simpa [signedEndpointAngularFourier, primeWindowPhase, f] using
      (setIntegral_eq_integral_of_ae_compl_eq_zero (Filter.Eventually.of_forall hf)).symm
  rw [h, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hD]
  let a : ℂ := -1 / 2 - Complex.I * ξ
  let b : ℂ := 1 / 2 - Complex.I * ξ
  let g (x : ℝ) := Complex.exp (a * x)
  let k (x : ℝ) := (Real.exp (-D / 2) : ℂ) * Complex.exp (b * x)
  have hg : Continuous g := by unfold g; fun_prop
  have hk : Continuous k := by unfold k; fun_prop
  rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_add
    (hg.intervalIntegrable _ _) (hk.intervalIntegrable _ _)]
  apply intervalIntegral.integral_congr
  intro x hx
  rw [uIcc_of_le hD] at hx
  simp only [f, signedEndpointProfile, indicator_of_mem hx, primeWindowPhase, Complex.ofReal_neg,
    Complex.ofReal_add, Complex.ofReal_exp, mul_add, g, k, a, b]
  rw [← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
  push_cast
  congr 2 <;> ring

/-- Uniform decay of the true endpoint Fourier integral, including its jumps
and the modulation shift. The same constant works at zero frequency. -/
public theorem norm_signedEndpointAngularFourier_le {D : ℝ} (hD : 1 ≤ D) (y ξ : ℝ) :
    ‖signedEndpointAngularFourier D y ξ‖ ≤ 12 / (1 + |ξ - y|) := by
  rw [signedEndpointAngularFourier_shift]
  let s := ξ - y
  rw [signedEndpointAngularFourier_interval (by linarith : 0 ≤ D)]
  let a : ℂ := -1 / 2 - Complex.I * s
  let b : ℂ := 1 / 2 - Complex.I * s
  change ‖(∫ x in (0 : ℝ)..D, Complex.exp (a * (x : ℂ))) +
    (Real.exp (-D / 2) : ℂ) * ∫ x in (0 : ℝ)..D, Complex.exp (b * (x : ℂ))‖ ≤
      12 / (1 + |s|)
  have har : a.re = -1 / 2 := by simp [a, Complex.mul_re]
  have hbr : b.re = 1 / 2 := by simp [b, Complex.mul_re]
  have hai : a.im = -s := by simp [a, Complex.mul_im]
  have hbi : b.im = -s := by simp [b, Complex.mul_im]
  have hden (c : ℂ) (hr : |c.re| = 1 / 2) (hi : c.im = -s) :
      (1 + |s|) / 3 ≤ ‖c‖ := by
    have h₁ := Complex.abs_re_le_norm c
    have h₂ := Complex.abs_im_le_norm c
    rw [hr] at h₁
    rw [hi, abs_neg] at h₂
    linarith
  have ha := hden a (by rw [har]; norm_num) hai
  have hb := hden b (by rw [hbr]; norm_num) hbi
  have hs : 0 < 1 + |s| := by positivity
  have hap : 0 < ‖a‖ := (div_pos hs (by norm_num)).trans_le ha
  have hbp : 0 < ‖b‖ := (div_pos hs (by norm_num)).trans_le hb
  rw [integral_exp_mul_complex (norm_pos_iff.mp hap),
    integral_exp_mul_complex (norm_pos_iff.mp hbp)]
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero]
  have han : ‖Complex.exp (a * (D : ℂ))‖ = Real.exp (-D / 2) := by
    rw [Complex.norm_exp, Complex.mul_re]
    simp [har]; ring_nf
  have hbn : ‖Complex.exp (b * (D : ℂ))‖ = Real.exp (D / 2) := by
    rw [Complex.norm_exp, Complex.mul_re]
    simp [hbr]; ring_nf
  have he : Real.exp (-D / 2) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have h₁ : ‖Complex.exp (a * (D : ℂ)) - 1‖ ≤ 2 := by
    have h := norm_sub_le (Complex.exp (a * (D : ℂ))) 1
    rw [han, norm_one] at h
    linarith
  have h₂ : Real.exp (-D / 2) * ‖Complex.exp (b * (D : ℂ)) - 1‖ ≤ 2 := by
    have h := norm_sub_le (Complex.exp (b * (D : ℂ))) 1
    rw [hbn, norm_one] at h
    apply (mul_le_mul_of_nonneg_left h (Real.exp_pos _).le).trans
    rw [mul_add, ← Real.exp_add, show -D / 2 + D / 2 = 0 by ring, Real.exp_zero, mul_one]
    linarith
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, norm_div, norm_div, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le,
    ← mul_div_assoc]
  calc
    _ ≤ 2 / ‖a‖ + 2 / ‖b‖ := by gcongr
    _ ≤ 2 / ((1 + |s|) / 3) + 2 / ((1 + |s|) / 3) := by gcongr
    _ = _ := by rw [div_div_eq_mul_div]; ring

private noncomputable def endpointU (D y x : ℝ) : ℂ :=
  primeWindowPhase y x * (signedEndpointProfile D x : ℂ)

private theorem endpointU_ae (D y : ℝ) :
    primeWindowModulate y (signedEndpointProfileVector D) =ᵐ[volume] endpointU D y := by
  filter_upwards [primeWindowModulate_ae y (signedEndpointProfileVector D),
    signedEndpointProfileVector_ae D] with x h₁ h₂
  simp [endpointU, h₁, h₂]

private theorem endpointU_integrable (D y : ℝ) : Integrable (endpointU D y) := by
  let g (x : ℝ) := primeWindowPhase y x * (↑(Real.exp (-x / 2) + Real.exp (-(D - x) / 2)) : ℂ)
  have hg : Continuous g := by unfold g primeWindowPhase; fun_prop
  have heq : endpointU D y = (Icc 0 D).indicator g := by
    funext x
    by_cases hx : x ∈ Icc 0 D <;> simp [endpointU, g, signedEndpointProfile, hx]
  rw [heq, integrable_indicator_iff measurableSet_Icc]
  exact hg.continuousOn.integrableOn_compact isCompact_Icc

private theorem endpoint_cycles_eq (D y t : ℝ) :
    (𝓕 (endpointU D y)) t = signedEndpointAngularFourier D y ((2 * Real.pi) * t) := by
  rw [Real.fourier_real_eq_integral_exp_smul, signedEndpointAngularFourier]
  apply integral_congr_ae
  refine Filter.Eventually.of_forall fun x ↦ ?_
  simp only [endpointU, smul_eq_mul, primeWindowPhase]
  congr 2
  push_cast
  ring

private theorem continuous_endpoint_cycles (D y : ℝ) : Continuous (𝓕 (endpointU D y)) :=
  VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
    (innerSL ℝ).continuous₂ (endpointU_integrable D y)

private theorem continuous_endpoint_angular (D y : ℝ) :
    Continuous (signedEndpointAngularFourier D y) := by
  convert (continuous_endpoint_cycles D y).comp (continuous_id.div_const (2 * Real.pi)) using 1
  funext ξ
  simp [endpoint_cycles_eq, mul_div_cancel₀ _ (by positivity : 2 * Real.pi ≠ 0)]

private theorem endpoint_weight_integrable {p : ℝ} (hp : p < -1) :
    Integrable (fun x : ℝ ↦ (1 + |x|) ^ p) := by
  let f (x : ℝ) := (1 + |x|) ^ p
  have hpos : IntegrableOn f (Ioi 0) := by
    apply (integrableOn_add_rpow_Ioi_of_lt (c := 0) (m := 1) hp (by norm_num)).congr_fun
      _ measurableSet_Ioi
    intro x hx
    simp [f, abs_of_pos (mem_Ioi.mp hx), add_comm]
  have hnonneg : IntegrableOn f (Ici 0) := hpos.congr_set_ae Ioi_ae_eq_Ici.symm
  have hneg : IntegrableOn f (Iio 0) := by
    have h := ((Measure.measurePreserving_neg (volume : Measure ℝ)).integrableOn_comp_preimage
      (Homeomorph.neg ℝ).measurableEmbedding).mpr hpos
    convert h using 1
    · funext x
      simp [f]
    · ext x
      simp
  simpa only [f, ← compl_Ici, union_compl_self, integrableOn_univ] using hnonneg.union hneg

private theorem endpoint_density_integrable {D : ℝ} (hD : 1 ≤ D) (y : ℝ) :
    Integrable (fun ξ : ℝ ↦ ‖signedEndpointAngularFourier D y ξ‖ ^ 2) := by
  have h := ((endpoint_weight_integrable (p := -2) (by norm_num)).const_mul 144)
  have h' := (measurePreserving_add_right volume (-y)).integrable_comp_of_integrable h
  apply h'.mono' (((continuous_endpoint_angular D y).norm.pow 2).aestronglyMeasurable)
  refine Filter.Eventually.of_forall fun ξ ↦ ?_
  change ‖‖signedEndpointAngularFourier D y ξ‖ ^ 2‖ ≤ 144 * (1 + |ξ + -y|) ^ (-2 : ℝ)
  rw [Real.norm_of_nonneg (sq_nonneg _), ← sub_eq_add_neg, Real.rpow_neg (by positivity),
    Real.rpow_two]
  calc
    _ ≤ (12 / (1 + |ξ - y|)) ^ 2 := by
      gcongr
      exact norm_signedEndpointAngularFourier_le hD y ξ
    _ = _ := by rw [div_pow, div_eq_mul_inv]; norm_num

private theorem endpoint_cycles_memLp {D : ℝ} (hD : 1 ≤ D) (y : ℝ) :
    MemLp (𝓕 (endpointU D y)) 2 volume := by
  apply (memLp_two_iff_integrable_sq_norm (continuous_endpoint_cycles D y).aestronglyMeasurable).mpr
  simpa only [endpoint_cycles_eq] using
    (endpoint_density_integrable hD y).comp_mul_left' (by positivity : 2 * Real.pi ≠ 0)

local notation "𝓗" => Lp ℂ 2 (volume : Measure ℝ)

set_option maxHeartbeats 800000 in
private theorem endpoint_cycles_toLp {D : ℝ} (hD : 1 ≤ D) (y : ℝ) :
    (endpoint_cycles_memLp hD y).toLp _ = 𝓕 (primeWindowModulate y (signedEndpointProfileVector D)) := by
  let u := primeWindowModulate y (signedEndpointProfileVector D)
  let v := (endpoint_cycles_memLp hD y).toLp _
  have hinj := LinearMap.ker_eq_bot.mp
    (Lp.ker_toTemperedDistributionCLM_eq_bot (F := ℂ) (μ := (volume : Measure ℝ)) (p := 2))
  apply hinj
  change (v : 𝓢'(ℝ, ℂ)) = ((𝓕 u : 𝓗) : 𝓢'(ℝ, ℂ))
  rw [← Lp.fourier_toTemperedDistribution_eq]
  ext g
  simp only [TemperedDistribution.fourier_apply, Lp.toTemperedDistribution_apply]
  calc
    _ = ∫ t, (𝓕 (endpointU D y)) t • g t := by
      apply integral_congr_ae
      filter_upwards [(endpoint_cycles_memLp hD y).coeFn_toLp] with x hx
      rw [show v x = _ from hx, smul_eq_mul, smul_eq_mul, mul_comm]
    _ = ∫ t, endpointU D y t • (𝓕 g) t := by
      have hfg (t : ℝ) : (𝓕 g) t = (𝓕 (⇑g)) t := congrFun (SchwartzMap.fourier_coe g) t
      simp_rw [hfg]
      exact (by
        simpa only [flip_innerₗ, FourierTransform.fourier, Real.instFourierTransform] using
          (VectorFourier.integral_fourierIntegral_smul_eq_flip (L := innerₗ ℝ)
            Real.continuous_fourierChar (innerSL ℝ).continuous₂ (endpointU_integrable D y) g.integrable) :
        (∫ t, (𝓕 (endpointU D y)) t • g t) = ∫ t, endpointU D y t • (𝓕 (⇑g)) t)
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [endpointU_ae D y] with x hx
      rw [show u x = _ from hx, smul_eq_mul, smul_eq_mul, mul_comm]

/-- The angular spectral measure `dξ/(2π)`, as a scalar multiple of Lebesgue measure. -/
@[expose] public noncomputable def endpointAngularMeasure : Measure ℝ :=
  ENNReal.ofReal ((2 * Real.pi)⁻¹) • volume

/-- The actual squared norm of the signed endpoint test. -/
@[expose] public noncomputable def signedEndpointMass (D : ℝ) : ℝ :=
  2 * (1 - Real.exp (-D)) + 2 * D * Real.exp (-D / 2)

/-- Angular Plancherel for the modulated endpoint test, with its explicit mass. -/
public theorem signedEndpointAngularFourier_mass {D : ℝ} (hD : 1 ≤ D) (y : ℝ) :
    (∫ ξ, ‖signedEndpointAngularFourier D y ξ‖ ^ 2 ∂endpointAngularMeasure) = signedEndpointMass D := by
  let v := (endpoint_cycles_memLp hD y).toLp _
  have hv : (∫ t, ‖(𝓕 (endpointU D y)) t‖ ^ 2) = ‖v‖ ^ 2 := by
    calc
      _ = ∫ t, ‖v t‖ ^ 2 := by
        apply integral_congr_ae
        filter_upwards [(endpoint_cycles_memLp hD y).coeFn_toLp] with t ht
        rw [show v t = _ from ht]
      _ = ∫ t, RCLike.re (inner ℂ (v t) (v t)) := by simp [norm_sq_eq_re_inner (𝕜 := ℂ)]
      _ = RCLike.re (inner ℂ v v) := by rw [L2.inner_def, integral_re (L2.integrable_inner v v)]
      _ = ‖v‖ ^ 2 := (norm_sq_eq_re_inner (𝕜 := ℂ) (x := v)).symm
  calc
    _ = ∫ t, ‖(𝓕 (endpointU D y)) t‖ ^ 2 := by
      simp only [endpointAngularMeasure, integral_smul_measure, endpoint_cycles_eq]
      rw [ENNReal.toReal_ofReal (by positivity : 0 ≤ (2 * Real.pi)⁻¹)]
      rw [Measure.integral_comp_mul_left (fun ξ ↦ ‖signedEndpointAngularFourier D y ξ‖ ^ 2),
        abs_of_pos (by positivity : 0 < (2 * Real.pi)⁻¹)]
    _ = _ := by
      rw [hv]
      dsimp only [v]
      rw [endpoint_cycles_toLp hD y, Lp.norm_fourier_eq,
        signedEndpointProfile_norm_sq (by linarith : 0 ≤ D), signedEndpointMass,
        show -D / 2 = -(D / 2) by ring, Real.exp_neg, Real.exp_neg]
      simp [div_eq_mul_inv]


end Fourier

section Symbol

open Complex

set_option maxHeartbeats 800000

-- The logarithmic difference is absolutely integrable on the positive half-line.
private theorem endpoint_log_eq_exponential {a : ℝ} (ha : 0 < a) (b : ℝ) :
    let z := (a : ℂ) + (b : ℂ) * I
    let F (x : ℝ) := (exp (-(a : ℂ) * (x : ℂ)) - exp (-z * (x : ℂ))) / (x : ℂ)
    IntegrableOn F (Ioi 0) ∧ (∫ x in Ioi (0 : ℝ), F x) = log z - log (a : ℂ) := by
  let w : ℂ := (b : ℂ) * I
  let z (t : ℝ) : ℂ := (a : ℂ) + (t : ℂ) * w
  let H (x t : ℝ) := w * exp (-z t * (x : ℂ))
  let F (x : ℝ) := (exp (-(a : ℂ) * (x : ℂ)) -
    exp (-((a : ℂ) + (b : ℂ) * I) * (x : ℂ))) / (x : ℂ)
  have hr (t : ℝ) : (z t).re = a := by simp [z, w, mul_re, mul_im]
  have hz (t : ℝ) : z t ≠ 0 := fun h ↦ ha.ne' (by simpa [h] using (hr t).symm)
  have hne (x : ℝ) (hx : 0 < x) : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hx.ne'
  have hX (x : ℝ) (hx : x ∈ Ioi (0 : ℝ)) :
      (∫ t in Ioc (0 : ℝ) 1, H x t) = F x := by
    rw [← intervalIntegral.integral_of_le zero_le_one]
    let G (t : ℝ) := -exp (-z t * (x : ℂ)) / (x : ℂ)
    have hG (t : ℝ) : HasDerivAt G (H x t) t := by
      have h1 : HasDerivAt z w t := by
        simpa only [id_eq, ofReal_one, one_mul, z] using
          ((hasDerivAt_id t).ofReal_comp.mul_const w).const_add (a : ℂ)
      have h2 : HasDerivAt G (-(exp (-z t * (x : ℂ)) * (-w * (x : ℂ))) / (x : ℂ)) t :=
        (h1.neg.mul_const (x : ℂ)).cexp.neg.div_const (x : ℂ)
      convert h2 using 1
      dsimp only [H]
      field_simp [hne x hx]
    have hc : Continuous (H x) := by unfold H z; fun_prop
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ ↦ hG t)
      (hc.intervalIntegrable 0 1)]
    simp only [G, F, show z 0 = (a : ℂ) by simp [z],
      show z 1 = (a : ℂ) + (b : ℂ) * I by simp [z, w]]
    ring
  have hzc : Continuous z := continuous_const.add (continuous_ofReal.mul continuous_const)
  have hT (t : ℝ) : (∫ x in Ioi (0 : ℝ), H x t) = w / z t := by
    have hzneg : (-z t).re < 0 := by simpa [hr] using neg_neg_of_pos ha
    change (∫ x in Ioi (0 : ℝ), w * exp (-z t * (x : ℂ))) = _
    rw [integral_const_mul, integral_exp_mul_complex_Ioi hzneg]
    simp [div_eq_mul_inv]
  have hH : Integrable (Function.uncurry H) ((volume.restrict (Ioi 0)).prod
      (volume.restrict (Ioc 0 1))) := by
    have : IsFiniteMeasure ((volume : Measure ℝ).restrict (Ioc 0 1)) :=
      isFiniteMeasure_restrict.mpr (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
    have hi := (integrableOn_exp_mul_Ioi (neg_neg_of_pos ha) 0).const_mul ‖w‖
    have hcont : Continuous (Function.uncurry H) :=
      continuous_const.mul (((hzc.comp continuous_snd).neg).mul
        (continuous_ofReal.comp continuous_fst)).cexp
    apply (hi.comp_fst (volume.restrict (Ioc 0 1))).mono' hcont.aestronglyMeasurable
    refine Filter.Eventually.of_forall fun p ↦ ?_
    change ‖w * exp (-z p.2 * (p.1 : ℂ))‖ ≤ ‖w‖ * Real.exp (-a * p.1)
    simp [norm_exp, mul_re, hr]
  have hF : (fun x ↦ ∫ t in Ioc (0 : ℝ) 1, H x t) =ᵐ[volume.restrict (Ioi 0)] F := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx using hX x hx
  have hlog (t : ℝ) : HasDerivAt (fun t : ℝ ↦ log (z t)) (w / z t) t := by
    have h := ((hasDerivAt_id (t : ℂ)).mul_const w).const_add (a : ℂ)
    have hs : z t ∈ slitPlane := mem_slitPlane_iff.mpr (Or.inl (by rwa [hr]))
    simpa only [id_eq, one_mul] using (h.clog hs).comp_ofReal
  have hcont : Continuous (fun t : ℝ ↦ w / z t) :=
    continuous_const.div hzc hz
  refine ⟨hH.integral_prod_left.congr hF, ?_⟩
  change (∫ x in Ioi (0 : ℝ), F x) = _
  rw [← integral_congr_ae hF, integral_integral_swap hH]
  simp_rw [hT]
  rw [← intervalIntegral.integral_of_le zero_le_one,
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ ↦ hlog t) (hcont.intervalIntegrable _ _)]
  simp [z, w]

private theorem endpoint_inv_kernel_le {x : ℝ} (hx : 0 < x) :
    ‖(1 - Real.exp (-x))⁻¹ - x⁻¹‖ ≤ 1 := by
  let d := 1 - Real.exp (-x)
  have hd : 0 < d := sub_pos.mpr (Real.exp_lt_one_iff.mpr (neg_neg_of_pos hx))
  have hdx : d ≤ x := by dsimp [d]; linarith [Real.add_one_le_exp (-x)]
  have hlow : x ≤ (1 + x) * d := by
    have h := Real.add_one_le_exp x
    have h' : (1 + x) * Real.exp (-x) ≤ 1 := by
      rw [Real.exp_neg, mul_inv_le_iff₀ (Real.exp_pos _), one_mul]
      simpa only [add_comm] using h
    dsimp [d]
    linarith only [h', mul_sub (1 + x) 1 (Real.exp (-x))]
  change ‖d⁻¹ - x⁻¹‖ ≤ 1
  rw [Real.norm_of_nonneg (sub_nonneg.mpr (inv_anti₀ hd hdx)), sub_le_iff_le_add,
    inv_eq_one_div d, div_le_iff₀ hd]
  apply (mul_le_mul_iff_left₀ hx).mp
  calc
    1 * x ≤ (1 + x) * d := by simpa using hlow
    _ = (1 + x⁻¹) * d * x := by field_simp [hx.ne']; ring

private theorem endpoint_digamma_cmp {a : ℝ} (ha : 0 < a) (b : ℝ) :
    let z := (a : ℂ) + (b : ℂ) * I
    ‖(digamma z - digamma (a : ℂ)) - (log z - log (a : ℂ))‖ ≤ 2 / a := by
  let z := (a : ℂ) + (b : ℂ) * I
  let f (x : ℝ) := (exp (-(a : ℂ) * (x : ℂ)) - exp (-z * (x : ℂ)))
  let K (s : ℂ) (x : ℝ) := (exp (-(x : ℂ)) - exp (-s * (x : ℂ))) / (1 - exp (-(x : ℂ)))
  let F (x : ℝ) := f x / (x : ℂ)
  have hGauss (s : ℂ) (hs : 0 < s.re) : IntegrableOn (K s) (Ioi 0) ∧
      (∫ x in Ioi (0 : ℝ), K s x) = digamma s - digamma 1 := by
    simpa [K] using digamma_sub_one_eq_exponential_integral (d := 1) (w := s)
      zero_lt_one (by simpa using hs)
  obtain ⟨hzK, hzVal⟩ := hGauss z (by simpa [z, mul_re] using ha)
  obtain ⟨haK, haVal⟩ := hGauss (a : ℂ) ha
  obtain ⟨hF, hFVal⟩ := endpoint_log_eq_exponential ha b
  change IntegrableOn F (Ioi 0) at hF
  change (∫ x in Ioi (0 : ℝ), F x) = _ at hFVal
  have hval : (∫ x in Ioi (0 : ℝ), K z x - K (a : ℂ) x - F x) =
      (digamma z - digamma (a : ℂ)) - (log z - log (a : ℂ)) := by
    change (∫ x in Ioi (0 : ℝ), (K z - K (a : ℂ)) x - F x) = _
    rw [integral_sub (hzK.sub haK) hF]
    change (∫ x in Ioi (0 : ℝ), K z x - K (a : ℂ) x) - _ = _
    rw [integral_sub hzK haK, hzVal, haVal, hFVal]
    dsimp only [z]
    ring
  change ‖(digamma z - digamma (a : ℂ)) - (log z - log (a : ℂ))‖ ≤ _
  rw [← hval]
  have hE : IntegrableOn (fun x : ℝ ↦ 2 * Real.exp (-a * x)) (Ioi 0) :=
    (integrableOn_exp_mul_Ioi (neg_neg_of_pos ha) 0).const_mul 2
  calc
    _ ≤ ∫ x in Ioi (0 : ℝ), 2 * Real.exp (-a * x) := by
      apply norm_integral_le_of_norm_le hE
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      have heq : K z x - K (a : ℂ) x - F x =
          f x * (↑((1 - Real.exp (-x))⁻¹ - x⁻¹) : ℂ) := by
        simp only [K, F, f, div_eq_mul_inv, Complex.ofReal_sub, Complex.ofReal_inv,
          Complex.ofReal_one, Complex.ofReal_exp, Complex.ofReal_neg]
        ring
      have hf : ‖f x‖ ≤ 2 * Real.exp (-a * x) := by
        dsimp only [f]
        refine (norm_sub_le _ _).trans ?_
        simp [norm_exp, mul_re, z, two_mul]
      rw [heq, norm_mul, Complex.norm_real]
      exact (mul_le_of_le_one_right (norm_nonneg _) (endpoint_inv_kernel_le hx)).trans hf
    _ = _ := by
      rw [integral_const_mul, integral_exp_mul_Ioi (neg_neg_of_pos ha), mul_zero, Real.exp_zero]
      ring

private theorem endpoint_digamma_line {a : ℝ} (ha : 1 / 4 ≤ a) (ha' : a ≤ 3 / 4) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ξ : ℝ,
      |(digamma ((a : ℂ) + (↑(ξ / 2) : ℂ) * I)).re - Real.log Real.pi -
        Real.log (2 + |ξ|)| ≤ C := by
  have hap : 0 < a := by linarith
  let A := (digamma (a : ℂ)).re - Real.log a - Real.log Real.pi
  refine ⟨2 / a + |A| + Real.log 10, ?_, fun ξ ↦ ?_⟩
  · exact add_nonneg (add_nonneg (div_nonneg zero_le_two hap.le) (abs_nonneg _))
      (Real.log_nonneg (by norm_num))
  let z : ℂ := (a : ℂ) + (↑(ξ / 2) : ℂ) * I
  have hr : z.re = a := by simp [z, mul_re]
  have hi : z.im = ξ / 2 := by simp [z, mul_im]
  have hza : a ≤ ‖z‖ := by
    rw [← hr]
    exact (le_abs_self z.re).trans (abs_re_le_norm z)
  have hzi : |ξ| / 2 ≤ ‖z‖ := by
    simpa only [hi, abs_div, abs_of_nonneg (show (0 : ℝ) ≤ 2 by norm_num)] using abs_im_le_norm z
  have hnorm : ‖z‖ ≤ 2 + |ξ| := by
    refine (norm_add_le _ _).trans ?_
    simp only [norm_mul, norm_I, mul_one, norm_real, Real.norm_eq_abs, abs_of_pos hap,
      abs_div, abs_of_nonneg (show (0 : ℝ) ≤ 2 by norm_num)]
    linarith [abs_nonneg ξ]
  have hnorm' : 2 + |ξ| ≤ 10 * ‖z‖ := by linarith
  have hlower := Real.log_le_log (hap.trans_le hza) hnorm
  have hupper := Real.log_le_log (show 0 < 2 + |ξ| by positivity) hnorm'
  rw [Real.log_mul (show (10 : ℝ) ≠ 0 by norm_num) (hap.trans_le hza).ne'] at hupper
  have hl : |Real.log ‖z‖ - Real.log (2 + |ξ|)| ≤ Real.log 10 := by
    rw [abs_of_nonpos (sub_nonpos.mpr hlower)]
    linarith
  have h0 : ‖(digamma z - digamma (a : ℂ)) - (log z - log (a : ℂ))‖ ≤ 2 / a :=
    endpoint_digamma_cmp hap (ξ / 2)
  have h0' := (abs_re_le_norm ((digamma z - digamma (a : ℂ)) - (log z - log (a : ℂ)))).trans h0
  simp only [sub_re, log_re, norm_real, Real.norm_of_nonneg hap.le] at h0'
  change |(digamma z).re - Real.log Real.pi - Real.log (2 + |ξ|)| ≤ _
  calc
    _ = |(((digamma z).re - (digamma (a : ℂ)).re) - (Real.log ‖z‖ - Real.log a)) +
        A + (Real.log ‖z‖ - Real.log (2 + |ξ|))| := by congr 1; dsimp [A]; ring
    _ ≤ _ := (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans
      (add_le_add h0' le_rfl)) hl)

end Symbol

section Quotient

/-- The conductor-free archimedean symbol for parity `κ`. -/
@[expose] public noncomputable def signedEndpointGammaSymbol (κ : Fin 2) (ξ : ℝ) : ℝ :=
  (Complex.digamma (((1 / 2 : ℂ) + (κ.val : ℂ) + Complex.I * (ξ : ℂ)) / 2)).re - Real.log Real.pi

/-- The angular Gamma energy divided by the squared norm of the signed endpoint test. -/
@[expose] public noncomputable def signedEndpointGammaQuotient (D y : ℝ) (κ : Fin 2) : ℝ :=
  (∫ ξ, signedEndpointGammaSymbol κ ξ * ‖signedEndpointAngularFourier D y ξ‖ ^ 2
    ∂endpointAngularMeasure) / signedEndpointMass D

private theorem continuous_signedEndpointGammaSymbol (κ : Fin 2) :
    Continuous (signedEndpointGammaSymbol κ) := by
  let S : Set ℂ := {z | 0 < z.re}
  have hS : IsOpen S := isOpen_lt continuous_const Complex.continuous_re
  have hΓ : DifferentiableOn ℂ Complex.Gamma S := fun _ hz ↦
    (Complex.hasDerivAt_Gamma_of_re_pos hz).differentiableAt.differentiableWithinAt
  have hψ : ContinuousOn Complex.digamma S := by
    rw [Complex.digamma_def]
    simp only [logDeriv]
    exact (hΓ.analyticOnNhd hS).deriv.continuousOn.div hΓ.continuousOn
      (fun _ hz ↦ Complex.Gamma_ne_zero_of_re_pos hz)
  let z (ξ : ℝ) : ℂ := ((1 / 2 : ℂ) + (κ.val : ℂ) + Complex.I * (ξ : ℂ)) / 2
  have hz (ξ : ℝ) : z ξ ∈ S := by
    change 0 < (z ξ).re
    have heq : z ξ = (↑((1 / 2 + (κ.val : ℝ)) / 2) : ℂ) + (↑(ξ / 2) : ℂ) * Complex.I := by
      dsimp only [z]
      push_cast
      ring
    rw [heq]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
      Complex.ofReal_im, mul_zero, zero_mul, sub_self, add_zero]
    positivity
  have hc : Continuous (fun ξ ↦ Complex.digamma (z ξ)) :=
    hψ.comp_continuous (by unfold z; fun_prop) hz
  exact (Complex.continuous_re.comp hc).sub continuous_const

private theorem endpoint_symbol_uniform :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (κ : Fin 2) (ξ : ℝ),
      |signedEndpointGammaSymbol κ ξ - Real.log (2 + |ξ|)| ≤ A := by
  obtain ⟨A₀, hA₀, h₀⟩ := endpoint_digamma_line (a := 1 / 4) (by norm_num) (by norm_num)
  obtain ⟨A₁, hA₁, h₁⟩ := endpoint_digamma_line (a := 3 / 4) (by norm_num) (by norm_num)
  have harg (ξ : ℝ) (κ : Fin 2) :
      ((1 / 2 : ℂ) + (κ.val : ℂ) + Complex.I * (ξ : ℂ)) / 2 =
        (↑((1 / 2 + (κ.val : ℝ)) / 2) : ℂ) + (↑(ξ / 2) : ℂ) * Complex.I := by
    push_cast
    ring
  refine ⟨A₀ + A₁, add_nonneg hA₀ hA₁, fun κ ξ ↦ ?_⟩
  rw [signedEndpointGammaSymbol, harg]
  fin_cases κ
  · convert (h₀ ξ).trans (le_add_of_nonneg_right hA₁) using 5; norm_num [Fin.val]
  · convert (h₁ ξ).trans (le_add_of_nonneg_left hA₀) using 5; norm_num [Fin.val]

private theorem endpoint_log_shift_le (ξ y : ℝ) :
    |Real.log (2 + |ξ|) - Real.log (2 + |y|)| ≤ Real.log (2 + |ξ - y|) := by
  have hbound (x t : ℝ) : 2 + |x| ≤ (2 + |t|) * (2 + |x - t|) := by
    have h := abs_add_le t (x - t)
    rw [show t + (x - t) = x by ring] at h
    nlinarith only [h, abs_nonneg t, abs_nonneg (x - t), mul_nonneg (abs_nonneg t) (abs_nonneg (x - t))]
  have h₁ := Real.log_le_log (show 0 < 2 + |ξ| by positivity) (hbound ξ y)
  have h₂ := Real.log_le_log (show 0 < 2 + |y| by positivity) (hbound y ξ)
  rw [Real.log_mul (by positivity) (by positivity)] at h₁ h₂
  rw [abs_sub_comm y ξ] at h₂
  exact abs_le.mpr ⟨by linarith, by linarith⟩

private theorem endpoint_log_le_rpow (s : ℝ) :
    Real.log (2 + |s|) ≤ 4 * (1 + |s|) ^ (1 / 2 : ℝ) := by
  have h := Real.log_le_rpow_div (x := 2 + |s|) (ε := 1 / 2) (by positivity) (by norm_num)
  have hc := Real.rpow_le_rpow (show 0 ≤ 2 + |s| by positivity)
    (show 2 + |s| ≤ 4 * (1 + |s|) by linarith [abs_nonneg s]) (show (0 : ℝ) ≤ 1 / 2 by norm_num)
  rw [Real.mul_rpow (by norm_num) (by positivity),
    show (4 : ℝ) ^ (1 / 2 : ℝ) = 2 by rw [← Real.sqrt_eq_rpow]; norm_num] at hc
  linarith

private theorem endpoint_mass_one_le {D : ℝ} (hD : 1 ≤ D) : 1 ≤ signedEndpointMass D := by
  have hdexp : 2 ≤ Real.exp D := by linarith [Real.add_one_le_exp D]
  have hexp : Real.exp (-D) ≤ 1 / 2 := by
    rw [Real.exp_neg, inv_eq_one_div, div_le_iff₀ (Real.exp_pos _)]
    linarith
  unfold signedEndpointMass
  have h : 0 ≤ 2 * D * Real.exp (-D / 2) := by positivity
  linarith

/-- Uniform in diameter `D ≥ 1`, real modulation `y`, and the two parities:
    the Gamma energy exists and its normalized value is `log (2 + |y|) + O(1)`.
    The angular measure is `dξ/(2π)` and the symbol includes `-log π`, not `log q`. -/
public theorem signedEndpointGammaQuotient_uniform :
    ∃ C : ℝ, 0 < C ∧ ∀ (D y : ℝ) (κ : Fin 2), 1 ≤ D →
      Integrable (fun ξ ↦ signedEndpointGammaSymbol κ ξ * ‖signedEndpointAngularFourier D y ξ‖ ^ 2)
        endpointAngularMeasure ∧
      |signedEndpointGammaQuotient D y κ - Real.log (2 + |y|)| ≤ C := by
  obtain ⟨A, hA, hsym⟩ := endpoint_symbol_uniform
  let W (s : ℝ) : ℝ := (144 * (A + 4)) * (1 + |s|) ^ (-3 / 2 : ℝ)
  have hW : Integrable W := (endpoint_weight_integrable (by norm_num)).const_mul _
  have hWμ : Integrable W endpointAngularMeasure := hW.smul_measure ENNReal.ofReal_ne_top
  let B := ∫ s, W s ∂endpointAngularMeasure
  have hB : 0 ≤ B := integral_nonneg (fun s ↦ by dsimp [W]; positivity)
  refine ⟨B + 1, by positivity, fun D y κ hD ↦ ?_⟩
  let L := Real.log (2 + |y|)
  let ρ (ξ : ℝ) := ‖signedEndpointAngularFourier D y ξ‖ ^ 2
  let E (ξ : ℝ) := (signedEndpointGammaSymbol κ ξ - L) * ρ ξ
  have hρ : Integrable ρ endpointAngularMeasure :=
    (endpoint_density_integrable hD y).smul_measure ENNReal.ofReal_ne_top
  have hWshift : Integrable (fun ξ ↦ W (ξ - y)) endpointAngularMeasure := by
    apply Integrable.smul_measure _ ENNReal.ofReal_ne_top
    simpa only [Function.comp_def, sub_eq_add_neg] using
      (measurePreserving_add_right volume (-y)).integrable_comp_of_integrable hW
  have hWval : (∫ ξ, W (ξ - y) ∂endpointAngularMeasure) = B := by
    simp only [endpointAngularMeasure, integral_smul_measure, B]
    congr 1
    simpa only [Function.comp_def, sub_eq_add_neg] using
      (measurePreserving_add_right volume (-y)).integral_comp (Homeomorph.addRight (-y)).measurableEmbedding W
  have hdom (ξ : ℝ) : ‖E ξ‖ ≤ W (ξ - y) := by
    let s := ξ - y
    let r := 1 + |s|
    have hr : 0 < r := by dsimp [r]; positivity
    have hr' : 1 ≤ r := le_add_of_nonneg_right (abs_nonneg s)
    have hsym' : |signedEndpointGammaSymbol κ ξ - L| ≤ A + Real.log (2 + |s|) := by
      rw [show signedEndpointGammaSymbol κ ξ - L =
        (signedEndpointGammaSymbol κ ξ - Real.log (2 + |ξ|)) +
        (Real.log (2 + |ξ|) - L) by ring]
      exact (abs_add_le _ _).trans (add_le_add (hsym κ ξ) (endpoint_log_shift_le ξ y))
    have hS : |signedEndpointGammaSymbol κ ξ - L| ≤ (A + 4) * r ^ (1 / 2 : ℝ) := by
      have hp : 1 ≤ r ^ (1 / 2 : ℝ) := Real.one_le_rpow hr' (by norm_num)
      dsimp only [r]
      linarith only [hsym', endpoint_log_le_rpow s, mul_le_mul_of_nonneg_left hp hA,
        add_mul A 4 (r ^ (1 / 2 : ℝ)), mul_one A]
    have hsq : ρ ξ ≤ (12 / r) ^ 2 := by
      dsimp only [ρ]
      gcongr
      exact norm_signedEndpointAngularFourier_le hD y ξ
    rw [show E ξ = (signedEndpointGammaSymbol κ ξ - L) * ρ ξ from rfl, norm_mul,
      Real.norm_eq_abs, Real.norm_of_nonneg (show 0 ≤ ρ ξ from sq_nonneg _)]
    calc
      _ ≤ ((A + 4) * r ^ (1 / 2 : ℝ)) * (12 / r) ^ 2 :=
        mul_le_mul hS hsq (sq_nonneg _) (by positivity)
      _ = W s := by
        change _ = (144 * (A + 4)) * r ^ (-3 / 2 : ℝ)
        rw [div_pow, div_eq_mul_inv (12 ^ 2 : ℝ) (r ^ 2), ← Real.rpow_two r,
          ← Real.rpow_neg hr.le]
        rw [show -3 / 2 = (1 / 2 : ℝ) + -2 by norm_num, Real.rpow_add hr]
        ring
  have hEc : Continuous E :=
    ((continuous_signedEndpointGammaSymbol κ).sub continuous_const).mul
      ((continuous_endpoint_angular D y).norm.pow 2)
  have hE : Integrable E endpointAngularMeasure := hWshift.mono' hEc.aestronglyMeasurable
    (Filter.Eventually.of_forall hdom)
  have hInt : Integrable (fun ξ ↦ signedEndpointGammaSymbol κ ξ * ρ ξ) endpointAngularMeasure := by
    convert hE.add (hρ.const_mul L) using 1
    funext ξ
    dsimp only [E, Pi.add_apply]
    ring
  have hEVal : (∫ ξ, E ξ ∂endpointAngularMeasure) =
      (∫ ξ, signedEndpointGammaSymbol κ ξ * ρ ξ ∂endpointAngularMeasure) - L * signedEndpointMass D := by
    simp only [E, sub_mul]
    rw [integral_sub hInt (hρ.const_mul L), integral_const_mul, signedEndpointAngularFourier_mass hD y]
  have hErr : ‖∫ ξ, E ξ ∂endpointAngularMeasure‖ ≤ B := by
    rw [← hWval]
    exact norm_integral_le_of_norm_le hWshift (Filter.Eventually.of_forall hdom)
  refine ⟨hInt, ?_⟩
  change |(∫ ξ, signedEndpointGammaSymbol κ ξ * ρ ξ ∂endpointAngularMeasure) / signedEndpointMass D - L| ≤ _
  have hN := endpoint_mass_one_le hD
  have hpN : 0 < signedEndpointMass D := zero_lt_one.trans_le hN
  rw [← mul_div_cancel_right₀ L hpN.ne', ← sub_div, ← hEVal, abs_div, abs_of_pos hpN]
  exact (div_le_self (abs_nonneg _) hN).trans (hErr.trans (by linarith))

end Quotient

end Masullo
