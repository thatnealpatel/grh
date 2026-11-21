module

public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic

/-! # Absolutely integrable kernels for the real logarithmic Fourier pairing -/

open Filter MeasureTheory Set
open scoped FourierTransform Topology SchwartzMap

namespace Masullo.RealLogFourier

/-- The scale-`a` Cauchy kernel without the factor `1 / π`. -/
@[expose] public noncomputable def cauchy (a x : ℝ) : ℝ := a / (a ^ 2 + x ^ 2)

private theorem cauchy_sub_integrals {x : ℝ} (hx : x ≠ 0) :
    IntegrableOn (fun a ↦ cauchy a x - cauchy a 1) (Ioi 0) ∧
      (∫ a in Ioi 0, cauchy a x - cauchy a 1) = -Real.log |x| ∧
      (∫ a in Ioi 0, |cauchy a x - cauchy a 1|) = abs (Real.log |x|) := by
  let G (a : ℝ) := Real.log ((a ^ 2 + x ^ 2) / (a ^ 2 + 1)) / 2
  have hderiv (a : ℝ) : HasDerivAt G (cauchy a x - cauchy a 1) a := by
    have ha : 0 < a ^ 2 + (1 : ℝ) := by positivity
    have hb : 0 < a ^ 2 + x ^ 2 := by positivity
    have hd (y : ℝ) : HasDerivAt (fun b : ℝ ↦ b ^ 2 + y) (2 * a) a := by
      simpa using ((hasDerivAt_id a).pow 2).add_const y
    convert (((hd _).div (hd _) ha.ne').log (div_ne_zero hb.ne' ha.ne')).div_const 2 using 1
    simp only [cauchy, one_pow, Pi.div_apply]
    field_simp
  have hlim : Tendsto G atTop (𝓝 0) := by
    have htop : Tendsto (fun a : ℝ ↦ a ^ 2 + 1) atTop atTop :=
      tendsto_atTop_add_const_right _ 1 (tendsto_pow_atTop (by decide : 2 ≠ 0))
    have hratio : Tendsto (fun a : ℝ ↦ 1 + (x ^ 2 - 1) * (a ^ 2 + 1)⁻¹) atTop (𝓝 1) := by
      simpa using (htop.inv_tendsto_atTop.const_mul (x ^ 2 - 1)).const_add 1
    have hratio' : Tendsto (fun a : ℝ ↦ (a ^ 2 + x ^ 2) / (a ^ 2 + 1)) atTop (𝓝 1) := by
      convert hratio using 1
      ext a
      have : 0 < a ^ 2 + (1 : ℝ) := by positivity
      field_simp
      ring
    simpa using (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp hratio'
      |>.div_const 2
  have hG : G 0 = Real.log |x| := by
    simp [G, Real.log_pow, Real.log_abs]
  rcases le_total (x ^ 2) (1 : ℝ) with h | h
  · have hp (a : ℝ) (ha : a ∈ Ioi (0 : ℝ)) : 0 ≤ cauchy a x - cauchy a 1 := by
      simp only [cauchy, one_pow, sub_nonneg]
      exact div_le_div_of_nonneg_left ha.out.le (by positivity) (by linarith)
    have hi := integral_Ioi_of_hasDerivAt_of_nonneg' (fun a _ ↦ hderiv a) hp hlim
    rw [hG, zero_sub] at hi
    refine ⟨integrableOn_Ioi_deriv_of_nonneg' (fun a _ ↦ hderiv a) hp hlim, hi, ?_⟩
    rw [setIntegral_congr_fun measurableSet_Ioi (fun a ha ↦ abs_of_nonneg (hp a ha)), hi]
    have : |x| ≤ 1 := by nlinarith [sq_abs x, abs_nonneg x]
    exact (abs_of_nonpos (Real.log_nonpos (abs_nonneg x) this)).symm
  · have hp (a : ℝ) (ha : a ∈ Ioi (0 : ℝ)) : cauchy a x - cauchy a 1 ≤ 0 := by
      simp only [cauchy, one_pow, sub_nonpos]
      exact div_le_div_of_nonneg_left ha.out.le (by positivity) (by linarith)
    have hi := integral_Ioi_of_hasDerivAt_of_nonpos' (fun a _ ↦ hderiv a) hp hlim
    rw [hG, zero_sub] at hi
    refine ⟨integrableOn_Ioi_deriv_of_nonpos' (fun a _ ↦ hderiv a) hp hlim, hi, ?_⟩
    rw [setIntegral_congr_fun measurableSet_Ioi (fun a ha ↦ abs_of_nonpos (hp a ha)), integral_neg,
      hi, neg_neg]
    have : 1 ≤ |x| := by nlinarith [sq_abs x, abs_nonneg x]
    exact (abs_of_nonneg (Real.log_nonneg this)).symm

private theorem integrable_log_mul_schwartz (v : 𝓢(ℝ, ℂ)) :
    Integrable (fun x ↦ (Real.log |x| : ℂ) * v x) := by
  have hm : Measurable (fun x ↦ (Real.log |x| : ℂ) * v x) := by fun_prop
  let S := Ioc (-1 : ℝ) 1
  have hlocal : IntegrableOn (fun x : ℝ ↦ Real.log x) S :=
    intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num) |>.mp
      intervalIntegral.intervalIntegrable_log'
  obtain ⟨B, _, hB⟩ := v.decay 0 0
  have hv (x : ℝ) : ‖v x‖ ≤ B := by simpa using hB x
  have h₁ : IntegrableOn (fun x ↦ (Real.log |x| : ℂ) * v x) S := by
    apply (hlocal.norm.mul_const B).mono' hm.aestronglyMeasurable
    filter_upwards with x
    simp only [norm_mul, Complex.norm_real, Real.log_abs, Real.norm_eq_abs]
    gcongr
    exact hv x
  have htail : Integrable (fun x : ℝ ↦ ‖x‖ * ‖v x‖) := by
    simpa using v.integrable_pow_mul volume 1
  have h₂ : IntegrableOn (fun x ↦ (Real.log |x| : ℂ) * v x) Sᶜ := by
    apply (htail.integrableOn (s := Sᶜ)).mono' hm.aestronglyMeasurable
    filter_upwards [ae_restrict_mem (measurableSet_Ioc.compl : MeasurableSet Sᶜ)] with x hx
    have hx' : 1 ≤ |x| := by
      by_contra! h
      exact hx ⟨(abs_lt.mp h).1, (abs_lt.mp h).2.le⟩
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.log_nonneg hx')]
    gcongr
    exact Real.log_le_self (abs_nonneg x)
  simpa using (integrableOn_union.mpr ⟨h₁, h₂⟩)

/-- The logarithm is absolutely integrable against a Schwartz function. -/
public theorem log_fourier_integrable (v : 𝓢(ℝ, ℂ)) :
    Integrable (fun x ↦ (Real.log |x| : ℂ) * 𝓕 (v : ℝ → ℂ) x) := by
  simpa only [SchwartzMap.fourier_coe] using integrable_log_mul_schwartz (𝓕 v)

/-- Use a subtracted Cauchy kernel to represent the negative logarithm.
The exchange of integrations is absolute, even before imposing a zero moment. -/
public theorem log_pairing_eq_cauchy {v : ℝ → ℂ} (hv : Continuous v)
    (hlog : Integrable (fun x ↦ (Real.log |x| : ℂ) * v x)) :
    -(∫ x, (Real.log |x| : ℂ) * v x) =
      ∫ a in Ioi (0 : ℝ), ∫ x, ((cauchy a x - cauchy a 1 : ℝ) : ℂ) * v x := by
  let F (x a : ℝ) := ((cauchy a x - cauchy a 1 : ℝ) : ℂ) * v x
  have hF : Measurable (Function.uncurry F) := by unfold F cauchy Function.uncurry; fun_prop
  have hi : Integrable (Function.uncurry F) (volume.prod (volume.restrict (Ioi 0))) := by
    refine (integrable_prod_iff hF.aestronglyMeasurable).2 ⟨?_, ?_⟩
    · filter_upwards [Measure.ae_ne volume (0 : ℝ)] with x hx
      exact ((cauchy_sub_integrals hx).1.ofReal).mul_const (v x)
    · apply hlog.norm.congr
      filter_upwards [Measure.ae_ne volume (0 : ℝ)] with x hx
      simp only [Function.uncurry_apply_pair, F, norm_mul, Complex.norm_real, Real.norm_eq_abs, integral_mul_const,
        (cauchy_sub_integrals hx).2.2]
  rw [← integral_integral_swap hi, ← integral_neg]
  apply integral_congr_ae
  filter_upwards [Measure.ae_ne volume (0 : ℝ)] with x hx
  have hcast : (∫ a in Ioi (0 : ℝ), ((cauchy a x - cauchy a 1 : ℝ) : ℂ)) =
      ((∫ a in Ioi (0 : ℝ), cauchy a x - cauchy a 1 : ℝ) : ℂ) := integral_ofReal
  simp only [F, integral_mul_const, hcast, (cauchy_sub_integrals hx).2.1,
    Complex.ofReal_neg, neg_mul]

/-- Spatial profile at a positive scale for the standard `2π` convention. -/
@[expose] public noncomputable def laplaceProfile (a z : ℝ) : ℂ :=
  (Real.exp (-(2 * Real.pi * a) * |z|) : ℂ)

/-- At a positive scale the two-sided exponential is integrable. -/
public theorem laplaceProfile_integrable {a : ℝ} (ha : 0 < a) :
    Integrable (laplaceProfile a) := by
  have h : 0 < 2 * Real.pi * a := by positivity
  have hp : IntegrableOn (laplaceProfile a) (Ioi 0) := by
    apply (integrableOn_exp_mul_Ioi (neg_neg_of_pos h) 0).ofReal.congr
    exact (ae_restrict_iff' measurableSet_Ioi).2 (.of_forall fun z hz ↦ by
      simp [laplaceProfile, abs_of_pos hz.out])
  have hn : IntegrableOn (laplaceProfile a) (Iic 0) := by
    apply (integrableOn_exp_mul_Iic h 0).ofReal.congr
    exact (ae_restrict_iff' measurableSet_Iic).2 (.of_forall fun z hz ↦ by
      simp [laplaceProfile, abs_of_nonpos hz.out, mul_neg, neg_mul])
  simpa using (integrableOn_union.mpr ⟨hp, hn⟩)

/-- The standard additive transform sends the two-sided exponential to the Cauchy kernel. -/
public theorem fourier_laplaceProfile {a : ℝ} (ha : 0 < a) (x : ℝ) :
    𝓕 (laplaceProfile a) x = (cauchy a x : ℂ) / Real.pi := by
  let b : ℝ := 2 * Real.pi * a
  let c : ℝ := 2 * Real.pi * x
  let p : ℂ := -(b : ℂ) - (c : ℂ) * Complex.I
  let q : ℂ := (b : ℂ) - (c : ℂ) * Complex.I
  have hb : 0 < b := by dsimp [b]; positivity
  have hp : p.re < 0 := by simpa [p, Complex.mul_re] using hb
  have hq : 0 < q.re := by simpa [q, Complex.mul_re] using hb
  let w (z : ℝ) := Complex.exp (↑(-2 * Real.pi * z * x) * Complex.I) • laplaceProfile a z
  have hw : Integrable w := by
    apply (laplaceProfile_integrable ha).norm.mono'
    · unfold w laplaceProfile; fun_prop
    · exact .of_forall fun z ↦ by simp [w, Complex.norm_exp, Complex.mul_re]
  rw [Real.fourier_real_eq_integral_exp_smul]
  change ∫ z, w z = _
  rw [← integral_add_compl (s := Ioi (0 : ℝ)) measurableSet_Ioi hw, compl_Ioi]
  have hphase (z t : ℝ) (ht : -(2 * Real.pi * a) * |z| = t * z) :
      w z = Complex.exp (((t : ℂ) - (c : ℂ) * Complex.I) * z) := by
    simp only [w, laplaceProfile, ht, smul_eq_mul, Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    dsimp [c]
    push_cast
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi (f := w) (g := fun z ↦ Complex.exp (p * z))
      (fun z hz ↦ by
        simpa only [p, Complex.ofReal_neg] using
          hphase z (-b) (by rw [abs_of_pos hz.out])),
    setIntegral_congr_fun measurableSet_Iic (f := w) (g := fun z ↦ Complex.exp (q * z))
      (fun z hz ↦ hphase z b (by rw [abs_of_nonpos hz.out]; dsimp [b]; ring)),
    integral_exp_mul_complex_Ioi hp, integral_exp_mul_complex_Iic hq]
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, cauchy, Complex.ofReal_div,
    Complex.ofReal_add, Complex.ofReal_pow]
  have hp' : p ≠ 0 := fun h ↦ by simp [h] at hp
  have hq' : q ≠ 0 := fun h ↦ by simp [h] at hq
  have hax : ((a : ℂ) ^ 2 + (x : ℂ) ^ 2) ≠ 0 := by
    exact_mod_cast (by positivity : 0 < a ^ 2 + x ^ 2).ne'
  field_simp [Real.pi_ne_zero, hp', hq', hax, Complex.ofReal_ne_zero.mpr Real.pi_ne_zero]
  dsimp [p, q, b, c]
  push_cast
  linear_combination (norm := ring_nf) (- (a : ℂ) * (x : ℂ)^2 * (Real.pi : ℂ)^2 * 4) * Complex.I_sq

/-- Bilinear Fourier exchange turns the Cauchy kernel on the frequency line
into the spatial Laplace profile, with no frequency reflection. -/
public theorem cauchy_pairing_eq_laplace {u : ℝ → ℂ} (hu : Continuous u)
    (hi : Integrable u) (huf : Integrable (𝓕 u)) {a : ℝ} (ha : 0 < a) :
    (∫ x, (cauchy a x : ℂ) * 𝓕 u x) =
      (Real.pi : ℂ) * ∫ z, laplaceProfile a z * u z := by
  have he := VectorFourier.integral_fourierIntegral_smul_eq_flip (L := innerₗ ℝ)
    Real.continuous_fourierChar continuous_inner (laplaceProfile_integrable ha) huf
  have hinv (z : ℝ) : 𝓕 (𝓕 u) z = u (-z) := by
    simpa only [Real.fourierInv_eq_fourier_neg, neg_neg] using
      congrFun (hu.fourierInv_fourier_eq hi huf) (-z)
  have he' : (∫ x, 𝓕 (laplaceProfile a) x * 𝓕 u x) =
      ∫ z, laplaceProfile a z * u (-z) := by
    rw [flip_innerₗ] at he
    change (∫ x, 𝓕 (laplaceProfile a) x • 𝓕 u x) =
      (∫ z, laplaceProfile a z • 𝓕 (𝓕 u) z) at he
    simpa only [smul_eq_mul, hinv] using he
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  rw [← integral_neg_eq_self (fun z ↦ laplaceProfile a z * u z) volume]
  simp only [show ∀ z, laplaceProfile a (-z) = laplaceProfile a z from
    fun z ↦ by simp [laplaceProfile]]
  rw [← he', ← integral_const_mul]
  congr 1
  funext x
  rw [fourier_laplaceProfile ha]
  field_simp

/-- Fourier inversion at zero removes the constant subtraction at each
positive scale. The two summands are not integrated separately in scale. -/
public theorem cauchy_sub_pairing_eq_laplace {u : ℝ → ℂ} (hu : Continuous u)
    (hi : Integrable u) (huf : Integrable (𝓕 u)) (hzero : u 0 = 0)
    {a : ℝ} (ha : 0 < a) :
    (∫ x, ((cauchy a x - cauchy a 1 : ℝ) : ℂ) * 𝓕 u x) =
      (Real.pi : ℂ) * ∫ z, laplaceProfile a z * u z := by
  have hinv := congrFun (hu.fourierInv_fourier_eq hi huf) 0
  rw [Real.fourierInv_eq', hzero] at hinv
  have hmass : (∫ x, 𝓕 u x) = 0 := by simpa using hinv
  have hkc : Integrable (fun x ↦ (cauchy a x : ℂ) * 𝓕 u x) := by
    apply (huf.norm.const_mul a⁻¹).mono'
    · have h : Continuous fun x ↦ (cauchy a x : ℂ) := by
        apply Complex.continuous_ofReal.comp
        exact continuous_const.div (by fun_prop) (fun x ↦ (by positivity : 0 < a ^ 2 + x ^ 2).ne')
      exact h.aestronglyMeasurable.mul huf.aestronglyMeasurable
    · filter_upwards with x
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by unfold cauchy; positivity)]
      gcongr
      unfold cauchy
      rw [div_le_iff₀ (by positivity)]
      calc
        a = a⁻¹ * a ^ 2 := by field_simp
        _ ≤ a⁻¹ * (a ^ 2 + x ^ 2) := by gcongr; exact le_add_of_nonneg_right (sq_nonneg x)
  simp only [Complex.ofReal_sub, sub_mul]
  rw [integral_sub hkc (huf.const_mul _), integral_const_mul, hmass, mul_zero, sub_zero,
    cauchy_pairing_eq_laplace hu hi huf ha]

/-- A linear bound near zero suffices for division by `|z|`; away from
zero absolute integrability of the original test suffices. -/
public theorem integrable_div_abs_of_local_bound {u : ℝ → ℂ} (hu : Continuous u)
    (hi : Integrable u) {ε C : ℝ} (hε : 0 < ε) (hbound : ∀ z, |z| < ε → ‖u z‖ ≤ C * |z|) :
    Integrable (fun z ↦ u z / ((|z| : ℝ) : ℂ)) := by
  let S := Ioo (-ε) ε
  have hm : Measurable (fun z ↦ u z / ((|z| : ℝ) : ℂ)) := hu.measurable.div (by fun_prop)
  have hlocal : IntegrableOn (fun z ↦ u z / ((|z| : ℝ) : ℂ)) S := by
    have hC : IntegrableOn (fun _ : ℝ ↦ max C 0) S :=
      integrableOn_const (by unfold S; exact measure_Ioo_lt_top.ne)
    apply hC.mono' hm.aestronglyMeasurable
    filter_upwards [ae_restrict_mem (measurableSet_Ioo : MeasurableSet S)] with z hz
    simp only [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_abs]
    by_cases hzero : z = 0
    · simp [hzero]
    · exact (div_le_iff₀ (abs_pos.mpr hzero)).2
        ((hbound z (abs_lt.mpr hz)).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (abs_nonneg _)))
  have htail : IntegrableOn (fun z ↦ u z / ((|z| : ℝ) : ℂ)) Sᶜ := by
    apply ((hi.norm.div_const ε).integrableOn (s := Sᶜ)).mono' hm.aestronglyMeasurable
    filter_upwards [ae_restrict_mem (measurableSet_Ioo.compl : MeasurableSet Sᶜ)] with z hz
    simp only [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_abs]
    exact div_le_div_of_nonneg_left (norm_nonneg _) hε (le_of_not_gt (fun h ↦ hz (abs_lt.mp h)))
  simpa using integrableOn_union.mpr ⟨hlocal, htail⟩

/-- Division by `|z|` for a compactly supported test vanishing near zero. -/
public theorem integrable_div_abs {u : ℝ → ℂ} (hu : Continuous u) (hc : HasCompactSupport u)
    {ε : ℝ} (hε : 0 < ε) (hgap : ∀ z, |z| < ε → u z = 0) :
    Integrable (fun z ↦ u z / ((|z| : ℝ) : ℂ)) :=
  integrable_div_abs_of_local_bound hu (hu.integrable_of_hasCompactSupport hc) (C := 0) hε
    (fun z hz ↦ by simp [hgap z hz])

private theorem laplace_scale_integral {z : ℝ} (hz : z ≠ 0) :
    let f (a : ℝ) := Real.exp (-(2 * Real.pi * a) * |z|)
    IntegrableOn f (Ioi 0) ∧ (∫ a in Ioi 0, f a) = (2 * Real.pi * |z|)⁻¹ := by
  have h : -(2 * Real.pi * |z|) < 0 := neg_neg_of_pos (by positivity)
  have he (a : ℝ) : -(2 * Real.pi * a) * |z| = -(2 * Real.pi * |z|) * a := by ring
  simp only [he]
  refine ⟨integrableOn_exp_mul_Ioi h 0, ?_⟩
  rw [integral_exp_mul_Ioi h]
  simp

/-- The positive-scale spatial integral has kernel `1 / (2 |z|)` off zero.
Its Fubini exchange needs only absolute integrability against `1 / |z|`. -/
public theorem laplace_integral_eq_half {u : ℝ → ℂ} (hu : Continuous u)
    (hi : Integrable (fun z ↦ u z / ((|z| : ℝ) : ℂ))) :
    (∫ a in Ioi (0 : ℝ), (Real.pi : ℂ) * ∫ z, laplaceProfile a z * u z) =
      (1 / 2 : ℂ) * ∫ z, u z / ((|z| : ℝ) : ℂ) := by
  let F (z a : ℝ) := (Real.pi : ℂ) * laplaceProfile a z * u z
  have hmeas : Measurable (Function.uncurry F) := by
    unfold F laplaceProfile Function.uncurry
    fun_prop
  have hFi : Integrable (Function.uncurry F) (volume.prod (volume.restrict (Ioi 0))) := by
    refine (integrable_prod_iff hmeas.aestronglyMeasurable).2 ⟨?_, ?_⟩
    · filter_upwards [Measure.ae_ne volume (0 : ℝ)] with z hz
      exact (((laplace_scale_integral hz).1.ofReal).const_mul (Real.pi : ℂ)).mul_const (u z)
    · apply (hi.norm.const_mul (1 / 2 : ℝ)).congr
      filter_upwards [Measure.ae_ne volume (0 : ℝ)] with z hz
      simp only [Function.uncurry_apply_pair, F, laplaceProfile, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos Real.pi_pos, abs_of_pos (Real.exp_pos _), integral_mul_const,
        integral_const_mul, (laplace_scale_integral hz).2, norm_div, abs_abs]
      have : |z| ≠ 0 := abs_ne_zero.mpr hz
      field_simp [Real.pi_ne_zero]
  simp_rw [← integral_const_mul, ← mul_assoc]
  change (∫ a in Ioi (0 : ℝ), ∫ z, F z a) = ∫ z, (1 / 2 : ℂ) * (u z / ((|z| : ℝ) : ℂ))
  rw [← integral_integral_swap hFi]
  apply integral_congr_ae
  filter_upwards [Measure.ae_ne volume (0 : ℝ)] with z hz
  have hcast : (∫ a in Ioi (0 : ℝ), (Real.exp (-(2 * Real.pi * a) * |z|) : ℂ)) =
      ((∫ a in Ioi (0 : ℝ), Real.exp (-(2 * Real.pi * a) * |z|) : ℝ) : ℂ) := integral_ofReal
  simp only [F, laplaceProfile, integral_mul_const, integral_const_mul, hcast,
    (laplace_scale_integral hz).2, Complex.ofReal_inv, Complex.ofReal_mul, Complex.ofReal_ofNat]
  have hz' := Complex.ofReal_ne_zero.mpr (abs_ne_zero.mpr hz)
  field_simp [Complex.ofReal_ne_zero.mpr Real.pi_ne_zero]

end Masullo.RealLogFourier
