module

public import Mathlib.Analysis.Fourier.Convolution
import Mathlib.Analysis.Fourier.LpSpace

/-! # The continuous shifted Hankel cut from a Fourier cap

Source: `8d0a4652e22f:.godel/bob/fixed-third-price-deletion-33.md:63–69,73–90`.
Scope: the necessary quadratic-form bound for a real half-line test and an integrable
real kernel (the source's `e^(-z/2) A(z)`). The application uses `l = -3/5` and
`C = cosh(39/20) / (6 cos(π/12))`; the numerical certificate and tail exclusion are
not part of this result.

Owner check session: `01a20db3-6987-747d-9d8d-903a502adedd`.
-/

open MeasureTheory
open scoped ContDiff Convolution FourierTransform SchwartzMap

namespace Masullo

-- Fubini for the integrable inputs to the classical Fourier integrals.
private theorem hankel_fourier_mul_swap {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g) :
    (∫ x, 𝓕 f x * g x) = ∫ x, f x * 𝓕 g x := by
  have hflip : (innerₗ ℝ).flip = innerₗ ℝ := by
    apply LinearMap.ext
    intro x
    apply LinearMap.ext
    intro y
    change inner ℝ y x = inner ℝ x y
    rw [Real.inner_apply, Real.inner_apply, mul_comm]
  change (∫ x, VectorFourier.fourierIntegral Real.fourierChar volume (innerₗ ℝ) f x * g x) =
    ∫ x, f x * VectorFourier.fourierIntegral Real.fourierChar volume (innerₗ ℝ) g x
  simpa only [hflip, ContinuousLinearMap.mul_apply'] using
    (VectorFourier.integral_bilin_fourierIntegral_eq_flip (ContinuousLinearMap.mul ℂ ℂ)
      Real.continuous_fourierChar (L := innerₗ ℝ) continuous_inner hf hg)

private theorem hankel_fourierInv_mul_swap {f g : ℝ → ℂ} (hf : Integrable f)
    (hg : Integrable g) : (∫ x, 𝓕⁻ f x * g x) = ∫ x, f x * 𝓕⁻ g x := by
  rw [Real.fourierInv_eq_fourier_comp_neg f, hankel_fourier_mul_swap hf.comp_neg hg]
  simpa only [neg_neg, Real.fourierInv_eq_fourier_neg] using
    (integral_neg_eq_self (fun x : ℝ ↦ f (-x) * 𝓕 g x) volume).symm

private theorem hankel_fourier_continuous {f : ℝ → ℂ} (hf : Integrable f) : Continuous (𝓕 f) :=
  VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
    (L := innerₗ ℝ) continuous_inner hf

private theorem hankel_ae_eq_of_schwartz {f g : ℝ → ℂ} (hf : LocallyIntegrable f)
    (hg : LocallyIntegrable g)
    (h : ∀ φ : 𝓢(ℝ, ℂ), (∫ x, φ x * f x) = ∫ x, φ x * g x) : f =ᵐ[volume] g := by
  refine ae_eq_of_integral_contDiff_smul_eq hf hg ?_
  intro φ hφ hc
  have hc' : HasCompactSupport (Complex.ofRealCLM ∘ φ) := hc.comp_left rfl
  have hφ' : ContDiff ℝ ∞ (Complex.ofRealCLM ∘ φ) := by fun_prop
  simpa [Complex.real_smul] using h (hc'.toSchwartzMap hφ')

-- Identify the classical transform with the Plancherel representative by testing both
-- against Schwartz functions. This does not assume the classical transform is already L².
private theorem hankel_fourier_eq_L2 {f : ℝ → ℂ} (hf : Integrable f) (hf2 : MemLp f 2) :
    𝓕 f =ᵐ[volume] ⇑(𝓕 (hf2.toLp f) : Lp ℂ 2 (volume : Measure ℝ)) := by
  refine hankel_ae_eq_of_schwartz (hankel_fourier_continuous hf).locallyIntegrable
    ((Lp.memLp (𝓕 (hf2.toLp f) : Lp ℂ 2 (volume : Measure ℝ))).locallyIntegrable
      (by norm_num)) ?_
  intro φ
  have h := congrArg (fun T : 𝓢'(ℝ, ℂ) ↦ T φ)
    (Lp.fourier_toTemperedDistribution_eq (hf2.toLp f))
  calc
    (∫ x, φ x * 𝓕 f x) = ∫ x, 𝓕 f x * φ x := by simp_rw [mul_comm (φ _)]
    _ = ∫ x, f x * 𝓕 (φ : ℝ → ℂ) x := hankel_fourier_mul_swap hf φ.integrable
    _ = ∫ x, 𝓕 φ x • (hf2.toLp f) x := by
      apply integral_congr_ae
      filter_upwards [hf2.coeFn_toLp] with x hx
      rw [hx, ← SchwartzMap.fourier_coe, smul_eq_mul, mul_comm]
    _ = ∫ x, φ x * (𝓕 (hf2.toLp f) : Lp ℂ 2 (volume : Measure ℝ)) x := by
      simpa only [TemperedDistribution.fourier_apply, Lp.toTemperedDistribution_apply,
        smul_eq_mul] using h

private theorem hankel_integral_sq_norm_eq_L2 (g : Lp ℂ 2 (volume : Measure ℝ)) :
    (∫ x, ‖g x‖ ^ 2) = ‖g‖ ^ 2 := by
  apply Complex.ofRealLI.injective
  change ((∫ x, ‖g x‖ ^ 2 : ℝ) : ℂ) = ((‖g‖ ^ 2 : ℝ) : ℂ)
  rw [← integral_complex_ofReal]
  calc
    (∫ x, (↑(‖g x‖ ^ 2) : ℂ)) = inner ℂ g g := by
      rw [L2.inner_def]
      simp only [inner_self_eq_norm_sq_to_K, Complex.ofReal_pow]
      rfl
    _ = (↑(‖g‖ ^ 2) : ℂ) := by
      rw [Complex.ofReal_pow]
      exact inner_self_eq_norm_sq_to_K g

private theorem hankel_plancherel {f : ℝ → ℂ} (hf : Integrable f) (hf2 : MemLp f 2) :
    (∫ w, ‖𝓕 f w‖ ^ 2) = ∫ x, ‖f x‖ ^ 2 := by
  let F : Lp ℂ 2 (volume : Measure ℝ) := 𝓕 (hf2.toLp f)
  calc
    (∫ w, ‖𝓕 f w‖ ^ 2) = ∫ w, ‖F w‖ ^ 2 := by
      apply integral_congr_ae
      filter_upwards [hankel_fourier_eq_L2 hf hf2] with w hw
      rw [hw]
    _ = ‖F‖ ^ 2 := hankel_integral_sq_norm_eq_L2 F
    _ = ‖hf2.toLp f‖ ^ 2 := by rw [show ‖F‖ = ‖hf2.toLp f‖ from Lp.norm_fourier_eq _]
    _ = ∫ x, ‖f x‖ ^ 2 := by
      rw [← hankel_integral_sq_norm_eq_L2]
      apply integral_congr_ae
      filter_upwards [hf2.coeFn_toLp] with x hx
      rw [hx]

-- L¹ inversion a.e. is enough for the pairing. Test against Schwartz functions rather than
-- assuming an everywhere Fourier inversion formula for the convolution representative.
private theorem hankel_fourier_inversion_ae {g : ℝ → ℂ} (hg : Integrable g)
    (hG : Integrable (𝓕 g)) : 𝓕⁻ (𝓕 g) =ᵐ[volume] g := by
  have hcont : Continuous (𝓕⁻ (𝓕 g)) := by
    rw [show 𝓕⁻ (𝓕 g) = (fun w ↦ 𝓕 (𝓕 g) (-w)) by
      funext w; exact Real.fourierInv_eq_fourier_neg _ w]
    exact (hankel_fourier_continuous hG).comp continuous_neg
  refine hankel_ae_eq_of_schwartz hcont.locallyIntegrable hg.locallyIntegrable ?_
  intro φ
  calc
    (∫ x, φ x * 𝓕⁻ (𝓕 g) x) = ∫ x, 𝓕⁻ (𝓕 g) x * φ x := by simp_rw [mul_comm (φ _)]
    _ = ∫ x, 𝓕 g x * 𝓕⁻ (φ : ℝ → ℂ) x := hankel_fourierInv_mul_swap hG φ.integrable
    _ = ∫ x, 𝓕 g x * (𝓕⁻ φ) x := by rw [SchwartzMap.fourierInv_coe]
    _ = ∫ x, g x * 𝓕 ((𝓕⁻ φ : 𝓢(ℝ, ℂ)) : ℝ → ℂ) x :=
      hankel_fourier_mul_swap hg (𝓕⁻ φ : 𝓢(ℝ, ℂ)).integrable
    _ = ∫ x, φ x * g x := by
      rw [← SchwartzMap.fourier_coe, FourierTransform.fourier_fourierInv_eq]
      simp_rw [mul_comm (g _)]

private theorem hankel_convolution_pairing_le {B F : ℝ → ℂ} {C : ℝ} (hB : Integrable B)
    (hF : Integrable F) (hF2 : MemLp F 2) (hcap : ∀ w, ‖𝓕⁻ B w‖ ≤ C) :
    ‖∫ x, B x * (F ⋆[ContinuousLinearMap.mul ℂ ℂ] F) x‖ ≤ C * ∫ x, ‖F x‖ ^ 2 := by
  let g := F ⋆[ContinuousLinearMap.mul ℂ ℂ] F
  have hg : Integrable g := hF.integrable_convolution (ContinuousLinearMap.mul ℂ ℂ) hF
  have hconv (w : ℝ) : 𝓕 g w = (𝓕 F w) ^ 2 := by
    simpa only [g, pow_two] using Real.fourier_mul_convolution_eq hF hF w
  have hL2 : MemLp (𝓕 F) 2 := (memLp_congr_ae (hankel_fourier_eq_L2 hF hF2)).mpr (Lp.memLp _)
  have hsquare : Integrable (fun w ↦ ‖𝓕 F w‖ ^ 2) := by
    simp only [pow_two]
    exact hL2.norm.integrable_mul hL2.norm
  have hG : Integrable (𝓕 g) :=
    hsquare.mono' (hankel_fourier_continuous hg).aestronglyMeasurable
      (ae_of_all _ fun w ↦ by rw [hconv, norm_pow])
  have hcap_prod (w : ℝ) : ‖𝓕⁻ B w * 𝓕 g w‖ ≤ C * ‖𝓕 F w‖ ^ 2 := by
    rw [norm_mul, hconv, norm_pow]
    exact mul_le_mul_of_nonneg_right (hcap w) (sq_nonneg _)
  have hprod : Integrable (fun w ↦ 𝓕⁻ B w * 𝓕 g w) := by
    apply (hsquare.const_mul C).mono' _ (ae_of_all _ hcap_prod)
    have hcont : Continuous (𝓕⁻ B) := by
      rw [Real.fourierInv_eq_fourier_comp_neg]
      exact hankel_fourier_continuous hB.comp_neg
    exact hcont.aestronglyMeasurable.mul hG.aestronglyMeasurable
  calc
    ‖∫ x, B x * g x‖ = ‖∫ x, B x * 𝓕⁻ (𝓕 g) x‖ := by
      congr 1
      apply integral_congr_ae
      filter_upwards [hankel_fourier_inversion_ae hg hG] with x hx
      rw [hx]
    _ = ‖∫ w, 𝓕⁻ B w * 𝓕 g w‖ := congrArg norm (hankel_fourierInv_mul_swap hB hG).symm
    _ ≤ ∫ w, ‖𝓕⁻ B w * 𝓕 g w‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ w, C * ‖𝓕 F w‖ ^ 2 := integral_mono_ae hprod.norm (hsquare.const_mul C)
      (ae_of_all _ hcap_prod)
    _ = C * ∫ x, ‖F x‖ ^ 2 := by rw [integral_const_mul, hankel_plancherel hF hF2]

-- Cauchy–Schwarz for the two L² factors; mathlib transports the second by the
-- measure-preserving reflection/translation `t ↦ z - t`.
private theorem hankel_real_convolution_bound {f : ℝ → ℝ} (hf : MemLp f 2) (z : ℝ) :
    ‖(f ⋆[ContinuousLinearMap.mul ℝ ℝ] f) z‖ ≤
      ‖ContinuousLinearMap.mul ℝ ℝ‖ * (eLpNorm f 2 volume).toReal *
        (eLpNorm f 2 volume).toReal := by
  have h := eNorm_convolution_le (L := ContinuousLinearMap.mul ℝ ℝ) (p := 2) (q := 2)
    hf.aestronglyMeasurable hf.aestronglyMeasurable z
  have hfin : ‖ContinuousLinearMap.mul ℝ ℝ‖ₑ * eLpNorm f 2 volume *
      eLpNorm f 2 volume ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.mul_ne_top (by simp) hf.eLpNorm_ne_top) hf.eLpNorm_ne_top
  simpa only [ENNReal.toReal_mul, toReal_eNorm] using ENNReal.toReal_mono hfin h

private theorem hankel_convolution_zero_of_neg {f : ℝ → ℝ} (hf : ∀ x < 0, f x = 0)
    {z : ℝ} (hz : z < 0) : (f ⋆[ContinuousLinearMap.mul ℝ ℝ] f) z = 0 := by
  rw [convolution_def, ← integral_zero ℝ ℝ]
  apply integral_congr_ae
  filter_upwards with t
  rw [ContinuousLinearMap.mul_apply']
  by_cases ht : t < 0
  · rw [hf t ht, zero_mul]
  · rw [hf (z - t) (sub_neg.mpr (hz.trans_le (le_of_not_gt ht))), mul_zero]

-- With the positive-frequency transform and `B(l + z)`, the phase has negative sign.
private theorem hankel_norm_fourierInv_translate (B : ℝ → ℂ) (l w : ℝ) :
    ‖𝓕⁻ (fun z ↦ B (l + z)) w‖ = ‖𝓕⁻ B w‖ := by
  have h := congrFun (VectorFourier.fourierIntegral_comp_add_right Real.fourierChar
    (volume : Measure ℝ) (-innerₗ ℝ) B l) w
  change 𝓕⁻ (fun z ↦ B (z + l)) w = Real.fourierChar (((-innerₗ ℝ) l) w) • 𝓕⁻ B w at h
  rw [show (fun z ↦ B (l + z)) = (fun z ↦ B (z + l)) by simp_rw [add_comm l],
    h, Circle.norm_smul]

-- Mathlib uses cycles per unit length; the input cap uses radians per unit length.
-- Only the cap is resampled at `2πw`; the Plancherel integral stays in Mathlib's convention.
private theorem hankel_angular_cap {b : ℝ → ℝ} {C : ℝ}
    (hcap : ∀ ξ : ℝ, ‖∫ z : ℝ, (b z : ℂ) *
      Complex.exp ((ξ : ℂ) * (z : ℂ) * Complex.I)‖ ≤ C) (w : ℝ) :
    ‖𝓕⁻ (fun z ↦ (b z : ℂ)) w‖ ≤ C := by
  have hphase (z : ℝ) : ((↑(2 * Real.pi * inner ℝ z w) : ℂ) * Complex.I) =
      (↑(2 * Real.pi * w) : ℂ) * (z : ℂ) * Complex.I := by
    rw [Real.inner_apply, ← mul_assoc, mul_right_comm (2 * Real.pi) z w, Complex.ofReal_mul]
  rw [Real.fourierInv_eq']
  simp_rw [hphase, smul_eq_mul, mul_comm (Complex.exp _)]
  exact hcap (2 * Real.pi * w)

/-- A uniform angular Fourier cap bounds every shifted Hankel test from a real `L¹ ∩ L²`
function extended by zero off `[0, ∞)`. The set integrand is integrable. -/
public theorem shiftedHankelCap {b f : ℝ → ℝ} {C l : ℝ} (hb : Integrable b)
    (hcap : ∀ ξ : ℝ, ‖∫ z : ℝ, (b z : ℂ) *
      Complex.exp ((ξ : ℂ) * (z : ℂ) * Complex.I)‖ ≤ C)
    (hf : Integrable f) (hf2 : MemLp f 2) (hzero : ∀ x < 0, f x = 0) (_hl : l ≤ 0) :
    IntegrableOn (fun z ↦ b (l + z) * (f ⋆[ContinuousLinearMap.mul ℝ ℝ] f) z) (Set.Ici 0) ∧
      |∫ z in Set.Ici (0 : ℝ), b (l + z) * (f ⋆[ContinuousLinearMap.mul ℝ ℝ] f) z| ≤
        C * ∫ z, |f z| ^ 2 := by
  let bs (z : ℝ) := b (l + z)
  let g := f ⋆[ContinuousLinearMap.mul ℝ ℝ] f
  have hbs : Integrable bs := (measurePreserving_add_left volume l).integrable_comp_of_integrable hb
  have hg : Integrable g := hf.integrable_convolution (ContinuousLinearMap.mul ℝ ℝ) hf
  have hconv : ConvolutionExists f f (ContinuousLinearMap.mul ℝ ℝ) :=
    ConvolutionExists.of_memLp_memLp (L := ContinuousLinearMap.mul ℝ ℝ) hf2 hf2
  let M := ‖ContinuousLinearMap.mul ℝ ℝ‖ * (eLpNorm f 2 volume).toReal *
    (eLpNorm f 2 volume).toReal
  have hpair : Integrable (fun z ↦ bs z * g z) := by
    apply (hbs.norm.mul_const M).mono' (hbs.aestronglyMeasurable.mul hg.aestronglyMeasurable)
    filter_upwards with z
    change ‖bs z * g z‖ ≤ ‖bs z‖ * M
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hankel_real_convolution_bound hf2 z) (norm_nonneg _)
  refine ⟨hpair.integrableOn, ?_⟩
  change |∫ z in Set.Ici (0 : ℝ), bs z * g z| ≤ C * ∫ z, |f z| ^ 2
  have hind : (Set.Ici (0 : ℝ)).indicator (fun z ↦ bs z * g z) = fun z ↦ bs z * g z := by
    funext z
    by_cases hz : z ∈ Set.Ici (0 : ℝ)
    · exact Set.indicator_of_mem hz _
    · rw [Set.indicator_of_notMem hz, show g z = 0 from
        hankel_convolution_zero_of_neg hzero (lt_of_not_ge hz), mul_zero]
  rw [← integral_indicator measurableSet_Ici, hind]
  let B (z : ℝ) : ℂ := bs z
  let F (z : ℝ) : ℂ := f z
  have hcap' (w : ℝ) : ‖𝓕⁻ B w‖ ≤ C := by
    change ‖𝓕⁻ (fun z ↦ (b (l + z) : ℂ)) w‖ ≤ C
    rw [hankel_norm_fourierInv_translate (fun z ↦ (b z : ℂ)) l w]
    exact hankel_angular_cap hcap w
  have hcoe (z : ℝ) : (g z : ℂ) = (F ⋆[ContinuousLinearMap.mul ℂ ℂ] F) z := by
    simp only [g, convolution_def, ContinuousLinearMap.mul_apply', F, ← Complex.ofReal_mul]
    exact (Complex.ofRealCLM.integral_comp_comm (hconv z)).symm
  have hp := hankel_convolution_pairing_le (B := B) (F := F) hbs.ofReal hf.ofReal hf2.ofReal hcap'
  simp only [← hcoe, B, ← Complex.ofReal_mul, integral_complex_ofReal, Complex.norm_real,
    Real.norm_eq_abs, F] at hp
  exact hp

end Masullo
