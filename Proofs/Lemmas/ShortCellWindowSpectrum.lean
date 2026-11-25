module

public import Lemmas.ShortCellReplacement
public import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.Fourier.LpSpace
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Ring

/-!
# The spectral probability measure of a unit window input

Source: `bbca37033019:.godel/bob/short-cell-weil-list.md:39–55`, unchanged at scan
pin `df36e0b4e122`. Owning check session: `01a21064-e15a-7bed-9349-0a50688b4367`.

The measure identifies the correlation used by `ShortCellReplacement.lean:30–36,395–411`
with the shift correlation in `ShortCellCrossing.lean:365–378`. We use the zero-extended
window input and do not address the untruncated block. Mathlib's Fourier integral uses
cycles frequency; pushing forward by `ν ↦ 2πν` gives the positive angular phase
for the translation `x ↦ x + t`.
-/

open MeasureTheory Set
open scoped ComplexInnerProductSpace ContDiff ENNReal FourierTransform SchwartzMap

namespace ShortCellWindowSpectrum

/-- The angular pushforward of the squared norm of the cycles Fourier integral. -/
@[expose] public noncomputable def angularSpectralMeasure (f : ℝ → ℂ) : Measure ℝ :=
  Measure.map (fun ν : ℝ ↦ 2 * Real.pi * ν)
    (volume.withDensity (fun ν : ℝ ↦ ENNReal.ofReal (‖𝓕 f ν‖ ^ 2)))

private theorem continuous_fourier_of_integrable {f : ℝ → ℂ} (hf : Integrable f) :
    Continuous (𝓕 f) := by
  rw [← Real.fourierTransform_toLp (memLp_one_iff_integrable.mpr hf)]
  exact (Real.Lp.fourierTransform _).continuous

/-- The two Fourier transforms agree by testing against real smooth compactly
supported functions, viewed as complex Schwartz functions. -/
private theorem lp_fourier_ae_eq_integral {f : ℝ → ℂ} (hf₁ : Integrable f)
    (hf₂ : MemLp f 2 volume) :
    ((𝓕 (hf₂.toLp f) : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) =ᵐ[volume] 𝓕 f := by
  let F : Lp ℂ 2 (volume : Measure ℝ) := hf₂.toLp f
  let G : Lp ℂ 2 (volume : Measure ℝ) := 𝓕 F
  change (G : ℝ → ℂ) =ᵐ[volume] 𝓕 f
  apply ae_eq_of_integral_contDiff_smul_eq
  · exact (Lp.memLp G).locallyIntegrable (by norm_num)
  · exact (continuous_fourier_of_integrable hf₁).locallyIntegrable
  intro g hg hgc
  have hgc' : HasCompactSupport (Complex.ofRealCLM ∘ g) := hgc.comp_left rfl
  have hg' : ContDiff ℝ ∞ (Complex.ofRealCLM ∘ g) := by fun_prop
  let ψ := hgc'.toSchwartzMap hg'
  have hflip : (innerₗ ℝ).flip = innerₗ ℝ := by
    apply LinearMap.ext
    intro x
    apply LinearMap.ext
    intro y
    exact real_inner_comm x y
  have hswap := VectorFourier.integral_fourierIntegral_smul_eq_flip (L := innerₗ ℝ)
    (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
    Real.continuous_fourierChar continuous_inner ψ.integrable hf₁
  rw [hflip] at hswap
  change (∫ x, (𝓕 (ψ : ℝ → ℂ)) x • f x) = ∫ x, ψ x • (𝓕 f) x at hswap
  change (∫ x, (g x : ℂ) * G x) = ∫ x, (g x : ℂ) * 𝓕 f x
  change (∫ x, ψ x • G x) = ∫ x, ψ x • (𝓕 f) x
  calc
    _ = (𝓕 (F : 𝓢'(ℝ, ℂ))) ψ := by
      rw [Lp.fourier_toTemperedDistribution_eq]
      exact (Lp.toTemperedDistribution_apply G ψ).symm
    _ = ∫ x, (𝓕 (ψ : ℝ → ℂ)) x • f x := by
      rw [TemperedDistribution.fourier_apply, Lp.toTemperedDistribution_apply]
      apply integral_congr_ae
      filter_upwards [hf₂.coeFn_toLp] with x hx
      rw [SchwartzMap.fourier_coe, hx]
    _ = _ := hswap

private theorem integral_fourier_pair {f g : ℝ → ℂ} (hf₁ : Integrable f) (hg₁ : Integrable g)
    (hf₂ : MemLp f 2 volume) (hg₂ : MemLp g 2 volume) :
    (∫ x, star (𝓕 f x) * 𝓕 g x) = ∫ x, star (f x) * g x := by
  let F : Lp ℂ 2 (volume : Measure ℝ) := hf₂.toLp f
  let G : Lp ℂ 2 (volume : Measure ℝ) := hg₂.toLp g
  let F' : Lp ℂ 2 (volume : Measure ℝ) := 𝓕 F
  let G' : Lp ℂ 2 (volume : Measure ℝ) := 𝓕 G
  calc
    _ = ⟪F', G'⟫ := by
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [lp_fourier_ae_eq_integral hf₁ hf₂, lp_fourier_ae_eq_integral hg₁ hg₂]
        with x hx hy
      change F' x = 𝓕 f x at hx
      change G' x = 𝓕 g x at hy
      simp only [RCLike.inner_apply', hx, hy]
      rfl
    _ = ⟪F, G⟫ := Lp.inner_fourier_eq F G
    _ = _ := by
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [hf₂.coeFn_toLp, hg₂.coeFn_toLp] with x hx hy
      change F x = f x at hx
      change G x = g x at hy
      simp only [RCLike.inner_apply', hx, hy]
      rfl

private noncomputable def toAngular (ν : ℝ) : ℝ := 2 * Real.pi * ν

private theorem fourier_translate (f : ℝ → ℂ) (t ν : ℝ) :
    𝓕 (fun x ↦ f (x + t)) ν = ShortCellReplacement.phase t (toAngular ν) * 𝓕 f ν := by
  have h := congrFun (VectorFourier.fourierIntegral_comp_add_right Real.fourierChar
    volume (innerₗ ℝ) f t) ν
  change 𝓕 (fun x ↦ f (x + t)) ν = Real.fourierChar ((innerₗ ℝ) t ν) • 𝓕 f ν at h
  have htν : (innerₗ ℝ) t ν = t * ν := Real.inner_apply t ν
  rw [h, htν, Circle.smul_def, Real.fourierChar_apply, smul_eq_mul, ShortCellReplacement.phase]
  rw [show 2 * Real.pi * (t * ν) = t * toAngular ν by unfold toAngular; ring]

private theorem star_mul_self_eq_norm_sq (z : ℂ) : star z * z = (↑(‖z‖ ^ 2) : ℂ) := by
  simpa only [Complex.ofReal_pow, starRingEnd_apply] using Complex.conj_mul' z

/-- For a unit-energy input zero outside `[0,D]`, the concrete angular Fourier
measure is a probability measure and represents the shift correlation at every shift. -/
public theorem angularSpectralMeasure_spec {D : ℝ} {f : ℝ → ℂ} (_hD : 0 < D)
    (hzero : ∀ x ∉ Icc 0 D, f x = 0) (hf : MemLp f 2 (volume.restrict (Icc 0 D)))
    (hunit : (∫ x, ‖f x‖ ^ 2) = 1) :
    IsProbabilityMeasure (angularSpectralMeasure f) ∧
      ∀ t : ℝ, ShortCellReplacement.spectralTransform (angularSpectralMeasure f) t =
        ∫ x, star (f x) * f (x + t) := by
  have hind : (Icc 0 D).indicator f = f := by
    funext x
    by_cases hx : x ∈ Icc 0 D
    · exact indicator_of_mem hx f
    · rw [indicator_of_notMem hx, hzero x hx]
  have hf₂ : MemLp f 2 volume := by
    simpa only [hind] using (memLp_indicator_iff_restrict measurableSet_Icc.nullMeasurableSet).2 hf
  have hf₁ : Integrable f := by
    let : IsFiniteMeasure ((volume : Measure ℝ).restrict (Icc 0 D)) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact isCompact_Icc.measure_lt_top⟩
    have hfr : IntegrableOn f (Icc 0 D) := hf.integrable (by norm_num)
    simpa only [hind] using (integrable_indicator_iff measurableSet_Icc).2 hfr
  have hF₂ : MemLp (𝓕 f) 2 volume :=
    (Lp.memLp (𝓕 (hf₂.toLp f) : Lp ℂ 2 (volume : Measure ℝ))).ae_eq
      (lp_fourier_ae_eq_integral hf₁ hf₂)
  have hsq : Integrable (fun ν ↦ ‖𝓕 f ν‖ ^ 2) :=
    hF₂.integrable_norm_pow (by decide : (2 : ℕ) ≠ 0)
  have henergy : (∫ ν, ‖𝓕 f ν‖ ^ 2) = 1 := by
    have heq := integral_fourier_pair hf₁ hf₁ hf₂ hf₂
    simp only [star_mul_self_eq_norm_sq, integral_complex_ofReal] at heq
    exact (Complex.ofReal_injective heq).trans hunit
  let ρ : ℝ → ℝ≥0∞ := fun ν ↦ ENNReal.ofReal (‖𝓕 f ν‖ ^ 2)
  have hρ : Measurable ρ :=
    ENNReal.measurable_ofReal.comp ((continuous_fourier_of_integrable hf₁).norm.pow 2).measurable
  have hmap : Measurable toAngular :=
    (continuous_const.mul (continuous_id : Continuous (id : ℝ → ℝ))).measurable
  refine ⟨⟨?_⟩, fun t ↦ ?_⟩
  · change (Measure.map toAngular (volume.withDensity ρ)) univ = 1
    rw [Measure.map_apply hmap MeasurableSet.univ, preimage_univ,
      withDensity_apply ρ MeasurableSet.univ, Measure.restrict_univ]
    change (∫⁻ ν, ENNReal.ofReal (‖𝓕 f ν‖ ^ 2)) = 1
    rw [← ofReal_integral_eq_lintegral_ofReal hsq (ae_of_all _ (fun _ ↦ sq_nonneg _)),
      henergy, ENNReal.ofReal_one]
  · have hp : Continuous (ShortCellReplacement.phase t) := by
      unfold ShortCellReplacement.phase
      fun_prop
    have hshift := measurePreserving_add_right (volume : Measure ℝ) t
    have hg₁ : Integrable (fun x ↦ f (x + t)) := (hshift.integrable_comp hf₁.aestronglyMeasurable).2 hf₁
    have hg₂ : MemLp (fun x ↦ f (x + t)) 2 volume := hf₂.comp_measurePreserving hshift
    change (∫ ξ, ShortCellReplacement.phase t ξ ∂Measure.map toAngular (volume.withDensity ρ)) = _
    rw [integral_map hmap.aemeasurable hp.aestronglyMeasurable,
      integral_withDensity_eq_integral_toReal_smul hρ (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top),
      ← integral_fourier_pair hf₁ hg₁ hf₂ hg₂]
    apply integral_congr_ae
    refine ae_of_all _ fun ν ↦ ?_
    change (ENNReal.ofReal (‖𝓕 f ν‖ ^ 2)).toReal • ShortCellReplacement.phase t (toAngular ν) =
      star (𝓕 f ν) * 𝓕 (fun x ↦ f (x + t)) ν
    rw [ENNReal.toReal_ofReal (sq_nonneg _), Complex.real_smul, fourier_translate,
      ← star_mul_self_eq_norm_sq]
    ring

end ShortCellWindowSpectrum
