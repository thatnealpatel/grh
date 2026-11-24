module

public import Lemmas.SmoothedEndpointTransform
public import Mathlib.Analysis.Convolution
import Mathlib.Analysis.Fourier.Convolution
import Mathlib.Analysis.Fourier.LpSpace
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# The shifted long-cutoff endpoint convolution pairing

Source: `daee96a913971252a4db7f06bcdbc73214431a9e:.godel/bob/endpoint-convolution-lift.md:10–20,36–48`.
Owning check session: `01a20e90-1953-703f-a5c5-0300053aba36`.

For each positive order and real shift, the half-tilted physical convolution power of a
bounded measurable real profile supported in `[a, ∞)` pairs with the half-tilted smoothed
spline in `L²`. The kernel may be signed and need only have integrable half-tilt. The formula
uses `exp(-ixz)` and the density `1 / (2π |1/2 + ix|²)` against Lebesgue measure. The source's
cap on the first transform is needed to realize a circle law, not for this identity. No prime
limit, circle-law construction, or numerical five-shift price is asserted here.
-/

open Complex MeasureTheory
open scoped ContDiff Convolution FourierTransform SchwartzMap

namespace Masullo

noncomputable section

/-- The ordinary real convolution power at positive orders, with first power `Y`. The
unused zeroth order is set to zero (the convolution unit is not a function). -/
@[expose] public def endpointConvolutionPower (Y : ℝ → ℝ) : ℕ → ℝ → ℝ
  | 0 => 0
  | 1 => Y
  | n + 2 => Y ⋆[ContinuousLinearMap.mul ℝ ℝ] endpointConvolutionPower Y (n + 1)

/-- Fourier transform in angular frequency `x`, without a `2π` in its kernel. -/
@[expose] public def endpointAngularFourier (f : ℝ → ℝ) (x : ℝ) : ℂ :=
  ∫ z : ℝ, exp (-(x : ℂ) * I * (z : ℂ)) * (f z : ℂ)

/-- The endpoint spectral parameter on the critical line. -/
@[expose] public def endpointPairingParameter (x : ℝ) : ℂ := 1 / 2 + (x : ℂ) * I

/-- `dx / (2π |1/2 + ix|²)`. -/
@[expose] public def endpointPairingMeasure : Measure ℝ :=
  volume.withDensity fun x ↦ ENNReal.ofReal (1 / (2 * Real.pi * ‖endpointPairingParameter x‖ ^ 2))

private def halfTilt (f : ℝ → ℝ) (z : ℝ) : ℝ := Real.exp (-z / 2) * f z

private def halfTiltComplex (f : ℝ → ℝ) (z : ℝ) : ℂ := (halfTilt f z : ℂ)

private def shiftedSplineTilt (k : ℝ → ℝ) (j : ℕ) (s z : ℝ) : ℝ :=
  Real.exp (-(s + z) / 2) * ∫ v : ℝ, k v * longCutoffProfile j (z + s + v)

private theorem bounded_L1_memLp_two {𝕜 : Type*} [RCLike 𝕜] {f : ℝ → 𝕜}
    (hf : Integrable f) {M : ℝ} (hM : ∀ z, ‖f z‖ ≤ M) : MemLp f 2 := by
  apply (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).2
  refine (hf.norm.mul_const M).mono' (hf.aestronglyMeasurable.norm.pow 2) ?_
  exact ae_of_all _ fun z ↦ by
    rw [Real.norm_of_nonneg (sq_nonneg _), pow_two]
    exact mul_le_mul_of_nonneg_left (hM z) (norm_nonneg _)

private theorem integrable_bounded_halfTilt {Y : ℝ → ℝ} (hY : Measurable Y) {a M : ℝ}
    (hzero : ∀ z < a, Y z = 0) (hbound : ∀ z, ‖Y z‖ ≤ M) :
    Integrable (halfTiltComplex Y) ∧ ∃ C : ℝ, ∀ z, ‖halfTiltComplex Y z‖ ≤ C := by
  have hexp : IntegrableOn (fun z : ℝ ↦ Real.exp (-z / 2)) (Set.Ici a) := by
    rw [integrableOn_Ici_iff_integrableOn_Ioi]
    convert integrableOn_exp_mul_Ioi (a := -(1 / 2)) (by norm_num) a using 1
    ext z
    congr 1
    ring
  have hmeas : Measurable (halfTiltComplex Y) :=
    Complex.continuous_ofReal.measurable.comp ((by fun_prop :
      Continuous (fun z : ℝ ↦ Real.exp (-z / 2))).measurable.mul hY)
  refine ⟨(hexp.integrable_indicator measurableSet_Ici).mul_const M |>.mono'
    hmeas.aestronglyMeasurable (ae_of_all _ fun z ↦ ?_),
    ⟨Real.exp (-a / 2) * M, fun z ↦ ?_⟩⟩
  · by_cases hz : z ∈ Set.Ici a
    · rw [Set.indicator_of_mem hz, halfTiltComplex, Complex.norm_real, halfTilt, norm_mul,
        Real.norm_of_nonneg (Real.exp_pos _).le]
      exact mul_le_mul_of_nonneg_left (hbound z) (Real.exp_pos _).le
    · have hz' : z < a := lt_of_not_ge hz
      simp [Set.indicator_of_notMem hz, halfTiltComplex, halfTilt, hzero z hz']
  · have hM : 0 ≤ M := (norm_nonneg (Y 0)).trans (hbound 0)
    by_cases hz : z < a
    · simpa [halfTiltComplex, halfTilt, hzero z hz] using
        mul_nonneg (Real.exp_pos (-a / 2)).le hM
    · rw [halfTiltComplex, Complex.norm_real, halfTilt, norm_mul,
        Real.norm_of_nonneg (Real.exp_pos _).le]
      exact mul_le_mul (Real.exp_le_exp.mpr (by linarith)) (hbound z)
        (norm_nonneg _) (Real.exp_pos _).le

-- A bounded right factor and an integrable left factor give a bound at every coordinate.
private theorem norm_integral_mul_le {𝕜 : Type*} [RCLike 𝕜] {f g : ℝ → 𝕜}
    (hf : Integrable f) {M : ℝ} (hg : ∀ t, ‖g t‖ ≤ M) :
    ‖∫ t, f t * g t‖ ≤ ∫ t, ‖f t‖ * M :=
  norm_integral_le_of_norm_le (hf.norm.mul_const M) (ae_of_all _ fun t ↦ by
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hg t) (norm_nonneg _))

-- The exponential factors multiply before taking the real convolution integral.
private theorem halfTiltComplex_convolution (f g : ℝ → ℝ) :
    halfTiltComplex (f ⋆[ContinuousLinearMap.mul ℝ ℝ] g) =
      halfTiltComplex f ⋆[ContinuousLinearMap.mul ℂ ℂ] halfTiltComplex g := by
  funext z
  simp only [halfTiltComplex, halfTilt, convolution_mul]
  rw [← integral_const_mul, ← integral_complex_ofReal]
  apply integral_congr_ae
  refine ae_of_all _ fun t ↦ ?_
  have he : Real.exp (-z / 2) = Real.exp (-t / 2) * Real.exp (-(z - t) / 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  simp only [← Complex.ofReal_mul, Complex.ofReal_inj]
  rw [he]
  ring

-- In Mathlib the Fourier frequency is in cycles; here it is in radians.
private theorem endpointAngularFourier_eq (f : ℝ → ℝ) (x : ℝ) :
    endpointAngularFourier f x = 𝓕 (fun z ↦ (f z : ℂ)) (x * (2 * Real.pi)⁻¹) := by
  rw [endpointAngularFourier, Real.fourier_eq']
  apply integral_congr_ae
  refine ae_of_all _ fun z ↦ ?_
  simp only [Real.inner_apply, smul_eq_mul]
  congr 2
  push_cast
  field_simp [Real.pi_ne_zero]

private theorem halfTilt_power (Y : ℝ → ℝ) (hY : Integrable (halfTiltComplex Y))
    (hbound : ∃ M : ℝ, ∀ z, ‖halfTiltComplex Y z‖ ≤ M) (n : ℕ) :
    Integrable (halfTiltComplex (endpointConvolutionPower Y (n + 1))) ∧
      (∃ M : ℝ, ∀ z, ‖halfTiltComplex (endpointConvolutionPower Y (n + 1)) z‖ ≤ M) ∧
      ∀ x, endpointAngularFourier (halfTilt (endpointConvolutionPower Y (n + 1))) x =
        endpointAngularFourier (halfTilt Y) x ^ (n + 1) := by
  induction n with
  | zero => exact ⟨hY, hbound, fun x ↦ (pow_one _).symm⟩
  | succ n ih =>
    obtain ⟨hi, ⟨M, hM⟩, hf⟩ := ih
    have hconv : halfTiltComplex (endpointConvolutionPower Y (n + 1 + 1)) =
        halfTiltComplex Y ⋆[ContinuousLinearMap.mul ℂ ℂ]
          halfTiltComplex (endpointConvolutionPower Y (n + 1)) :=
      halfTiltComplex_convolution _ _
    refine ⟨hconv ▸ hY.integrable_convolution _ hi, ⟨∫ t, ‖halfTiltComplex Y t‖ * M, ?_⟩, ?_⟩
    · intro z
      rw [hconv, convolution_mul]
      exact norm_integral_mul_le hY (fun t ↦ hM (z - t))
    · intro x
      rw [endpointAngularFourier_eq, show (fun z ↦ (halfTilt
        (endpointConvolutionPower Y (n + 1 + 1)) z : ℂ)) = _ from hconv,
        Real.fourier_mul_convolution_eq hY hi, pow_succ']
      exact congrArg₂ (· * ·) (endpointAngularFourier_eq (halfTilt Y) x).symm
        ((endpointAngularFourier_eq (halfTilt (endpointConvolutionPower Y (n + 1))) x).symm.trans
          (hf x))

private theorem bounded_longCutoffProfile_halfTilt (j : ℕ) :
    ∃ M : ℝ, ∀ z, ‖halfTilt (longCutoffProfile j) z‖ ≤ M := by
  let c (l : ℕ) : ℝ := (-1 : ℝ) ^ l * ((j - 1).choose l : ℝ)
  refine ⟨∑ l ∈ Finset.range j, ‖c l‖ * 2 ^ (j - l), fun z ↦ ?_⟩
  by_cases hz : z < 0
  · simpa [halfTilt, longCutoffProfile, hz] using
      Finset.sum_nonneg (s := Finset.range j) (fun l _ ↦
        mul_nonneg (norm_nonneg (c l)) (by positivity : 0 ≤ (2 : ℝ) ^ (j - l)))
  have hz₀ : 0 ≤ z := le_of_not_gt hz
  have hterm (n : ℕ) : Real.exp (-z / 2) * (z ^ n / (n.factorial : ℝ)) ≤ 2 ^ n := by
    have h := mul_le_mul_of_nonneg_left
      (Real.pow_div_factorial_le_exp (z / 2) (by linarith : 0 ≤ z / 2) n)
      (Real.exp_pos (-z / 2)).le
    rw [← Real.exp_add, neg_div, neg_add_cancel, Real.exp_zero, div_pow, ← neg_div] at h
    have heq : Real.exp (-z / 2) * ((z ^ n / 2 ^ n) / (n.factorial : ℝ)) =
        (Real.exp (-z / 2) * (z ^ n / (n.factorial : ℝ))) / 2 ^ n := by ring
    rw [heq] at h
    simpa only [one_mul] using (div_le_iff₀ (by positivity : 0 < (2 : ℝ) ^ n)).mp h
  simp only [halfTilt, longCutoffProfile, ite_eq_right hz, Finset.mul_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun l _ ↦ ?_)
  change ‖Real.exp (-z / 2) * (c l * _)‖ ≤ _
  rw [mul_left_comm, norm_mul, Real.norm_of_nonneg (show
    0 ≤ Real.exp (-z / 2) * (z ^ (j - l) / ((j - l).factorial : ℝ)) by positivity)]
  exact mul_le_mul_of_nonneg_left (hterm (j - l)) (norm_nonneg _)

private theorem shiftedSplineTilt_eq {k : ℝ → ℝ} (j : ℕ) (s z : ℝ) :
    shiftedSplineTilt k j s z =
      ∫ v : ℝ, (k v * Real.exp (v / 2)) * halfTilt (longCutoffProfile j) (z + s + v) := by
  rw [shiftedSplineTilt, ← integral_const_mul]
  apply integral_congr_ae
  refine ae_of_all _ fun v ↦ ?_
  have he : Real.exp (-(s + z) / 2) = Real.exp (v / 2) * Real.exp (-(z + s + v) / 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  change Real.exp (-(s + z) / 2) * (k v * longCutoffProfile j (z + s + v)) =
    (k v * Real.exp (v / 2)) * (Real.exp (-(z + s + v) / 2) * longCutoffProfile j (z + s + v))
  rw [he]
  ring

private theorem shiftedSplineTilt_L1_L2 {k : ℝ → ℝ}
    (hk : Integrable (fun v ↦ k v * Real.exp (v / 2))) (j : ℕ) (s : ℝ) :
    Integrable (fun z ↦ (shiftedSplineTilt k j s z : ℂ)) ∧
      MemLp (fun z ↦ (shiftedSplineTilt k j s z : ℂ)) 2 := by
  have hi : Integrable (fun z ↦ (shiftedSplineTilt k j s z : ℂ)) :=
    (integrable_longCutoffProfile_smoothed_halfTilt hk j s).2.ofReal
  obtain ⟨M, hM⟩ := bounded_longCutoffProfile_halfTilt j
  refine ⟨hi, bounded_L1_memLp_two hi (M := ∫ v, ‖k v * Real.exp (v / 2)‖ * M) fun z ↦ ?_⟩
  rw [Complex.norm_real, shiftedSplineTilt_eq]
  exact norm_integral_mul_le hk (fun v ↦ hM (z + s + v))

-- As in `ShiftedHankelCap`, identify the classical Fourier integral with the
-- Plancherel representative by testing the two against Schwartz functions.
private theorem endpoint_fourier_mul_swap {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g) :
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

private theorem endpoint_fourier_eq_L2 {f : ℝ → ℂ} (hf : Integrable f) (hf₂ : MemLp f 2) :
    𝓕 f =ᵐ[volume] ⇑(𝓕 (hf₂.toLp f) : Lp ℂ 2 (volume : Measure ℝ)) := by
  let F : Lp ℂ 2 (volume : Measure ℝ) := 𝓕 (hf₂.toLp f)
  have hcont : Continuous (𝓕 f) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (L := innerₗ ℝ) continuous_inner hf
  refine ae_eq_of_integral_contDiff_smul_eq hcont.locallyIntegrable
    ((Lp.memLp F).locallyIntegrable (by norm_num)) ?_
  intro φ hφ hc
  have hcc : HasCompactSupport (Complex.ofRealCLM ∘ φ) := hc.comp_left rfl
  have hφc : ContDiff ℝ ∞ (Complex.ofRealCLM ∘ φ) := by fun_prop
  let ψ := hcc.toSchwartzMap hφc
  have h := congrArg (fun T : 𝓢'(ℝ, ℂ) ↦ T ψ)
    (Lp.fourier_toTemperedDistribution_eq (hf₂.toLp f))
  calc
    (∫ x, φ x • 𝓕 f x) = ∫ x, 𝓕 f x * ψ x := by
      simp [ψ, Complex.real_smul, mul_comm]
    _ = ∫ x, f x * 𝓕 (ψ : ℝ → ℂ) x := endpoint_fourier_mul_swap hf ψ.integrable
    _ = ∫ x, 𝓕 ψ x • (hf₂.toLp f) x := by
      apply integral_congr_ae
      filter_upwards [hf₂.coeFn_toLp] with x hx
      rw [hx, ← SchwartzMap.fourier_coe, smul_eq_mul, mul_comm]
    _ = ∫ x, ψ x * F x := by
      simpa only [TemperedDistribution.fourier_apply, Lp.toTemperedDistribution_apply,
        smul_eq_mul] using h
    _ = ∫ x, φ x • F x := by simp [ψ, Complex.real_smul]

-- Plancherel pairs the conjugate of the first Fourier factor with the second.
-- Rescaling the frequency by `2π` contributes `1/(2π)` to the pairing.
private theorem endpoint_angular_plancherel {f g : ℝ → ℝ}
    (hf : Integrable (fun z ↦ (f z : ℂ))) (hg : Integrable (fun z ↦ (g z : ℂ)))
    (hf₂ : MemLp (fun z ↦ (f z : ℂ)) 2) (hg₂ : MemLp (fun z ↦ (g z : ℂ)) 2) :
    let P := fun x ↦ (starRingEnd ℂ) (endpointAngularFourier f x) * endpointAngularFourier g x
    Integrable (fun z ↦ f z * g z) ∧ Integrable P ∧
      (∫ z, f z * g z) = (2 * Real.pi)⁻¹ * (∫ x, P x).re := by
  intro P
  let U := hf₂.toLp (fun z ↦ (f z : ℂ))
  let V := hg₂.toLp (fun z ↦ (g z : ℂ))
  let W := fun x ↦ (starRingEnd ℂ) (𝓕 (fun z ↦ (f z : ℂ)) x) * 𝓕 (fun z ↦ (g z : ℂ)) x
  have hspace : (fun z ↦ f z * g z) =ᵐ[volume] (fun z ↦ (inner ℂ (U z) (V z)).re) := by
    filter_upwards [hf₂.coeFn_toLp, hg₂.coeFn_toLp] with z hz hz'
    change _ = (inner ℂ ((hf₂.toLp _) z) ((hg₂.toLp _) z)).re
    rw [hz, hz']
    simp [RCLike.inner_apply, mul_comm]
  have hfreq : W =ᵐ[volume] (fun x ↦ inner ℂ ((𝓕 U : Lp ℂ 2 _) x) ((𝓕 V : Lp ℂ 2 _) x)) := by
    filter_upwards [endpoint_fourier_eq_L2 hf hf₂, endpoint_fourier_eq_L2 hg hg₂] with x hx hx'
    dsimp [W, U, V] at *
    rw [← hx, ← hx']
    exact mul_comm _ _
  have hW : Integrable W := (L2.integrable_inner (𝕜 := ℂ) (𝓕 U) (𝓕 V)).congr hfreq.symm
  have hπ : 0 < 2 * Real.pi := by positivity
  have hP (x : ℝ) : P x = W (x * (2 * Real.pi)⁻¹) := by
    simp only [P, W, endpointAngularFourier_eq]
  refine ⟨(L2.integrable_inner (𝕜 := ℂ) U V).re.congr hspace.symm, ?_, ?_⟩
  · rw [show P = _ from funext hP]
    exact (integrable_comp_mul_right_iff W (inv_ne_zero hπ.ne')).2 hW
  · have hrescale : (∫ x, W x) = (2 * Real.pi)⁻¹ • ∫ x, P x := by
      have hscale (x : ℝ) : P (x * (2 * Real.pi)) = W x := by
        rw [hP, mul_assoc, mul_inv_cancel₀ hπ.ne', mul_one]
      simpa only [hscale, abs_of_pos (inv_pos.mpr hπ)] using
        Measure.integral_comp_mul_right P (2 * Real.pi)
    calc
      (∫ z, f z * g z) = ∫ z, (inner ℂ (U z) (V z)).re := integral_congr_ae hspace
      _ = (inner ℂ U V).re := by
        rw [L2.inner_def]
        exact integral_re (𝕜 := ℂ) (L2.integrable_inner U V)
      _ = (inner ℂ (𝓕 U) (𝓕 V)).re := by rw [Lp.inner_fourier_eq]
      _ = (∫ x, W x).re := by rw [L2.inner_def, integral_congr_ae hfreq]
      _ = _ := by rw [hrescale, Complex.smul_re, smul_eq_mul]

/-- The exact shifted endpoint pairing, including absolute integrability on both sides.
The physical profile is the ordinary `j`-fold convolution with the source's real coefficient;
`Q` is `e^(isx) g(w) m_j(x)` with `m_j = α m^j`. Positivity of `C₁` retains the
source normalization; the algebraic equality itself uses totalized division. -/
public theorem endpoint_convolution_pairing {Y k : ℝ → ℝ} (hY : Measurable Y)
    {a M : ℝ} (hzero : ∀ z < a, Y z = 0) (hbound : ∀ z, ‖Y z‖ ≤ M)
    (hk : Integrable (fun v ↦ k v * Real.exp (v / 2))) {j : ℕ} (hj : 1 ≤ j)
    (s : ℝ) {C₁ : ℝ} (_hC₁ : 0 < C₁) (Cj α : ℝ) :
    let Jhat := endpointAngularFourier (fun z ↦ Real.exp (-z / 2) * Y z);
    let m := (fun x ↦
      let w := endpointPairingParameter x;
      -((starRingEnd ℂ) w / w) * (starRingEnd ℂ) (Jhat x) / (C₁ : ℂ));
    let F := (fun z ↦ ((-1 : ℝ) ^ (j + 1) * Cj * α / C₁ ^ j) * endpointConvolutionPower Y j z);
    let Q := (fun x : ℝ ↦ exp ((s : ℂ) * (x : ℂ) * I) *
      (∫ v : ℝ, (k v : ℂ) * exp (endpointPairingParameter x * (v : ℂ))) *
        ((α : ℂ) * m x ^ j));
    let S := (fun z ↦ ∫ v : ℝ, k v * longCutoffProfile j (z + s + v));
    Integrable (fun z ↦ Real.exp (-z) * F z * S z) ∧ Integrable Q endpointPairingMeasure ∧
      Real.exp (-s / 2) * (∫ z, Real.exp (-z) * F z * S z) =
        -Cj * (∫ x, Q x ∂endpointPairingMeasure).re := by
  intro Jhat m F Q S
  let A := halfTilt (endpointConvolutionPower Y j)
  let B := shiftedSplineTilt k j s
  obtain ⟨hY₁, hYb⟩ := integrable_bounded_halfTilt hY hzero hbound
  have hpow := halfTilt_power Y hY₁ hYb (j - 1)
  rw [Nat.sub_add_cancel hj] at hpow
  obtain ⟨hA₁, ⟨MA, hAb⟩, hFA⟩ := hpow
  have hA₂ := bounded_L1_memLp_two hA₁ hAb
  obtain ⟨hB₁, hB₂⟩ := shiftedSplineTilt_L1_L2 hk j s
  let P := fun x ↦ (starRingEnd ℂ) (endpointAngularFourier A x) * endpointAngularFourier B x
  obtain ⟨hphys, hP, hpair⟩ := endpoint_angular_plancherel (f := A) (g := B) hA₁ hB₁ hA₂ hB₂
  change Integrable P at hP
  change (∫ z, A z * B z) = (2 * Real.pi)⁻¹ * (∫ x, P x).re at hpair
  have hFB (x : ℝ) : endpointAngularFourier B x =
      exp ((s : ℂ) * (x : ℂ) * I) *
        (∫ v : ℝ, (k v : ℂ) * exp (endpointPairingParameter x * (v : ℂ))) *
        ((((‖endpointPairingParameter x‖ ^ 2)⁻¹ : ℝ) : ℂ) *
          ((starRingEnd ℂ) (endpointPairingParameter x) / endpointPairingParameter x) ^ j) :=
    integral_longCutoffProfile_smoothed_halfTilt hk hj s x
  let b : ℝ := α * (-1) ^ j / C₁ ^ j
  let D : ℝ := (-1) ^ (j + 1) * Cj * α / C₁ ^ j
  have hD : D = -Cj * b := by dsimp [D, b]; rw [pow_succ]; ring
  let d (x : ℝ) := 1 / (2 * Real.pi * ‖endpointPairingParameter x‖ ^ 2)
  have hd (x : ℝ) : 0 ≤ d x := by dsimp [d]; positivity
  have hdmeas : Measurable (fun x ↦ ENNReal.ofReal (d x)) := by
    dsimp [d, endpointPairingParameter]
    fun_prop
  have hdtop : ∀ᵐ x : ℝ, ENNReal.ofReal (d x) < ⊤ := ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top
  have hweighted (x : ℝ) :
      (ENNReal.ofReal (d x)).toReal • Q x = ((2 * Real.pi)⁻¹ * b : ℝ) • P x := by
    have hdprod : d x = (2 * Real.pi)⁻¹ * (‖endpointPairingParameter x‖ ^ 2)⁻¹ := by
      simp only [d, one_div, mul_inv]
    rw [ENNReal.toReal_ofReal (hd x), hdprod]
    dsimp only [P, Q, m, b]
    rw [show endpointAngularFourier A x = Jhat x ^ j from hFA x, hFB, map_pow]
    simp only [Complex.real_smul, Complex.ofReal_mul, Complex.ofReal_inv, Complex.ofReal_div,
      Complex.ofReal_pow, Complex.ofReal_neg, Complex.ofReal_one, div_pow, mul_pow,
      neg_pow ((starRingEnd ℂ) (endpointPairingParameter x) / endpointPairingParameter x) j]
    ring
  have hspec : Integrable Q endpointPairingMeasure := by
    change Integrable Q (volume.withDensity fun x ↦ ENNReal.ofReal (d x))
    apply (integrable_withDensity_iff_integrable_smul' hdmeas hdtop).2
    exact (hP.smul ((2 * Real.pi)⁻¹ * b)).congr (ae_of_all _ fun x ↦ (hweighted x).symm)
  have hI : (∫ x, Q x ∂endpointPairingMeasure) = ((2 * Real.pi)⁻¹ * b : ℝ) • (∫ x, P x) := by
    change (∫ x, Q x ∂volume.withDensity (fun x ↦ ENNReal.ofReal (d x))) = _
    rw [integral_withDensity_eq_integral_toReal_smul hdmeas hdtop]
    simp_rw [hweighted, integral_smul]
  have hmodel (z : ℝ) : Real.exp (-z) * F z * S z = (Real.exp (s / 2) * D) * (A z * B z) := by
    have hexp : Real.exp (-z) =
        Real.exp (s / 2) * (Real.exp (-z / 2) * Real.exp (-(s + z) / 2)) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    dsimp only [F, S, D, A, B, halfTilt, shiftedSplineTilt]
    rw [hexp]
    ring
  refine ⟨(hphys.const_mul (Real.exp (s / 2) * D)).congr (ae_of_all _ fun z ↦ (hmodel z).symm),
    hspec, ?_⟩
  simp_rw [hmodel, integral_const_mul]
  rw [← mul_assoc, ← mul_assoc, ← Real.exp_add, show -s / 2 + s / 2 = 0 by ring,
    Real.exp_zero, one_mul, hpair, hD, hI, Complex.smul_re, smul_eq_mul]
  ring

end

end Masullo
