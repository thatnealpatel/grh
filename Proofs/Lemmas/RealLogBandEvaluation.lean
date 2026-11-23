module

public import Lemmas.RealLogLevel
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral

/-! # Evaluation on real logarithmic band generators -/

open MeasureTheory Set
open scoped FourierTransform SchwartzMap

namespace Masullo.OperatorTrace.RealLogLevel

private theorem toReal_eLpNorm_two_eq_sqrt {ν : Measure ℝ} {u : ℝ → ℂ} (hu : MemLp u 2 ν) :
    (eLpNorm u 2 ν).toReal = Real.sqrt (∫ t, ‖u t‖ ^ 2 ∂ν) := by
  rw [hu.eLpNorm_eq_integral_rpow_norm (by simp) (by simp),
    ENNReal.toReal_ofReal (by positivity), Real.sqrt_eq_rpow]
  norm_num [Real.rpow_natCast]

private theorem norm_schwartz_toLp_two_eq_sqrt (f : 𝓢(ℝ, ℂ)) :
    ‖f.toLp 2 volume‖ = Real.sqrt (∫ t, ‖f t‖ ^ 2) := by
  rw [SchwartzMap.norm_toLp' (by simp) (by simp), Real.sqrt_eq_rpow]
  norm_num [Real.rpow_natCast]

/-- For the additive `2π` Fourier convention, the evaluation bound uses the square root
of the Lebesgue length of the Fourier band. -/
public theorem norm_apply_le_of_fourier_support {Y : ℝ} (hY : 0 < Y) {f : 𝓢(ℝ, ℂ)}
    (hf : Function.support (⇑(𝓕 f : 𝓢(ℝ, ℂ))) ⊆ Icc (-Y) Y) (t : ℝ) :
    ‖f t‖ ≤ Real.sqrt (2 * Y) * ‖f.toLp 2 volume‖ := by
  let g : 𝓢(ℝ, ℂ) := 𝓕 f
  let s : Set ℝ := Icc (-Y) Y
  have hg (ξ : ℝ) (hξ : ξ ∉ s) : g ξ = 0 :=
    Function.notMem_support.mp (fun h ↦ hξ (hf h))
  have hinv : f t = 𝓕 (g : ℝ → ℂ) (-t) := by
    rw [← Real.fourierInv_eq_fourier_neg, ← SchwartzMap.fourierInv_coe]
    exact congrArg (fun u : 𝓢(ℝ, ℂ) ↦ u t) (FourierTransform.fourierInv_fourier_eq f).symm
  have hvol : volume.real s = 2 * Y := by
    change volume.real (Icc (-Y) Y) = 2 * Y
    rw [measureReal_def, Real.volume_Icc, ENNReal.toReal_ofReal (by linarith)]
    ring
  have : IsFiniteMeasure (volume.restrict s) :=
    isFiniteMeasure_restrict.mpr (isCompact_Icc.measure_lt_top (μ := volume)).ne
  have hg2 : MemLp (g : ℝ → ℂ) 2 (volume.restrict s) :=
    (g.memLp 2).mono_measure Measure.restrict_le_self
  have h1 : MemLp (fun _ : ℝ ↦ (1 : ℂ)) 2 (volume.restrict s) := memLp_const 1
  have hCS := integral_mul_norm_le_Lp_mul_Lq Real.HolderConjugate.two_two
    (f := fun _ : ℝ ↦ (1 : ℂ)) (g := (g : ℝ → ℂ)) (by simpa using h1) (by simpa using hg2)
  have hsq : (∫ ξ in s, ‖g ξ‖ ^ 2) = ∫ t, ‖f t‖ ^ 2 := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun ξ hξ ↦ by simp [hg ξ hξ])]
    exact SchwartzMap.integral_norm_sq_fourier f
  calc
    ‖f t‖ = ‖𝓕 (g : ℝ → ℂ) (-t)‖ := congrArg norm hinv
    _ ≤ ∫ ξ, ‖g ξ‖ := Real.norm_fourier_le_integral_norm _ _
    _ = ∫ ξ in s, ‖g ξ‖ :=
      (setIntegral_eq_integral_of_forall_compl_eq_zero (fun ξ hξ ↦ by simp [hg ξ hξ])).symm
    _ ≤ Real.sqrt (2 * Y) * Real.sqrt (∫ t, ‖f t‖ ^ 2) := by
      simpa only [← Real.sqrt_eq_rpow, Real.rpow_two, norm_one, one_pow, one_mul,
        setIntegral_const, smul_eq_mul, mul_one, hvol, hsq] using hCS
    _ = _ := congrArg (Real.sqrt (2 * Y) * ·)
      (norm_schwartz_toLp_two_eq_sqrt f).symm

private theorem integral_sq_norm_profile {f : 𝓢(ℝ, ℂ)} (hf : Function.Even f) :
    (∫ x, ‖profile f x‖ ^ 2) = 2 * ∫ t, ‖f t‖ ^ 2 := by
  have h (x : ℝ) : ‖profile f x‖ ^ 2 = 4 * (Real.exp x * ‖f (Real.exp x)‖ ^ 2) := by
    rw [profile, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity), mul_pow,
      mul_pow, ← Real.exp_nat_mul]
    ring_nf
  have habs (t : ℝ) : f |t| = f t := by
    rcases le_total 0 t with ht | ht
    · rw [abs_of_nonneg ht]
    · rw [abs_of_nonpos ht, hf t]
  calc
    _ = 4 * (∫ t in Ioi (0 : ℝ), ‖f t‖ ^ 2) := by
      simp_rw [h, integral_const_mul]
      congr 1
      exact integral_comp_exp (fun t ↦ ‖f t‖ ^ 2)
    _ = 2 * ∫ t, ‖f t‖ ^ 2 := by
      have hfold := integral_comp_abs (f := fun t ↦ ‖f t‖ ^ 2)
      simp only [habs] at hfold
      rw [hfold]
      ring

/-- A weighted `L²` representative of an even Schwartz profile has norm at least
`√2` times the unweighted `L²` norm of the original Schwartz function. -/
public theorem sqrt_two_mul_norm_toLp_le {α : ℝ} {r : ℕ} (hα : 0 ≤ α)
    {f : 𝓢(ℝ, ℂ)} (hf : Function.Even f) {v : H α r}
    (hv : (v : ℝ → ℂ) =ᵐ[μ α r] profile f) :
    Real.sqrt 2 * ‖f.toLp 2 volume‖ ≤ ‖v‖ := by
  have hμ : (volume : Measure ℝ) ≤ μ α r := by
    calc
      volume = volume.withDensity 1 := withDensity_one.symm
      _ ≤ μ α r := by
        refine withDensity_mono (ae_of_all _ fun x ↦ ?_)
        change 1 ≤ ENNReal.ofReal (weight α r x)
        rw [← ENNReal.ofReal_one]
        apply ENNReal.ofReal_le_ofReal
        exact one_le_mul_of_one_le_of_one_le (Real.one_le_exp (by positivity))
          (one_le_pow₀ (le_add_of_nonneg_right (sq_nonneg x)))
  have hw : MemLp (profile f) 2 (μ α r) := (memLp_congr_ae hv).mp (Lp.memLp v)
  have hu : MemLp (profile f) 2 volume := hw.mono_measure hμ
  calc
    Real.sqrt 2 * ‖f.toLp 2 volume‖ = Real.sqrt (∫ x, ‖profile f x‖ ^ 2) := by
      rw [norm_schwartz_toLp_two_eq_sqrt, integral_sq_norm_profile hf,
        Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
    _ = (eLpNorm (profile f) 2 volume).toReal := (toReal_eLpNorm_two_eq_sqrt hu).symm
    _ ≤ (eLpNorm (profile f) 2 (μ α r)).toReal :=
      ENNReal.toReal_mono hw.eLpNorm_ne_top (eLpNorm_mono_measure _ hμ)
    _ = (eLpNorm (v : ℝ → ℂ) 2 (μ α r)).toReal :=
      congrArg ENNReal.toReal (eLpNorm_congr_ae hv).symm
    _ = ‖v‖ := (Lp.norm_def v).symm

/-- Pointwise evaluation of the concrete admissible profile, bounded by the norm of
its weighted `L²` representative. The representative hypothesis is precisely the
almost-everywhere equality in `generators`. -/
public theorem norm_profile_le_of_admissible {α Y : ℝ} {r : ℕ}
    (hα : 0 ≤ α) (hY : 0 < Y) {f : 𝓢(ℝ, ℂ)} (hf : Admissible Y f)
    {v : H α r} (hv : (v : ℝ → ℂ) =ᵐ[μ α r] profile f) (x : ℝ) :
    ‖profile f x‖ ≤ 2 * Real.sqrt Y * Real.exp (x / 2) * ‖v‖ := by
  rcases hf with ⟨heven, hband, _, _⟩
  have hpoint := norm_apply_le_of_fourier_support hY (f := f) hband (Real.exp x)
  have hnorm := sqrt_two_mul_norm_toLp_le hα heven hv
  rw [profile, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  calc
    _ ≤ (2 * Real.exp (x / 2)) * (Real.sqrt (2 * Y) * ‖f.toLp 2 volume‖) :=
      mul_le_mul_of_nonneg_left hpoint (by positivity)
    _ = (2 * Real.sqrt Y * Real.exp (x / 2)) * (Real.sqrt 2 * ‖f.toLp 2 volume‖) := by
      rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hnorm (by positivity)

end Masullo.OperatorTrace.RealLogLevel
