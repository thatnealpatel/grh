import Mathlib.Analysis.Fourier.AddCircle

/-! # Windowed Fourier synthesis in `L²`

Pull a continuous function on the circle back to the real line and multiply by an `L²` window.
The target measure need not be the circle's Haar measure, or even locally finite.
-/

open MeasureTheory

namespace AdHoc

noncomputable section

variable {L : ℝ} [Fact (0 < L)] {μ : Measure ℝ}

private theorem norm_windowProduct_le (η : Lp ℂ 2 μ) (f : C(AddCircle L, ℂ)) (x : ℝ) :
    ‖η x * f (x : AddCircle L)‖ ≤ ‖f‖ * ‖η x‖ := by
  rw [norm_mul, mul_comm ‖f‖]
  exact mul_le_mul_of_nonneg_left (f.norm_coe_le_norm _) (norm_nonneg _)

private theorem memLp_windowProduct (η : Lp ℂ 2 μ) (f : C(AddCircle L, ℂ)) :
    MemLp (fun x : ℝ => η x * f (x : AddCircle L)) 2 μ := by
  have hc : Continuous (fun x : ℝ => f (x : AddCircle L)) :=
    f.continuous.comp (AddCircle.continuous_mk' L)
  exact (Lp.memLp η).of_le_mul ((Lp.aestronglyMeasurable η).mul hc.aestronglyMeasurable)
    (Filter.Eventually.of_forall (norm_windowProduct_le η f))

private def windowValue (η : Lp ℂ 2 μ) (f : C(AddCircle L, ℂ)) : Lp ℂ 2 μ :=
  (memLp_windowProduct η f).toLp _

private theorem windowValue_ae (η : Lp ℂ 2 μ) (f : C(AddCircle L, ℂ)) :
    (windowValue η f : ℝ → ℂ) =ᵐ[μ] fun x => η x * f (x : AddCircle L) :=
  (memLp_windowProduct η f).coeFn_toLp

private theorem norm_windowValue_le (η : Lp ℂ 2 μ) (f : C(AddCircle L, ℂ)) :
    ‖windowValue η f‖ ≤ ‖η‖ * ‖f‖ := by
  rw [mul_comm]
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [windowValue_ae η f] with x hx
  rw [hx]
  exact norm_windowProduct_le η f x

/-- Pull back a periodic profile and multiply it by an `L²(μ)` window. -/
def W (η : Lp ℂ 2 μ) : C(AddCircle L, ℂ) →L[ℂ] Lp ℂ 2 μ :=
  LinearMap.mkContinuous
    { toFun := windowValue η
      map_add' := fun f g => by
        apply Lp.ext
        filter_upwards [windowValue_ae η (f + g), windowValue_ae η f, windowValue_ae η g,
          Lp.coeFn_add (windowValue η f) (windowValue η g)] with x hfg hf hg hadd
        simp only [hfg, hadd, Pi.add_apply, hf, hg, ContinuousMap.add_apply, mul_add]
      map_smul' := fun c f => by
        apply Lp.ext
        filter_upwards [windowValue_ae η (c • f), windowValue_ae η f,
          Lp.coeFn_smul c (windowValue η f)] with x hcf hf hsmul
        simp only [hcf, hsmul, Pi.smul_apply, hf, ContinuousMap.smul_apply, RingHom.id_apply,
          smul_eq_mul]
        exact mul_left_comm _ _ _ }
    ‖η‖ (norm_windowValue_le η)

/-- The windowed profile is represented by the pointwise product almost everywhere. -/
theorem W_apply_ae (η : Lp ℂ 2 μ) (f : C(AddCircle L, ℂ)) :
    (W η f : ℝ → ℂ) =ᵐ[μ] fun x => η x * f (x : AddCircle L) :=
  windowValue_ae η f

/-- If a window is given as a square-integrable function, the formula uses that function itself. -/
theorem W_toLp_apply_ae {w : ℝ → ℂ} (hw : MemLp w 2 μ) (f : C(AddCircle L, ℂ)) :
    (W (hw.toLp w) f : ℝ → ℂ) =ᵐ[μ] fun x => w x * f (x : AddCircle L) := by
  filter_upwards [W_apply_ae (hw.toLp w) f, hw.coeFn_toLp] with x hprod hwx
  rw [hprod, hwx]

/-- A continuous compactly supported window can be used for any measure finite on compacts,
including a locally finite weighted measure. For a bounded measurable compactly supported
window, use `HasCompactSupport.memLp_of_bound` and `W_toLp_apply_ae`. -/
theorem W_compactSupport_apply_ae [IsFiniteMeasureOnCompacts μ] {w : ℝ → ℂ}
    (hw : Continuous w) (hs : HasCompactSupport w) (f : C(AddCircle L, ℂ)) :
    (W ((hw.memLp_of_hasCompactSupport (μ := μ) hs).toLp w) f : ℝ → ℂ) =ᵐ[μ]
      fun x => w x * f (x : AddCircle L) :=
  W_toLp_apply_ae (hw.memLp_of_hasCompactSupport (μ := μ) hs) f

/-- The `L²` norm of a windowed profile is bounded by its uniform norm times the window norm. -/
theorem norm_W_apply_le (η : Lp ℂ 2 μ) (f : C(AddCircle L, ℂ)) :
    ‖W η f‖ ≤ ‖η‖ * ‖f‖ :=
  norm_windowValue_le η f

/-- Fourier modes have uniform norm one, so windowing them costs at most the window norm. -/
theorem norm_W_fourier_le (η : Lp ℂ 2 μ) (k : ℤ) :
    ‖W (L := L) η (fourier k)‖ ≤ ‖η‖ := by
  simpa only [fourier_norm, mul_one] using norm_W_apply_le η (fourier (T := L) k)

/-- The Fourier synthesis of a continuous profile with summable coefficients converges after
windowing in the norm topology of `L²(μ)`. In particular this applies to smooth profiles with
summable coefficients. -/
theorem hasSum_windowed_fourier_series (η : Lp ℂ 2 μ) {f : C(AddCircle L, ℂ)}
    (h : Summable (fourierCoeff f)) :
    HasSum (fun k => fourierCoeff f k • W (L := L) η (fourier k)) (W η f) := by
  simpa only [map_smul] using (hasSum_fourier_series_of_summable (f := f) h).mapL (W (L := L) η)

end

end AdHoc
