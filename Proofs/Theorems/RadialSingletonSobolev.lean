module

public import Theorems.RadialHardySobolevCompletion
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.MeasureTheory.Function.ContinuousMapDense

/-! # The singleton radial Hardy–Sobolev completion

The original all-weight profile map for `I = {0}` has dense range in the
full weighted `L²` in the normalized logarithmic coordinate. This is the
identity-module radial case of Masullo §1.1.3 (p. 12), with the singleton
norm of (9.2.2.4), (9.2.2.34), and the weight in (9.1.2.3).
-/

open MeasureTheory Metric Set
open scoped ContDiff Convolution ENNReal Topology

namespace Masullo

/-- At `a = b = 0`, the endpoint maximum contributes no weight. -/
public theorem logSobolevWeight_singleton (s x : ℝ) :
    logSobolevWeight 0 0 s x = (1 + |x| ^ 2) ^ (s / 2) := by
  simp [logSobolevWeight, sq_abs]

private theorem singleton_locallyFinite (s : ℝ) :
    IsLocallyFiniteMeasure (logSobolevMeasure 0 0 s) := by
  have h : Continuous (logSobolevWeight 0 0 s) := by
    change Continuous (fun x ↦ logSobolevWeight 0 0 s x)
    simp only [logSobolevWeight_singleton, sq_abs]
    exact (show Continuous (fun x : ℝ ↦ 1 + x ^ 2) by fun_prop).rpow_const
      (fun x ↦ Or.inl (show 1 + x ^ 2 ≠ 0 by positivity))
  exact IsLocallyFiniteMeasure.withDensity_coe (μ := volume) (continuous_real_toNNReal.comp h)

private theorem compactSmooth_mem_allProfiles {u : ℝ → ℂ}
    (h : ContDiff ℝ ∞ u) (hc : HasCompactSupport u) : u ∈ logWeightedProfiles univ := by
  refine ⟨h, fun a ↦ ?_⟩
  have hw : ContDiff ℝ ∞ (logStageWeight a) :=
    Complex.ofRealCLM.contDiff.comp (Real.contDiff_exp.comp (contDiff_const.mul contDiff_id))
  exact ⟨hc.mul_left.toSchwartzMap (hw.mul h), fun _ ↦ rfl⟩

private theorem exists_smooth_approx {μ : Measure ℝ} [IsLocallyFiniteMeasure μ]
    {g : ℝ → ℂ} (hg : Continuous g) (hgc : HasCompactSupport g) {ε : ℝ} (hε : 0 < ε) :
    ∃ u : ℝ → ℂ, ContDiff ℝ ∞ u ∧ HasCompactSupport u ∧
      (eLpNorm (g - u) 2 μ).toReal < ε := by
  let K := cthickening 1 (tsupport g)
  have hK : IsCompact K := hgc.isCompact.cthickening
  let M := μ K ^ (1 / (2 : ℝ≥0∞).toReal)
  have hM : M ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (by positivity) hK.measure_lt_top.ne
  let η := ε / (1 + M.toReal)
  have hη : 0 < η := div_pos hε (by positivity)
  obtain ⟨δ, hδ, hclose⟩ := Metric.uniformContinuous_iff.mp
    (hgc.uniformContinuous_of_continuous hg) η hη
  let r := min δ 1
  have hr : 0 < r := lt_min hδ one_pos
  let φ : ContDiffBump (0 : ℝ) := ⟨r / 2, r, half_pos hr, half_lt_self hr⟩
  let u := φ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g
  have hu : ContDiff ℝ ∞ u :=
    φ.hasCompactSupport_normed.contDiff_convolution_left _ φ.contDiff_normed hg.locallyIntegrable
  have huc : HasCompactSupport u := φ.hasCompactSupport_normed.convolution _ hgc
  refine ⟨u, hu, huc, ?_⟩
  have hgu (x : ℝ) : dist (g x) (u x) ≤ η := by
    rw [dist_comm]
    exact φ.dist_normed_convolution_le hg.aestronglyMeasurable (fun y hy ↦
      (hclose (lt_of_lt_of_le (mem_ball.mp hy) (min_le_left δ 1))).le)
  have huK : Function.support u ⊆ K := by
    intro x hx
    obtain ⟨y, hy, z, hz, rfl⟩ := support_convolution_subset
      (ContinuousLinearMap.lsmul ℝ ℝ) hx
    apply closedBall_subset_cthickening (subset_closure hz)
    rw [φ.support_normed_eq] at hy
    have hy' := mem_ball.mp hy
    exact mem_closedBall.mpr (by simpa using hy'.le.trans (min_le_right δ 1))
  have hbound := eLpNorm_sub_le_of_dist_bdd μ (p := 2) (by simp)
    hK.isClosed.measurableSet.nullMeasurableSet hη.le (hg.sub hu.continuous).aestronglyMeasurable
    hgu (subset_closure.trans (self_subset_cthickening (tsupport g))) huK
  calc
    (eLpNorm (g - u) 2 μ).toReal ≤ η * M.toReal := by
      simpa [M, ENNReal.toReal_mul, ENNReal.toReal_ofReal hη.le] using
        ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hM) hbound
    _ < ε := by
      dsimp [η]
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
      nlinarith

/-- Any element of the ambient singleton weighted `L²` can be approximated
in norm by the original embedding of compactly supported all-weight profiles. -/
public theorem exists_logSobolevAllToLp_singleton_dist_lt (s : ℝ)
    (Y : Lp ℂ 2 (logSobolevMeasure 0 0 s)) {ε : ℝ} (hε : 0 < ε) :
    ∃ u : logWeightedProfiles univ, HasCompactSupport u.1 ∧
      dist Y (logSobolevAllToLp (le_refl (0 : ℝ)) s u) < ε := by
  let μ := logSobolevMeasure 0 0 s
  let : IsLocallyFiniteMeasure (logSobolevMeasure 0 0 s) := singleton_locallyFinite s
  obtain ⟨g, hgc, hYg, hg, hgLp⟩ := (Lp.memLp Y).exists_hasCompactSupport_eLpNorm_sub_le (by simp)
    (ε := ENNReal.ofReal (ε / 2)) (by simp [half_pos hε])
  obtain ⟨u, hu, huc, hgu⟩ := exists_smooth_approx (μ := μ) hg hgc (half_pos hε)
  let f : logWeightedProfiles univ := ⟨u, compactSmooth_mem_allProfiles hu huc⟩
  let Z := hgLp.toLp g
  let W := logSobolevAllToLp (le_refl (0 : ℝ)) s f
  have hZ : (Z : ℝ → ℂ) =ᵐ[μ] g := hgLp.coeFn_toLp
  have hW : (W : ℝ → ℂ) =ᵐ[μ] u := logSobolevAllToLp_ae_eq (le_refl (0 : ℝ)) s f
  have hYZ : dist Y Z ≤ ε / 2 := by
    rw [Lp.dist_def, eLpNorm_congr_ae (Filter.EventuallyEq.rfl.sub hZ)]
    simpa [ENNReal.toReal_ofReal (half_pos hε).le] using
      ENNReal.toReal_mono ENNReal.ofReal_ne_top hYg
  have hZW : dist Z W < ε / 2 := by
    rw [Lp.dist_def, eLpNorm_congr_ae (hZ.sub hW)]
    exact hgu
  exact ⟨f, huc, (dist_triangle Y Z W).trans_lt (by linarith)⟩

/-- With the original embedding and its norm, the radial singleton completion
fills the weighted `L²`; it is not merely a common closure of two profile spaces. -/
public theorem logSobolevAllToLp_denseRange_singleton (s : ℝ) :
    DenseRange (logSobolevAllToLp (le_refl (0 : ℝ)) s) := by
  intro Y
  apply Metric.mem_closure_range_iff.mpr
  intro ε hε
  obtain ⟨u, _, hu⟩ := exists_logSobolevAllToLp_singleton_dist_lt s Y hε
  exact ⟨u, hu⟩

end Masullo
