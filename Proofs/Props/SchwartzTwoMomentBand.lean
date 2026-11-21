module

public import Lemmas.SchwartzBandCorrection
import Mathlib.Analysis.Distribution.SchwartzSpace.CompactSupport

/-!
# Preserving both zero modes when imposing a finite Fourier band

In the rational real band of Masullo (7.3.2.14), p. 355, the band
is in additive Fourier frequency. The following approximation is a
project argument on the real Schwartz generators: It preserves both
conditions in (7.3.2.15) before taking a theta image or a Hilbert closure.
-/

open Filter MeasureTheory Set FourierTransform
open scoped ContDiff FourierTransform SchwartzMap Topology

namespace Masullo

/-- Approximate on the frequency side by compactly supported Schwartz functions,
correct evaluation and mass exactly, then take the even part. -/
public theorem exists_tendsto_fourierBand_twoMoments (b : 𝓢(ℝ, ℂ)) (he : Function.Even b)
    (hb : b 0 = 0) (hFb : (𝓕 b) 0 = 0) :
    ∃ u : ℕ → 𝓢(ℝ, ℂ), Tendsto u atTop (𝓝 b) ∧
      ∀ n, Function.Even (⇑(u n)) ∧ u n 0 = 0 ∧ (𝓕 (u n)) 0 = 0 ∧
        ∃ B : ℝ, 0 < B ∧ ∀ ξ : ℝ, B < |ξ| → (𝓕 (u n)) ξ = 0 := by
  let f := 𝓕 b
  have hf : Function.Even f := fourier_preserves_realSchwartz_even he
  have hm : bandSchwartzMass f = 0 := by
    rw [← fourierInv_zero_eq_bandSchwartzMass, show 𝓕⁻ f = b from fourierInv_fourier_eq b]
    exact hb
  obtain ⟨v, hv, hlim⟩ := mem_closure_iff_seq_limit.mp
    (SchwartzMap.dense_hasCompactSupport (F := ℂ) f)
  let w (k : 𝓢(ℝ, ℂ)) := k - k 0 • bandSchwartzBump 0
  let z (k : 𝓢(ℝ, ℂ)) := w k - (bandSchwartzMass (w k) / bandSchwartzMass (bandSchwartzBump 2)) • bandSchwartzBump 2
  let e (k : 𝓢(ℝ, ℂ)) := (2 : ℂ)⁻¹ • (z k + bandSchwartzReflect (z k))
  have hw0 (k) : w k 0 = 0 := by simp [w, bandSchwartzBump_zero]
  have hz0 (k) : z k 0 = 0 := by simp [z, hw0, bandSchwartzBump_two_zero]
  have hzm (k) : bandSchwartzMass (z k) = 0 := by
    dsimp only [z]
    rw [map_sub, map_smul, smul_eq_mul, div_mul_cancel₀ _ bandSchwartzMass_bump_two_ne, sub_self]
  have her (k) : Function.Even (e k) := by intro x; simp [e, bandSchwartzReflect, add_comm]
  have he0 (k) : e k 0 = 0 := by simp [e, bandSchwartzReflect, hz0]
  have hem (k) : bandSchwartzMass (e k) = 0 := by
    have hr : bandSchwartzMass (bandSchwartzReflect (z k)) = bandSchwartzMass (z k) := by
      change (∫ x : ℝ, z k (-x)) = ∫ x : ℝ, z k x
      exact (Measure.measurePreserving_neg (volume : Measure ℝ)).integral_comp
        (Homeomorph.neg ℝ).measurableEmbedding _
    dsimp only [e]
    rw [map_smul, map_add, hr, hzm, add_zero, smul_zero]
  have hwf : w f = f := by simp [w, f, hFb]
  have hzf : z f = f := by simp only [z, hwf, hm, zero_div, zero_smul, sub_zero]
  have hef : e f = f := by
    have hrf : bandSchwartzReflect f = f := by ext x; exact hf x
    dsimp only [e]
    rw [hzf, hrf, ← two_smul ℂ f, inv_smul_smul₀ (by norm_num : (2 : ℂ) ≠ 0)]
  have hev : Continuous (fun k : 𝓢(ℝ, ℂ) ↦ k 0) :=
    ((BoundedContinuousFunction.lipschitz_eval_const (0 : ℝ)).continuous).comp
      (SchwartzMap.toBoundedContinuousFunctionCLM ℂ ℝ ℂ).continuous
  have hw : Continuous w := continuous_id.sub (hev.smul continuous_const)
  have hz : Continuous z := hw.sub (((bandSchwartzMass.continuous.comp hw).div_const _).smul continuous_const)
  have hcont : Continuous e := by
    simpa only [e, Pi.smul_def, Pi.add_apply, Function.comp_apply] using
      (hz.add (bandSchwartzReflect.continuous.comp hz)).const_smul ((2 : ℂ)⁻¹)
  refine ⟨fun n ↦ 𝓕⁻ (e (v n)), ?_, fun n ↦ ?_⟩
  · simpa only [Function.comp_def, hef, f, fourierInv_fourier_eq] using
      (continuous_fourierInv.continuousAt.tendsto.comp ((hcont.tendsto f).comp hlim))
  · refine ⟨fourierInv_preserves_realSchwartz_even (her _), (fourierInv_zero_eq_bandSchwartzMass _).trans (hem _), ?_⟩
    rw [fourier_fourierInv_eq]
    refine ⟨he0 _, ?_⟩
    have hwc : HasCompactSupport (w (v n) : ℝ → ℂ) :=
      (hv n).sub ((bandSchwartzBump_compact 0).smul_left (f := fun _ ↦ v n 0))
    have hzc : HasCompactSupport (z (v n) : ℝ → ℂ) :=
      hwc.sub ((bandSchwartzBump_compact 2).smul_left (f := fun _ ↦ bandSchwartzMass (w (v n)) / bandSchwartzMass (bandSchwartzBump 2)))
    have hrc : HasCompactSupport (bandSchwartzReflect (z (v n)) : ℝ → ℂ) :=
      hzc.comp_homeomorph (Homeomorph.neg ℝ)
    have hc : HasCompactSupport (e (v n) : ℝ → ℂ) := (hzc.add hrc).smul_left
    obtain ⟨R, hR⟩ := hc.isCompact.isBounded.subset_closedBall (0 : ℝ)
    refine ⟨max 1 R, lt_of_lt_of_le one_pos (le_max_left ..), fun ξ hξ ↦ ?_⟩
    by_contra! h
    have ht := hR (subset_tsupport _ (Function.mem_support.mpr h))
    exact (not_le.mpr ((le_max_right 1 R).trans_lt hξ)) (by simpa [Real.dist_eq] using ht)

end Masullo
