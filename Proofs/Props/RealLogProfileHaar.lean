module

public import Lemmas.RealLogCutoff
public import Props.RealPrincipalValue

/-! # The real principal value in multiplicative coordinates

Masullo (B.4.4.2), p. 620, translates the identity to zero and multiplies
by the inverse half power. Connes, Appendix II (34)–(37), uses half of
full real multiplicative Haar. With the standard additive transform of
(B.4.4.1), the half weighting is already built into the additive functional;
applying the factor `1/M∞ = 1/2` of (B.4.4.16) to that functional again
would halve the local term. This normalization repair concerns the local
scalar term used in (12.5.1.1), not the global `S`-piece evaluation.
-/

open Filter MeasureTheory Set
open scoped ContDiff ENNReal FourierTransform Topology

namespace Masullo

/-- A smooth compactly supported log profile gives the smooth compactly
supported additive test required in (B.4.4.2), with identity value `F 0`. -/
public theorem real_log_profile_additive_test {F : ℝ → ℂ} (hF : ContDiff ℝ ∞ F)
    (hc : HasCompactSupport F) :
    ContDiff ℝ ∞ (realLogProfileAdditive F) ∧ HasCompactSupport (realLogProfileAdditive F) ∧
      realLogProfileAdditive F 0 = F 0 := by
  obtain ⟨hd, hk⟩ := RealLogProfileHaar.additive_test hF hc
  exact ⟨hd, hk, by simp [realLogProfileAdditive]⟩

/-- Connes (36) in the real radial chart of (B.4.4.2), before taking the
limit. Both integrals are absolute for each positive cutoff radius. -/
public theorem real_log_profile_haar_cutoff {F : ℝ → ℂ} (hF : ContDiff ℝ ∞ F)
    (hc : HasCompactSupport F) {ε : ℝ} (hε : 0 < ε) :
    let u := realLogProfileAdditive F
    let w (y : ℝˣ) := F (Real.log |(y : ℝ)|) * (((|(y : ℝ)| ^ (1 / 2 : ℝ)) : ℝ) : ℂ) /
      ((|1 - (y : ℝ)| : ℝ) : ℂ)
    let μ := (1 / 2 : ℝ≥0∞) • realMultiplicativeHaar
    IntegrableOn (fun z ↦ u z / ((|z| : ℝ) : ℂ)) {z | ε ≤ |z|} ∧
      IntegrableOn w {y | ε ≤ |1 - (y : ℝ)|} μ ∧
      (1 / 2 : ℂ) * (∫ z in {z | ε ≤ |z|}, u z / ((|z| : ℝ) : ℂ)) =
        ∫ y in {y | ε ≤ |1 - (y : ℝ)|}, w y ∂μ := by
  obtain ⟨hd, hk, _⟩ := real_log_profile_additive_test hF hc
  have hi := RealLogFourier.integrableOn_div_abs_cutoff (hk.toSchwartzMap hd).integrable hε
  -- Translate `y = 1 + z` and use the two-sided density `dy / |y|` on real units.
  obtain ⟨ht, ht'⟩ := RealLogProfileHaar.translate_cutoff (realLogProfileAdditive F) ε
  obtain ⟨hm, hm'⟩ := RealLogProfileHaar.density_cutoff F ε
  have hw := hm.mpr (ht.mp hi)
  dsimp only
  refine ⟨hi, ?_, ?_⟩
  · rw [IntegrableOn, Measure.restrict_smul]
    exact hw.smul_measure (by norm_num)
  · rw [Measure.restrict_smul, integral_smul_measure, ht', ← hm']
    norm_num [Complex.real_smul]

/-- The real contribution in (B.4.4.2) in the normalization of Connes
(36)–(37). The logarithmic counterterm is at the multiplicative identity;
the contact term has been moved to the right of the limit. -/
public theorem real_log_profile_haar_principalValue {F : ℝ → ℂ} (hF : ContDiff ℝ ∞ F)
    (hc : HasCompactSupport F) :
    let u := realLogProfileAdditive F
    let μ := (1 / 2 : ℝ≥0∞) • realMultiplicativeHaar
    Tendsto (fun ε : ℝ ↦
      (∫ y in {y : ℝˣ | ε ≤ |1 - (y : ℝ)|}, F (Real.log |(y : ℝ)|) *
        (((|(y : ℝ)| ^ (1 / 2 : ℝ)) : ℝ) : ℂ) / ((|1 - (y : ℝ)| : ℝ) : ℂ) ∂μ) +
        (Real.log ε : ℂ) * F 0) (𝓝[Ioi 0] 0)
      (𝓝 (-(∫ ξ, (Real.log |ξ| : ℂ) * 𝓕 u ξ) -
        ((Real.log (2 * Real.pi) + Real.eulerMascheroniConstant : ℝ) : ℂ) * F 0)) := by
  obtain ⟨hd, hk, h₀⟩ := real_log_profile_additive_test hF hc
  have h := (real_log_fourier_cutoff (hk.toSchwartzMap hd)).2
  have hu : (hk.toSchwartzMap hd : ℝ → ℂ) = realLogProfileAdditive F := rfl
  simp only [hu, h₀] at h
  refine h.congr' ?_
  filter_upwards [eventually_mem_nhdsWithin] with ε hε
  rw [(real_log_profile_haar_cutoff hF hc (show 0 < ε from hε)).2.2]

/-- Absolute integrability on every positive symmetric log cutoff. The Haar
measure has both signs, including the regular contribution around `-1`. -/
public theorem real_log_profile_haar_log_cutoff_integrable {F : ℝ → ℂ}
    (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F) {ε : ℝ} (hε : 0 < ε) :
    IntegrableOn (realLogProfileHaarKernel F) {y : ℝˣ | ε ≤ |Real.log (|(y : ℝ)|)|}
      ((1 / 2 : ℝ≥0∞) • realMultiplicativeHaar) := by
  obtain ⟨hd, hk, _⟩ := real_log_profile_additive_test hF hc
  exact (RealLogCutoff.haar_logCutoff_eq (hk.toSchwartzMap hd).integrable hε).1

/-- The symmetric log cutoff has the same counterterm and contact term as
the corrected physical cutoff for (B.4.3.13) and (B.4.4.2).
The project repair is `tendsto_logAddSet_compensated`: It restores
both deleted neighborhoods in the integrable remainder and compares the two
asymmetric radii at the singularity. No assumption on `F 0` is needed. -/
public theorem real_log_profile_haar_log_principalValue {F : ℝ → ℂ} (hF : ContDiff ℝ ∞ F)
    (hc : HasCompactSupport F) :
    let u := realLogProfileAdditive F
    let μ := (1 / 2 : ℝ≥0∞) • realMultiplicativeHaar
    Tendsto (fun ε : ℝ ↦
      (∫ y in {y : ℝˣ | ε ≤ |Real.log (|(y : ℝ)|)|}, realLogProfileHaarKernel F y ∂μ) +
        (Real.log ε : ℂ) * F 0) (𝓝[Ioi 0] 0)
      (𝓝 (-(∫ ξ, (Real.log |ξ| : ℂ) * 𝓕 u ξ) -
        ((Real.log (2 * Real.pi) + Real.eulerMascheroniConstant : ℝ) : ℂ) * F 0)) := by
  obtain ⟨hd, hk, h₀⟩ := real_log_profile_additive_test hF hc
  let u := hk.toSchwartzMap hd
  obtain ⟨_, hi, hv⟩ := real_log_fourier_unit_subtraction u
  have hu : (u : ℝ → ℂ) = realLogProfileAdditive F := rfl
  simp only [hu, h₀] at hv
  have ht := RealLogCutoff.tendsto_logAddSet_compensated u.integrable hi
  rw [hu, h₀] at ht
  simp only
  rw [hv, add_sub_cancel_right]
  refine ht.congr' ?_
  filter_upwards [eventually_mem_nhdsWithin] with ε hε
  rw [(RealLogCutoff.haar_logCutoff_eq u.integrable (show 0 < ε from hε)).2]

/-- The log cutoff can replace the physical one before passing to the
finite part. In the log cutoff inversion preserves the integration set,
unlike a finite physical cutoff. This is a local comparison for the inverse
argument in (12.4.1.25), not a proof of the sum replacement there. -/
public theorem real_log_profile_haar_cutoff_difference {F : ℝ → ℂ} (hF : ContDiff ℝ ∞ F)
    (hc : HasCompactSupport F) :
    let μ := (1 / 2 : ℝ≥0∞) • realMultiplicativeHaar
    Tendsto (fun ε : ℝ ↦
      (∫ y in {y : ℝˣ | ε ≤ |Real.log (|(y : ℝ)|)|}, realLogProfileHaarKernel F y ∂μ) -
      (∫ y in {y : ℝˣ | ε ≤ |1 - (y : ℝ)|}, realLogProfileHaarKernel F y ∂μ))
      (𝓝[Ioi 0] 0) (𝓝 0) := by
  have h := (real_log_profile_haar_log_principalValue hF hc).sub
    (real_log_profile_haar_principalValue hF hc)
  simpa only [realLogProfileHaarKernel, add_sub_add_right_eq_sub, sub_self] using h

end Masullo
