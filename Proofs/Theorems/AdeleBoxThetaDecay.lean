module

public import Theorems.AdeleBoxFourierRapidDecay
public import Theorems.AdeleBoxThetaInversion

/-! # Zero-mode-corrected theta decay at small norm

Theorem 2.2.3.4(2), (2.2.3.5) and (2.2.3.7), PDF p. 83, uses
inversion followed by large-norm decay of the Fourier theta sum.
`adeleBoxSpan_theta_inversion` supplies that identity pointwise, and
`adeleBoxSpan_fourier_rapidDecay` bounds the absolute mass of the
reflected sum for the same additive Fourier integral. We use order
`N + 1` to absorb the inverse norm in (2.2.3.7). This is a fixed-test
estimate on actual ideles, before quotient measurability or averaging.
Source reading: Provisional pinned Markdown and numbered PDF layout.
-/

open IsDedekindDomain MeasureTheory NumberField
open scoped Classical Masullo.AdeleStage

namespace Masullo

variable {K : Type*} [Field K] [NumberField K]
local notation "A" => AdeleRing (𝓞 K) K
local notation "J" => IdeleGroup (𝓞 K) K
local notation "V" => HeightOneSpectrum (𝓞 K)
local notation "ι" => algebraMap K A
local notation "d" => IdeleGroup.unitEmbedding (𝓞 K) K

/-- The fixed-box-span estimate (2.2.3.5), with both zero corrections
retained and threshold one. -/
public theorem adeleBoxSpan_theta_smallNorm_decay (μ : Measure A) [μ.IsAddHaarMeasure]
    (E : Finset V) (hμ : ∀ S : Finset V, E ⊆ S →
      μ.comap (adeleFiniteStageEmbedding K S) = adeleFiniteStageHaar K S)
    {f : A → ℂ} (hf : f ∈ adeleBoxSpan K) (N : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ h : J, ideleNorm h ≤ 1 →
      ‖(∑' t : Kˣ, f ((h : A) * ι (t : K))) - (ideleNorm h)⁻¹ • adeleFourier μ f 0 + f 0‖ ≤
        C * ideleNorm h ^ N := by
  obtain ⟨C, hC, hdecay⟩ := adeleBoxSpan_fourier_rapidDecay μ E hμ hf (N + 1)
  refine ⟨C, hC, fun h hh ↦ ?_⟩
  have hpos : 0 < ideleNorm h :=
    ideleClassNorm_mk h ▸ ideleClassNorm_pos (QuotientGroup.mk h)
  have hinv : 1 ≤ ideleNorm h⁻¹ := by
    rw [map_inv]
    exact (one_le_inv₀ hpos).mpr hh
  obtain ⟨hs, hb⟩ := hdecay h⁻¹ hinv
  let q (t : Kˣ) := adeleFourier μ f ((↑(h⁻¹) : A) * ι (t : K))
  have hsample (t : Kˣ) : adeleFourier μ f ((d t * h⁻¹ : J) : A) = q t := by
    change adeleFourier μ f (ι (t : K) * (↑(h⁻¹) : A)) = q t
    rw [mul_comm]
  simp only [hsample] at hs hb
  have hθ := (adeleBoxSpan_theta_inversion μ E hμ hf h).2.2
  -- Inversion gives the corrected sum before any character averaging.
  have hcorrected : (∑' t : Kˣ, f ((h : A) * ι (t : K))) -
      (ideleNorm h)⁻¹ • adeleFourier μ f 0 + f 0 = (ideleNorm h)⁻¹ • (∑' t, q t) := by
    rw [hθ]
    abel
  have hpow : (ideleNorm h⁻¹) ^ (-((N + 1 : ℕ) : ℤ)) = ideleNorm h ^ (N + 1) := by
    rw [map_inv, inv_zpow, zpow_neg, inv_inv, zpow_natCast]
  rw [hcorrected, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hpos.le)]
  calc
    _ ≤ (ideleNorm h)⁻¹ * (∑' t, ‖q t‖) := by
      gcongr
      exact norm_tsum_le_tsum_norm hs
    _ ≤ (ideleNorm h)⁻¹ * (C * ideleNorm h ^ (N + 1)) := by
      rw [hpow] at hb
      exact mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr hpos.le)
    _ = C * ideleNorm h ^ N := by
      calc
        _ = (C * ideleNorm h ^ N) * (ideleNorm h * (ideleNorm h)⁻¹) := by
          rw [pow_succ]
          ac_rfl
        _ = _ := by rw [mul_inv_cancel₀ hpos.ne', mul_one]

end Masullo
