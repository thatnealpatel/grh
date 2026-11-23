module

public import Theorems.FixedAnnulusTraceDensity
public import Theorems.RationalThetaBandClosure
import Lemmas.WeightedAnnulusTrace

/-!
# The fixed-position trace density in the global rational theta chart

For the rational trivial isotype, (10.4.1.6–7), p. 457, and (11.2.1.8–10),
p. 489, motivate compact position localization and a right band projection.
We use the repaired weighted rational theta levels of `RationalThetaBandClosure`,
not the local one-place level of `fixedAnnulus_traceDensity`. Unlike the cited
condensation theorem, the construction permits tests below norm one. It
constructs the chart model of `Mρ A QY`; comparison to the printed
`Mρ P_geom A QY` needs the full geometric range invariance separately.
In the `L²(dx)`
chart, ordinary log convolution acquires one weight on the output and its
reciprocal on the input. An additional right multiplier acts *before* the band
projector. No input mask is commuted through the projector.
-/

open Filter MeasureTheory Set InnerProductSpace
open scoped InnerProductSpace ENNReal Topology

namespace Masullo.OperatorTrace

local notation "H" => Lp ℂ 2 (volume : Measure ℝ)

/-- At fixed annulus and band, the chart form of localized convolution after
projection onto the rational global theta band has an integrable basis-trace
density, also representing every further right-multiplied trace. The density
comes from the rank-one presentation, not restriction of an a.e. kernel to the
Haar diagonal. This theorem takes neither cutoff limit. -/
public theorem rationalThetaBand_traceDensity (a α s Y : ℝ) (hs : 0 ≤ s) (hα : 0 ≤ α)
    {ρ φ : ℝ → ℂ} (hρ : Continuous ρ) (hρK : HasCompactSupport ρ)
    (hφ : ContDiff ℝ 2 φ) (hφK : HasCompactSupport φ) :
    let w := symmetricStripWeightRoot α s
    let P := (rationalThetaWeightedEvenImage a hs hα {ξ | |ξ| ≤ Y}).toSubmodule.starProjection
    ∃ (B : H →L[ℂ] H) (d : ℝ → ℂ),
      (∀ z : H, (B z : ℝ → ℂ) =ᵐ[volume] fun x =>
        (ρ x * (w x : ℂ)) * ∫ y, φ (x - y) * (P z) y * (w y : ℂ)⁻¹) ∧
      Integrable d volume ∧
      (∀ {ι : Type*} (b : HilbertBasis ι ℂ H),
        HasSum (fun i => ⟪b i, B (b i)⟫_ℂ) (∫ x, d x)) ∧
      ∀ {m : ℝ → ℂ} (hm : MemLp m ∞ volume),
        Integrable (fun x => m x * d x) volume ∧
        ∀ {ι : Type*} (b : HilbertBasis ι ℂ H),
          HasSum (fun i => ⟪b i, B (logMultiplier hm (b i))⟫_ℂ) (∫ x, m x * d x) := by
  let w := symmetricStripWeightRoot α s
  let P := (rationalThetaWeightedEvenImage a hs hα {ξ | |ξ| ≤ Y}).toSubmodule.starProjection
  obtain ⟨L, hL, p, q, f, hf, hA⟩ := exists_weightedAnnulus_window
    (continuous_symmetricStripWeightRoot α s) (symmetricStripWeightRoot_pos α s) hρ hρK hφ hφK
  let _ := hL
  let B := (windowKernel p q f).comp P
  let d := windowKernelTraceDensity p q f P
  refine ⟨B, d, fun z => hA (P z), (windowKernel_traceDensity_integrable p q f hf P).1,
    fun b => windowKernel_traceDensity b p q f hf P, ?_⟩
  · intro m hm
    refine ⟨hm.integrable_mul (memLp_one_iff_integrable.2
      (windowKernel_traceDensity_integrable p q f hf P).1),
      fun b => (windowKernel_localized_traceDensity b p q f hf P hm).2⟩

/-- At fixed position cutoff, exhaust the global rational theta Fourier band.
The same localized convolution acts on every projected vector and on the full
weighted theta projection. This is the chart trace analogue of (11.2.1.10),
p. 489, also for tests supported below norm one. No position limit is taken. -/
public theorem rationalThetaBand_trace_tendsto (a α s : ℝ) (hs : 0 ≤ s) (hα : 0 ≤ α)
    {Y : ℕ → ℝ} (hY : Monotone Y) (hcofinal : ∀ R : ℝ, ∃ n, R ≤ Y n)
    {ρ φ : ℝ → ℂ} (hρ : Continuous ρ) (hρK : HasCompactSupport ρ)
    (hφ : ContDiff ℝ 2 φ) (hφK : HasCompactSupport φ) :
    let w := symmetricStripWeightRoot α s
    let Q (n : ℕ) :=
      (rationalThetaWeightedEvenImage a hs hα {ξ | |ξ| ≤ Y n}).toSubmodule.starProjection
    let P := (rationalThetaWeightedEvenImage a hs hα univ).toSubmodule.starProjection
    ∃ (A : H →L[ℂ] H) (T : ℕ → ℂ) (Tlim : ℂ),
      (∀ z : H, (A z : ℝ → ℂ) =ᵐ[volume] fun x =>
        (ρ x * (w x : ℂ)) * ∫ y, φ (x - y) * z y * (w y : ℂ)⁻¹) ∧
      Tendsto T atTop (𝓝 Tlim) ∧
      ∀ {ι : Type*} (b : HilbertBasis ι ℂ H),
        (∀ n, HasSum (fun i => ⟪b i, A (Q n (b i))⟫_ℂ) (T n)) ∧
        HasSum (fun i => ⟪b i, A (P (b i))⟫_ℂ) Tlim := by
  intro w Q P
  -- The period and the summable expansion do not depend on the band.
  obtain ⟨L, hL, p, q, f, hf, hA⟩ := exists_weightedAnnulus_window
    (continuous_symmetricStripWeightRoot α s) (symmetricStripWeightRoot_pos α s) hρ hρK hφ hφK
  let _ := hL
  let trace (S : H →L[ℂ] H) :=
    ∑' k : ℤ, ⟪W q (fourier (T := L) k), S (outputMode p f k)⟫_ℂ
  refine ⟨windowKernel p q f, fun n => trace (Q n), trace P, hA, ?_, ?_⟩
  · -- Strong projector convergence supplies the termwise limits in the trace series.
    exact tendsto_windowKernel_trace p q f hf
      (tendsto_rationalThetaWeightedEvenBand_projection a hs hα hY hcofinal)
      (fun n z => Submodule.norm_starProjection_apply_le _ z)
  · intro ι b
    exact ⟨fun n => (windowKernel_trace b p q f hf (Q n)).2,
      (windowKernel_trace b p q f hf P).2⟩

end Masullo.OperatorTrace
