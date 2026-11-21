module

public import Theorems.RationalAdeleL2Fourier
import Theorems.RationalAdeleSchwartzDensity
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-! # The Fourier integral on rational adelic `L¹ ∩ L²`

The normalized Fourier integral agrees almost everywhere with the unitary
extension on every integrable square-integrable representative, giving
(D.1.1.9) and the integral agreement in (D.1.1.10), p. 747, on the
rational frequency model. The pointwise error bound is (D.1.1.7) applied
to a difference. Neither result requires identification of the full dual.
-/

open Filter MeasureTheory NumberField Topology
open scoped ComplexConjugate ENNReal

namespace Masullo

local notation "A" => AdeleRing (𝓞 ℚ) ℚ
local notation "μA" => rationalAdeleAddHaar
local notation "F" => rationalAdeleFourier
local notation "U" => rationalAdeleL2Fourier
local notation "J" => rationalAdeleSchwartzToL2

set_option linter.concreteInstances false

variable [MeasurableSpace A] [BorelSpace A]

/-- Rational adelic Schwartz functions are integrable for normalized additive Haar. -/
public theorem integrable_rationalAdeleSchwartzLF (g : RationalAdeleSchwartzLF) :
    Integrable g.toUnion.val μA := by
  obtain ⟨n, hn⟩ := mem_rationalAdeleSchwartzStageUnion.mp g.toUnion.property
  rw [← rationalAdeleLFAssembly_read n g hn, rationalAdeleLFAssembly_toUnion,
    rationalAdeleFactorialStageAssembly_val, rationalAdeleStageCoordinates_symm_eq_boxSum]
  exact integrable_finsetSum _ fun j _ ↦ (integrable_rationalAdeleBox _ _ _).const_mul 1

/-- The `L¹` distance bounds the Fourier error at every rational adelic frequency. -/
public theorem eNorm_rationalAdeleFourier_sub_le {f g : A → ℂ}
    (hf : Integrable f μA) (hg : Integrable g μA) (y : A) :
    ‖F f y - F g y‖ₑ ≤ eLpNorm (f - g) 1 μA := by
  let phase (x : A) := conj (rationalAdeleAddChar (x * y))
  have hc : Continuous phase := Complex.continuous_conj.comp
    (continuous_rationalAdeleAddChar.comp (continuous_id.mul continuous_const))
  have hp (x : A) : ‖phase x‖ = 1 :=
    (Complex.norm_conj _).trans (norm_rationalAdeleAddChar _)
  have ht {u : A → ℂ} (hu : Integrable u μA) :
      Integrable (fun x ↦ u x * phase x) μA :=
    hu.mul_bdd hc.aestronglyMeasurable (c := 1) (Eventually.of_forall fun x ↦ (hp x).le)
  change ‖(∫ x, f x * phase x ∂μA) - (∫ x, g x * phase x ∂μA)‖ₑ ≤ _
  rw [← eDist_eq_eNorm_sub, eLpNorm_one_eq_lintegral_eNorm (hf.sub hg).aestronglyMeasurable]
  refine (edist_integral_le_lintegral_edist (ht hf) (ht hg)).trans_eq (lintegral_congr fun x ↦ ?_)
  simp only [eDist_eq_eNorm_sub, ← sub_mul, ← ofReal_norm, norm_mul, hp, mul_one, Pi.sub_apply]

/-- The normalized Fourier integral represents the unitary transform on every
integrable `L²` input, with no pointwise measurability or moment hypothesis. -/
public theorem rationalAdeleL2Fourier_ae_eq_integral {f : A → ℂ}
    (hf₁ : Integrable f μA) (hf₂ : MemLp f 2 μA) :
    (U (hf₂.toLp f) : A → ℂ) =ᵐ[μA] F f := by
  obtain ⟨ε, -, hε, hεlim⟩ := exists_seq_strictAnti_tendsto' (zero_lt_one' ℝ≥0∞)
  choose g hg₁ hg₂ using fun n ↦ exists_rationalAdeleSchwartzLF_L1_L2_approx
    (memLp_one_iff_integrable.mpr hf₁) hf₂ (hε n).1 (hε n).1
  have hclose (δ : ℝ≥0∞) (hδ : 0 < δ) : ∀ᶠ n in atTop, ε n < δ :=
    (tendsto_order.mp hεlim).2 δ hδ
  -- Convergence in `L²`, followed by the unitary and an a.e. subsequence.
  have hL₂ : Tendsto (fun n ↦ J (g n)) atTop (𝓝 (hf₂.toLp f)) := by
    refine EMetric.tendsto_nhds.2 fun δ hδ ↦ (hclose δ hδ).mono fun n hn ↦ ?_
    rw [edist_comm, Lp.edist_def, eLpNorm_congr_ae (hf₂.coeFn_toLp.sub
      (rationalAdeleSchwartzToL2_ae_eq (g n)))]
    exact (hg₂ n).trans hn
  have hU := (rationalAdeleL2Fourier.continuous.tendsto (hf₂.toLp f)).comp hL₂
  obtain ⟨s, hs, hae⟩ := (tendstoInMeasure_of_tendsto_Lp hU).exists_seq_tendsto_ae
  have hcore := ae_all_iff.2 (fun n ↦ rationalAdeleL2Fourier_ae_eq_onSchwartz (g n))
  filter_upwards [hae, hcore] with y hy hcorey
  -- The same subsequence converges at every frequency by the `L¹` error bound.
  have hL₁ : Tendsto (fun n ↦ F (g n).toUnion.val y) atTop (𝓝 (F f y)) := by
    refine EMetric.tendsto_nhds.2 fun δ hδ ↦ (hclose δ hδ).mono fun n hn ↦ ?_
    rw [edist_comm, eDist_eq_eNorm_sub]
    exact (eNorm_rationalAdeleFourier_sub_le hf₁ (integrable_rationalAdeleSchwartzLF (g n)) y).trans_lt
      ((hg₁ n).trans hn)
  exact tendsto_nhds_unique (hy.congr fun n ↦ hcorey (s n)) (hL₁.comp hs.tendsto_atTop)

/-- The integral transform of an integrable `L²` input belongs to `L²`. -/
public theorem rationalAdeleFourier_memLp_two {f : A → ℂ}
    (hf₁ : Integrable f μA) (hf₂ : MemLp f 2 μA) : MemLp (F f) 2 μA :=
  (Lp.memLp (U (hf₂.toLp f))).ae_eq (rationalAdeleL2Fourier_ae_eq_integral hf₁ hf₂)

/-- Parseval for the normalized Fourier integral on `L¹ ∩ L²`. -/
public theorem eLpNorm_rationalAdeleFourier_two {f : A → ℂ}
    (hf₁ : Integrable f μA) (hf₂ : MemLp f 2 μA) : eLpNorm (F f) 2 μA = eLpNorm f 2 μA := by
  rw [← eLpNorm_congr_ae (rationalAdeleL2Fourier_ae_eq_integral hf₁ hf₂), ← Lp.eNorm_def,
    rationalAdeleL2Fourier.eNorm_map, Lp.eNorm_toLp]

end Masullo
