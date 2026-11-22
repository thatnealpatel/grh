module

public import Lemmas.IdeleFiniteStageMeasure
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Order.Filter.AtTopBot.CountablyGenerated

/-! # Exhaustion of idele integrals by open stages

In (3.2.2.6), p. 126, Masullo invokes a global product formula for the
absolute mass. He asserts the right-half-plane complex product (3.4.1.6),
displayed on p. 143, and footnote 3 on p. 144 asks for more justification.
Using the open stages of the restricted product (A.3.2.5), p. 560, we
pass from bounded stage absolute masses to global integrability and
convergence of both integrals. The finite-stage tensor theorem computes
the inputs; this result does not prove the Euler bounds or identify the
zeta density.
Source readings are provisional (Markdown and PDF layout).
-/

open Filter IsDedekindDomain MeasureTheory NumberField Set Topology
open scoped Classical ENNReal Masullo

namespace Masullo

variable (K : Type*) [Field K] [NumberField K]

local notation "V" => HeightOneSpectrum (𝓞 K)
local notation "I" => IdeleGroup (𝓞 K) K
local notation "U" S => range (ideleFiniteStageEmbedding K S)

/-- A uniform bound for the absolute masses on the stages above `E`
implies global integrability. Both integrals are limits along the finite
stages ordered by inclusion, with `E` kept in every stage. -/
public theorem ideleFiniteStage_exhaust [MeasurableSpace I] [BorelSpace I]
    (E : Finset V) (μ : Measure I) (g : I → ℂ) (B : ℝ)
    (hi : ∀ S : Finset V, E ⊆ S → IntegrableOn g (U S) μ)
    (hb : ∀ S : Finset V, E ⊆ S → (∫ x in U S, ‖g x‖ ∂μ) ≤ B) :
    Integrable g μ ∧ (∫ x, ‖g x‖ ∂μ) ≤ B ∧
      Tendsto (fun S : Finset V ↦ ∫ x in U (E ∪ S), g x ∂μ) atTop (𝓝 (∫ x, g x ∂μ)) ∧
      Tendsto (fun S : Finset V ↦ ∫ x in U (E ∪ S), ‖g x‖ ∂μ) atTop (𝓝 (∫ x, ‖g x‖ ∂μ)) := by
  classical
  let : Countable V := countable_ideleFinitePlaces K
  let stage (S : Finset V) := U (E ∪ S)
  have hmono : Monotone stage := by
    intro S T hST
    change stage S ⊆ stage T
    dsimp only [stage]
    rw [range_ideleFiniteStageEmbedding, range_ideleFiniteStageEmbedding]
    exact fun _ hx v hv ↦ hx v (fun hv' ↦ hv (Finset.union_subset_union_right hST hv'))
  have hcover : (⋃ S, stage S) = univ := by
    refine eq_univ_of_forall fun x ↦ ?_
    have hx : x ∈ ⋃ S : Finset V, U S := by
      rw [iUnion_range_ideleFiniteStageEmbedding]; exact mem_univ _
    obtain ⟨S, hS⟩ := mem_iUnion.mp hx
    refine mem_iUnion.mpr ⟨S, ?_⟩
    change x ∈ U (E ∪ S)
    rw [range_ideleFiniteStageEmbedding] at hS ⊢
    exact fun v hv ↦ hS v (fun hmem ↦ hv (Finset.mem_union_right _ hmem))
  have hmeas (S : Finset V) : MeasurableSet (stage S) :=
    (isOpenEmbedding_ideleFiniteStageEmbedding K (E ∪ S)).isOpen_range.measurableSet
  have hint (S : Finset V) : IntegrableOn g (stage S) μ := hi _ Finset.subset_union_left
  -- The stage representatives give global AE strong measurability.
  have ha := AEStronglyMeasurable.iUnion (fun S ↦ (hint S).aestronglyMeasurable)
  rw [hcover, Measure.restrict_univ] at ha
  -- The extended absolute integral is the supremum of the stage masses.
  have hmass : (∫⁻ x, ‖g x‖ₑ ∂μ) ≤ ENNReal.ofReal B := by
    rw [← Measure.restrict_univ (μ := μ), ← hcover,
      setLIntegral_iUnion_of_directed _ hmono.directed_le]
    refine iSup_le fun S ↦ ?_
    rw [← ofReal_integral_norm_eq_lintegral_eNorm (hint S)]
    exact ENNReal.ofReal_le_ofReal (hb _ Finset.subset_union_left)
  have hg : Integrable g μ :=
    ⟨ha, hasFiniteIntegral_iff_eNorm.mpr (hmass.trans_lt ENNReal.ofReal_lt_top)⟩
  have hB : 0 ≤ B := (integral_nonneg fun x ↦ norm_nonneg (g x)).trans (hb E (by rfl))
  refine ⟨hg, (ENNReal.ofReal_le_ofReal_iff hB).mp ?_, ?_, ?_⟩
  · rw [ofReal_integral_norm_eq_lintegral_eNorm hg]
    exact hmass
  -- Now that the global density is integrable, both set integrals converge.
  · have hi' : IntegrableOn g (⋃ S, stage S) μ := by simpa [hcover] using hg
    simpa only [hcover, Measure.restrict_univ] using
      tendsto_setIntegral_of_monotone hmeas hmono hi'
  · have hi' : IntegrableOn (fun x ↦ ‖g x‖) (⋃ S, stage S) μ := by
      simpa [hcover] using hg.norm
    simpa only [hcover, Measure.restrict_univ] using
      tendsto_setIntegral_of_monotone hmeas hmono hi'

end Masullo
