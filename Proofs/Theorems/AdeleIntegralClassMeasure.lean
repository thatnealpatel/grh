module

public import Lemmas.AdeleIntegralQuotient
public import Theorems.AdeleIntegralCellMass

/-! # Probability Haar and counting integration on the global additive adelic classes

Definition A.3.1.1, PDF p. 555, pairs probability Haar on the adelic classes
with counting measure on the diagonal; Theorem C.4.4.3, p. 718, and Theorem
D.1.2.1, p. 747, give the quotient integral formula. Here the Haar measure
upstairs is fixed by the box Fourier stage comaps. Rather than infer
covolume from the set in (A.2.1.1), we push the restriction to the corrected
full-dimensional Borel cell to the actual quotient. Its mass is already one
by `adeleIntegralCell_mass_one`. The pointwise partition, open inverse
charts, and counting reindexing give Borel periodization and integration
for this very measure. Source readings are provisional (pinned Markdown
and numbered PDF layout). No S-local assertion is made.
-/

open IsDedekindDomain MeasureTheory NumberField Set
open scoped ENNReal Masullo.AdeleStage

namespace Masullo

noncomputable section

variable (K : Type*) [Field K] [NumberField K]

local notation "V" => HeightOneSpectrum (𝓞 K)
local notation "A" => AdeleRing (𝓞 K) K
local notation "Δ" => AdeleRing.principalSubgroup (𝓞 K) K
local notation "Q" => A ⧸ Δ
local notation "π" => QuotientAddGroup.mk' Δ

/-- Push forward the upstream measure restricted to the half-open cell. -/
@[expose] public def adeleIntegralClassMeasure (μ : Measure A) : Measure Q :=
  (μ.restrict (adeleIntegralCell K)).map π

/-- The same stage-comap normalization as in box Fourier induces probability Haar on the
actual additive classes, without a scaling of either measure. -/
public theorem adeleIntegralClassMeasure_haar_probability (μ : Measure A) [μ.IsAddHaarMeasure]
    (E : Finset V) (hμ : ∀ S : Finset V, E ⊆ S →
      μ.comap (adeleFiniteStageEmbedding K S) = adeleFiniteStageHaar K S) :
    (adeleIntegralClassMeasure K μ).IsAddHaarMeasure ∧
      IsProbabilityMeasure (adeleIntegralClassMeasure K μ) := by
  let : Countable Δ := countable_adelePrincipalSubgroup K
  let : CompactSpace Q := compactSpace_adeleIntegralQuotient K
  let : IsClosed (Δ : Set A) := isClosed_adelePrincipalSubgroup K
  have hprob : IsProbabilityMeasure (adeleIntegralClassMeasure K μ) := by
    constructor
    rw [adeleIntegralClassMeasure, Measure.map_apply (measurable_adeleIntegralQuotient K)
      MeasurableSet.univ, preimage_univ, Measure.restrict_apply_univ,
      adeleIntegralCell_mass_one K μ E hμ]
  let := hprob
  have hInv : (adeleIntegralClassMeasure K μ).IsAddLeftInvariant :=
    addInvariant_map_restrict π (adeleIntegralCell_isAddFundamentalDomain K μ)
      (measurable_adeleIntegralQuotient K) QuotientAddGroup.mk_surjective
      (adeleIntegralQuotient_vadd K)
  let := hInv
  exact ⟨Measure.isAddHaarMeasure_of_isCompact_nonempty_interior _ univ isCompact_univ
    (by simp) (by simp) (by simp), hprob⟩

/-- Weil's formula for nonnegative Borel functions, using counting measure on `K`.
No integrability premise is needed. -/
public theorem adeleIntegralClassMeasure_lintegral_counting (μ : Measure A) [μ.IsAddHaarMeasure]
    {f : A → ℝ≥0∞} (hf : Measurable f) :
    ∃ F : Q → ℝ≥0∞, Measurable F ∧
      (∀ a : A, F (π a) = ∑' t : K, f (algebraMap K A t + a)) ∧
      (∫⁻ c, F c ∂adeleIntegralClassMeasure K μ) = ∫⁻ a, f a ∂μ := by
  let : Countable Δ := countable_adelePrincipalSubgroup K
  obtain ⟨F, hF, hcount⟩ := exists_adeleCountingPeriodization K hf
  refine ⟨F, hF, hcount, lintegral_addPeriodization π (adeleIntegralCell_isAddFundamentalDomain K μ)
    (measurable_adeleIntegralQuotient K) hf hF (fun a ↦ (hcount a).trans ?_)⟩
  exact adelePrincipalIndex_tsum K f a

/-- Weil's formula for Borel integrable complex functions, with almost everywhere
absolute summability on the quotient for every representative of the class. -/
public theorem adeleIntegralClassMeasure_integral_counting (μ : Measure A) [μ.IsAddHaarMeasure]
    {f : A → ℂ} (hf : Measurable f) (hfi : Integrable f μ) :
    ∃ F : Q → ℂ, Measurable F ∧
      (∀ a : A, F (π a) = ∑' t : K, f (algebraMap K A t + a)) ∧
      (∀ᵐ c ∂adeleIntegralClassMeasure K μ, ∀ a : A, π a = c →
        Summable (fun t : K ↦ ‖f (algebraMap K A t + a)‖)) ∧
      Integrable F (adeleIntegralClassMeasure K μ) ∧
      (∫ c, F c ∂adeleIntegralClassMeasure K μ) = ∫ a, f a ∂μ := by
  let : Countable Δ := countable_adelePrincipalSubgroup K
  obtain ⟨F, hF, hcount⟩ := exists_adeleCountingPeriodization K hf
  refine ⟨F, hF, hcount, ?_, integral_addPeriodization π (adeleIntegralCell_isAddFundamentalDomain K μ)
    (measurable_adeleIntegralQuotient K) hf hfi hF (fun a ↦ (hcount a).trans ?_)⟩
  · obtain ⟨G, hG, hsum, hGint⟩ := adeleIntegralClassMeasure_lintegral_counting K μ hf.eNorm
    filter_upwards [ae_lt_top hG (hGint.trans_ne hfi.2.ne)] with c hc a ha
    apply tsum_eNorm_ne_top_iff_summable_norm.mp
    rw [← hsum a, ha]
    exact hc.ne
  · exact adelePrincipalIndex_tsum K f a

end

end Masullo
