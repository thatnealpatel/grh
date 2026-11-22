module

public import Theorems.FiniteCompletionMultiplicativeHaar
public import Theorems.IdeleRestrictedProductHaar
public import Theorems.IdeleHeckeGaussian

/-! # The discriminant-normalized restricted product on the ideles

Lemma A.3.2.4, (A.3.2.5), PDF p. 560, prescribes the restricted product
of the local Haar measures of Definition A.3.2.2 and invokes the fact
that the finite unit masses are one off a finite set. The project
proves that fact via the global different and gives the measure on the
actual ideles by its restrictions to the open stages. Its common
calibration box retains the inverse square root of the absolute field
discriminant. No comparison with the quotient volume (A.3.2.1) is made
here. Source reading: Provisional, from the pinned Markdown and numbered
PDF text, not the rendered page.
-/

open IsDedekindDomain MeasureTheory NumberField TopologicalSpace
open scoped ENNReal Masullo

namespace Masullo

variable (K : Type*) [Field K] [NumberField K]

local notation "V" => HeightOneSpectrum (𝓞 K)
local notation "I" => IdeleGroup (𝓞 K) K
local notation "D" => differentIdeal ℤ (𝓞 K)

variable [∀ v : InfinitePlace K, MeasurableSpace v.Completionˣ]
  [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)ˣ]
  [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletionIntegers K)ˣ]
  [∀ v : InfinitePlace K, BorelSpace v.Completionˣ]
  [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)ˣ]
  [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletionIntegers K)ˣ]
  [MeasurableSpace (IdeleGroup (𝓞 K) K)] [BorelSpace (IdeleGroup (𝓞 K) K)]

/-- The prescribed local multiplicative Haar measures determine a unique
Borel measure by the stage product formulas. On every box with integral
units at all finite places, its mass is the Archimedean mass times
`|disc K|⁻¹ᐟ²`. -/
public theorem exists_discriminantNormalizedIdeleHaar :
    ∃ μ : Measure I, μ.IsHaarMeasure ∧ μ.Regular ∧
      (∀ ν : Measure I, ν = μ ↔ ∀ S : Finset V,
        (∀ v ∉ S, multiplicity v.asIdeal D = 0) →
        ν.comap (ideleFiniteStageEmbedding K S) =
          ideleFiniteStageProduct K (fun v ↦ archimedeanCompletionHaar v)
            (fun v ↦ finiteCompletionMultiplicativeHaar v) S) ∧
      (∀ B : PositiveCompacts ((v : InfinitePlace K) → v.Completionˣ),
        μ (ideleCalibrationBox K B) = Measure.pi (fun v : InfinitePlace K ↦ archimedeanCompletionHaar v) B *
          ENNReal.ofReal ((Real.sqrt ((discr K).natAbs : ℝ))⁻¹)) := by
  classical
  let E := (finite_differentIdeal_multiplicity_support (K := K)).toFinset
  have hE (S : Finset V) : E ⊆ S ↔ ∀ v ∉ S, multiplicity v.asIdeal D = 0 := by
    have hmem (v : V) : v ∈ E ↔ multiplicity v.asIdeal D ≠ 0 := Set.Finite.mem_toFinset _
    exact ⟨fun h v hv ↦ not_not.mp (fun hn ↦ hv (h ((hmem v).mpr hn))),
      fun h v hv ↦ by_contra fun hn ↦ (hmem v).mp hv (h v hn)⟩
  have hoff := (hE E).mp (Finset.Subset.refl E)
  let μa : (v : InfinitePlace K) → Measure v.Completionˣ := fun v ↦ archimedeanCompletionHaar v
  let μf : (v : V) → Measure (v.adicCompletion K)ˣ := fun v ↦ finiteCompletionMultiplicativeHaar v
  let (v : InfinitePlace K) : (μa v).IsHaarMeasure := archimedeanCompletionHaar_isHaarMeasure v
  let (v : V) : (μf v).IsHaarMeasure := finiteCompletionMultiplicativeHaar_isHaarMeasure v
  obtain ⟨μ, hμ, hr, hstage, hbox⟩ := exists_ideleRestrictedProductHaar K μa μf E
    (fun v hv ↦ finiteCompletionMultiplicativeHaar_unitMass_eq_one v (hoff v hv))
  refine ⟨μ, hμ, hr, ?_, ?_⟩
  · intro ν
    rw [hstage ν]
    exact ⟨fun h S hS ↦ h S ((hE S).mpr hS), fun h S hS ↦ h S ((hE S).mp hS)⟩
  · intro B
    rw [hbox B]
    congr 1
    have hfin : (∏ v ∈ E, finiteCompletionUnitMass K μf v) ≠ ∞ := by
      apply ENNReal.prod_ne_top
      intro v _
      rw [finiteCompletionUnitMass, finiteCompletionMultiplicativeHaar_unitMass]
      exact ENNReal.ofReal_ne_top
    rw [← ENNReal.ofReal_toReal hfin, ENNReal.toReal_prod,
      prod_finiteCompletionMultiplicativeHaar_unitMass E hoff]

end Masullo
