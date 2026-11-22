module

public import Lemmas.IdeleUnitWindowCoordinates
public import Theorems.DiscriminantNormalizedIdeleHaar
public import Theorems.IdeleClassStrip

/-! # The local-product mass of the split unit window

Section A.3.3.1, PDF p. 561, uses the idelic log-norm splitting to give the
mass of the full strip in terms of the prescribed quotient volume. Here we
compute its identity-class piece upstairs, directly from the local product
of (A.3.2.5), p. 560, without invoking the quotient volume. The stage
restriction in `exists_discriminantNormalizedIdeleHaar` implements that
product. The project supplies `image_ideleLogSplit_unitWindow` to transport
the actual window into the stage, and `measure_archimedeanUnitWindowStrip`
to split the Archimedean coordinates without a Jacobian factor.

Source reading: Provisional, from the pinned Markdown and numbered PDF text,
not the rendered pages.
-/

open IsDedekindDomain MeasureTheory NumberField Set TopologicalSpace
open NumberField.Units (regulator torsionOrder)
open NumberField.Units.dirichletUnitTheorem (w₀)
open scoped ENNReal Masullo

namespace Masullo

variable {K : Type*} [Field K] [NumberField K]

local notation "V" => HeightOneSpectrum (𝓞 K)
local notation "I" => IdeleGroup (𝓞 K) K
local notation "L" => Multiplicative ℝ
local notation "D" => differentIdeal ℤ (𝓞 K)
local notation "W" => (w₀ : InfinitePlace K)
local notation "σ" => ideleLogSplit (ideleLogSection W) (ideleLogNorm_section W)

variable [∀ w : InfinitePlace K, MeasurableSpace w.Completionˣ]
  [∀ w : HeightOneSpectrum (𝓞 K), MeasurableSpace (w.adicCompletion K)ˣ]
  [∀ w : HeightOneSpectrum (𝓞 K), MeasurableSpace (w.adicCompletionIntegers K)ˣ]
  [∀ w : InfinitePlace K, BorelSpace w.Completionˣ]
  [∀ w : HeightOneSpectrum (𝓞 K), BorelSpace (w.adicCompletion K)ˣ]
  [∀ w : HeightOneSpectrum (𝓞 K), BorelSpace (w.adicCompletionIntegers K)ˣ]
  [MeasurableSpace (IdeleGroup (𝓞 K) K)] [BorelSpace (IdeleGroup (𝓞 K) K)]

/-- For every Borel log set, the identity-class strip contributes the log
mass times the Archimedean `E₀` mass times the inverse square root of the
absolute discriminant. Only the normalized restriction to one stage
containing the different support is used. The sector place `v` is arbitrary;
the radial section is at the place omitted from the retained logs. -/
public theorem measure_ideleLogSplit_unitWindow (μ : Measure I) (S : Finset V)
    (hS : ∀ w ∉ S, multiplicity w.asIdeal D = 0)
    (hstage : μ.comap (ideleFiniteStageEmbedding K S) =
      ideleFiniteStageProduct K (fun w ↦ archimedeanCompletionHaar w)
        (fun w ↦ finiteCompletionMultiplicativeHaar w) S)
    (v : InfinitePlace K) {J : Set L} (hJ : MeasurableSet J) :
    let ω := Measure.pi fun w : InfinitePlace K ↦ archimedeanAngularMeasure w
    μ (σ '' (J ×ˢ ideleUnitWindow v)) =
      logVolume J * (ENNReal.ofReal (regulator K) * (ω univ / (torsionOrder K : ℝ≥0∞))) *
        ENNReal.ofReal ((Real.sqrt ((discr K).natAbs : ℝ))⁻¹) := by
  intro ω
  -- Pull the actual split window into the stage, with integral units even in S.
  let j := (isOpenEmbedding_ideleFiniteStageEmbedding K S).measurableEmbedding
  rw [image_ideleLogSplit_unitWindow, ← image_ideleStageUnitRectangle _ _ S, ← j.comap_apply,
    hstage, ideleFiniteStageProduct_unitRectangle _ _ _ _ _
      (fun w hw ↦ finiteCompletionMultiplicativeHaar_unitMass_eq_one w (hS w hw))]
  -- The omitted finite factors have mass one; the active unit masses retain the different.
  let μf : (w : V) → Measure (w.adicCompletion K)ˣ := fun w ↦ finiteCompletionMultiplicativeHaar w
  have hfin : (∏ w ∈ S, finiteCompletionUnitMass K μf w) ≠ ∞ := by
    apply ENNReal.prod_ne_top
    intro w _
    rw [finiteCompletionUnitMass, finiteCompletionMultiplicativeHaar_unitMass]
    exact ENNReal.ofReal_ne_top
  have hprod : (∏ w ∈ S, finiteCompletionUnitMass K μf w) =
      ENNReal.ofReal ((Real.sqrt ((discr K).natAbs : ℝ))⁻¹) := by
    rw [← ENNReal.ofReal_toReal hfin, ENNReal.toReal_prod,
      prod_finiteCompletionMultiplicativeHaar_unitMass S hS]
  -- The two Archimedean masses come from the local coordinates, not quotient Haar.
  rw [measure_archimedeanUnitWindowStrip v hJ, measure_archimedeanUnitDomainCoordinates, hprod]

/-- For `T ≥ 1`, the closed positive-radius strip `[1,T]` is represented by
`[0, log T]` in the log coordinate. The formula also holds for real `T`
without this interpretation; `ENNReal.ofReal` gives zero for negative width.
In particular `T = 1` contributes zero. -/
public theorem measure_ideleLogSplit_unitWindow_Icc (μ : Measure I) (S : Finset V)
    (hS : ∀ w ∉ S, multiplicity w.asIdeal D = 0)
    (hstage : μ.comap (ideleFiniteStageEmbedding K S) =
      ideleFiniteStageProduct K (fun w ↦ archimedeanCompletionHaar w)
        (fun w ↦ finiteCompletionMultiplicativeHaar w) S)
    (v : InfinitePlace K) (T : ℝ) :
    let ω := Measure.pi fun w : InfinitePlace K ↦ archimedeanAngularMeasure w
    μ (σ '' ((Multiplicative.toAdd ⁻¹' Icc (0 : ℝ) (Real.log T)) ×ˢ ideleUnitWindow v)) =
      ENNReal.ofReal (Real.log T) * (ENNReal.ofReal (regulator K) * (ω univ / (torsionOrder K : ℝ≥0∞))) *
        ENNReal.ofReal ((Real.sqrt ((discr K).natAbs : ℝ))⁻¹) := by
  intro ω
  rw [measure_ideleLogSplit_unitWindow μ S hS hstage v (measurableSet_Icc.preimage measurable_toAdd),
    ← Measure.map_apply measurable_toAdd measurableSet_Icc, map_toAdd_logVolume,
    Real.volume_Icc, sub_zero]

/-- Sum the normalized unit-window contributions over the disjoint ideal-class
pieces of the full strip in §A.3.3.1. This is still an upstairs measure;
it does not identify the quotient Haar measure. -/
public theorem measure_ideleLogSplit_fundamentalDomain (μ : Measure I) [μ.IsMulLeftInvariant]
    (S : Finset V) (hS : ∀ w ∉ S, multiplicity w.asIdeal D = 0)
    (hstage : μ.comap (ideleFiniteStageEmbedding K S) =
      ideleFiniteStageProduct K (fun w ↦ archimedeanCompletionHaar w)
        (fun w ↦ finiteCompletionMultiplicativeHaar w) S)
    (v : InfinitePlace K) (r : ClassGroup (𝓞 K) → ideleNormOne (K := K))
    (hr : ∀ p, ideleIdealClassNormOne (r p) = p) {J : Set L} (hJ : MeasurableSet J) :
    let ω := Measure.pi fun w : InfinitePlace K ↦ archimedeanAngularMeasure w
    μ (σ '' (J ×ˢ ideleFundamentalDomain v r)) =
      (classNumber K : ℝ≥0∞) *
        (logVolume J * (ENNReal.ofReal (regulator K) * (ω univ / (torsionOrder K : ℝ≥0∞))) *
          ENNReal.ofReal ((Real.sqrt ((discr K).natAbs : ℝ))⁻¹)) := by
  intro ω
  rw [measure_ideleFundamentalDomain_strip_eq_classNumber_mul μ _ _ v r hr hJ,
    measure_ideleLogSplit_unitWindow μ S hS hstage v hJ]

end Masullo
