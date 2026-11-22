module

public import Theorems.IdeleUnitWindowMass

import Lemmas.HaarLogSplit

/-! # Haar decomposition by idelic log norm

In §A.3.3.1, PDF p. 561, Masullo takes the product decomposition of Haar
measure in the coordinates from Lemma A.2.2.9, p. 547. We fix the scale of
the norm-one factor by Haar uniqueness with Lebesgue measure on the log
line, not by restriction of ambient Haar to the norm-one subgroup. Its
mass on the Borel fundamental domain follows from the independently
computed local-product strip mass, using a unit-length log interval.
This does not yet identify the counting-normalized quotient measure of
(D.1.2.1), p. 747. Source reading: Provisional, from Markdown and numbered
PDF text, not rendered pages.
-/

open IsDedekindDomain MeasureTheory NumberField Set
open NumberField.Units (regulator torsionOrder)
open NumberField.Units.dirichletUnitTheorem (w₀)
open scoped ENNReal Masullo

namespace Masullo

variable {K : Type*} [Field K] [NumberField K]

local notation "V" => HeightOneSpectrum (𝓞 K)
local notation "I" => IdeleGroup (𝓞 K) K
local notation "I₁" => ideleNormOne (K := K)
local notation "L" => Multiplicative ℝ
local notation "D" => differentIdeal ℤ (𝓞 K)
local notation "W" => (w₀ : InfinitePlace K)
local notation "σ" => ideleLogSplit (ideleLogSection W) (ideleLogNorm_section W)

variable [MeasurableSpace (IdeleGroup (𝓞 K) K)] [BorelSpace (IdeleGroup (𝓞 K) K)]
  [MeasurableSpace (ideleNormOne (K := K))] [BorelSpace (ideleNormOne (K := K))]

/-- For any continuous homomorphic log section, the transport of upstairs Haar
has Lebesgue measure on the log line and a Haar measure on the actual norm-one group. -/
public theorem ideleLogSplit_haar (s : L →ₜ* I) (hs : ∀ x, ideleLogNorm (s x) = x)
    (μ : Measure I) [μ.IsHaarMeasure] :
    ∃ ν : Measure I₁, ν.IsHaarMeasure ∧ μ.map (ideleLogSplit s hs).symm = logVolume.prod ν := by
  let : SecondCountableTopology I := secondCountable_ideleGroup K
  let : SecondCountableTopology I₁ :=
    (Topology.IsInducing.subtypeVal (t := (I₁ : Set I))).secondCountableTopology
  exact logVolume_prod_of_split_haar (ideleLogSplit s hs) μ

variable [∀ w : InfinitePlace K, MeasurableSpace w.Completionˣ]
  [∀ w : HeightOneSpectrum (𝓞 K), MeasurableSpace (w.adicCompletion K)ˣ]
  [∀ w : HeightOneSpectrum (𝓞 K), MeasurableSpace (w.adicCompletionIntegers K)ˣ]
  [∀ w : InfinitePlace K, BorelSpace w.Completionˣ]
  [∀ w : HeightOneSpectrum (𝓞 K), BorelSpace (w.adicCompletion K)ˣ]
  [∀ w : HeightOneSpectrum (𝓞 K), BorelSpace (w.adicCompletionIntegers K)ˣ]

/-- The norm-one Haar factor measures the fundamental domain by the local-product
mass of a log strip of length one. The normalization premise uses the stage
restriction at one stage containing the different support. -/
public theorem measure_ideleFundamentalDomain_of_logSplit (μ : Measure I) [μ.IsMulLeftInvariant]
    (ν : Measure I₁) [SFinite ν] (hν : μ.map (σ).symm = logVolume.prod ν)
    (S : Finset V) (hS : ∀ w ∉ S, multiplicity w.asIdeal D = 0)
    (hstage : μ.comap (ideleFiniteStageEmbedding K S) =
      ideleFiniteStageProduct K (fun w ↦ archimedeanCompletionHaar w)
        (fun w ↦ finiteCompletionMultiplicativeHaar w) S)
    (v : InfinitePlace K) (r : ClassGroup (𝓞 K) → I₁)
    (hr : ∀ p, ideleIdealClassNormOne (r p) = p) :
    let ω := Measure.pi fun w : InfinitePlace K ↦ archimedeanAngularMeasure w
    ν (ideleFundamentalDomain v r) = (classNumber K : ℝ≥0∞) *
      (ENNReal.ofReal (regulator K) * (ω univ / (torsionOrder K : ℝ≥0∞))) *
      ENNReal.ofReal ((Real.sqrt ((discr K).natAbs : ℝ))⁻¹) := by
  intro ω
  let J := Multiplicative.toAdd ⁻¹' Icc (0 : ℝ) 1
  have hJ : MeasurableSet J := measurableSet_Icc.preimage measurable_toAdd
  have hlength : logVolume J = 1 := by
    rw [← Measure.map_apply measurable_toAdd measurableSet_Icc, map_toAdd_logVolume,
      Real.volume_Icc, sub_zero, ENNReal.ofReal_one]
  have hstrip : μ (σ '' (J ×ˢ ideleFundamentalDomain v r)) = ν (ideleFundamentalDomain v r) := by
    let e := (σ).toHomeomorph.toMeasurableEquiv
    let R := J ×ˢ ideleFundamentalDomain v r
    have he : μ.map e.symm = logVolume.prod ν := hν
    calc
      μ (σ '' R) = μ (e.symm ⁻¹' R) := congrArg μ (e.toEquiv.image_eq_preimage_symm R)
      _ = (μ.map e.symm) R := (e.symm.map_apply R).symm
      _ = ν (ideleFundamentalDomain v r) := by
        rw [he, Measure.prod_prod, hlength, one_mul]
  rw [← hstrip, measure_ideleLogSplit_fundamentalDomain μ S hS hstage v r hr hJ, hlength, one_mul]
  exact (mul_assoc _ _ _).symm

end Masullo
