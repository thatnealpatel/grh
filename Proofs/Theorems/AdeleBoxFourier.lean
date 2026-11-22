module

public import Theorems.AdeleTraceCharacter
public import Theorems.AdeleRestrictedProductHaar
public import Lemmas.FiniteBoxStageFourier

import Mathlib.MeasureTheory.Integral.Prod

/-! # The adelic Fourier integral for a translated finite box

The conjugated kernel and the tensor of local indicators come from
Masullo's (2.2.4.32), PDF p. 92. That display assumes a compactly supported
Archimedean factor and prints the finite indicator at the frequency. For
this integral the indicator restricts the integration variable. The
cofinal stage comaps from the restricted-product prescription (before
Definition A.3.1.2, p. 556) and the corrected signs in `AdeleTraceCharacter`
let us prove the product identity for a Schwartz factor, at every diagonal
frequency. This does not identify the counting-normalized quotient measure
of Definition A.3.1.1, p. 555. Source readings are provisional, based on the
pinned Markdown and numbered PDF layout.
-/

open IsDedekindDomain MeasureTheory NumberField Set
open scoped Classical ComplexConjugate Masullo.AdeleStage SchwartzMap

namespace Masullo

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

local notation "A" => AdeleRing (𝓞 K) K
local notation "F" => FiniteAdeleRing (𝓞 K) K
local notation "V" => HeightOneSpectrum (𝓞 K)
local notation "E∞" => mixedEmbedding.euclidean.mixedSpace K

/-- A Schwartz function at infinity times a translated finite-box indicator. -/
@[expose] public def adeleBoxTensor (φ : 𝓢(E∞, ℂ)) (a : F) (g : Fˣ) (z : A) : ℂ :=
  φ ((archimedeanEuclideanToAdele K).symm z.1) *
    (finiteAdeleBox a g).indicator (fun _ ↦ (1 : ℂ)) z.2

/-- The global Fourier kernel on the actual adeles, sampled at the diagonal. -/
@[expose] public def adeleBoxFourierIntegrand (φ : 𝓢(E∞, ℂ)) (a : F) (g : Fˣ) (y : K) (z : A) : ℂ :=
  adeleBoxTensor φ a g z * conj (numberFieldAdeleAddChar (z * algebraMap K A y))

/-- Integrability and Fourier factorization for any measure with the prescribed
cofinal stage comaps. Existence of such a Haar measure is proved in
`exists_adeleRestrictedProductHaar`. There is no nonzero-frequency premise. -/
public theorem adeleBox_fourier_integral (μ : Measure A) (E : Finset V)
    (hμ : ∀ S : Finset V, E ⊆ S →
      μ.comap (adeleFiniteStageEmbedding K S) = adeleFiniteStageHaar K S)
    (φ : 𝓢(E∞, ℂ)) (a : F) (g : Fˣ) (y : K) :
    Integrable (adeleBoxFourierIntegrand φ a g y) μ ∧
      (∫ z, adeleBoxFourierIntegrand φ a g y z ∂μ) =
        archimedeanTraceFourier K φ (archimedeanEuclideanEmbedding K y) *
          ∏ᶠ v, finiteBoxLocalFourier a g y v := by
  obtain ⟨S, hES, hS⟩ := exists_finiteBoxStageConditions a g y E
  let := adeleFiniteStageOutside_isProbabilityMeasure K S hS.mass
  let j := adeleFiniteStageEmbedding K S
  let H := adeleBoxFourierIntegrand φ a g y
  have hj : MeasurableEmbedding (j : AdeleFiniteStage K S → A) :=
    measurableEmbedding_adeleFiniteStageEmbedding K S
  -- The finite box is contained in this stage, so restricting loses no mass of the integrand.
  have hzero : ∀ z ∉ range j, H z = 0 := by
    intro z hz
    have hz' : z.2 ∉ finiteAdeleBox a g :=
      fun h ↦ hz (finiteAdeleBox_preimage_snd_subset_stage a g S hS.center hS.scale h)
    simp [H, adeleBoxFourierIntegrand, adeleBoxTensor, hz']
  have hi : (range j).indicator H = H := by
    funext z
    by_cases hz : z ∈ range j
    · exact indicator_of_mem hz _
    · rw [indicator_of_notMem hz, hzero z hz]
  have hr : μ.restrict (range j) = (adeleFiniteStageHaar K S).map j := by
    rw [← hj.map_comap μ, hμ S hES]
  -- On the product stage the actual conjugated character splits into the two kernels.
  have hcomp (b : AdeleFiniteStage K S) : H (j b) =
      archimedeanAdeleFourierIntegrand K φ y b.1 *
        finiteAdeleBoxFourierKernel a g y (j (0, b.2)).2 := by
    have hfst : (j b).1 = b.1 := adeleFiniteStageEmbedding_infinite K S b
    have hsnd : (j b).2 = (j (0, b.2)).2 := adeleFiniteStageEmbedding_finite_eq_zero S b
    simp only [H, adeleBoxFourierIntegrand, adeleBoxTensor, archimedeanAdeleFourierIntegrand,
      finiteAdeleBoxFourierKernel]
    change (φ ((archimedeanEuclideanToAdele K).symm (j b).1) *
          (finiteAdeleBox a g).indicator (fun _ ↦ (1 : ℂ)) (j b).2) *
        conj (numberFieldInfiniteAdeleAddChar K ((j b).1 * algebraMap K (InfiniteAdeleRing K) y) *
          numberFieldFiniteAdeleAddChar ((j b).2 * algebraMap K F y)) =
      (φ ((archimedeanEuclideanToAdele K).symm b.1) *
        conj (numberFieldInfiniteAdeleAddChar K (b.1 * algebraMap K (InfiniteAdeleRing K) y))) *
      ((finiteAdeleBox a g).indicator (fun _ ↦ (1 : ℂ)) (j (0, b.2)).2 *
        conj (numberFieldFiniteAdeleAddChar ((j (0, b.2)).2 * algebraMap K F y)))
    rw [hfst, hsnd, map_mul]
    ac_rfl
  let f := archimedeanAdeleFourierIntegrand K φ y
  let k := fun b ↦ finiteAdeleBoxFourierKernel a g y (j (0, b)).2
  have hfun : (fun b : AdeleFiniteStage K S ↦ H (j b)) =
      (fun b ↦ f b.1 * k b.2) := funext hcomp
  obtain ⟨hf, hfi⟩ := finiteAdeleBox_stage_fourier a g y S hS
  have hArch := integrable_archimedeanAdeleFourierIntegrand K φ y
  constructor
  · change Integrable H μ
    rw [← hi, integrable_indicator_iff (hj.measurableSet_range), IntegrableOn, hr,
      hj.integrable_map_iff]
    change Integrable (fun b : AdeleFiniteStage K S ↦ H (j b)) _
    rw [hfun, adeleFiniteStageHaar]
    have hp := hArch.mul_prod hf
    exact hp
  · change (∫ z, H z ∂μ) = _
    rw [← hi, integral_indicator hj.measurableSet_range, hr, hj.integral_map]
    change (∫ b : AdeleFiniteStage K S, H (j b) ∂adeleFiniteStageHaar K S) = _
    rw [hfun, adeleFiniteStageHaar, integral_prod_mul f k]
    exact congrArg₂ (· * ·) (archimedeanAdeleFourierIntegrand_integral K φ y) hfi

/-- One regular Haar measure with the prescribed local scales satisfies the
factorization and integrability simultaneously for every translated box and
Schwartz factor. Its defining comaps are retained in the statement. -/
public theorem exists_adeleBox_fourier_integral :
    ∃ (E : Finset V) (μ : Measure A), μ.IsAddHaarMeasure ∧ μ.Regular ∧
      (∀ S : Finset V, E ⊆ S →
        μ.comap (adeleFiniteStageEmbedding K S) = adeleFiniteStageHaar K S) ∧
      ∀ (φ : 𝓢(E∞, ℂ)) (a : F) (g : Fˣ) (y : K),
        Integrable (adeleBoxFourierIntegrand φ a g y) μ ∧
          (∫ z, adeleBoxFourierIntegrand φ a g y z ∂μ) =
            archimedeanTraceFourier K φ (archimedeanEuclideanEmbedding K y) *
              ∏ᶠ v, finiteBoxLocalFourier a g y v := by
  obtain ⟨E, hE⟩ := exists_finiteCompletionIntegerMass_exceptions K
  have hmass (v : V) (hv : v ∉ E) : finiteCompletionIntegerMass K v = 1 := by
    by_contra hne
    exact hv ((hE v).mpr hne)
  obtain ⟨μ, hhaar, hreg, hμ, _⟩ := exists_adeleRestrictedProductHaar K E hmass
  have hcomap := (hμ μ).mp rfl
  exact ⟨E, μ, hhaar, hreg, hcomap, adeleBox_fourier_integral μ E hcomap⟩

end

end Masullo
