module

public import Lemmas.AdeleFourier
public import Theorems.AdeleRestrictedProductHaar
public import Lemmas.FiniteBoxStageFourier

import Mathlib.MeasureTheory.Integral.Prod

/-! # The adelic Fourier integral for a translated finite box

Masullo's (2.2.4.32), PDF p. 92, supplies the conjugated kernel and tensor
shape, but assumes a compactly supported Archimedean factor and prints the
finite test at the frequency. Here it restricts the integration variable;
the signs are those of the corrected `AdeleTraceCharacter`. The stage comaps
implement the local Haar prescription at Definition A.3.1.2, p. 556, and the
local box integrals extend the integer-ring calculation of Example A.3.1.10,
p. 558. The resulting product at actual adelic frequencies supplies a
Fourier input to the use of (2.2.3.4) for the transformed test in (2.2.3.7),
p. 83. It does not prove the fixed-ideal estimate (2.2.3.8) or either theta
bound. Source readings are provisional, from pinned Markdown and PDF layout.
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

/-- Exact Fourier factorization at every actual adelic frequency, under the
same cofinal comap hypotheses as the diagonal Poisson theorem. -/
public theorem adeleBox_fourier_at (μ : Measure A) (E : Finset V)
    (hμ : ∀ S : Finset V, E ⊆ S →
      μ.comap (adeleFiniteStageEmbedding K S) = adeleFiniteStageHaar K S)
    (φ : 𝓢(E∞, ℂ)) (a : F) (g : Fˣ) (y : A) :
    Integrable (fun z : A ↦ adeleBoxTensor φ a g z * conj (numberFieldAdeleAddChar (z * y))) μ ∧
      adeleFourier μ (adeleBoxTensor φ a g) y =
        archimedeanTraceFourier K φ ((archimedeanEuclideanToAdele K).symm y.1) *
          ∏ᶠ v : V, finiteBoxLocalFourierAt a g v (y.2 v) := by
  -- Enlarge the stage to include the finite exceptions of this actual frequency.
  obtain ⟨S, hES, hS⟩ := exists_finiteBoxStageConditionsAt a g y.2 E
  let := adeleFiniteStageOutside_isProbabilityMeasure K S hS.mass
  let j := adeleFiniteStageEmbedding K S
  let H (z : A) := adeleBoxTensor φ a g z * conj (numberFieldAdeleAddChar (z * y))
  have hj : MeasurableEmbedding (j : AdeleFiniteStage K S → A) :=
    measurableEmbedding_adeleFiniteStageEmbedding K S
  -- The spatial box is contained in the stage; the integrand is unchanged by restriction.
  have hi : (range j).indicator H = H := by
    funext z
    by_cases hz : z ∈ range j
    · exact indicator_of_mem hz _
    · have hz' : z.2 ∉ finiteAdeleBox a g :=
        fun h ↦ hz (finiteAdeleBox_preimage_snd_subset_stage a g S hS.center hS.scale h)
      rw [indicator_of_notMem hz]
      simp [H, adeleBoxTensor, hz']
  have hr : μ.restrict (range j) = (adeleFiniteStageHaar K S).map j := by
    rw [← hj.map_comap μ, hμ S hES]
  -- On the actual product stage, the conjugated global character splits into two kernels.
  let f := archimedeanAdeleFourierIntegrandAt K φ y.1
  let k := fun b ↦ finiteAdeleBoxFourierKernelAt a g y.2 (j (0, b)).2
  have hfun : (fun b : AdeleFiniteStage K S ↦ H (j b)) = (fun b ↦ f b.1 * k b.2) := by
    funext b
    change (φ ((archimedeanEuclideanToAdele K).symm (j b).1) *
          (finiteAdeleBox a g).indicator (fun _ ↦ (1 : ℂ)) (j b).2) *
        conj (numberFieldInfiniteAdeleAddChar K ((j b).1 * y.1) *
          numberFieldFiniteAdeleAddChar ((j b).2 * y.2)) =
      (φ ((archimedeanEuclideanToAdele K).symm b.1) *
        conj (numberFieldInfiniteAdeleAddChar K (b.1 * y.1))) *
      ((finiteAdeleBox a g).indicator (fun _ ↦ (1 : ℂ)) (j (0, b.2)).2 *
        conj (numberFieldFiniteAdeleAddChar ((j (0, b.2)).2 * y.2)))
    rw [adeleFiniteStageEmbedding_infinite K S b, adeleFiniteStageEmbedding_finite_eq_zero S b,
      map_mul]
    ac_rfl
  obtain ⟨hf, hfi⟩ := finiteAdeleBox_stage_fourier_at a g y.2 S hS
  have hArch := integrable_archimedeanAdeleFourierIntegrandAt K φ y.1
  -- Transfer integrability and integrate on the product of the stage measures.
  constructor
  · change Integrable H μ
    rw [← hi, integrable_indicator_iff hj.measurableSet_range, IntegrableOn, hr,
      hj.integrable_map_iff]
    change Integrable (fun b : AdeleFiniteStage K S ↦ H (j b)) _
    rw [hfun, adeleFiniteStageHaar]
    exact hArch.mul_prod hf
  · change (∫ z, H z ∂μ) = _
    rw [← hi, integral_indicator hj.measurableSet_range, hr, hj.integral_map]
    change (∫ b : AdeleFiniteStage K S, H (j b) ∂adeleFiniteStageHaar K S) = _
    rw [hfun, adeleFiniteStageHaar, integral_prod_mul f k]
    exact congrArg₂ (· * ·) (archimedeanAdeleFourierIntegrandAt_integral K φ y.1) hfi

/-- The original diagonal Fourier factorization, including at frequency zero. -/
public theorem adeleBox_fourier_integral (μ : Measure A) (E : Finset V)
    (hμ : ∀ S : Finset V, E ⊆ S →
      μ.comap (adeleFiniteStageEmbedding K S) = adeleFiniteStageHaar K S)
    (φ : 𝓢(E∞, ℂ)) (a : F) (g : Fˣ) (y : K) :
    Integrable (adeleBoxFourierIntegrand φ a g y) μ ∧
      (∫ z, adeleBoxFourierIntegrand φ a g y z ∂μ) =
        archimedeanTraceFourier K φ (archimedeanEuclideanEmbedding K y) *
          ∏ᶠ v, finiteBoxLocalFourier a g y v := by
  have h := adeleBox_fourier_at μ E hμ φ a g (algebraMap K A y)
  rw [AdeleRing.algebraMap_fst_def, ← euclideanToAdele_embedding K y,
    ContinuousAddEquiv.symm_apply_apply] at h
  exact h

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
