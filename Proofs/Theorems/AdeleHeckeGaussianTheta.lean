module

public import Theorems.AdeleHeckeTest
public import Theorems.AdeleBoxThetaInversion
import Lemmas.MixedSchwartzGaussian
import all Lemmas.IdeleStageNormCoordinates

/-! # Theta inversion for the corrected Hecke Gaussian

Definition 3.4.3.2, PDF p. 152, supplies the real parity factors
(3.4.3.3)–(4), the positive complex width and prefactor (3.4.3.5)–(6),
and the finite tests and restricted tensor (3.4.3.7)–(9). The printed
complex monomial has the character's own angular weight. As in
`Theorems.ArchimedeanCompletionGaussian`, we instead use the opposite
weight for the bilinear zeta pairing (3.3.1.7), PDF p. 130.

To apply the pointwise repair of (2.2.3.2), PDF p. 82, we need this
*same* test as a Schwartz factor in the actual additive box span.
`mixedSchwartzGaussian` supplies the Schwartz bounds by scaling an
isotropic Gaussian and multiplying by the coordinate monomials.
We use the very choices already made in `archimedeanHeckeGaussian`,
transport them to the infinite components of each actual idele, and
apply the finite-stage tensor and box-span inversion results.
Source reading: Pinned Markdown and numbered PDF layout; the angular
notation is confirmed by the prior independent rendered angular review.
-/

open IsDedekindDomain MeasureTheory NumberField
open scoped Classical SchwartzMap Masullo.AdeleStage

namespace Masullo

noncomputable section

variable {K : Type*} [Field K] [NumberField K]
variable (χ : HeckeCharacter (𝓞 K) K) (hχ : ∀ x : IdeleClassGroup (𝓞 K) K, ‖χ x‖ = 1)
variable [∀ v : InfinitePlace K, MeasurableSpace v.Completionˣ]
  [∀ v : InfinitePlace K, BorelSpace v.Completionˣ]

local notation "A" => AdeleRing (𝓞 K) K
local notation "J" => IdeleGroup (𝓞 K) K
local notation "V" => HeightOneSpectrum (𝓞 K)
local notation "ι" => algebraMap K A

/-- The additive Archimedean factor with exactly the parity and complex
index used by `archimedeanHeckeGaussian`. `complexZetaGaussian` gives
that index the opposite angular weight in the test. -/
public def archimedeanHeckeSchwartz : 𝓢(mixedEmbedding.euclidean.mixedSpace K, ℂ) :=
  mixedSchwartzGaussian
    (fun v ↦ (realCompletionGaussianPair χ hχ v.property).choose)
    (fun v ↦ (complexCompletionGaussianPair χ hχ v.property).choose)

/-- In the actual completion coordinates, the additive Schwartz factor
restricts to the existing product of Archimedean Gaussian tests. -/
public theorem archimedeanHeckeSchwartz_idele (a : J) :
    archimedeanHeckeSchwartz χ hχ ((archimedeanEuclideanToAdele K).symm (a : A).1) =
      ∏ v, archimedeanHeckeGaussian χ hχ v (ideleInfiniteCoordinates K a v) := by
  rw [archimedeanHeckeSchwartz, mixedSchwartzGaussian_apply, archimedeanEuclideanToAdele_symm_mixed,
    InfiniteAdeleRing.ringEquiv_mixedSpace_apply, InfinitePlace.prod_eq_prod_mul_prod]
  congr 1
  · apply Finset.prod_congr rfl
    intro v _
    rw [archimedeanHeckeGaussian, dite_eq_left v.property]
    rfl
  · apply Finset.prod_congr rfl
    intro v _
    rw [archimedeanHeckeGaussian, dite_eq_right (InfinitePlace.not_isReal_iff_isComplex.mpr v.property)]
    rfl

/-- With the corrected Archimedean factor, the additive tensor of
(3.4.3.9) restricts to the same stage test as the idelic Gaussian. -/
public theorem adeleHeckeTest_archimedeanHeckeSchwartz_coe_idele (S : Finset V) (a : J) :
    adeleHeckeTest χ S (archimedeanHeckeSchwartz χ hχ) (a : A) = ideleHeckeGaussian χ hχ S a := by
  exact adeleHeckeTest_coe_idele χ S (archimedeanHeckeSchwartz χ hχ)
    (fun x ↦ ∏ v, archimedeanHeckeGaussian χ hχ v (x v)) (archimedeanHeckeSchwartz_idele χ hχ) a

/-- At every actual idele, the corrected Hecke test satisfies the pointwise
identity (2.2.3.2) for the stage-normalized additive Haar. Both full
diagonal series are absolutely summable, and both zero terms are retained.
No unramifiedness off `S` is needed for the equality of stage tests. -/
public theorem adeleHeckeGaussian_theta_inversion (μ : Measure A) [μ.IsAddHaarMeasure]
    (E : Finset V) (hμ : ∀ T : Finset V, E ⊆ T →
      μ.comap (adeleFiniteStageEmbedding K T) = adeleFiniteStageHaar K T)
    (S : Finset V) (a : J) :
    let f := adeleHeckeTest χ S (archimedeanHeckeSchwartz χ hχ)
    Summable (fun t : K ↦ ‖f ((a : A) * ι t)‖) ∧
      Summable (fun t : K ↦ ‖adeleFourier μ f ((↑(a⁻¹) : A) * ι t)‖) ∧
      (∑' t : Kˣ, ideleHeckeGaussian χ hχ S (a * IdeleGroup.unitEmbedding (𝓞 K) K t)) =
        (ideleNorm a)⁻¹ • (∑' t : Kˣ, adeleFourier μ f ((↑(a⁻¹) : A) * ι (t : K))) +
        (ideleNorm a)⁻¹ • adeleFourier μ f 0 - f 0 := by
  let f := adeleHeckeTest χ S (archimedeanHeckeSchwartz χ hχ)
  have hf : f ∈ adeleBoxSpan K := adeleHeckeTest_mem_adeleBoxSpan χ S _
  obtain ⟨hs, hs', hθ⟩ := adeleBoxSpan_theta_inversion μ E hμ hf a
  refine ⟨hs, hs', ?_⟩
  calc
    _ = ∑' t : Kˣ, f ((a : A) * ι (t : K)) := by
      apply tsum_congr
      intro t
      exact (adeleHeckeTest_archimedeanHeckeSchwartz_coe_idele χ hχ S
        (a * IdeleGroup.unitEmbedding (𝓞 K) K t)).symm
    _ = _ := hθ

end

end Masullo
