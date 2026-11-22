module

public import Theorems.DiscriminantNormalizedIdeleHaar
import Theorems.FiniteHeckeRamification

/-! # The discriminant-normalized Gaussian pairing above one

Definition 3.4.3.2 and the following paragraph, PDF p. 152, use a Gaussian
pairing to define the completion. For the restricted-product Haar of
(A.3.2.2) and (A.3.2.5), p. 560, we evaluate that pairing with the
corrected complex angular weight in `ideleHeckeGaussian`. The raw integral
retains the actual finite unit masses omitted in a unit-mass Euler
normalization. This is not the meromorphic eigendistribution identity
(3.4.3.15), p. 153, or a comparison with the quotient volume (A.3.2.1).
Source reading: Provisional, from the pinned Markdown and numbered PDF layout.
-/

open IsDedekindDomain MeasureTheory NumberField
open scoped Masullo

namespace Masullo

variable {K : Type*} [Field K] [NumberField K]

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

/-- A single Gaussian tensor pairs absolutely with a unitary Hecke character
for every `Re s > 1` on the discriminant-normalized multiplicative Haar
measure. Its integral equals the completed Euler product times the inverse
square root of the absolute field discriminant. -/
public theorem exists_discriminantNormalizedIdeleHeckeGaussian_zetaIntegral
    (χ : HeckeCharacter (𝓞 K) K) (hχ : ∀ a : IdeleClassGroup (𝓞 K) K, ‖χ a‖ = 1) :
    ∃ (T : Finset V) (μ : Measure I), μ.IsHaarMeasure ∧ μ.Regular ∧
      (∀ v ∉ T, χ.IsUnramifiedAt v ∧ multiplicity v.asIdeal D = 0) ∧
      (∀ S : Finset V, (∀ v ∉ S, multiplicity v.asIdeal D = 0) →
        μ.comap (ideleFiniteStageEmbedding K S) =
          ideleFiniteStageProduct K (fun v ↦ archimedeanCompletionHaar v)
            (fun v ↦ finiteCompletionMultiplicativeHaar v) S) ∧
      ∀ s : ℂ, 1 < s.re →
        let g (a : I) := ideleHeckeGaussian χ hχ T a *
          χ (QuotientGroup.mk' (IdeleGroup.principalSubgroup (𝓞 K) K) a) *
          (‖(a : AdeleRing (𝓞 K) K)‖ : ℂ) ^ s
        Integrable g μ ∧ (∫ a, g a ∂μ) =
          (((Real.sqrt ((discr K).natAbs : ℝ))⁻¹ : ℝ) : ℂ) * completedHeckeEulerProduct χ hχ s := by
  classical
  -- Include the two independent finite exceptional sets before choosing `s`.
  obtain ⟨Sχ, hSχ⟩ := exists_finset_isUnramifiedAt χ
  let E := finite_differentIdeal_multiplicity_support (K := K)
  let T := Sχ ∪ E.toFinset
  have hT (v : V) (hv : v ∉ T) : χ.IsUnramifiedAt v ∧ multiplicity v.asIdeal D = 0 := by
    refine ⟨hSχ v (fun h ↦ hv (Finset.mem_union_left _ h)), ?_⟩
    by_contra h
    exact hv (Finset.mem_union_right _ (E.mem_toFinset.mpr h))
  obtain ⟨μ, hμ, hreg, hstage, _⟩ := exists_discriminantNormalizedIdeleHaar K
  have hprod (S : Finset V) (hS : ∀ v ∉ S, multiplicity v.asIdeal D = 0) :=
    (hstage μ).mp rfl S hS
  refine ⟨T, μ, hμ, hreg, hT, hprod, fun s hs ↦ ?_⟩
  have hzero : ∀ v ∉ T, multiplicity v.asIdeal D = 0 := fun v hv ↦ (hT v hv).2
  have hunit (v : V) (hv : v ∉ T) :=
    finiteCompletionMultiplicativeHaar_unitMass_eq_one v (hzero v hv)
  have hval := ideleHeckeGaussian_zetaIntegral χ hχ (fun v ↦ finiteCompletionMultiplicativeHaar v)
    T hunit (fun v hv ↦ (hT v hv).1) μ
    (fun S hS ↦ hprod S (fun v hv ↦ hzero v (fun h ↦ hv (hS h)))) hs
  -- The product of the finite unit masses is the global discriminant factor.
  have hscale := congrArg Complex.ofReal (prod_finiteCompletionMultiplicativeHaar_unitMass T hzero)
  rw [Complex.ofReal_prod] at hscale
  dsimp only at hval ⊢
  rw [hscale] at hval
  exact hval

end Masullo
