module

public import Theorems.IdeleHeckeGaussian
import all Theorems.ComplexGaussianMellin
import Theorems.IdeleFiniteStageZetaDensity
import all Theorems.RealGaussianMellin
import Lemmas.FiniteHeckeRestriction
import Lemmas.FiniteLocalNormShell
import Lemmas.IdeleFiniteStageMeasure
import all Lemmas.IdeleStageNormCoordinates

/-! # Borel measurability of the idelic Hecke Gaussian -/

open IsDedekindDomain MeasureTheory NumberField InfinitePlace.Completion
open scoped Classical

namespace Masullo

variable {K : Type*} [Field K] [NumberField K]

local notation "V" => HeightOneSpectrum (𝓞 K)
local notation "I" => IdeleGroup (𝓞 K) K
local notation "F" v => HeightOneSpectrum.adicCompletion K v

private theorem continuous_gaussianFiniteCoordinate (v : V) :
    Continuous (fun a : I ↦ ideleFiniteCoordinate K a v) := by
  unfold ideleFiniteCoordinate
  apply Continuous.units_map
  exact (RestrictedProduct.continuous_eval v).comp continuous_snd

private theorem continuous_gaussianInfiniteCoordinate (v : InfinitePlace K) :
    Continuous (fun a : I ↦ ideleInfiniteCoordinates K a v) := by
  unfold ideleInfiniteCoordinates
  apply Continuous.units_map
  exact (continuous_apply v).comp continuous_fst

private theorem measurable_gaussianFiniteTest (χ : HeckeCharacter (𝓞 K) K) (v : V)
    [MeasurableSpace (F v)ˣ] [BorelSpace (F v)ˣ] : Measurable (finiteHeckeGaussian χ v) := by
  unfold finiteHeckeGaussian
  by_cases hv : χ.IsUnramifiedAt v
  · simp only [ite_eq_left hv]
    exact Measurable.ite ((isClosed_le Units.continuous_val.norm
      continuous_const).measurableSet) measurable_const measurable_const
  · simp only [ite_eq_right hv]
    exact (continuous_finiteHeckeRestriction χ v).measurable.inv.indicator
      (measurableSet_finiteLocalUnitSet v)

variable [ma : ∀ v : InfinitePlace K, MeasurableSpace v.Completionˣ]
  [ba : ∀ v : InfinitePlace K, BorelSpace v.Completionˣ]
  (χ : HeckeCharacter (𝓞 K) K) (hχ : ∀ x : IdeleClassGroup (𝓞 K) K, ‖χ x‖ = 1)

private theorem measurable_gaussianInfiniteTest (v : InfinitePlace K) :
    Measurable (archimedeanHeckeGaussian χ hχ v) := by
  unfold archimedeanHeckeGaussian
  by_cases hv : v.IsReal
  · simp only [dite_eq_left hv]
    apply Measurable.comp (g := realZetaGaussian _)
    · unfold realZetaGaussian
      fun_prop
    · exact ((isometry_extensionEmbeddingOfIsReal hv).continuous.comp Units.continuous_val).measurable
  · simp only [dite_eq_right hv]
    apply Measurable.comp (g := complexZetaGaussian _)
    · unfold complexZetaGaussian
      split_ifs <;> fun_prop
    · exact ((isometry_extensionEmbedding v).continuous.comp Units.continuous_val).measurable

/-- The Gaussian tensor is Borel measurable on the ideles for every exceptional set `T`. -/
public theorem measurable_ideleHeckeGaussian
    [mf : ∀ v : V, MeasurableSpace (F v)ˣ] [bf : ∀ v : V, BorelSpace (F v)ˣ]
    [MeasurableSpace I] [BorelSpace I] (T : Finset V) :
    Measurable (ideleHeckeGaussian χ hχ T) := by
  -- The off-stage condition is a countable intersection of local closed norm bounds.
  let : Countable V := countable_ideleFinitePlaces K
  have htail : MeasurableSet {a : I | ∀ v ∉ T, ‖(a : AdeleRing (𝓞 K) K).2 v‖ ≤ 1} := by
    have h := MeasurableSet.iInter fun v : {v : V // v ∉ T} ↦
      (isClosed_le ((Units.continuous_val.comp (continuous_gaussianFiniteCoordinate v.val)).norm)
        (continuous_const (y := (1 : ℝ)))).measurableSet (α := I)
    convert h using 1
    ext a
    simp only [Set.mem_ofPred_eq, Set.mem_iInter, Subtype.forall, Function.comp_apply,
      ideleFiniteCoordinate_val]
  unfold ideleHeckeGaussian ideleZetaTest
  refine Measurable.ite htail (Measurable.mul ?_ ?_) measurable_const
  · exact Finset.measurable_prod _ fun v _ ↦
      (measurable_gaussianInfiniteTest χ hχ v).comp (continuous_gaussianInfiniteCoordinate v).measurable
  · exact Finset.measurable_prod T fun v _ ↦
      (measurable_gaussianFiniteTest χ v).comp (continuous_gaussianFiniteCoordinate v).measurable

end Masullo
