module

public import Theorems.AdeleBoxFourier

import Lemmas.FiniteIdeleIdealCoordinates

/-! # Diagonal samples of adelic box tensors -/

open IsDedekindDomain MeasureTheory NumberField Set
open scoped Classical ComplexConjugate Masullo.AdeleStage Pointwise SchwartzMap WithZero

namespace Masullo

variable {K : Type*} [Field K] [NumberField K]

local notation "A" => AdeleRing (𝓞 K) K
local notation "F" => FiniteAdeleRing (𝓞 K) K
local notation "V" => HeightOneSpectrum (𝓞 K)
local notation "E∞" => mixedEmbedding.euclidean.mixedSpace K
local notation "K[" v "]" => HeightOneSpectrum.adicCompletion K v
local notation "w[" v "]" => (Valued.v : Valuation K[v] ℤᵐ⁰)

private theorem mem_localBox_iff (a : F) (g : Fˣ) (v : V) (z : K[v]) :
    z ∈ (a v + ·) '' (g.val v • (v.adicCompletionIntegers K : Set K[v])) ↔
      w[v] (z - a v) ≤ w[v] (g.val v) := by
  rw [mem_image]
  constructor
  · rintro ⟨u, hu, rfl⟩
    obtain ⟨t, ht, rfl⟩ := mem_smul_set.mp hu
    rw [add_sub_cancel_left]
    change w[v] (g.val v * t) ≤ w[v] (g.val v)
    rw [map_mul]
    exact mul_le_of_le_one_right zero_le ht
  · intro hz
    have hg : g.val v ≠ 0 := ((FiniteAdeleRing.isUnit_iff.mp g.isUnit).1 v)
    have ht : (z - a v) / g.val v ∈ v.adicCompletionIntegers K := by
      change w[v] ((z - a v) / g.val v) ≤ 1
      rwa [map_div₀, div_le_one₀ (pos_iff_ne_zero.mpr (finiteIdele_valuation_ne_zero g v))]
    refine ⟨z - a v, mem_smul_set.mpr ⟨_, ht, ?_⟩, add_sub_cancel _ _⟩
    exact mul_div_cancel₀ _ hg

/-- The diagonal of a box tensor is the Euclidean Schwartz profile restricted
by the translated valuation inequalities used in lattice Poisson summation. -/
public theorem adeleBoxTensor_diagonal_eq_indicator (φ : 𝓢(E∞, ℂ)) (a : F) (g : Fˣ) (t : K) :
    adeleBoxTensor φ a g (algebraMap K A t) =
      {x : K | ∀ v : V, w[v] (algebraMap K K[v] x - a v) ≤ w[v] (g.val v)}.indicator
        (φ ∘ archimedeanEuclideanEmbedding K) t := by
  let S : Set K := {x | ∀ v : V, w[v] (algebraMap K K[v] x - a v) ≤ w[v] (g.val v)}
  have hS : (algebraMap K A t).2 ∈ finiteAdeleBox a g ↔ t ∈ S := by
    change (∀ v : V, algebraMap K K[v] t ∈ _) ↔ _
    exact forall_congr' fun v ↦ mem_localBox_iff a g v _
  change _ = S.indicator (φ ∘ archimedeanEuclideanEmbedding K) t
  rw [adeleBoxTensor, AdeleRing.algebraMap_fst_def, ← euclideanToAdele_embedding,
    ContinuousAddEquiv.symm_apply_apply]
  by_cases ht : t ∈ S
  · rw [indicator_of_mem ht, indicator_of_mem (hS.mpr ht), mul_one, Function.comp_apply]
  · rw [indicator_of_notMem ht, indicator_of_notMem (mt hS.mp ht), mul_zero]

end Masullo
