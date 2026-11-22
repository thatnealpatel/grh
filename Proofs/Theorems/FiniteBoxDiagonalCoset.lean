module

public import Lemmas.FiniteAdeleDenominators
public import Lemmas.FiniteIdeleIdealMembership

/-! # The diagonal in a translated finite adelic box

For the adelic Poisson step of Masullo, Theorem 2.2.3.2, PDF p. 82, we need
an explicit index set for a translated finite box before using Archimedean
Poisson summation. Lemma 2.2.2.1(3), PDF pp. 78–80, gives a fractional-ideal
bound on supported indices, not the exact translated coset. Lemma A.2.1.2(1),
PDF p. 545, states a covering whose finite projection gives the unit-radius
existence case. Here a common denominator and the checked integral
congruences give a point for every radius idele. Subtracting that point leaves
the homogeneous box, whose diagonal is the ideal of the finite idele.
-/

open Ideal IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField
open scoped nonZeroDivisors WithZero

namespace Masullo

variable {K : Type*} [Field K] [NumberField K]

local notation "V" => HeightOneSpectrum (𝓞 K)
local notation "F" => FiniteAdeleRing (𝓞 K) K
local notation "J" => FractionalIdeal (𝓞 K)⁰ K
local notation "w[" v "]" => (Valued.v : Valuation (HeightOneSpectrum.adicCompletion K v) ℤᵐ⁰)
local notation "k[" v "]" => algebraMap K (HeightOneSpectrum.adicCompletion K v)
local notation "j[" v "]" => algebraMap (𝓞 K) (HeightOneSpectrum.adicCompletion K v)
local notation "i[" v "]" => algebraMap (𝓞 K) (HeightOneSpectrum.adicCompletionIntegers K v)

private theorem exists_finiteBox_diagonal (a : F) (g : Fˣ) :
    ∃ x₀ : K, ∀ v : V, w[v] (k[v] x₀ - a v) ≤ w[v] (g.val v) := by
  obtain ⟨d₁, hd₁, ha⟩ := exists_finiteAdele_clearDenominator a
  obtain ⟨d₂, hd₂, hg⟩ := exists_finiteAdele_clearDenominator g.val
  let d := d₁ * d₂
  have hd : d ≠ 0 := mul_ne_zero hd₁ hd₂
  have tint (v : V) (z : 𝓞 K) : w[v] (j[v] z) ≤ 1 := (i[v] z).property
  have ha' (v : V) : w[v] (j[v] d * a v) ≤ 1 := by
    rw [show d = d₁ * d₂ from rfl, (j[v]).map_mul, mul_right_comm, w[v].map_mul]
    exact mul_le_mul (ha v) (tint v d₂) zero_le zero_le_one
  have hg' (v : V) : w[v] (j[v] d * g.val v) ≤ 1 := by
    rw [show d = d₁ * d₂ from rfl, (j[v]).map_mul, mul_assoc, w[v].map_mul]
    exact mul_le_mul (tint v d₁) (hg v) zero_le zero_le_one
  let δ := Units.mk0 (algebraMap (𝓞 K) K d)
    (map_ne_zero_of_mem_nonZeroDivisors _ (FaithfulSMul.algebraMap_injective (𝓞 K) K)
      (mem_nonZeroDivisors_of_ne_zero hd))
  let g' := FiniteAdeleRing.unitEmbedding (𝓞 K) K δ * g
  have hg'apply (v : V) : g'.val v = j[v] d * g.val v := by
    change (FiniteAdeleRing.unitEmbedding (𝓞 K) K δ).val v * g.val v = _
    rw [FiniteAdeleRing.unitEmbedding_apply, FiniteAdeleRing.algebraMap_apply]
    rfl
  obtain ⟨I, hI, -, hcoord⟩ := exists_ideal_finiteIdeleIdeal_of_integral g' (fun v ↦ by
    rw [hg'apply]; exact hg' v)
  let a' (v : V) : v.adicCompletionIntegers K := ⟨j[v] d * a v, ha' v⟩
  obtain ⟨z, hz⟩ := exists_ringOfIntegers_sub_mem_finiteCompletionIdeal I hI a'
  refine ⟨(algebraMap (𝓞 K) K z) / δ.val, fun v ↦ ?_⟩
  have hs := (hcoord v _).mp (hz v)
  rw [hg'apply] at hs
  change w[v] (j[v] z - j[v] d * a v) ≤ w[v] (j[v] d * g.val v) at hs
  have hdv : j[v] d ≠ 0 := map_ne_zero_of_mem_nonZeroDivisors _
    (FaithfulSMul.algebraMap_injective (𝓞 K) (HeightOneSpectrum.adicCompletion K v))
    (mem_nonZeroDivisors_of_ne_zero hd)
  rw [map_div₀]
  change w[v] (j[v] z / j[v] d - a v) ≤ _
  apply le_of_mul_le_mul_left _ (pos_iff_ne_zero.mpr ((map_ne_zero w[v]).mpr hdv))
  rw [← w[v].map_mul, ← w[v].map_mul, mul_sub, mul_div_cancel₀ _ hdv]
  exact hs

/-- The full diagonal pullback of the translated box `a + g ∏ O_v` is a
nonempty translate of the fractional ideal of `g`. The inequalities use the
multiplicative local valuations, including at places where the radius is one. -/
public theorem exists_finiteBox_diagonalCoset (a : F) (g : Fˣ) :
    ∃ x₀ : K, ∀ x : K, (∀ v : V, w[v] (k[v] x - a v) ≤ w[v] (g.val v)) ↔
      x - x₀ ∈ (finiteIdeleIdeal K g : J) := by
  obtain ⟨x₀, hx₀⟩ := exists_finiteBox_diagonal a g
  refine ⟨x₀, fun x ↦ ?_⟩
  rw [mem_finiteIdeleIdeal_iff]
  constructor
  · intro hx v
    rw [map_sub, ← sub_sub_sub_cancel_right (k[v] x) (k[v] x₀) (a v)]
    exact (w[v].map_sub _ _).trans (max_le (hx v) (hx₀ v))
  · intro hx v
    have h := hx v
    rw [map_sub] at h
    rw [← sub_add_sub_cancel (k[v] x) (k[v] x₀) (a v)]
    exact (w[v].map_add _ _).trans (max_le h (hx₀ v))

end Masullo
