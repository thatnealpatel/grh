module

public import Theorems.FiniteIdeleIdeal
public import Lemmas.FiniteBoxCongruences

/-! # Coordinate membership in the ideal of a finite idele -/

open Ideal IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField
open scoped nonZeroDivisors WithZero

namespace Masullo

variable {K : Type*} [Field K] [NumberField K]

local notation "V" => HeightOneSpectrum (𝓞 K)
local notation "F" => FiniteAdeleRing (𝓞 K) K
local notation "J" => FractionalIdeal (𝓞 K)⁰ K
local notation "w[" v "]" => (Valued.v : Valuation (HeightOneSpectrum.adicCompletion K v) ℤᵐ⁰)
local notation "k[" v "]" => algebraMap K (HeightOneSpectrum.adicCompletion K v)

private theorem le_iff_le_count {A B : J} (hA : A ≠ 0) (hB : B ≠ 0) :
    A ≤ B ↔ ∀ v : V, FractionalIdeal.count K v B ≤ FractionalIdeal.count K v A := by
  refine ⟨fun h v ↦ FractionalIdeal.count_mono K v hA h, fun h ↦ ?_⟩
  have hAB : A * B⁻¹ ≤ 1 := by
    apply le_one_of_count_nonneg (mul_ne_zero hA (inv_ne_zero hB))
    intro v
    rw [FractionalIdeal.count_mul K v hA (inv_ne_zero hB), FractionalIdeal.count_inv]
    exact sub_nonneg.mpr (h v)
  have hle := mul_le_mul_right hAB B
  rwa [mul_left_comm, mul_inv_cancel₀ hB, mul_one, mul_one] at hle

/-- The homogeneous box of a finite idele pulls back to its fractional ideal. -/
public theorem mem_finiteIdeleIdeal_iff (g : Fˣ) (x : K) :
    x ∈ (finiteIdeleIdeal K g : J) ↔ ∀ v : V, w[v] (k[v] x) ≤ w[v] (g.val v) := by
  by_cases hx : x = 0
  · subst x
    exact iff_of_true ((finiteIdeleIdeal K g : J).zero_mem) (by simp)
  rw [← FractionalIdeal.spanSingleton_le_iff_mem,
    le_iff_le_count (FractionalIdeal.spanSingleton_ne_zero_iff.mpr hx) (finiteIdeleIdeal K g).ne_zero]
  apply forall_congr'
  intro v
  rw [count_finiteIdeleIdeal, count_spanSingleton_eq_neg_log_valuation x hx, neg_le_neg_iff]
  have hv : w[v] (k[v] x) = v.valuation K x := v.valuedAdicCompletion_eq_valuation' x
  exact (WithZero.log_le_log ((map_ne_zero (v.valuation K)).mpr hx)
    (finiteIdele_valuation_ne_zero g v)).trans (by rw [hv])

/-- An idele with integral coordinates gives an integral ideal. Its extension
at a place imposes exactly the original coordinate's valuation bound. -/
public theorem exists_ideal_finiteIdeleIdeal_of_integral (g : Fˣ)
    (hg : ∀ v : V, w[v] (g.val v) ≤ 1) :
    ∃ I : Ideal (𝓞 K), I ≠ ⊥ ∧ (I : J) = finiteIdeleIdeal K g ∧
      ∀ (v : V) (x : v.adicCompletionIntegers K),
        x ∈ I.map (algebraMap (𝓞 K) (v.adicCompletionIntegers K)) ↔
          w[v] (x : v.adicCompletion K) ≤ w[v] (g.val v) := by
  have hle : (finiteIdeleIdeal K g : J) ≤ 1 := by
    apply le_one_of_count_nonneg (finiteIdeleIdeal K g).ne_zero
    intro v
    rw [count_finiteIdeleIdeal, le_neg, neg_zero, ← WithZero.log_one,
      WithZero.log_le_log (finiteIdele_valuation_ne_zero g v) one_ne_zero]
    exact hg v
  obtain ⟨I, hI⟩ := FractionalIdeal.le_one_iff_exists_coeIdeal.mp hle
  have hI₀ : I ≠ ⊥ := by
    intro h
    apply (finiteIdeleIdeal K g).ne_zero
    simp [h, ← hI]
  refine ⟨I, hI₀, hI, fun v x ↦ ?_⟩
  classical
  have hcount : (multiplicity v.asIdeal I : ℤ) = -(w[v] (g.val v)).log := by
    rw [← count_finiteIdeleIdeal g v, ← hI, FractionalIdeal.count_coeIdeal K v hI₀,
      Associates.factors_mk _ hI₀, Associates.count_some v.associates_irreducible,
      ← Multiset.count_map_eq_count' _ _ Subtype.val_injective,
      Associates.map_subtype_coe_factors', UniqueFactorizationMonoid.factors_eq_normalizedFactors]
    change _ = (((UniqueFactorizationMonoid.normalizedFactors I).map Associates.mk).count
      (Associates.mk v.asIdeal) : ℤ)
    rw [Multiset.count_map_eq_count' _ _ (Associates.mk_injective (M := Ideal (𝓞 K))),
      v.count_normalizedFactors_eq_multiplicity hI₀]
  rw [map_finiteCompletion_ideal v I hI₀, mem_completionIdeal_pow_iff v, hcount, neg_neg,
    WithZero.exp_log (finiteIdele_valuation_ne_zero g v)]

end Masullo
