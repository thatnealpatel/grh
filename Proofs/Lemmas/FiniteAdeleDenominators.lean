module

public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing

/-! # A common denominator for the finite adele coordinates

Only finitely many coordinates are nonintegral. At each such place one
can clear the local denominator by a power of a global integer of
valuation `exp (-1)`. The product of these powers also clears the tuple:
At every other place the added factors are integral.
-/

open Filter IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField
open scoped WithZero

namespace Masullo

variable {K : Type*} [Field K] [NumberField K]

local notation "V" => HeightOneSpectrum (𝓞 K)
local notation "F" => FiniteAdeleRing (𝓞 K) K
local notation "j[" v "]" => algebraMap (𝓞 K) (HeightOneSpectrum.adicCompletion K v)
local notation "w[" v "]" => (Valued.v : Valuation (HeightOneSpectrum.adicCompletion K v) ℤᵐ⁰)

private theorem finiteCompletion_val_ringOfIntegers (v : V) (a : 𝓞 K) :
    w[v] (j[v] a) = v.intValuation a := by
  change w[v] ((algebraMap (𝓞 K) K a : K) : v.adicCompletion K) = _
  rw [v.valuedAdicCompletion_eq_valuation', v.valuation_of_algebraMap]

private theorem exists_local_clearer (v : V) (a : v.adicCompletion K) :
    ∃ d : 𝓞 K, d ≠ 0 ∧ w[v] (j[v] d * a) ≤ 1 := by
  by_cases h : w[v] a ≤ 1
  · exact ⟨1, one_ne_zero, by simpa using h⟩
  obtain ⟨π, hπ⟩ := v.intValuation_exists_uniformizer
  have hπ₀ : π ≠ 0 := by
    intro hz
    exact WithZero.exp_ne_zero (a := (-1 : ℤ)) (by rw [hz, map_zero] at hπ; exact hπ.symm)
  have ha₀ : w[v] a ≠ 0 := ne_of_gt (zero_lt_one.trans (lt_of_not_ge h))
  have hn : 0 ≤ WithZero.log (w[v] a) := by
    rw [← WithZero.log_one]
    exact (WithZero.log_le_log one_ne_zero ha₀).2 (le_of_not_ge h)
  let n := (WithZero.log (w[v] a)).toNat
  refine ⟨π ^ n, pow_ne_zero _ hπ₀, ?_⟩
  rw [map_mul, finiteCompletion_val_ringOfIntegers, map_pow, hπ, ← WithZero.exp_nsmul,
    nsmul_eq_mul, mul_neg, mul_one, Int.toNat_of_nonneg hn]
  nth_rw 2 [← WithZero.exp_log ha₀]
  rw [← WithZero.exp_add, neg_add_cancel, WithZero.exp_zero]

/-- A finite adele can be made integral at every place by multiplication
by one nonzero global integer. -/
public theorem exists_finiteAdele_clearDenominator (a : F) :
    ∃ d : 𝓞 K, d ≠ 0 ∧ ∀ v : V, w[v] (j[v] d * a v) ≤ 1 := by
  classical
  let S := a.finite_valued_one_lt.toFinset
  choose d hd hdval using fun v : V ↦ exists_local_clearer v (a v)
  refine ⟨∏ v ∈ S, d v, Finset.prod_ne_zero_iff.mpr fun v _ ↦ hd v, ?_⟩
  intro v
  by_cases hv : v ∈ S
  · rw [← Finset.mul_prod_erase S d hv, (j[v]).map_mul, mul_right_comm, w[v].map_mul]
    have hrest : w[v] (j[v] (∏ x ∈ S.erase v, d x)) ≤ 1 := by
      rw [finiteCompletion_val_ringOfIntegers]
      exact v.intValuation_le_one _
    exact mul_le_mul (hdval v) hrest zero_le zero_le_one
  · rw [map_mul, finiteCompletion_val_ringOfIntegers]
    have ha : w[v] (a v) ≤ 1 := by
      apply le_of_not_gt
      intro h
      exact hv (a.finite_valued_one_lt.mem_toFinset.mpr h)
    exact mul_le_mul (v.intValuation_le_one _) ha zero_le zero_le_one

end Masullo
