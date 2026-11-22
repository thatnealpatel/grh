module

public import Lemmas.FiniteCompletionCRT

/-! # Simultaneous congruences in completed integer rings

For a nonzero integral ideal, a tuple of local cosets modulo its extensions
has a global integral representative. This is the integral step in pulling
back a finite adelic box to the number-field diagonal for Theorem 2.2.3.2,
PDF p. 82. It uses the canonical completion CRT and includes all finite
places, not only the ones at which a congruence is imposed.
-/

open Ideal IsDedekindDomain NumberField

namespace Masullo

variable {K : Type*} [Field K] [NumberField K]

local notation "V" => HeightOneSpectrum (𝓞 K)
local notation "O[" v "]" => HeightOneSpectrum.adicCompletionIntegers K v
local notation "i[" v "]" => algebraMap (𝓞 K) O[v]

/-- Reduction modulo the extension of a nonzero ideal is unrestricted at places
not dividing it. -/
private theorem finiteCompletion_map_ideal_eq_top (I : Ideal (𝓞 K)) (hI : I ≠ ⊥)
    (v : V) (hv : ¬v.asIdeal ∣ I) : I.map i[v] = ⊤ := by
  rw [map_finiteCompletion_ideal v I hI, multiplicity_eq_zero_of_not_dvd hv,
    pow_zero, Ideal.one_eq_top]

/-- Every tuple of local integer cosets modulo the extensions of `I` has a
representative in the global integer ring. -/
public theorem exists_ringOfIntegers_sub_mem_finiteCompletionIdeal
    (I : Ideal (𝓞 K)) (hI : I ≠ ⊥) (a : ∀ v : V, O[v]) :
    ∃ x : 𝓞 K, ∀ v : V, i[v] x - a v ∈ I.map i[v] := by
  classical
  obtain ⟨q, hq⟩ := (finiteCompletionIdealQuotientEquiv I hI).surjective
    (fun v ↦ Ideal.Quotient.mk (I.map i[v.1]) (a v.1))
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective q
  refine ⟨x, fun v ↦ ?_⟩
  by_cases hv : v.asIdeal ∣ I
  · have h := congrFun hq ⟨v, hv⟩
    rw [finiteCompletionIdealQuotientEquiv_mk] at h
    exact Ideal.Quotient.eq.mp h
  · simp [finiteCompletion_map_ideal_eq_top I hI v hv]

/-- For a fixed representative of the local residue classes, the set of all
other global representatives is exactly its translate of the global ideal. -/
public theorem sub_mem_finiteCompletionIdeal_iff
    (I : Ideal (𝓞 K)) (hI : I ≠ ⊥) (a : ∀ v : V, O[v])
    (x₀ : 𝓞 K) (hx₀ : ∀ v : V, i[v] x₀ - a v ∈ I.map i[v]) (x : 𝓞 K) :
    (∀ v : V, i[v] x - a v ∈ I.map i[v]) ↔ x - x₀ ∈ I := by
  constructor
  · intro hx
    apply Ideal.Quotient.eq.mp
    apply (finiteCompletionIdealQuotientEquiv I hI).injective
    funext v
    rw [finiteCompletionIdealQuotientEquiv_mk, finiteCompletionIdealQuotientEquiv_mk]
    apply Ideal.Quotient.eq.mpr
    simpa only [sub_sub_sub_cancel_right] using (I.map i[v.1]).sub_mem (hx v.1) (hx₀ v.1)
  · intro hx v
    have h := Ideal.mem_map_of_mem i[v] hx
    rw [map_sub] at h
    simpa only [sub_add_sub_cancel] using (I.map i[v]).add_mem h (hx₀ v)

end Masullo
