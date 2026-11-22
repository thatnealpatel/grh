module

public import Lemmas.FiniteCompletionCodifferent

/-! # Trace dual with the canonical p-adic scalar action

Specialize the fixed-prime codifferent comparison at the prime below the
given place. The transported and canonical scalar actions agree because
their algebra maps agree.
-/

open IsDedekindDomain NumberField
open scoped Masullo

namespace Masullo

variable {K : Type*} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

local notation "p" => finiteCompletionBasePrime v
local notation "R" => ℤ_[p]
local notation "F" => v.adicCompletion K
local notation "O" => v.adicCompletionIntegers K

private theorem dvd_basePrime : v.asIdeal ∣ Ideal.span ({(p : 𝓞 K)} : Set (𝓞 K)) := by
  apply (finitePlace_dvd_primeSpan_iff p v).mpr
  rw [← map_natCast (algebraMap ℤ (𝓞 K)), ← Ideal.mem_under, finiteCompletionBasePrime_val]
  let u := v.under ℤ
  change ((Rat.HeightOneSpectrum.natGenerator u : ℕ) : ℤ) ∈ u.asIdeal
  apply (Ideal.apply_mem_of_equiv_iff (f := Rat.IsIntegralClosure.intEquiv ℤ)).mp
  rw [map_natCast]
  exact (Rat.HeightOneSpectrum.natGenerator_dvd_iff u).mp dvd_rfl

set_option quotPrecheck false in
local notation "Td" => Submodule.traceDual R ℚ_[p] (1 : Submodule O F)
set_option quotPrecheck false in
local notation "TD" => Submodule.traceDual ℤ ℚ (1 : Submodule (𝓞 K) K)

/-- The global codifferent span is the local trace dual for the completion's
canonical p-adic scalar action. -/
public theorem finiteCompletion_traceDual_eq_span_globalCodifferent :
    Td = Submodule.span O ((algebraMap K F) '' (TD : Set K)) := by
  ext x
  rw [Submodule.mem_traceDual]
  simp only [Submodule.mem_one, forall_exists_index, forall_apply_eq_imp_iff,
    Algebra.traceForm_apply]
  let w : {w : HeightOneSpectrum (𝓞 K) //
      w.asIdeal ∣ Ideal.span ({(p : 𝓞 K)} : Set (𝓞 K))} := ⟨v, dvd_basePrime v⟩
  have h : finiteCompletionOverPrimeFieldAlgebra (p : ℕ) w = finiteCompletionPadicAlgebra v := by
    apply Algebra.algebra_ext
    intro a
    rw [finiteCompletionOverPrimeFieldAlgebra_algebraMap, cast_eq]
    rfl
  have ht := finiteCompletion_traceDual_iff_mem_span_globalCodifferent (p : ℕ) w x
  change (∀ y : O, @Algebra.trace ℚ_[p] F _ _ (finiteCompletionOverPrimeFieldAlgebra (p : ℕ) w)
      (x * algebraMap O F y) ∈ (algebraMap R ℚ_[p]).range) ↔
    x ∈ Submodule.span O ((algebraMap K F) '' (TD : Set K)) at ht
  rw [h] at ht
  exact ht

end Masullo
