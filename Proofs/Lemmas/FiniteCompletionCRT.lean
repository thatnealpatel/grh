module

public import Lemmas.FiniteCompletionPrimePow
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas

/-! # Chinese remainders in the actual finite completions

The discriminant in Masullo (A.3.2.2), p. 560, uses the actual local integer
ring. For an integral base-change comparison, we first compare the reductions
of the global and local integer rings modulo the rational prime, including the
nilpotent layers at ramified places. The comparison here works for every
nonzero global ideal and records the image of each global integer.
-/

open Ideal IsDedekindDomain NumberField
open scoped BigOperators

namespace Masullo

variable {K : Type*} [Field K] [NumberField K]

local notation "V" => HeightOneSpectrum (𝓞 K)
local notation "Places(" I ")" => {v : V // HeightOneSpectrum.asIdeal v ∣ I}
local notation "e[" v ", " I "]" => multiplicity (HeightOneSpectrum.asIdeal v) I
local notation "i[" v "]" => algebraMap (𝓞 K) (HeightOneSpectrum.adicCompletionIntegers K v)

private theorem idealFactorization (I : Ideal (𝓞 K)) (hI : I ≠ ⊥) :
    letI := (Ideal.finite_factors hI).fintype
    ∏ v : Places(I), v.1.asIdeal ^ e[v.1, I] = I := by
  classical
  let hfin := Ideal.finite_factors hI
  let _ := hfin.fintype
  let f (v : V) := v.asIdeal ^ e[v, I]
  calc
    ∏ v : Places(I), f v.1 = ∏ v ∈ hfin.toFinset, f v :=
      (Finset.prod_subtype (F := hfin.fintype) hfin.toFinset (fun _ ↦ hfin.mem_toFinset) f).symm
    _ = ∏ᶠ v : V, f v := (finprod_eq_prod_of_mulSupport_subset f (by
      intro v hv
      change v ∈ hfin.toFinset
      rw [Set.Finite.mem_toFinset]
      by_contra h
      exact hv (by simp [f, multiplicity_eq_zero_of_not_dvd h]))).symm
    _ = I := Ideal.finprod_heightOneSpectrum_pow_multiplicity hI

private noncomputable def globalIdealCRT (I : Ideal (𝓞 K)) (hI : I ≠ ⊥) :
    (𝓞 K ⧸ I) ≃+* ∀ v : Places(I), 𝓞 K ⧸ v.1.asIdeal ^ e[v.1, I] :=
  letI := (Ideal.finite_factors hI).fintype
  HeightOneSpectrum.quotientEquivPiOfProdEq I Subtype.val
    (fun v : Places(I) ↦ e[v.1, I]) (fun _ _ h ↦ Subtype.val_injective.ne h)
    (idealFactorization I hI)

/-- The quotient by a nonzero global ideal is the product of its quotients in the
actual completion integers at the primes dividing it. -/
public noncomputable def finiteCompletionIdealQuotientEquiv (I : Ideal (𝓞 K)) (hI : I ≠ ⊥) :
    (𝓞 K ⧸ I) ≃+* ∀ v : Places(I), v.1.adicCompletionIntegers K ⧸ I.map i[v.1] :=
  (globalIdealCRT I hI).trans <| RingEquiv.piCongrRight fun v ↦
    (finiteCompletionPrimePowQuotientEquiv v.1 e[v.1, I]).trans <|
      Ideal.quotEquivOfEq (map_finiteCompletion_ideal v.1 I hI).symm

/-- In every coordinate, the quotient equivalence is the canonical global-integer map. -/
public theorem finiteCompletionIdealQuotientEquiv_mk (I : Ideal (𝓞 K)) (hI : I ≠ ⊥)
    (x : 𝓞 K) (v : Places(I)) :
    finiteCompletionIdealQuotientEquiv I hI (Ideal.Quotient.mk I x) v =
      Ideal.Quotient.mk (I.map i[v.1]) (i[v.1] x) := by
  have h (v : Places(I)) : globalIdealCRT I hI (Ideal.Quotient.mk I x) v =
      Ideal.Quotient.mk (v.1.asIdeal ^ e[v.1, I]) x := rfl
  change Ideal.quotEquivOfEq (map_finiteCompletion_ideal v.1 I hI).symm
    (finiteCompletionPrimePowQuotientEquiv v.1 e[v.1, I]
      (globalIdealCRT I hI (Ideal.Quotient.mk I x) v)) = _
  rw [h, finiteCompletionPrimePowQuotientEquiv_mk, Ideal.quotEquivOfEq_mk]

local notation "P[" p "]" => Ideal.span ({(p : 𝓞 K)} : Set (𝓞 K))

/-- The index set for the reduction modulo `p` consists of exactly the places over `p`. -/
public theorem finitePlace_dvd_primeSpan_iff (p : ℕ) (v : V) :
    v.asIdeal ∣ P[p] ↔ (p : 𝓞 K) ∈ v.asIdeal :=
  Ideal.dvd_iff_le.trans (Ideal.span_singleton_le_iff_mem v.asIdeal)

private theorem primeSpan_ne_bot (p : ℕ) [hp : Fact p.Prime] :
    P[p] ≠ (⊥ : Ideal (𝓞 K)) :=
  mt Ideal.span_singleton_eq_bot.mp (Nat.cast_ne_zero.mpr hp.out.ne_zero)

private theorem map_primeSpan (p : ℕ) (v : V) :
    P[p].map i[v] = Ideal.span ({(p : v.adicCompletionIntegers K)} : Set _) := by
  rw [Ideal.map_span, Set.image_singleton, map_natCast]

/-- Reduction modulo the rational prime agrees with the product of the reductions
modulo the same prime in the actual completions. -/
public noncomputable def finiteCompletionModPrimeEquiv (p : ℕ) [Fact p.Prime] :
    (𝓞 K ⧸ P[p]) ≃+* ∀ v : Places(P[p]),
      v.1.adicCompletionIntegers K ⧸ Ideal.span ({(p : v.1.adicCompletionIntegers K)} : Set _) :=
  (finiteCompletionIdealQuotientEquiv P[p] (primeSpan_ne_bot p)).trans <|
    RingEquiv.piCongrRight fun v ↦ Ideal.quotEquivOfEq (map_primeSpan p v.1)

/-- The reduction modulo the rational prime keeps the canonical class map. -/
public theorem finiteCompletionModPrimeEquiv_mk (p : ℕ) [Fact p.Prime]
    (x : 𝓞 K) (v : Places(P[p])) :
    finiteCompletionModPrimeEquiv p (Ideal.Quotient.mk P[p] x) v =
      Ideal.Quotient.mk _ (i[v.1] x) := by
  change Ideal.quotEquivOfEq (map_primeSpan p v.1)
    (finiteCompletionIdealQuotientEquiv P[p] (primeSpan_ne_bot p) (Ideal.Quotient.mk P[p] x) v) = _
  rw [finiteCompletionIdealQuotientEquiv_mk, Ideal.quotEquivOfEq_mk]

end Masullo
