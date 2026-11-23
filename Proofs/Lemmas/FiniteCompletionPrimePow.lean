module

public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Lemmas.FiniteCompletionCompact

/-! # Prime-power quotients of the finite completion

The local discriminant in (A.3.2.2), p. 560, is taken in the actual
completion. Comparing it with the global different requires integral
comparison even at ramified places, where reducing modulo the base
prime retains a higher power of the local maximal ideal. We identify
these prime-power quotients via the canonical map, and compute the
extension of every nonzero global ideal to the completion integers.
-/

open Ideal IsDedekindDomain IsLocalRing NumberField Set WithZero
open scoped WithZero

namespace Masullo

variable {K : Type*} [Field K] [NumberField K]
  (v : HeightOneSpectrum (𝓞 K))

local notation "F" => v.adicCompletion K
local notation "O" => v.adicCompletionIntegers K
local notation "i" => algebraMap (𝓞 K) O
local notation "m" => maximalIdeal O
local notation "w" => (Valued.v : Valuation F ℤᵐ⁰)

private theorem completionValuation_algebraMap (a : 𝓞 K) :
    w (i a : F) = v.intValuation a := by
  change w ((algebraMap (𝓞 K) K a : K) : F) = _
  rw [v.valuedAdicCompletion_eq_valuation', v.valuation_of_algebraMap]

private theorem valuation_pow_uniformizer (π : O) (hπ : w (π : F) = exp (-1 : ℤ)) (n : ℕ) :
    w (↑(π ^ n) : F) = exp (-(n : ℤ)) := by
  change w ((algebraMap O F π) ^ n) = _
  rw [map_pow]
  change w (π : F) ^ n = _
  rw [hπ, ← exp_nsmul, nsmul_eq_mul, mul_neg, mul_one]

private theorem mem_span_pow_iff (π x : O) (hπ : w (π : F) = exp (-1 : ℤ)) (n : ℕ) :
    x ∈ Ideal.span ({π ^ n} : Set O) ↔ w (x : F) ≤ exp (-(n : ℤ)) := by
  rw [Ideal.mem_span_singleton, (HeightOneSpectrum.adicCompletionIntegers.integers K v).dvd_iff_le]
  change w (x : F) ≤ w (↑(π ^ n) : F) ↔ _
  rw [valuation_pow_uniformizer v π hπ]

private theorem maximalIdeal_eq_span (π : O) (hπ : w (π : F) = exp (-1 : ℤ)) :
    m = Ideal.span ({π} : Set O) := by
  ext x
  rw [show x ∈ m ↔ w (x : F) < 1 from Valuation.mem_maximalIdeal_iff F w]
  rw [← pow_one π, mem_span_pow_iff v π x hπ]
  change w (x : F) < 1 ↔ w (x : F) ≤ exp (-1 : ℤ)
  by_cases h : w (x : F) = 0
  · simp [h]
  · rw [← exp_log h, ← exp_zero, exp_lt_exp, exp_le_exp]
    omega

/-- The valuation bound equivalent to membership in a power of the local maximal ideal. -/
public theorem mem_completionIdeal_pow_iff (x : O) (n : ℕ) :
    x ∈ m ^ n ↔ w (x : F) ≤ exp (-(n : ℤ)) := by
  obtain ⟨a, ha⟩ := v.intValuation_exists_uniformizer
  have hπ := (completionValuation_algebraMap v a).trans ha
  rw [maximalIdeal_eq_span v (i a) hπ, Ideal.span_singleton_pow,
    mem_span_pow_iff v (i a) x hπ]

/-- Contraction of each local prime power recovers the same global prime power. -/
public theorem comap_finiteCompletion_maximalIdeal_pow (n : ℕ) :
    (m ^ n).comap i = v.asIdeal ^ n := by
  ext a
  rw [Ideal.mem_comap, mem_completionIdeal_pow_iff v, completionValuation_algebraMap v,
    v.intValuation_le_pow_iff_mem]

/-- Extension of the prime at `v` gives the maximal ideal of the actual integer ring. -/
public theorem map_finiteCompletion_prime : v.asIdeal.map i = m := by
  have hc : Ideal.comap i m = v.asIdeal := by simpa using comap_finiteCompletion_maximalIdeal_pow v 1
  refine le_antisymm (Ideal.map_le_iff_le_comap.mpr hc.ge) ?_
  obtain ⟨a, ha⟩ := v.intValuation_exists_uniformizer
  rw [maximalIdeal_eq_span v (i a) ((completionValuation_algebraMap v a).trans ha)]
  exact (Ideal.span_singleton_le_iff_mem _).mpr <| Ideal.mem_map_of_mem i <|
    (v.intValuation_lt_one_iff_mem a).mp (ha.trans_lt (by simp [← exp_zero]))

private theorem map_otherPrime_eq_top (u : HeightOneSpectrum (𝓞 K)) (hu : u ≠ v) :
    u.asIdeal.map i = ⊤ := by
  by_contra h
  have hc : Ideal.comap i m = v.asIdeal := by simpa using comap_finiteCompletion_maximalIdeal_pow v 1
  have hle := Ideal.map_le_iff_le_comap.mp (IsLocalRing.le_maximalIdeal h)
  rw [hc] at hle
  exact hu (HeightOneSpectrum.ext (u.isMaximal.eq_of_le v.isMaximal.ne_top hle))

/-- The extension of a nonzero global ideal has the exponent of `v` in that ideal. -/
public theorem map_finiteCompletion_ideal (I : Ideal (𝓞 K)) (hI : I ≠ ⊥) :
    I.map i = m ^ multiplicity v.asIdeal I := by
  classical
  have hfin : (Function.mulSupport fun u : HeightOneSpectrum (𝓞 K) ↦
      u.asIdeal ^ multiplicity u.asIdeal I).Finite :=
    (Ideal.finite_factors hI).subset fun u hu ↦ by
      by_contra h
      exact hu (by simp [multiplicity_eq_zero_of_not_dvd h])
  conv_lhs => rw [← Ideal.finprod_heightOneSpectrum_pow_multiplicity hI]
  change Ideal.mapHom i (∏ᶠ u : HeightOneSpectrum (𝓞 K), u.asIdeal ^ multiplicity u.asIdeal I) = _
  rw [map_finprod (Ideal.mapHom i) hfin, finprod_eq_single _ v]
  · change (v.asIdeal ^ multiplicity v.asIdeal I).map i = _
    rw [Ideal.map_pow, map_finiteCompletion_prime v]
  · intro u hu
    change (u.asIdeal ^ multiplicity u.asIdeal I).map i = 1
    rw [Ideal.map_pow, map_otherPrime_eq_top v u hu]
    rw [← Ideal.one_eq_top, one_pow]

private theorem exists_sub_mem_completionIdeal_pow (x : O) (n : ℕ) :
    ∃ a : 𝓞 K, i a - x ∈ m ^ n := by
  obtain ⟨a₀, ha₀⟩ := v.intValuation_exists_uniformizer
  let π : O := i a₀
  have hspan : m = Ideal.span ({π} : Set O) :=
    maximalIdeal_eq_span v π ((completionValuation_algebraMap v a₀).trans ha₀)
  have hπ : π ∈ m := by rw [hspan]; exact Ideal.mem_span_singleton_self _
  induction n generalizing x with
  | zero => exact ⟨0, by simp [Ideal.one_eq_top]⟩
  | succ n ih =>
    obtain ⟨q, hq⟩ := (finiteCompletionResidueEquiv K v).surjective (residue O x)
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective q
    rw [finiteCompletionResidueEquiv_mk] at hq
    have hb : x - i b ∈ m := by
      rw [← residue_eq_zero_iff, map_sub, hq, sub_self]
    rw [hspan, Ideal.mem_span_singleton] at hb
    obtain ⟨y, hy⟩ := hb
    obtain ⟨c, hc⟩ := ih y
    refine ⟨b + a₀ * c, ?_⟩
    rw [map_add, map_mul, pow_succ']
    change i b + π * i c - x ∈ m * m ^ n
    have heq : i b + π * i c - x = π * (i c - y) := by
      calc
        _ = π * i c - (x - i b) := by ring
        _ = _ := by rw [hy, mul_sub]
    rw [heq]
    exact Ideal.mul_mem_mul hπ hc

private noncomputable def finiteCompletionQuotientHom (n : ℕ) :
    (𝓞 K ⧸ v.asIdeal ^ n) →+* (O ⧸ m ^ n) :=
  Ideal.Quotient.lift _ ((Ideal.Quotient.mk _).comp i) fun a ha ↦ by
    change Ideal.Quotient.mk (m ^ n) (i a) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem]
    exact show a ∈ (m ^ n).comap i from (comap_finiteCompletion_maximalIdeal_pow v n).symm ▸ ha

/-- Global and completed integers have the same quotient by each corresponding prime power. -/
public noncomputable def finiteCompletionPrimePowQuotientEquiv (n : ℕ) :
    (𝓞 K ⧸ v.asIdeal ^ n) ≃+* (O ⧸ m ^ n) :=
  RingEquiv.ofBijective (finiteCompletionQuotientHom v n)
    ⟨RingHom.lift_injective_of_ker_le_ideal _ _ fun a ha ↦ by
        change Ideal.Quotient.mk (m ^ n) (i a) = 0 at ha
        rw [Ideal.Quotient.eq_zero_iff_mem] at ha
        rwa [← comap_finiteCompletion_maximalIdeal_pow v n],
      fun y ↦ by
        obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
        obtain ⟨a, ha⟩ := exists_sub_mem_completionIdeal_pow v x n
        exact ⟨Ideal.Quotient.mk _ a, Ideal.Quotient.eq.mpr ha⟩⟩

/-- Every prime-power quotient of the completion integers is finite. -/
public theorem finite_finiteCompletionPrimePowQuotient (n : ℕ) : Finite (O ⧸ m ^ n) := by
  have h : v.asIdeal ^ n ≠ ⊥ := by
    by_cases hn : n = 0
    · simp [hn]
    · exact fun hz ↦ v.ne_bot ((Ideal.pow_eq_bot hn).mp hz)
  let := Ring.HasFiniteQuotients.finiteQuotient h
  exact Finite.of_equiv _ (finiteCompletionPrimePowQuotientEquiv v n).toEquiv

/-- The quotient equivalence sends the class of a global integer to the class of its image. -/
public theorem finiteCompletionPrimePowQuotientEquiv_mk (n : ℕ) (a : 𝓞 K) :
    finiteCompletionPrimePowQuotientEquiv v n (Ideal.Quotient.mk _ a) =
      Ideal.Quotient.mk _ (i a) := by
  unfold finiteCompletionPrimePowQuotientEquiv
  change finiteCompletionQuotientHom v n (Ideal.Quotient.mk _ a) = _
  rfl

end Masullo
