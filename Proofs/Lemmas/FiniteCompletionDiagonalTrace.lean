module

public import Lemmas.FiniteCompletionDiagonalSupport
public import Lemmas.FiniteCompletionFractionBaseChange
import Mathlib.RingTheory.Localization.NormTrace

/-! # The diagonal trace at a rational prime

The sum uses the actual completions and their transported canonical scalar actions.
We compare integral traces first, then clear one nonzero integer denominator.
-/

open IsDedekindDomain NumberField
open scoped BigOperators Masullo nonZeroDivisors

namespace Masullo

variable {K : Type*} [Field K] [NumberField K] (p : ℕ) [Fact p.Prime]

local notation "P" => Ideal.span ({(p : 𝓞 K)} : Set (𝓞 K))
local notation "V" => {v : HeightOneSpectrum (𝓞 K) // HeightOneSpectrum.asIdeal v ∣ P}
local notation "O[" v "]" => HeightOneSpectrum.adicCompletionIntegers K (Subtype.val v)
local notation "F[" v "]" => HeightOneSpectrum.adicCompletion K (Subtype.val v)

attribute [local instance] finiteCompletionOverPrimeAlgebra finiteCompletionOverPrimeFieldAlgebra

private theorem trace_completion_integer (v : V) (y : O[v]) :
    Algebra.trace ℚ_[p] F[v] (algebraMap O[v] F[v] y) =
      algebraMap ℤ_[p] ℚ_[p] (Algebra.trace ℤ_[p] O[v] y) := by
  let : Algebra ℤ_[p] F[v] :=
    ((algebraMap ℚ_[p] F[v]).comp (algebraMap ℤ_[p] ℚ_[p])).toAlgebra
  let : IsScalarTower ℤ_[p] ℚ_[p] F[v] := .of_algebraMap_eq fun _ ↦ rfl
  let : IsScalarTower ℤ_[p] O[v] F[v] :=
    .of_algebraMap_eq fun r ↦ (finiteCompletionOverPrime_algebraMap_int p v r).symm
  let := finiteCompletionOverPrime_isLocalization p v
  let := finiteCompletionOverPrime_moduleFree p v
  let := finiteCompletionOverPrime_moduleFinite p v
  exact Algebra.trace_localization ℤ_[p] (ℤ_[p])⁰ y

private theorem sum_trace_completion_integer (a : 𝓞 K) :
    letI := finiteCompletionOverPrimeFintype (K := K) p
    (∑ v : V, Algebra.trace ℚ_[p] F[v] (algebraMap K F[v] (algebraMap (𝓞 K) K a))) =
      algebraMap ℚ ℚ_[p] (Algebra.trace ℚ K (algebraMap (𝓞 K) K a)) := by
  let : Fintype V := finiteCompletionOverPrimeFintype (K := K) p
  have h (v : V) : algebraMap K F[v] (algebraMap (𝓞 K) K a) =
      algebraMap O[v] F[v] (algebraMap (𝓞 K) O[v] a) := by
    change _ = (↑(algebraMap (𝓞 K) O[v] a) : F[v])
    rw [HeightOneSpectrum.algebraMap_adicCompletionIntegers_apply]
    rfl
  simp_rw [h, trace_completion_integer]
  rw [← map_sum, finiteCompletionIntegralBaseChange_trace_global,
    Algebra.trace_localization ℤ ℤ⁰, ← IsScalarTower.algebraMap_apply,
    ← IsScalarTower.algebraMap_apply]

/-- A diagonal element has base trace equal to the sum of its traces at the
actual completion fields over the given prime. -/
public theorem finiteCompletion_sum_trace_overPrime (x : K) :
    letI := finiteCompletionOverPrimeFintype (K := K) p
    (∑ v : V, Algebra.trace ℚ_[p] F[v] (algebraMap K F[v] x)) =
      algebraMap ℚ ℚ_[p] (Algebra.trace ℚ K x) := by
  let : Fintype V := finiteCompletionOverPrimeFintype (K := K) p
  obtain ⟨⟨a, s⟩, hs⟩ := IsLocalization.surj (Algebra.algebraMapSubmonoid (𝓞 K) ℤ⁰) x
  obtain ⟨d, hd0, hd⟩ := s.property
  have hdx : (d : ℤ) • x = algebraMap (𝓞 K) K a := by
    rw [zsmul_eq_mul, mul_comm, ← map_intCast (algebraMap ℤ K),
      IsScalarTower.algebraMap_apply ℤ (𝓞 K) K]
    change x * algebraMap (𝓞 K) K (algebraMap ℤ (𝓞 K) d) = _
    rw [hd]
    exact hs
  have h := sum_trace_completion_integer p a
  rw [← hdx] at h
  simp only [map_zsmul, ← Finset.smul_sum] at h
  exact mul_left_cancel₀ (Int.cast_ne_zero.mpr (mem_nonZeroDivisors_iff_ne_zero.mp hd0))
    (by simpa only [zsmul_eq_mul] using h)

private theorem phase_eq_of_baseMap (q : Nat.Primes) (v : HeightOneSpectrum (𝓞 K))
    (h : q = finiteCompletionBasePrime v) (x : K)
    (A : letI : Fact (q : ℕ).Prime := ⟨q.property⟩
      Algebra ℚ_[(q : ℕ)] (v.adicCompletion K)) :
    letI : Fact (q : ℕ).Prime := ⟨q.property⟩
    (∀ a : ℚ_[(q : ℕ)], @algebraMap _ (v.adicCompletion K) _ _ A a =
      finiteCompletionPadicMap v (cast (congrArg (fun r : Nat.Primes ↦ @Padic r.1 ⟨r.2⟩) h) a)) →
    finiteCompletionDiagonalPhase v x = padicStdAddChar (q : ℕ)
      (@Algebra.trace _ (v.adicCompletion K) _ _ A (algebraMap K (v.adicCompletion K) x)) := by
  subst q
  intro hA
  have hAlg : A = finiteCompletionPadicAlgebra v := by
    apply Algebra.algebra_ext
    intro a
    change _ = finiteCompletionPadicMap v a
    simpa only [cast_eq] using hA a
  subst A
  exact finiteCompletionDiagonalPhase_apply v x

/-- The phase with the transported action in the fixed-prime trace sum is
exactly the positive phase for the canonical action at the place. -/
public theorem finiteCompletionDiagonalPhase_eq_overPrime (v : V) (x : K) :
    finiteCompletionDiagonalPhase v.1 x = padicStdAddChar p
      (Algebra.trace ℚ_[p] F[v] (algebraMap K F[v] x)) := by
  let q : Nat.Primes := ⟨p, Fact.out⟩
  have h : q = finiteCompletionBasePrime v.1 :=
    (Subtype.ext (finiteCompletionBasePrime_eq_of_dvd_primeSpan p v)).symm
  exact phase_eq_of_baseMap q v.1 h x (finiteCompletionOverPrimeFieldAlgebra p v)
    (finiteCompletionOverPrimeFieldAlgebra_algebraMap p v)

end Masullo
