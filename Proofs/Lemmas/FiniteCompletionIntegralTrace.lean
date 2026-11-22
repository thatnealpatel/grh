module

public import Lemmas.FiniteCompletionIntegralBaseChange
public import Mathlib.RingTheory.Trace.Basic
import Mathlib.LinearAlgebra.Finsupp.VectorSpace

/-! # Integral trace at a fixed rational prime

Masullo (A.3.1.8), p. 558, uses the local trace character, and (A.3.2.2),
p. 560, prescribes the Haar unit mass using the local discriminant. The
project comparison below splits the integral trace into the actual local
blocks. Identifying the trace duals and computing the discriminant are
separate steps.
-/

open IsDedekindDomain NumberField
open scoped BigOperators TensorProduct

namespace Masullo

section Product

variable {R I : Type*} [CommRing R] [Fintype I]
  {S : I → Type*} [∀ i, CommRing (S i)] [∀ i, Algebra R (S i)]
  {J : I → Type*}

private noncomputable def productBasis (b : ∀ i, Module.Basis (J i) R (S i)) :
    Module.Basis (Σ i, J i) R ((i : I) → S i) :=
  (DFinsupp.basis b).map DFinsupp.linearEquivFunOnFintype

private theorem productBasis_repr (b : ∀ i, Module.Basis (J i) R (S i))
    (x : (i : I) → S i) (i : I) (j : J i) :
    (productBasis b).repr x ⟨i, j⟩ = (b i).repr (x i) j := rfl

private theorem productBasis_apply_self (b : ∀ i, Module.Basis (J i) R (S i))
    (i : I) (j : J i) : productBasis b ⟨i, j⟩ i = b i j := by
  classical
  apply (b i).repr.injective
  ext k
  rw [← productBasis_repr, Module.Basis.repr_self, Module.Basis.repr_self]
  by_cases h : j = k
  · subst k
    simp
  · have h' : (⟨i, j⟩ : Σ i, J i) ≠ ⟨i, k⟩ := fun e ↦ h (Sigma.mk.inj_iff.mp e).2.eq
    simp [h, h']

private theorem trace_pi [∀ i, Fintype (J i)] (b : ∀ i, Module.Basis (J i) R (S i))
    (x : (i : I) → S i) :
    Algebra.trace R _ x = ∑ i, Algebra.trace R (S i) (x i) := by
  classical
  rw [Algebra.trace_eq_matrix_trace (productBasis b)]
  simp only [Algebra.trace_eq_matrix_trace (b _), Matrix.trace, Matrix.diag_apply,
    Algebra.leftMulMatrix_apply, Algebra.toMatrix_lmul', Fintype.sum_sigma,
    productBasis_repr, Pi.mul_apply, productBasis_apply_self]

end Product

variable {K : Type*} [Field K] [NumberField K] (p : ℕ) [hp : Fact p.Prime]

local notation "P" => Ideal.span ({(p : 𝓞 K)} : Set (𝓞 K))
local notation "V" => {v : HeightOneSpectrum (𝓞 K) // HeightOneSpectrum.asIdeal v ∣ P}
local notation "O[" v "]" => HeightOneSpectrum.adicCompletionIntegers K (Subtype.val v)
local notation "A" => ℤ_[p] ⊗[ℤ] 𝓞 K

attribute [local instance] finiteCompletionOverPrimeAlgebra

/-- The places over `p` form a finite index type for the local trace sum. -/
@[instance_reducible] public noncomputable def finiteCompletionOverPrimeFintype : Fintype V :=
  (Ideal.finite_factors (I := P)
    (mt Ideal.span_singleton_eq_bot.mp (Nat.cast_ne_zero.mpr hp.out.ne_zero))).fintype

/-- Under the canonical integral base change, the trace is the sum of the
traces of multiplication in the actual completion integer rings. -/
public theorem finiteCompletionIntegralBaseChange_trace (t : A) :
    letI := finiteCompletionOverPrimeFintype (K := K) p
    Algebra.trace ℤ_[p] A t =
      ∑ v : V, Algebra.trace ℤ_[p] O[v] (finiteCompletionIntegralBaseChange p t v) := by
  let : Fintype V := finiteCompletionOverPrimeFintype (K := K) p
  let (v : V) : Module.Free ℤ_[p] O[v] := finiteCompletionOverPrime_moduleFree p v
  let (v : V) : Module.Finite ℤ_[p] O[v] := finiteCompletionOverPrime_moduleFinite p v
  rw [← Algebra.trace_eq_of_algEquiv (finiteCompletionIntegralBaseChange p)]
  exact trace_pi (fun v : V ↦ Module.Free.chooseBasis ℤ_[p] O[v]) _

/-- The integral trace of a global integer, cast into `ℤ_[p]`, is the sum
of its integral traces over the places above `p`. -/
public theorem finiteCompletionIntegralBaseChange_trace_global (x : 𝓞 K) :
    letI := finiteCompletionOverPrimeFintype (K := K) p
    (∑ v : V, Algebra.trace ℤ_[p] O[v] (algebraMap (𝓞 K) O[v] x)) =
      algebraMap ℤ ℤ_[p] (Algebra.trace ℤ (𝓞 K) x) := by
  have h := finiteCompletionIntegralBaseChange_trace p ((1 : ℤ_[p]) ⊗ₜ[ℤ] x)
  simp only [finiteCompletionIntegralBaseChange_tmul, one_smul] at h
  rw [← h, Algebra.trace_apply, ← Algebra.baseChange_lmul, LinearMap.trace_baseChange,
    ← Algebra.trace_apply]

end Masullo
