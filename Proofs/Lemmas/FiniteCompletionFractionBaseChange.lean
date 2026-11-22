module

public import Lemmas.FiniteCompletionIntegralTrace
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.TensorProduct.Pi

/-! # Fraction algebras at a fixed rational prime

For the trace character in Masullo (A.3.1.8), p. 558, and the Haar
normalization in (A.3.2.2), p. 560, the project compares the actual
completion fields and their trace pairings. This is not a proof that
the local trace dual equals the extension of the global codifferent.
-/

open IsDedekindDomain NumberField
open scoped BigOperators nonZeroDivisors TensorProduct

namespace Masullo

variable {K : Type*} [Field K] [NumberField K]

local notation "P[" p "]" => Ideal.span ({(p : 𝓞 K)} : Set (𝓞 K))
local notation "V[" p "]" => {v : HeightOneSpectrum (𝓞 K) // HeightOneSpectrum.asIdeal v ∣ P[p]}
local notation "O[" v "]" => HeightOneSpectrum.adicCompletionIntegers K (Subtype.val v)
local notation "F[" v "]" => HeightOneSpectrum.adicCompletion K (Subtype.val v)

@[instance_reducible] private noncomputable def transportedFieldAlgebra (p : ℕ) [Fact p.Prime]
    (v : HeightOneSpectrum (𝓞 K)) (h : (finiteCompletionBasePrime v : ℕ) = p) :
    Algebra ℚ_[p] (v.adicCompletion K) := by
  subst p
  exact finiteCompletionPadicAlgebra v

/-- The canonical completed field map, transported to the common rational prime. -/
@[instance_reducible] public noncomputable def finiteCompletionOverPrimeFieldAlgebra
    (p : ℕ) [Fact p.Prime] (v : V[p]) : Algebra ℚ_[p] F[v] :=
  transportedFieldAlgebra p v.1 (finiteCompletionBasePrime_eq_of_dvd_primeSpan p v)

attribute [local instance] finiteCompletionOverPrimeAlgebra finiteCompletionOverPrimeFieldAlgebra

private theorem algebraMap_transportedFieldAlgebra (p : ℕ) [Fact p.Prime]
    (v : HeightOneSpectrum (𝓞 K)) (h : (finiteCompletionBasePrime v : ℕ) = p) (a : ℚ_[p]) :
    letI := transportedFieldAlgebra p v h
    algebraMap ℚ_[p] (v.adicCompletion K) a =
      finiteCompletionPadicMap v (cast (by subst p; rfl) a) := by
  subst p
  rfl

/-- The fixed-prime field algebra uses the checked completed map at the same prime. -/
public theorem finiteCompletionOverPrimeFieldAlgebra_algebraMap (p : ℕ) [Fact p.Prime]
    (v : V[p]) (a : ℚ_[p]) : algebraMap ℚ_[p] F[v] a =
      finiteCompletionPadicMap v.1
        (cast (congrArg (fun q : Nat.Primes ↦ @Padic q.1 ⟨q.2⟩)
          (show (⟨p, Fact.out⟩ : Nat.Primes) = finiteCompletionBasePrime v.1 from
            (Subtype.ext (finiteCompletionBasePrime_eq_of_dvd_primeSpan p v)).symm)) a) :=
  algebraMap_transportedFieldAlgebra p v.1 (finiteCompletionBasePrime_eq_of_dvd_primeSpan p v) a

variable (p : ℕ) [Fact p.Prime]

local notation "A" => ℤ_[p] ⊗[ℤ] 𝓞 K
local notation "L" => ℚ_[p] ⊗[ℤ_[p]] A

private theorem padicInt_cast_coe {q q' : Nat.Primes} (h : q = q')
    (r : @PadicInt q.1 ⟨q.2⟩) :
    (↑(cast (congrArg (fun b : Nat.Primes ↦ @PadicInt b.1 ⟨b.2⟩) h) r) : @Padic q'.1 ⟨q'.2⟩) =
      cast (congrArg (fun b : Nat.Primes ↦ @Padic b.1 ⟨b.2⟩) h) (r : @Padic q.1 ⟨q.2⟩) := by
  cases h
  rfl

/-- The two maps into a completion field agree on the base integers. -/
public theorem finiteCompletionOverPrime_algebraMap_int (v : V[p]) (r : ℤ_[p]) :
    algebraMap O[v] F[v] (algebraMap ℤ_[p] O[v] r) =
      algebraMap ℚ_[p] F[v] (algebraMap ℤ_[p] ℚ_[p] r) := by
  rw [finiteCompletionOverPrimeAlgebra_algebraMap, finiteCompletionOverPrimeFieldAlgebra_algebraMap]
  rw [show ∀ z : O[v], algebraMap O[v] F[v] z = (z : F[v]) from fun _ ↦ rfl,
    coe_finiteCompletionPadicIntMap]
  let q : Nat.Primes := ⟨p, Fact.out⟩
  let h : q = finiteCompletionBasePrime v.1 :=
    (Subtype.ext (finiteCompletionBasePrime_eq_of_dvd_primeSpan p v)).symm
  exact congrArg (finiteCompletionPadicMap v.1) (padicInt_cast_coe h r)

private noncomputable def localHom (v : V[p]) : ℚ_[p] ⊗[ℤ_[p]] O[v] →ₐ[ℚ_[p]] F[v] := by
  letI : Algebra ℤ_[p] F[v] :=
    ((algebraMap ℚ_[p] F[v]).comp (algebraMap ℤ_[p] ℚ_[p])).toAlgebra
  letI : IsScalarTower ℤ_[p] ℚ_[p] F[v] := .of_algebraMap_eq fun _ ↦ rfl
  letI : IsScalarTower ℤ_[p] O[v] F[v] :=
    .of_algebraMap_eq fun r ↦ (finiteCompletionOverPrime_algebraMap_int p v r).symm
  exact Algebra.TensorProduct.lift (Algebra.ofId ℚ_[p] F[v])
    (IsScalarTower.toAlgHom ℤ_[p] O[v] F[v]) (fun _ _ ↦ Commute.all ..)

private theorem localHom_tmul (v : V[p]) (a : ℚ_[p]) (y : O[v]) :
    localHom p v (a ⊗ₜ[ℤ_[p]] y) = a • algebraMap O[v] F[v] y := by
  simp only [localHom, Algebra.TensorProduct.lift_tmul, Algebra.smul_def]
  rfl

private noncomputable def localEquiv (v : V[p]) : ℚ_[p] ⊗[ℤ_[p]] O[v] ≃ₐ[ℚ_[p]] F[v] := by
  letI : Algebra O[v] (ℚ_[p] ⊗[ℤ_[p]] O[v]) := Algebra.TensorProduct.rightAlgebra
  haveI := finiteCompletionOverPrime_isLocalization p v
  refine AlgEquiv.ofBijective (localHom p v) (IsLocalization.bijective
    (Algebra.algebraMapSubmonoid O[v] (ℤ_[p])⁰) (localHom p v).toRingHom ?_)
  apply RingHom.ext
  intro y
  change localHom p v ((1 : ℚ_[p]) ⊗ₜ[ℤ_[p]] y) = _
  rw [localHom_tmul, one_smul]

/-- Extending the canonical integral splitting to the base fraction field
identifies the fraction algebra with the actual completion fields over `p`. -/
public noncomputable def finiteCompletionFractionBaseChange : L ≃ₐ[ℚ_[p]] (∀ v : V[p], F[v]) := by
  classical
  letI := finiteCompletionOverPrimeFintype (K := K) p
  exact (Algebra.TensorProduct.congr (.refl : ℚ_[p] ≃ₐ[ℚ_[p]] ℚ_[p])
    (finiteCompletionIntegralBaseChange p)).trans
      ((Algebra.TensorProduct.piRight ℤ_[p] ℚ_[p] ℚ_[p] _).trans
        (AlgEquiv.piCongrRight fun v ↦ localEquiv p v))

/-- The fraction splitting extends the integral splitting by the actual
completion inclusions and the canonical completed field action. -/
public theorem finiteCompletionFractionBaseChange_tmul (a : ℚ_[p]) (t : A) (v : V[p]) :
    finiteCompletionFractionBaseChange p (a ⊗ₜ[ℤ_[p]] t) v =
      a • algebraMap O[v] F[v] (finiteCompletionIntegralBaseChange p t v) := by
  unfold finiteCompletionFractionBaseChange
  simp only [AlgEquiv.trans_apply, Algebra.TensorProduct.congr_apply,
    Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.piRight_tmul,
    AlgEquiv.piCongrRight_apply]
  exact localHom_tmul p v a _

private theorem local_moduleFinite (q : ℕ) [Fact q.Prime]
    (w : HeightOneSpectrum (𝓞 K)) (h : (finiteCompletionBasePrime w : ℕ) = q) :
    letI := transportedFieldAlgebra q w h
    Module.Finite ℚ_[q] (w.adicCompletion K) := by
  subst q
  exact finiteCompletion_moduleFinite w

/-- The trace on the fraction algebra is the sum of the actual local field traces. -/
public theorem finiteCompletionFractionBaseChange_trace (x : L) :
    letI := finiteCompletionOverPrimeFintype (K := K) p
    Algebra.trace ℚ_[p] L x = ∑ v : V[p],
      Algebra.trace ℚ_[p] F[v] (finiteCompletionFractionBaseChange p x v) := by
  let : Fintype V[p] := finiteCompletionOverPrimeFintype (K := K) p
  let (v : V[p]) : Module.Finite ℚ_[p] F[v] :=
    local_moduleFinite p v.1 (finiteCompletionBasePrime_eq_of_dvd_primeSpan p v)
  rw [← Algebra.trace_eq_of_algEquiv (finiteCompletionFractionBaseChange p)]
  exact algebraTrace_pi (fun v : V[p] ↦ Module.Free.chooseBasis ℚ_[p] F[v]) _

/-- The trace dual of the integral tensor lattice inside the fraction
algebra is the product of the local trace duals. A test supported at one
place isolates its trace, without a condition at any other place. -/
public theorem finiteCompletionFractionBaseChange_traceDual_iff (x : L) :
    (∀ t : A, Algebra.trace ℚ_[p] L (x * ((1 : ℚ_[p]) ⊗ₜ[ℤ_[p]] t)) ∈
      (algebraMap ℤ_[p] ℚ_[p]).range) ↔
    (∀ (v : V[p]) (y : O[v]), Algebra.trace ℚ_[p] F[v]
      (finiteCompletionFractionBaseChange p x v * algebraMap O[v] F[v] y) ∈
        (algebraMap ℤ_[p] ℚ_[p]).range) := by
  classical
  let : Fintype V[p] := finiteCompletionOverPrimeFintype (K := K) p
  have h (t : A) : Algebra.trace ℚ_[p] L (x * ((1 : ℚ_[p]) ⊗ₜ[ℤ_[p]] t)) =
      ∑ v : V[p], Algebra.trace ℚ_[p] F[v] (finiteCompletionFractionBaseChange p x v *
        algebraMap O[v] F[v] (finiteCompletionIntegralBaseChange p t v)) := by
    rw [finiteCompletionFractionBaseChange_trace]
    simp only [map_mul, Pi.mul_apply, finiteCompletionFractionBaseChange_tmul, one_smul]
  constructor
  · intro hx v y
    let z : (w : V[p]) → O[w] := Function.update 0 v y
    let t := (finiteCompletionIntegralBaseChange p).symm z
    have ht := hx t
    rw [h] at ht
    simp only [t, AlgEquiv.apply_symm_apply] at ht
    rw [Finset.sum_eq_single v] at ht
    · simpa [z] using ht
    · intro w _ hw
      simp [z, Function.update_of_ne hw]
    · simp
  · intro hx t
    rw [h]
    exact Subring.sum_mem _ fun v _ ↦ hx v (finiteCompletionIntegralBaseChange p t v)

end Masullo
