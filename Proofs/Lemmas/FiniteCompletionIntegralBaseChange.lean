module

public import Lemmas.FiniteCompletionCRT
public import Lemmas.FiniteCompletionIntegralLattice
public import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.RingTheory.Nakayama
import Mathlib.RingTheory.TensorProduct.Finite

/-! # Integral base change at a rational prime

For the local discriminant in Masullo (A.3.2.2), p. 560, we need to
compare the global integer ring with the actual completion integers.
This project result lifts the canonical Chinese remainder comparison
modulo `p`, using Nakayama on the target and on the kernel. It does not
yet compare the trace duals or compute the discriminant.
-/

open IsDedekindDomain NumberField
open scoped TensorProduct Pointwise nonZeroDivisors

namespace Masullo

variable {K : Type*} [Field K] [NumberField K]

local notation "P[" p "]" => Ideal.span ({(p : 𝓞 K)} : Set (𝓞 K))
local notation "V[" p "]" => {v : HeightOneSpectrum (𝓞 K) // HeightOneSpectrum.asIdeal v ∣ P[p]}
local notation "O[" v "]" => HeightOneSpectrum.adicCompletionIntegers K (Subtype.val v)
local notation "i[" v "]" => algebraMap (𝓞 K) O[v]

/-- At a place dividing `p𝓞 K`, the previously constructed base prime is `p`. -/
public theorem finiteCompletionBasePrime_eq_of_dvd_primeSpan (p : ℕ) [hp : Fact p.Prime]
    (v : V[p]) : (finiteCompletionBasePrime v.1 : ℕ) = p := by
  apply (Nat.prime_dvd_prime_iff_eq (finiteCompletionBasePrime v.1).property hp.out).mp
  rw [finiteCompletionBasePrime_val]
  apply (Rat.HeightOneSpectrum.natGenerator_dvd_iff _).mpr
  rw [← map_natCast (Rat.IsIntegralClosure.intEquiv ℤ)]
  apply Ideal.apply_mem_of_equiv_iff.mpr
  change (↑p : ℤ) ∈ v.1.asIdeal.under ℤ
  rw [Ideal.mem_under, map_natCast]
  exact (finitePlace_dvd_primeSpan_iff p v.1).mp v.2

@[instance_reducible] private noncomputable def transportedAlgebra (p : ℕ) [Fact p.Prime]
    (v : HeightOneSpectrum (𝓞 K)) (h : (finiteCompletionBasePrime v : ℕ) = p) :
    Algebra ℤ_[p] (v.adicCompletionIntegers K) := by
  subst p
  exact finiteCompletionPadicIntAlgebra v

/-- The base action at a place over `p` is the canonical completed map,
transported to the common rational prime. -/
@[instance_reducible] public noncomputable def finiteCompletionOverPrimeAlgebra (p : ℕ) [Fact p.Prime]
    (v : V[p]) : Algebra ℤ_[p] O[v] :=
  transportedAlgebra p v.1 (finiteCompletionBasePrime_eq_of_dvd_primeSpan p v)

attribute [local instance] finiteCompletionOverPrimeAlgebra

private theorem algebraMap_transportedAlgebra (p : ℕ) [Fact p.Prime]
    (v : HeightOneSpectrum (𝓞 K)) (h : (finiteCompletionBasePrime v : ℕ) = p) (a : ℤ_[p]) :
    letI := transportedAlgebra p v h
    algebraMap ℤ_[p] (v.adicCompletionIntegers K) a =
      finiteCompletionPadicIntMap v (cast (by subst p; rfl) a) := by
  subst p
  rfl

/-- The transported base map is the checked completed map on the same
`p`-adic integer, cast back to the prime attached to the place. -/
public theorem finiteCompletionOverPrimeAlgebra_algebraMap (p : ℕ) [Fact p.Prime]
    (v : V[p]) (a : ℤ_[p]) : algebraMap ℤ_[p] O[v] a =
      finiteCompletionPadicIntMap v.1
        (cast (congrArg (fun q : Nat.Primes ↦ @PadicInt q.1 ⟨q.2⟩)
          (show (⟨p, Fact.out⟩ : Nat.Primes) = finiteCompletionBasePrime v.1 from
            (Subtype.ext (finiteCompletionBasePrime_eq_of_dvd_primeSpan p v)).symm)) a) :=
  algebraMap_transportedAlgebra p v.1 (finiteCompletionBasePrime_eq_of_dvd_primeSpan p v) a

private theorem injective_transportedAlgebra (p : ℕ) [Fact p.Prime]
    (v : HeightOneSpectrum (𝓞 K)) (h : (finiteCompletionBasePrime v : ℕ) = p) :
    letI := transportedAlgebra p v h
    Function.Injective (algebraMap ℤ_[p] (v.adicCompletionIntegers K)) := by
  subst p
  intro a b hab
  change finiteCompletionPadicIntMap v a = finiteCompletionPadicIntMap v b at hab
  apply Subtype.ext
  apply (finiteCompletionPadicMap v).injective
  simpa only [coe_finiteCompletionPadicIntMap] using congrArg Subtype.val hab

private theorem finite_transportedAlgebra (p : ℕ) [Fact p.Prime]
    (v : HeightOneSpectrum (𝓞 K)) (h : (finiteCompletionBasePrime v : ℕ) = p) :
    letI := transportedAlgebra p v h
    Module.Finite ℤ_[p] (v.adicCompletionIntegers K) := by
  subst p
  exact finiteCompletionIntegers_moduleFinite v

private theorem free_transportedAlgebra (p : ℕ) [Fact p.Prime]
    (v : HeightOneSpectrum (𝓞 K)) (h : (finiteCompletionBasePrime v : ℕ) = p) :
    letI := transportedAlgebra p v h
    Module.Free ℤ_[p] (v.adicCompletionIntegers K) := by
  subst p
  exact finiteCompletionIntegers_moduleFree v

/-- The local integer lattice is free over the common base prime, with the
scalar action used by the integral base-change equivalence. -/
public theorem finiteCompletionOverPrime_moduleFree (p : ℕ) [Fact p.Prime] (v : V[p]) :
    Module.Free ℤ_[p] O[v] :=
  free_transportedAlgebra p v.1 (finiteCompletionBasePrime_eq_of_dvd_primeSpan p v)

/-- The local integer lattice is finite over the common base prime. -/
public theorem finiteCompletionOverPrime_moduleFinite (p : ℕ) [Fact p.Prime] (v : V[p]) :
    Module.Finite ℤ_[p] O[v] :=
  finite_transportedAlgebra p v.1 (finiteCompletionBasePrime_eq_of_dvd_primeSpan p v)

private theorem isLocalization_transportedAlgebra (p : ℕ) [Fact p.Prime]
    (v : HeightOneSpectrum (𝓞 K)) (h : (finiteCompletionBasePrime v : ℕ) = p) :
    letI := transportedAlgebra p v h
    IsLocalization (Algebra.algebraMapSubmonoid (v.adicCompletionIntegers K) (ℤ_[p])⁰)
      (v.adicCompletion K) := by
  subst p
  exact finiteCompletionIntegers_isLocalization v

/-- The actual local field inverts the nonzero integers of the common base prime. -/
public theorem finiteCompletionOverPrime_isLocalization (p : ℕ) [Fact p.Prime] (v : V[p]) :
    IsLocalization (Algebra.algebraMapSubmonoid O[v] (ℤ_[p])⁰) (v.1.adicCompletion K) :=
  isLocalization_transportedAlgebra p v.1 (finiteCompletionBasePrime_eq_of_dvd_primeSpan p v)

variable (p : ℕ) [hp : Fact p.Prime]

local notation "A" => ℤ_[p] ⊗[ℤ] 𝓞 K
set_option quotPrecheck false in
local notation "B" => (∀ v : V[p], O[v])
local notation "π" => (p : ℤ_[p])

private noncomputable def diagonal : 𝓞 K →+* B where
  toFun x v := i[v] x
  map_one' := funext fun _ ↦ map_one _
  map_zero' := funext fun _ ↦ map_zero _
  map_add' _ _ := funext fun _ ↦ map_add _ _ _
  map_mul' _ _ := funext fun _ ↦ map_mul _ _ _

private noncomputable def baseChangeHom : A →ₐ[ℤ_[p]] B :=
  Algebra.TensorProduct.lift (Algebra.ofId ℤ_[p] B) (diagonal p).toIntAlgHom
    (fun _ _ ↦ Commute.all ..)

private noncomputable def incl : 𝓞 K →ₐ[ℤ] A := Algebra.TensorProduct.includeRight

private theorem baseChangeHom_tmul (a : ℤ_[p]) (x : 𝓞 K) (v : V[p]) :
    baseChangeHom p (a ⊗ₜ[ℤ] x) v = a • i[v] x := by
  unfold baseChangeHom
  rw [Algebra.TensorProduct.lift_tmul, Algebra.smul_def]
  rfl

private theorem baseChangeHom_incl (x : 𝓞 K) (v : V[p]) :
    baseChangeHom p (incl p x) v = i[v] x := by
  change baseChangeHom p (1 ⊗ₜ[ℤ] x) v = _
  rw [baseChangeHom_tmul, one_smul]

omit [NumberField K] in
private theorem source_reduction (u : A) : ∃ x : 𝓞 K, ∃ z : A, u = incl p x + π • z := by
  induction u using TensorProduct.inductionOn with
  | tmul a x =>
    have h := PadicInt.sub_zmodRepr_mem a
    rw [PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton] at h
    obtain ⟨r, hr⟩ := h
    refine ⟨a.zmodRepr • x, r ⊗ₜ[ℤ] x, ?_⟩
    have ha : a = (a.zmodRepr : ℤ_[p]) + π * r := by
      rw [← hr, add_sub_cancel]
    conv_lhs => rw [ha, TensorProduct.add_tmul]
    change _ = (1 : ℤ_[p]) ⊗ₜ[ℤ] (a.zmodRepr • x) + π • (r ⊗ₜ[ℤ] x)
    change _ = _ + (π • r) ⊗ₜ[ℤ] x
    rw [smul_eq_mul, ← natCast_zsmul x, ← TensorProduct.smul_tmul (R := ℤ)]
    simp
  | add u w hu hw =>
    obtain ⟨x, z, rfl⟩ := hu
    obtain ⟨y, t, rfl⟩ := hw
    exact ⟨x + y, z + t, by rw [map_add, smul_add]; abel⟩

private theorem target_reduction (y : B) : ∃ x : 𝓞 K, ∃ z : B,
    y = baseChangeHom p (incl p x) + π • z := by
  classical
  let P' (v : V[p]) := Ideal.span ({(p : O[v])} : Set O[v])
  obtain ⟨q, hq⟩ := (finiteCompletionModPrimeEquiv (K := K) p).surjective
    (fun v ↦ Ideal.Quotient.mk (P' v) (y v))
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective q
  have h (v : V[p]) : (p : O[v]) ∣ y v - i[v] x := by
    have hv := congrFun hq v
    rw [finiteCompletionModPrimeEquiv_mk] at hv
    exact Ideal.mem_span_singleton.mp (Ideal.Quotient.eq.mp hv.symm)
  choose z hz using h
  refine ⟨x, z, funext fun v ↦ ?_⟩
  change y v = baseChangeHom p (incl p x) v + π • z v
  rw [baseChangeHom_incl, Algebra.smul_def, map_natCast, ← hz, add_sub_cancel]

private theorem source_dvd_of_target_dvd (u : A) (y : B) (h : baseChangeHom p u = π • y) :
    ∃ z : A, u = π • z := by
  obtain ⟨x, z, rfl⟩ := source_reduction p u
  rw [map_add, map_smul] at h
  have hx : Ideal.Quotient.mk P[p] x = Ideal.Quotient.mk P[p] 0 := by
    apply (finiteCompletionModPrimeEquiv p).injective
    funext v
    rw [finiteCompletionModPrimeEquiv_mk, finiteCompletionModPrimeEquiv_mk, map_zero, map_zero]
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    apply Ideal.mem_span_singleton.mpr
    have hv := congrFun h v
    change baseChangeHom p (incl p x) v + π • baseChangeHom p z v = π • y v at hv
    simp only [baseChangeHom_incl, Algebra.smul_def, map_natCast] at hv
    exact ⟨y v - baseChangeHom p z v, by rw [mul_sub, ← hv, add_sub_cancel_right]⟩
  obtain ⟨t, ht⟩ := Ideal.mem_span_singleton.mp (by simpa using Ideal.Quotient.eq.mp hx)
  refine ⟨incl p t + z, ?_⟩
  simp only [ht, map_mul, map_natCast, smul_add]
  have hπ : π • incl p t = (p : A) * incl p t :=
    (Algebra.smul_def π (incl p t)).trans (congrArg (· * incl p t) (map_natCast _ p))
  rw [hπ]

private theorem primeSpan_le_jacobson : Ideal.span ({π} : Set ℤ_[p]) ≤ Ring.jacobson ℤ_[p] := by
  rw [← PadicInt.maximalIdeal_eq_span_p, IsLocalRing.ringJacobson_eq_maximalIdeal]

private theorem baseChangeHom_surjective : Function.Surjective (baseChangeHom (K := K) p) := by
  classical
  let : Finite V[p] := (Ideal.finite_factors (I := P[p])
    (mt Ideal.span_singleton_eq_bot.mp (Nat.cast_ne_zero.mpr hp.out.ne_zero)))
  let (v : V[p]) : Module.Finite ℤ_[p] O[v] := finiteCompletionOverPrime_moduleFinite p v
  rw [← funext (baseChangeHom p).toLinearMap_apply]
  have : Module.Finite ℤ_[p] B := inferInstance
  refine LinearMap.surjective_of_surjective_comp_mkQ (baseChangeHom (K := K) p).toLinearMap
    (Ideal.span {π}) (primeSpan_le_jacobson p) ?_
  intro q
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  obtain ⟨x, z, hy⟩ := target_reduction p y
  refine ⟨incl p x, (Submodule.Quotient.eq _).mpr ?_⟩
  rw [AlgHom.toLinearMap_apply, hy, sub_add_cancel_left, Submodule.ideal_span_singleton_smul]
  exact (Submodule.mem_smul_pointwise_iff_exists _ _ _).mpr ⟨-z, Submodule.mem_top, smul_neg ..⟩

private theorem baseChangeHom_injective : Function.Injective (baseChangeHom (K := K) p) := by
  let f := (baseChangeHom (K := K) p).toLinearMap
  change Function.Injective f
  apply LinearMap.ker_eq_bot.mp
  apply Submodule.eq_bot_of_le_smul_of_le_jacobson (Ideal.span {π}) f.ker
    (IsNoetherian.noetherian _) _ (primeSpan_le_jacobson p)
  intro u hu
  have h : baseChangeHom p u = π • (0 : B) := by
    simpa [f, AlgHom.toLinearMap_apply] using (LinearMap.mem_ker.mp hu)
  obtain ⟨z, hz⟩ := source_dvd_of_target_dvd p u 0 h
  rw [Submodule.ideal_span_singleton_smul]
  refine (Submodule.mem_smul_pointwise_iff_exists _ _ _).mpr ⟨z, ?_, hz.symm⟩
  apply LinearMap.mem_ker.mpr
  rw [show f z = baseChangeHom p z from (baseChangeHom p).toLinearMap_apply z]
  have he : baseChangeHom p (π • z) = 0 := by rw [← hz, h, smul_zero]
  rw [map_smul] at he
  funext v
  have hv := congrFun he v
  change π • baseChangeHom p z v = 0 at hv
  rw [Algebra.smul_def, mul_eq_zero] at hv
  refine hv.resolve_left fun hzero ↦ (Nat.cast_ne_zero.mpr hp.out.ne_zero : π ≠ 0) ?_
  exact injective_transportedAlgebra p v.1 (finiteCompletionBasePrime_eq_of_dvd_primeSpan p v)
    (hzero.trans (map_zero _).symm)

/-- The canonical integral base change splits into the actual finite
completion integers at the places over the chosen rational prime. -/
public noncomputable def finiteCompletionIntegralBaseChange : A ≃ₐ[ℤ_[p]] B :=
  AlgEquiv.ofBijective (baseChangeHom p) ⟨baseChangeHom_injective p, baseChangeHom_surjective p⟩

/-- The map uses the canonical embedding of each global integer and the
completed base action in each coordinate. -/
public theorem finiteCompletionIntegralBaseChange_tmul (a : ℤ_[p]) (x : 𝓞 K) (v : V[p]) :
    finiteCompletionIntegralBaseChange p (a ⊗ₜ[ℤ] x) v = a • i[v] x :=
  baseChangeHom_tmul p a x v

end Masullo
