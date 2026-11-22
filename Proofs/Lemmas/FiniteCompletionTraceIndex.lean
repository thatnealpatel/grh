module

public import Lemmas.FiniteCompletionIntegralLattice
public import Mathlib.RingTheory.DedekindDomain.Different
public import Mathlib.RingTheory.Discriminant
import Lemmas.PadicLatticeIndex
import Mathlib.RingTheory.Localization.NormTrace

/-! # The local trace Gram cokernel

Masullo (A.3.1.2), PDF p. 556, uses the norm of the discriminant for
additive Haar normalization; (A.3.2.2), p. 560, uses it for multiplicative
Haar. This project calculation identifies its inverse with the index of
the integers in the local trace dual. It does not identify the local
trace dual with the extension of the global codifferent.
-/

open IsDedekindDomain NumberField Module
open scoped Masullo nonZeroDivisors

namespace Masullo

variable {K : Type*} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

local notation "p" => finiteCompletionBasePrime v
local notation "F" => v.adicCompletion K
local notation "O" => v.adicCompletionIntegers K
local notation "iO" => IsScalarTower.toAlgHom ℤ_[p] O F
set_option quotPrecheck false in
local notation "D" => (Submodule.traceDual ℤ_[p] ℚ_[p] (1 : Submodule O F)).restrictScalars ℤ_[p]

/-- The inclusion of the integer lattice in its trace dual, by the actual
completion inclusion and compatibility of integral and field trace. -/
public noncomputable def finiteCompletionIntegersToTraceDual : O →ₗ[ℤ_[p]] D := by
  letI := finiteCompletionIntegers_moduleFree v
  letI := finiteCompletionIntegers_moduleFinite v
  letI := finiteCompletionIntegers_isLocalization v
  refine (iO).toLinearMap.codRestrict D fun x ↦ ?_
  change ((iO) x : F) ∈ Submodule.traceDual ℤ_[p] ℚ_[p] (1 : Submodule O F)
  rw [Submodule.mem_traceDual]
  intro y hy
  obtain ⟨z, rfl⟩ := Submodule.mem_one.mp hy
  refine ⟨Algebra.trace ℤ_[p] O (x * z), ?_⟩
  rw [Algebra.traceForm_apply]
  change algebraMap ℤ_[p] ℚ_[p] (Algebra.trace ℤ_[p] O (x * z)) =
    Algebra.trace ℚ_[p] F (algebraMap O F x * algebraMap O F z)
  rw [← map_mul, Algebra.trace_localization ℤ_[p] (ℤ_[p])⁰]

/-- The trace-dual inclusion is the canonical field embedding on representatives. -/
public theorem coe_finiteCompletionIntegersToTraceDual (x : O) :
    ((finiteCompletionIntegersToTraceDual v x : D) : F) = iO x := by
  unfold finiteCompletionIntegersToTraceDual
  rfl

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

attribute [local instance] finiteCompletion_moduleFinite

local notation "G[" b "]" => Matrix.toLin' (Algebra.traceMatrix ℤ_[p] b)

private noncomputable def localBasis (b : Basis ι ℤ_[p] O) : Basis ι ℚ_[p] F := by
  letI := finiteCompletionIntegers_isLocalization v
  exact b.localizationLocalization ℚ_[p] (ℤ_[p])⁰ F

omit [Fintype ι] [DecidableEq ι] in
private theorem localBasis_apply (b : Basis ι ℤ_[p] O) (i : ι) : localBasis v b i = (iO) (b i) := by
  let := finiteCompletionIntegers_isLocalization v
  exact Basis.localizationLocalization_apply ℚ_[p] (ℤ_[p])⁰ F b i

private theorem traceDual_eq_span (b : Basis ι ℤ_[p] O) : D = Submodule.span ℤ_[p] (Set.range (localBasis v b).traceDual) := by
  apply Submodule.traceDual_span_of_basis
  have hl : (1 : Submodule O F).restrictScalars ℤ_[p] = LinearMap.range (iO).toLinearMap := by
    ext x
    exact Submodule.mem_one
  rw [hl, LinearMap.range_eq_map, ← b.span_eq, Submodule.map_span, ← Set.range_comp]
  congr 2
  funext i
  exact (localBasis_apply v b i).symm

private noncomputable def traceCoords (b : Basis ι ℤ_[p] O) : D ≃ₗ[ℤ_[p]] (ι → ℤ_[p]) := by
  exact (LinearEquiv.ofEq _ _ (traceDual_eq_span v b)).trans
    ((localBasis v b).traceDual.restrictScalars ℤ_[p]).equivFun

private theorem traceCoords_apply (b : Basis ι ℤ_[p] O) (x : D) (i : ι) :
    algebraMap ℤ_[p] ℚ_[p] (traceCoords v b x i) =
      Algebra.trace ℚ_[p] F ((x : F) * (iO) (b i)) := by
  simp only [traceCoords, LinearEquiv.trans_apply, Basis.equivFun_apply,
    Basis.restrictScalars_repr_apply, Basis.traceDual_repr_apply, Algebra.traceForm_apply,
    localBasis_apply, LinearEquiv.coe_ofEq_apply]

private theorem traceCoords_comp (b : Basis ι ℤ_[p] O) :
    (traceCoords v b).toLinearMap ∘ₗ finiteCompletionIntegersToTraceDual v =
      G[b] ∘ₗ b.equivFun.toLinearMap := by
  let := Module.Free.of_basis b
  let := Module.Finite.of_basis b
  let := finiteCompletionIntegers_isLocalization v
  apply b.ext
  intro j
  funext i
  apply (FaithfulSMul.algebraMap_injective ℤ_[p] ℚ_[p])
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, traceCoords_apply, Matrix.toLin'_apply,
    Matrix.mulVec, dotProduct, Basis.equivFun_self, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
    Finset.mem_univ, ite_true, Algebra.traceMatrix_apply, Algebra.traceForm_apply]
  change Algebra.trace ℚ_[p] F (algebraMap O F (b j) * algebraMap O F (b i)) = _
  rw [← map_mul, Algebra.trace_localization ℤ_[p] (ℤ_[p])⁰, mul_comm]

/-- The cokernel of the integral trace Gram matrix is the trace-dual
lattice modulo the integer lattice. The equivalence is induced by the
inverse of the trace-coordinate map for the integral basis. -/
public noncomputable def finiteCompletionTraceGramQuotientEquiv (b : Basis ι ℤ_[p] O) :
    ((ι → ℤ_[p]) ⧸ LinearMap.range G[b]) ≃ₗ[ℤ_[p]]
      (D ⧸ LinearMap.range (finiteCompletionIntegersToTraceDual v)) := by
  refine (Submodule.Quotient.equiv _ _ (traceCoords v b) ?_).symm
  rw [← LinearMap.range_comp, traceCoords_comp, LinearMap.range_comp,
    LinearEquiv.range, Submodule.map_top]

/-- The inverse quotient comparison sends a trace-dual representative
to the class of its integral trace coordinates. -/
public theorem finiteCompletionTraceGramQuotientEquiv_symm_mk (b : Basis ι ℤ_[p] O)
    (x : D) (c : ι → ℤ_[p])
    (hc : ∀ i, algebraMap ℤ_[p] ℚ_[p] (c i) = Algebra.trace ℚ_[p] F ((x : F) * (iO) (b i))) :
    (finiteCompletionTraceGramQuotientEquiv v b).symm (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk c := by
  have h : traceCoords v b x = c := funext fun i ↦
    FaithfulSMul.algebraMap_injective ℤ_[p] ℚ_[p] ((traceCoords_apply v b x i).trans (hc i).symm)
  change Submodule.Quotient.mk (traceCoords v b x) = _
  rw [h]

/-- The base p-adic norm of the local discriminant is the reciprocal
index of the integer lattice in the local trace dual. -/
public theorem finiteCompletion_norm_discr_eq_inv_card_traceDual_quotient (b : Basis ι ℤ_[p] O) :
    ‖Algebra.discr ℤ_[p] b‖ =
      (Nat.card (D ⧸ LinearMap.range (finiteCompletionIntegersToTraceDual v)) : ℝ)⁻¹ := by
  have hI : Function.Injective (finiteCompletionIntegersToTraceDual v) := fun x y h ↦
    Subtype.ext (congrArg (fun z : D ↦ (z : F)) h)
  have hc : Function.Injective (G[b] ∘ₗ b.equivFun.toLinearMap) := by
    rw [← traceCoords_comp v b]
    exact (traceCoords v b).injective.comp hI
  have hG : Function.Injective G[b] := by
    intro x y h
    obtain ⟨x, rfl⟩ := b.equivFun.surjective x
    obtain ⟨y, rfl⟩ := b.equivFun.surjective y
    exact congrArg b.equivFun (hc h)
  rw [Algebra.discr_def, ← LinearMap.det_toLin',
    padicInt_norm_det_eq_inv_card_quotient_range G[b] hG,
    Nat.card_congr (finiteCompletionTraceGramQuotientEquiv v b).toEquiv]

/-- The trace-dual lattice quotient has finite cardinality. -/
public theorem finite_finiteCompletionTraceDual_quotient (b : Basis ι ℤ_[p] O) :
    Finite (D ⧸ LinearMap.range (finiteCompletionIntegersToTraceDual v)) := by
  let := finiteCompletionIntegers_isLocalization v
  apply Nat.finite_of_card_ne_zero
  intro h
  have hd := finiteCompletion_norm_discr_eq_inv_card_traceDual_quotient v b
  simp only [h, Nat.cast_zero, inv_zero, norm_eq_zero] at hd
  apply Algebra.discr_not_zero_of_basis ℚ_[p] (localBasis v b)
  change Algebra.discr ℚ_[p] (b.localizationLocalization ℚ_[p] (ℤ_[p])⁰ F) = 0
  rw [Algebra.discr_localizationLocalization, hd, map_zero]

end Masullo
