module

public import Lemmas.FiniteCompletionTraceIndex

/-! # From the trace-dual quotient to the quotient by the different

For the local normalization in (A.3.1.2), PDF p. 556, we identify the
trace dual with the inverse different. Multiplying by an integral
generator sends the trace dual onto the completion integers, carrying
the integer sublattice to the different ideal.
-/

open IsDedekindDomain NumberField
open scoped Masullo nonZeroDivisors

namespace Masullo

variable {K : Type*} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

local notation "p" => finiteCompletionBasePrime v
local notation "R" => ℤ_[p]
local notation "F" => v.adicCompletion K
local notation "O" => v.adicCompletionIntegers K
local notation "d" => differentIdeal R O
local notation "iO" => IsScalarTower.toAlgHom R O F
set_option quotPrecheck false in
local notation "D" => Submodule.traceDual R ℚ_[p] (1 : Submodule O F)
set_option quotPrecheck false in
local notation "D'" => (D).restrictScalars R

attribute [local instance] finiteCompletion_moduleFinite finiteCompletionIntegers_moduleFinite
  finiteCompletionIntegers_moduleFree

/-- The inverse of the actual local different is the local trace-dual lattice. -/
public theorem finiteCompletion_traceDual_eq_inv_differentIdeal :
    D = (((d : FractionalIdeal O⁰ F)⁻¹ : FractionalIdeal O⁰ F) : Submodule O F) := by
  rw [coeIdeal_differentIdeal R ℚ_[p] F O, inv_inv, FractionalIdeal.coeToSubmodule_dual_one]

private theorem localDifferent_ne_bot : d ≠ ⊥ := differentIdeal_ne_bot

private theorem localDifferent_generator_ne_zero (a : O) (ha : Ideal.span {a} = d) :
    (iO a : F) ≠ 0 := by
  intro h
  have h₀ : a = 0 := Subtype.ext h
  exact localDifferent_ne_bot v (by simpa [h₀] using ha.symm)

private theorem traceDual_eq_span_inv (a : O) (ha : Ideal.span {a} = d) :
    D = Submodule.span O {(iO a : F)⁻¹} := by
  rw [finiteCompletion_traceDual_eq_inv_differentIdeal v, ← ha,
    FractionalIdeal.coeIdeal_span_singleton, FractionalIdeal.spanSingleton_inv,
    FractionalIdeal.coeToSubmodule_spanSingleton]
  rfl

private noncomputable def divideGenerator (a : O) (ha : Ideal.span {a} = d) : O ≃ₗ[R] D' := by
  let f : O →ₗ[R] F := ((iO).toLinearMap).smulRight (iO a : F)⁻¹
  -- Divide by the generator in the field, then restrict to the trace dual.
  let j : O →ₗ[R] D' := f.codRestrict D' fun x ↦ by
    change ((iO x : F) * (iO a : F)⁻¹) ∈ D
    rw [traceDual_eq_span_inv v a ha, Submodule.mem_span_singleton]
    exact ⟨x, rfl⟩
  refine LinearEquiv.ofBijective j ⟨?_, ?_⟩
  · intro x y h
    apply Subtype.ext
    exact mul_right_cancel₀ (inv_ne_zero (localDifferent_generator_ne_zero v a ha))
      (congrArg (fun z : D' ↦ (z : F)) h)
  · intro x
    have hx : (x : F) ∈ Submodule.span O {(iO a : F)⁻¹} :=
      traceDual_eq_span_inv v a ha ▸ x.property
    obtain ⟨y, hy⟩ := Submodule.mem_span_singleton.mp hx
    exact ⟨y, Subtype.ext hy⟩

private theorem divideGenerator_apply (a : O) (ha : Ideal.span {a} = d) (x : O) :
    ((divideGenerator v a ha x : D') : F) = (iO x : F) * (iO a : F)⁻¹ := rfl

private theorem map_different_divideGenerator (a : O) (ha : Ideal.span {a} = d) :
    ((d).restrictScalars R).map (divideGenerator v a ha).toLinearMap =
      LinearMap.range (finiteCompletionIntegersToTraceDual v) := by
  ext z
  change (∃ x : O, x ∈ d ∧ divideGenerator v a ha x = z) ↔
    ∃ y : O, finiteCompletionIntegersToTraceDual v y = z
  simp only [← ha, Ideal.mem_span_singleton]
  have hm (y : O) : divideGenerator v a ha (a * y) = finiteCompletionIntegersToTraceDual v y := by
    apply Subtype.ext
    rw [divideGenerator_apply, coe_finiteCompletionIntegersToTraceDual, map_mul, mul_right_comm,
      mul_inv_cancel₀ (localDifferent_generator_ne_zero v a ha), one_mul]
  constructor
  · rintro ⟨_, ⟨y, rfl⟩, rfl⟩
    exact ⟨y, (hm y).symm⟩
  · rintro ⟨y, rfl⟩
    exact ⟨a * y, ⟨y, rfl⟩, hm y⟩

/-- Multiplication by a generator of the local different carries the trace-dual
quotient onto the quotient of the integers by the different. -/
public noncomputable def finiteCompletionTraceDualQuotientEquiv (a : O) (ha : Ideal.span {a} = d) :
    (D' ⧸ LinearMap.range (finiteCompletionIntegersToTraceDual v)) ≃ₗ[R] (O ⧸ d) :=
  (Submodule.Quotient.equiv ((d).restrictScalars R) _ (divideGenerator v a ha)
    (map_different_divideGenerator v a ha)).symm

/-- On representatives, the inverse comparison divides by the chosen generator. -/
public theorem finiteCompletionTraceDualQuotientEquiv_symm_mk (a : O) (ha : Ideal.span {a} = d)
    (x : O) (z : D') (hz : (z : F) = (iO x : F) * (iO a : F)⁻¹) :
    (finiteCompletionTraceDualQuotientEquiv v a ha).symm (Ideal.Quotient.mk d x) =
      Submodule.Quotient.mk z := by
  have h : divideGenerator v a ha x = z := Subtype.ext hz.symm
  change Submodule.Quotient.mk (divideGenerator v a ha x) = Submodule.Quotient.mk z
  rw [h]

end Masullo
