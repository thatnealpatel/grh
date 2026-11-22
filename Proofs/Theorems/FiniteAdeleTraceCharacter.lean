module

public import Theorems.NumberFieldDiagonalPhase
public import Mathlib.NumberTheory.NumberField.AdeleRing

/-! # The finite part of the corrected number-field adelic character

Example A.3.1.10, PDF p. 558, supplies the positive local trace characters.
For the global pairing of (A.3.1.7), use their conjugates, while keeping the
positive Archimedean phase. The diagonal repair is `numberFieldDiagonal_phase_eq_one`.
Here the unit tail makes the product on actual finite adeles well-defined and
continuous. Conjugating for (2.2.4.32), p. 92, leaves the positive finite kernel.
Source reading: Provisional Markdown and numbered PDF layout.
-/

open NumberField IsDedekindDomain Filter Set Topology Function
open scoped BigOperators ComplexConjugate Masullo Padic RestrictedProduct

namespace Masullo

variable {K : Type*} [Field K] [NumberField K]

local notation "V" => HeightOneSpectrum (𝓞 K)
local notation:max "F" v:max => HeightOneSpectrum.adicCompletion K v
local notation:max "O" v:max => HeightOneSpectrum.adicCompletionIntegers K v
local notation "Af" => FiniteAdeleRing (𝓞 K) K

/-- The positive `p`-adic character pulled back by the trace of the actual completion. -/
@[expose] public noncomputable def finiteCompletionTraceAddChar (v : V) : AddChar (F v) ℂ :=
  (padicStdAddChar (finiteCompletionBasePrime v)).compAddMonoidHom
    (Algebra.trace ℚ_[finiteCompletionBasePrime v] (F v)).toAddMonoidHom

public theorem finiteCompletionTraceAddChar_apply (v : V) (x : F v) :
    finiteCompletionTraceAddChar v x = padicStdAddChar (finiteCompletionBasePrime v)
      (Algebra.trace ℚ_[finiteCompletionBasePrime v] (F v) x) := rfl

private theorem continuous_localTrace (v : V) :
    Continuous (finiteCompletionTraceAddChar v : F v → ℂ) := by
  let _ := finiteCompletion_moduleFinite v
  change Continuous (fun x : F v ↦ padicStdAddChar (finiteCompletionBasePrime v)
    (Algebra.trace ℚ_[finiteCompletionBasePrime v] (F v) x))
  exact (continuous_padicStdAddChar _).comp
    (Algebra.trace ℚ_[finiteCompletionBasePrime v] (F v)).continuous_of_finiteDimensional

private theorem localTrace_eq_one (v : V) {x : F v} (hx : x ∈ O v) :
    finiteCompletionTraceAddChar v x = 1 :=
  finiteCompletion_traceChar_eq_one_of_integral v ⟨x, hx⟩

private theorem finite_support (a : Af) :
    HasFiniteMulSupport (fun v : V ↦ conj (finiteCompletionTraceAddChar v (a v))) := by
  refine (eventually_cofinite.mp a.cofinite_mem_adicCompletionIntegers).subset ?_
  intro v hv hx
  apply hv
  change conj (finiteCompletionTraceAddChar v (a v)) = 1
  rw [localTrace_eq_one v hx, map_one]

/-- The product of conjugate trace phases on the actual finite adele ring.
It is an additive character since the local products have finite support. -/
@[expose] public noncomputable def numberFieldFiniteAdeleAddChar : AddChar Af ℂ where
  toFun a := ∏ᶠ v : V, conj (finiteCompletionTraceAddChar v (a v))
  map_zero_eq_one' := by
    change (∏ᶠ v : V, conj (finiteCompletionTraceAddChar v 0)) = 1
    simp
  map_add_eq_mul' a b := by
    change (∏ᶠ v : V, conj (finiteCompletionTraceAddChar v (a v + b v))) = _
    simp only [AddChar.map_add_eq_mul, map_mul]
    exact finprod_mul_distrib (finite_support a) (finite_support b)

/-- Any set containing the nonintegral coordinates computes the product. -/
public theorem numberFieldFiniteAdeleAddChar_eq_prod (a : Af) (S : Finset V)
    (hS : ∀ v ∉ S, a v ∈ O v) :
    numberFieldFiniteAdeleAddChar a = ∏ v ∈ S, conj (finiteCompletionTraceAddChar v (a v)) := by
  apply finprod_eq_prod_of_mulSupport_subset
  intro v hv
  by_contra h
  apply hv
  change conj (finiteCompletionTraceAddChar v (a v)) = 1
  rw [localTrace_eq_one v (hS v h), map_one]

/-- Continuity for the actual restricted-product topology. On each stage the
character is a finite product of continuous projected local trace phases. -/
public theorem continuous_numberFieldFiniteAdeleAddChar :
    Continuous (numberFieldFiniteAdeleAddChar : Af → ℂ) := by
  apply RestrictedProduct.continuous_dom.mpr
  intro S hS
  classical
  let T := (mem_cofinite.mp (le_principal_iff.mp hS)).toFinset
  have hT (v : V) : v ∉ T → v ∈ S := by simp [T]
  have heq : numberFieldFiniteAdeleAddChar ∘ RestrictedProduct.inclusion _ _ hS =
      fun a ↦ ∏ v ∈ T, conj (finiteCompletionTraceAddChar v (a v)) := by
    funext a
    apply numberFieldFiniteAdeleAddChar_eq_prod
    intro v hv
    exact (eventually_principal.mp a.property) v (hT v hv)
  have hc := continuous_finsetProd T fun v _ ↦ Complex.continuous_conj.comp <|
    (continuous_localTrace v).comp
      (RestrictedProduct.continuous_eval (R := fun v : V ↦ F v)
        (A := fun v : V ↦ (O v : Set (F v))) (𝓕 := 𝓟 S) v)
  exact heq.symm ▸ hc

/-- The finite Fourier kernel on a stage has positive local phases. -/
public theorem conj_numberFieldFiniteAdeleAddChar_eq_prod (a : Af) (S : Finset V)
    (hS : ∀ v ∉ S, a v ∈ O v) :
    conj (numberFieldFiniteAdeleAddChar a) = ∏ v ∈ S, finiteCompletionTraceAddChar v (a v) := by
  rw [numberFieldFiniteAdeleAddChar_eq_prod a S hS, map_prod]
  simp only [Complex.conj_conj]

/-- The character takes values of absolute value one. -/
public theorem norm_numberFieldFiniteAdeleAddChar (a : Af) :
    ‖numberFieldFiniteAdeleAddChar a‖ = 1 := by
  classical
  let S := (eventually_cofinite.mp a.cofinite_mem_adicCompletionIntegers).toFinset
  have hS (v : V) : v ∉ S → a v ∈ O v := by simp [S]
  rw [numberFieldFiniteAdeleAddChar_eq_prod a S hS, norm_prod]
  simp only [Complex.norm_conj, finiteCompletionTraceAddChar_apply, norm_padicStdAddChar,
    Finset.prod_const_one]

/-- On the diagonal this part cancels the positive Archimedean trace phase. -/
public theorem numberFieldFiniteAdeleAddChar_diagonal (x : K) :
    Complex.exp (2 * Real.pi * Complex.I * (Algebra.trace ℚ K x : ℂ)) *
      numberFieldFiniteAdeleAddChar (algebraMap K Af x) = 1 := by
  unfold numberFieldFiniteAdeleAddChar
  change _ * (∏ᶠ v : V, conj (finiteCompletionTraceAddChar v ((algebraMap K Af x) v))) = 1
  have h (v : V) : finiteCompletionTraceAddChar v ((algebraMap K Af x) v) =
      finiteCompletionDiagonalPhase v x := by
    rw [finiteCompletionTraceAddChar_apply, finiteCompletionDiagonalPhase_apply]
    rfl
  simp_rw [h]
  exact numberFieldDiagonal_phase_eq_one x

end Masullo
