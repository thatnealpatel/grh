module

public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.Padics.HeightOneSpectrum
public import Lemmas.RationalPadicPhase

/-! # The finite factor of the rational adelic character -/

open NumberField IsDedekindDomain Filter Set Topology Function
open scoped BigOperators ComplexConjugate Padic RestrictedProduct

namespace Masullo

local notation "V" => HeightOneSpectrum (𝓞 ℚ)
local notation:max "F" v:max => HeightOneSpectrum.adicCompletion ℚ v
local notation:max "O" v:max => HeightOneSpectrum.adicCompletionIntegers ℚ v
local notation "pOf" => Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)
local notation "ePadic" => Rat.HeightOneSpectrum.adicCompletion.padicEquiv

local instance (v : V) : Fact (pOf v : ℕ).Prime := ⟨(pOf v).property⟩

/-- The conjugate of the positive standard character, transported to the finite completion. -/
public noncomputable def rationalLocalFiniteAddChar (v : V) : AddChar (F v) ℂ where
  toFun x := conj (padicStdAddChar (pOf v : ℕ) (ePadic v x))
  map_zero_eq_one' := by simp
  map_add_eq_mul' x y := by rw [map_add, AddChar.map_add_eq_mul, map_mul]

public theorem rationalLocalFiniteAddChar_apply (v : V) (x : F v) :
    rationalLocalFiniteAddChar v x =
      conj (@padicStdAddChar (pOf v : ℕ) ⟨(pOf v).property⟩ (ePadic v x)) := by
  rfl

public theorem rationalLocalFiniteAddChar_eq_one_iff (v : V) (x : F v) :
    rationalLocalFiniteAddChar v x = 1 ↔ x ∈ O v := by
  rw [rationalLocalFiniteAddChar_apply, ← map_one (starRingEnd ℂ),
    (show Injective (conj : ℂ → ℂ) from star_injective).eq_iff,
    padicStdAddChar_eq_one_iff]
  have h := Rat.HeightOneSpectrum.adicCompletion.padicEquiv_bijOn v
  change ePadic v x ∈ PadicInt.subring (pOf v) ↔ _
  refine ⟨fun hx ↦ ?_, fun hx ↦ h.mapsTo hx⟩
  obtain ⟨y, hy, heq⟩ := h.surjOn hx
  exact (ePadic v).injective heq ▸ hy

public theorem rationalLocalFiniteAddChar_rat (v : V) (r : ℚ) :
    rationalLocalFiniteAddChar v (algebraMap ℚ (F v) r) = conj (rationalPadicPhase (pOf v) r) := by
  rw [rationalLocalFiniteAddChar_apply, AlgHomClass.commutes, rationalPadicPhase_apply]
  rfl

private theorem continuous_rationalLocalFiniteAddChar (v : V) :
    Continuous (rationalLocalFiniteAddChar v : F v → ℂ) :=
  Complex.continuous_conj.comp <|
    (continuous_padicStdAddChar (pOf v : ℕ)).comp (ePadic v).continuous

private theorem finite_support (a : FiniteAdeleRing (𝓞 ℚ) ℚ) :
    HasFiniteMulSupport (fun v : V ↦ rationalLocalFiniteAddChar v (a v)) := by
  refine (eventually_cofinite.mp a.cofinite_mem_adicCompletionIntegers).subset fun v hv ↦ ?_
  exact fun h ↦ hv ((rationalLocalFiniteAddChar_eq_one_iff v (a v)).mpr h)

/-- All but finitely many factors in this product are one by adelic integrality. -/
public noncomputable def rationalFiniteAdeleAddChar : AddChar (FiniteAdeleRing (𝓞 ℚ) ℚ) ℂ where
  toFun a := ∏ᶠ v : V, rationalLocalFiniteAddChar v (a v)
  map_zero_eq_one' := by
    change (∏ᶠ v : V, rationalLocalFiniteAddChar v 0) = 1
    simp
  map_add_eq_mul' a b := by
    change (∏ᶠ v : V, rationalLocalFiniteAddChar v (a v + b v)) = _
    simp only [AddChar.map_add_eq_mul]
    exact finprod_mul_distrib (finite_support a) (finite_support b)

public theorem rationalFiniteAdeleAddChar_eq_prod (a : FiniteAdeleRing (𝓞 ℚ) ℚ) (S : Finset V)
    (hS : ∀ v ∉ S, a v ∈ O v) :
    rationalFiniteAdeleAddChar a = ∏ v ∈ S, rationalLocalFiniteAddChar v (a v) := by
  apply finprod_eq_prod_of_mulSupport_subset
  intro v hv
  by_contra h
  exact hv ((rationalLocalFiniteAddChar_eq_one_iff v (a v)).mpr (hS v h))

public theorem continuous_rationalFiniteAdeleAddChar :
    Continuous (rationalFiniteAdeleAddChar : FiniteAdeleRing (𝓞 ℚ) ℚ → ℂ) := by
  apply RestrictedProduct.continuous_dom.mpr
  intro S hS
  classical
  let T := (mem_cofinite.mp (le_principal_iff.mp hS)).toFinset
  have hT (v : V) : v ∉ T → v ∈ S := by
    simp [T]
  have heq : rationalFiniteAdeleAddChar ∘ RestrictedProduct.inclusion _ _ hS =
      fun a ↦ ∏ v ∈ T, rationalLocalFiniteAddChar v (a v) := by
    funext a
    apply rationalFiniteAdeleAddChar_eq_prod
    intro v hv
    exact (eventually_principal.mp a.property) v (hT v hv)
  have hc := continuous_finsetProd T fun v _ ↦
    (continuous_rationalLocalFiniteAddChar v).comp
      (RestrictedProduct.continuous_eval (R := fun v : V ↦ F v)
        (A := fun v : V ↦ (O v : Set (F v))) (𝓕 := 𝓟 S) v)
  exact heq.symm ▸ hc

public theorem norm_rationalFiniteAdeleAddChar (a : FiniteAdeleRing (𝓞 ℚ) ℚ) :
    ‖rationalFiniteAdeleAddChar a‖ = 1 := by
  classical
  let S := (eventually_cofinite.mp a.cofinite_mem_adicCompletionIntegers).toFinset
  have hS : ∀ v ∉ S, a v ∈ O v := by
    intro v hv
    simpa [S] using hv
  rw [rationalFiniteAdeleAddChar_eq_prod a S hS, norm_prod]
  simp only [rationalLocalFiniteAddChar_apply, Complex.norm_conj, norm_padicStdAddChar,
    Finset.prod_const_one]

end Masullo
