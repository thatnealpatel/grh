module

public import Theorems.FiniteCompletionIntegersFourier

/-! # The second annihilator at a finite completion -/

open IsDedekindDomain MeasureTheory NumberField Set
open scoped Masullo nonZeroDivisors

namespace Masullo

variable {K : Type*} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
local notation "p" => finiteCompletionBasePrime v
local notation "F" => v.adicCompletion K
local notation "O" => v.adicCompletionIntegers K
local notation "Diff" => differentIdeal ℤ_[p] O
local notation "C" => ((Diff : FractionalIdeal O⁰ F)⁻¹ : FractionalIdeal O⁰ F)
attribute [local instance] finiteCompletion_moduleFinite finiteCompletionIntegers_moduleFinite
  finiteCompletionIntegers_moduleFree

private theorem generator_ne_zero (a : O) (ha : Ideal.span {a} = Diff) : (a : F) ≠ 0 := by
  intro h
  have h₀ : a = 0 := Subtype.ext h
  exact differentIdeal_ne_bot (by simpa [h₀] using ha.symm)

/-- For any generator of the different, the codifferent is `a⁻¹ O`, expressed
as the inverse image of the integer ring under multiplication by `a`. -/
public theorem finiteCompletion_mem_codifferent_iff (a : O) (ha : Ideal.span {a} = Diff) (x : F) :
    x ∈ C ↔ (a : F) * x ∈ O := by
  change x ∈ (C : Submodule O F) ↔ _
  rw [← ha, FractionalIdeal.coeIdeal_span_singleton, FractionalIdeal.spanSingleton_inv,
    FractionalIdeal.coeToSubmodule_spanSingleton, Submodule.mem_span_singleton]
  have h := generator_ne_zero v a ha
  constructor
  · rintro ⟨y, rfl⟩
    change (a : F) * ((y : F) * (a : F)⁻¹) ∈ O
    rw [mul_left_comm, mul_inv_cancel₀ h, mul_one]
    exact y.property
  · intro hx
    refine ⟨⟨_, hx⟩, ?_⟩
    change (a : F) * x * (a : F)⁻¹ = x
    field_simp

/-- Set-theoretic dilation form of the principal codifferent. -/
public theorem finiteCompletion_codifferent_eq_image (a : O) (ha : Ideal.span {a} = Diff) :
    (C : Set F) = (fun y : F ↦ (a : F)⁻¹ * y) '' (O : Set F) := by
  ext x
  rw [SetLike.mem_coe, finiteCompletion_mem_codifferent_iff v a ha]
  have h := generator_ne_zero v a ha
  constructor
  · intro hx
    exact ⟨_, hx, inv_mul_cancel_left₀ h x⟩
  · rintro ⟨y, hy, rfl⟩
    rwa [← mul_assoc, mul_inv_cancel₀ h, one_mul]

private theorem trivial_on_integers (z : F) :
    (∀ y : O, padicStdAddChar p (Algebra.trace ℚ_[p] F (z * (y : F))) = 1) ↔ z ∈ C := by
  rw [finiteCompletion_traceChar_trivial_iff, finiteCompletion_traceDual_eq_inv_differentIdeal]
  rfl

/-- The trace-character annihilator of the inverse different is exactly `O`. -/
public theorem finiteCompletion_codifferent_annihilator (x : F) :
    (∀ y ∈ C, padicStdAddChar p (Algebra.trace ℚ_[p] F (x * y)) = 1) ↔ x ∈ O := by
  let a := Submodule.IsPrincipal.generator Diff
  have ha : Ideal.span {a} = Diff := Ideal.span_singleton_generator _
  have h := generator_ne_zero v a ha
  have hc := finiteCompletion_mem_codifferent_iff v a ha
  have hm (z : F) : (a : F) * ((a : F)⁻¹ * z) = z := by rw [← mul_assoc, mul_inv_cancel₀ h, one_mul]
  have he : (∀ y ∈ C, padicStdAddChar p (Algebra.trace ℚ_[p] F (x * y)) = 1) ↔
      ∀ y : O, padicStdAddChar p (Algebra.trace ℚ_[p] F (((a : F)⁻¹ * x) * (y : F))) = 1 := by
    constructor
    · intro H y
      simpa [mul_assoc, mul_left_comm] using H ((a : F)⁻¹ * y) ((hc _).2 ((hm _).symm ▸ y.property))
    · intro H y hy
      have e : ((a : F)⁻¹ * x) * ((a : F) * y) = x * y := by field_simp
      simpa only [e] using H ⟨_, (hc _).1 hy⟩
  rw [he, trivial_on_integers, hc, hm]

public theorem measurableSet_finiteCompletion_codifferent [MeasurableSpace F] [BorelSpace F] :
    MeasurableSet (C : Set F) := by
  let a := Submodule.IsPrincipal.generator Diff
  have he : (C : Set F) = (fun x : F ↦ (a : F) * x) ⁻¹' (O : Set F) :=
    Set.ext (finiteCompletion_mem_codifferent_iff v a (Ideal.span_singleton_generator _))
  rw [he]
  exact ((Valued.isOpen_valuationSubring F).preimage (continuous_const.mul continuous_id)).measurableSet

/-- The negative-sign transform of the second lattice indicator. -/
public theorem finiteCompletion_codifferent_fourier [MeasurableSpace F] [BorelSpace F]
    (μ : Measure F) [μ.IsAddHaarMeasure] (x : F) :
    (∫ y in (C : Set F), star (padicStdAddChar p (Algebra.trace ℚ_[p] F (x * y))) ∂μ) =
      (μ.real (C : Set F) : ℂ) * (O : Set F).indicator (fun _ ↦ (1 : ℂ)) x := by
  classical
  let χ (y : F) := padicStdAddChar p (Algebra.trace ℚ_[p] F (x * y))
  have hadd (a b : F) : χ (a + b) = χ a * χ b := by
    simp only [χ, mul_add, map_add, AddChar.map_add_eq_mul]
  have e := addSubgroup_integral_star_char (C : Submodule O F).toAddSubgroup
    (measurableSet_finiteCompletion_codifferent v) μ χ hadd
  change (∫ y in (C : Set F), star (χ y) ∂μ) =
    (if ∀ y ∈ C, χ y = 1 then (μ.real (C : Set F) : ℂ) else 0) at e
  rw [e]
  by_cases hx : x ∈ O
  · rw [ite_eq_left ((finiteCompletion_codifferent_annihilator v x).2 hx), indicator_of_mem hx, mul_one]
  · rw [ite_eq_right (mt (finiteCompletion_codifferent_annihilator v x).1 hx), indicator_of_notMem hx, mul_zero]

end Masullo
