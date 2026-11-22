module

public import Mathlib.NumberTheory.NumberField.HeckeLFunction
public import Mathlib.Analysis.Complex.Basic

/-! # Conjugation of a Hecke character and its local restrictions -/

open IsDedekindDomain NumberField
open scoped ComplexConjugate

namespace Masullo

variable {K : Type*} [Field K] [NumberField K]

/-- The conjugate character in (3.2.1.6), p. 123, by pointwise conjugation
on idele classes. Its construction does not need unitarity. -/
@[expose] public def heckeConjugate (χ : HeckeCharacter (𝓞 K) K) : HeckeCharacter (𝓞 K) K where
  toFun x := conj (χ x)
  map_one' := by simp
  map_mul' x y := by simp
  continuous_toFun := Complex.continuous_conj.comp χ.continuous

/-- Conjugation preserves unitarity. -/
public theorem heckeConjugate_unitary (χ : HeckeCharacter (𝓞 K) K)
    (hχ : ∀ x : IdeleClassGroup (𝓞 K) K, ‖χ x‖ = 1)
    (x : IdeleClassGroup (𝓞 K) K) : ‖heckeConjugate χ x‖ = 1 := by
  change ‖conj (χ x)‖ = 1
  simpa using hχ x

/-- Restriction to the units of a finite completion commutes with conjugation. -/
public theorem heckeConjugate_restrict_unit (χ : HeckeCharacter (𝓞 K) K)
    (v : HeightOneSpectrum (𝓞 K)) (x : (v.adicCompletion K)ˣ) :
    (heckeConjugate χ).restrict v x = conj (χ.restrict v x) := by
  simp only [HeckeCharacter.restrict, MulChar.ofUnitHom_coe, MonoidHom.comp_apply,
    MonoidHom.coe_toHomUnits]
  rfl

/-- A finite place is unramified for the conjugate character exactly when
it is unramified for the original character. -/
public theorem heckeConjugate_isUnramifiedAt_iff (χ : HeckeCharacter (𝓞 K) K)
    (v : HeightOneSpectrum (𝓞 K)) :
    (heckeConjugate χ).IsUnramifiedAt v ↔ χ.IsUnramifiedAt v := by
  simp only [HeckeCharacter.isUnramifiedAt_iff]
  have h (x : (v.adicCompletionIntegers K)ˣ) :
      (heckeConjugate χ).restrict v x = conj (χ.restrict v x) :=
    heckeConjugate_restrict_unit χ v ((Units.map (v.adicCompletionIntegers K).subtype.toMonoidHom) x)
  simp only [h, map_eq_one_iff _ (starRingEnd ℂ).injective]

end Masullo
