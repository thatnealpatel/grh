module

public import Lemmas.FiniteHeckeMajorant
public import Mathlib.NumberTheory.NumberField.HeckeLFunction
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Tactic.Ring

/-! Normalization of the restriction of a unitary Hecke character to a finite place. -/

open IsDedekindDomain NumberField

namespace Masullo

variable {K : Type*} [Field K] [NumberField K]
local notation "Places" => HeightOneSpectrum (𝓞 K)

/-- A unitary idele-class character has unitary restriction to each local multiplicative group. -/
public theorem norm_heckeRestrict_of_unitary (χ : HeckeCharacter (𝓞 K) K)
    (hχ : ∀ x : IdeleClassGroup (𝓞 K) K, ‖χ x‖ = 1)
    (v : Places) {x : v.adicCompletion K} (hx : x ≠ 0) : ‖χ.restrict v x‖ = 1 := by
  let u : (v.adicCompletion K)ˣ := Units.mk0 x hx
  change ‖χ.restrict v (u : v.adicCompletion K)‖ = 1
  rw [HeckeCharacter.restrict, MulChar.ofUnitHom_coe]
  exact hχ (IdeleClassGroup.ofAdicCompletion (𝓞 K) K v u)

/-- For a uniformizer, the normalized absolute value is the inverse ideal norm. -/
public theorem norm_uniformizer_eq_inv_finitePlaceNorm (v : Places) (π : v.adicCompletion K)
    (hπ : Valued.v.IsUniformizer π) : ‖π‖ = (finitePlaceNorm v)⁻¹ := by
  rw [FinitePlace.norm_def, WithZeroMulInt.toNNReal_neg_apply _ hπ.val_ne_zero, hπ.val,
    Valuation.IsRankOneDiscrete.generator_eq_exp_neg_one_of_surjective
      (HeightOneSpectrum.valuedAdicCompletion_surjective K v)]
  simp [finitePlaceNorm]

/-- The complex power of the uniformizer norm is `exp(-s log q_v)`. -/
public theorem uniformizer_norm_cpow (v : Places) (π : v.adicCompletion K)
    (hπ : Valued.v.IsUniformizer π) (s : ℂ) :
    (‖π‖ : ℂ) ^ s = Complex.exp (-s * (Real.log (finitePlaceNorm v) : ℂ)) := by
  have hq : 0 < finitePlaceNorm v := lt_of_lt_of_le (by norm_num) (two_le_finitePlaceNorm v)
  rw [norm_uniformizer_eq_inv_finitePlaceNorm v π hπ,
    Complex.cpow_def_of_ne_zero (by exact_mod_cast inv_ne_zero hq.ne'),
    ← Complex.ofReal_log (inv_nonneg.mpr hq.le), Real.log_inv, Complex.ofReal_neg]
  congr 1
  ring

end Masullo
