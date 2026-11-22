module

public import Theorems.IdeleIdealClass
public import Mathlib.NumberTheory.NumberField.Discriminant.Basic

/-! # The finite idelic norm as a fractional ideal norm -/

open Filter IsDedekindDomain NumberField
open scoped BigOperators nonZeroDivisors WithZero

namespace Masullo

variable {K : Type*} [Field K] [NumberField K]

local notation "V" => HeightOneSpectrum (𝓞 K)
local notation "F" => IsDedekindDomain.FiniteAdeleRing (𝓞 K) K
local notation "J" => FractionalIdeal (𝓞 K)⁰ K
local notation "A" => AdeleRing (𝓞 K) K
local notation "I" => IdeleGroup (𝓞 K) K

private theorem absNorm_eq_finprod_count (j : Jˣ) :
    (FractionalIdeal.absNorm (j : J) : ℝ) =
      ∏ᶠ v : V, (v.asIdeal.absNorm : ℝ) ^ FractionalIdeal.count K v (j : J) := by
  let N : J →*₀ ℝ := (Rat.castHom ℝ).toMonoidWithZeroHom.comp FractionalIdeal.absNorm
  let f (v : V) : J := (v.asIdeal : J) ^ FractionalIdeal.count K v (j : J)
  have hf : f.HasFiniteMulSupport := by
    apply eventually_cofinite.mp
    filter_upwards [FractionalIdeal.finite_factors (j : J)] with v hv
    simp [f, hv]
  change N (j : J) = _
  calc
    _ = N (∏ᶠ v, f v) := congrArg N
      (FractionalIdeal.finprod_heightOneSpectrum_factorization' K j.ne_zero).symm
    _ = ∏ᶠ v, N (f v) := map_finprod N hf
    _ = _ := finprod_congr fun v ↦ by
      change N ((v.asIdeal : J) ^ _) = _
      rw [map_zpow₀]
      change ((FractionalIdeal.absNorm (v.asIdeal : J) : ℝ) ^ _) = _
      rw [FractionalIdeal.coeIdeal_absNorm, Rat.cast_natCast]

/-- The finite part of the product norm is the absolute norm of the inverse fractional ideal.
The inverse accounts for the local convention that a uniformizer has norm `1 / q_v`. -/
private theorem absNorm_inv_finiteIdeleIdeal (f : Fˣ) :
    (FractionalIdeal.absNorm ((finiteIdeleIdeal K f)⁻¹ : J) : ℝ) = ‖(f : F)‖ := by
  rw [← Units.val_inv_eq_inv_val, absNorm_eq_finprod_count,
    NumberField.FiniteAdeleRing.norm_eq_finprod_of_unit]
  apply finprod_congr
  intro v
  rw [Units.val_inv_eq_inv_val, FractionalIdeal.count_inv, count_finiteIdeleIdeal, neg_neg,
    FinitePlace.norm_def,
    WithZeroMulInt.toNNReal_neg_apply (NumberField.HeightOneSpectrum.absNorm_ne_zero v)
      (finiteIdele_valuation_ne_zero f v), NNReal.coe_zpow, NNReal.coe_natCast]

/-- The project’s idelic norm factors as the normalized archimedean product times the absolute
norm of the inverse of the ideal associated to its finite part. -/
public theorem ideleNorm_eq_archimedean_mul_absNorm_inv_finiteIdeleIdeal (g : I) :
    ideleNorm g = (∏ w : InfinitePlace K, ‖(g : A).1 w‖ ^ w.mult) *
      (FractionalIdeal.absNorm ((finiteIdeleIdeal K (ideleFinitePart g))⁻¹ : J) : ℝ) := by
  rw [absNorm_inv_finiteIdeleIdeal, ideleNorm_apply,
    AdeleRing.norm_apply_of_isUnit g.isUnit,
    NumberField.FiniteAdeleRing.norm_eq_finprod_of_unit]
  simp only [ideleFinitePart_apply]

end Masullo
