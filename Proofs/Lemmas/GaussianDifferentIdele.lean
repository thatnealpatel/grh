module

public import Lemmas.IdeleGaussianIdeal
public import Lemmas.IdeleMixedScale
public import Theorems.ArchimedeanIdealDual
import Lemmas.FiniteIdeleIdealNorm
import Mathlib.NumberTheory.NumberField.Discriminant.Different

/-! # The idele translating inversion by the different

With the ideal convention used here, the different (not its inverse) is
the finite ideal of the idele used to translate `g⁻¹`. Its archimedean component is one.
-/

open IsDedekindDomain NumberField
open scoped Classical nonZeroDivisors

namespace Masullo

variable (K : Type*) [Field K] [NumberField K]
local notation "J" => FractionalIdeal (𝓞 K)⁰ K
local notation "I" => IdeleGroup (𝓞 K) K
local notation "D" => ((differentIdeal ℤ (𝓞 K) : Ideal (𝓞 K)) : J)

private noncomputable def differentUnit : Jˣ :=
  Units.mk0 D (FractionalIdeal.coeIdeal_eq_zero.not.mpr differentIdeal_ne_bot)

private noncomputable def finiteDifferentLift : (FiniteAdeleRing (𝓞 K) K)ˣ :=
  if differentUnit K = 1 then 1 else (finiteIdeleIdeal_surjective K (differentUnit K)).choose

private theorem finiteDifferentLift_spec : finiteIdeleIdeal K (finiteDifferentLift K) = differentUnit K := by
  unfold finiteDifferentLift
  split_ifs with h
  · rw [h, map_one]
  · exact (finiteIdeleIdeal_surjective K (differentUnit K)).choose_spec

/-- One fixed idele with archimedean component one and finite ideal the different. -/
public noncomputable def gaussianDifferentIdele : I :=
  MulEquiv.prodUnits.symm (1, finiteDifferentLift K)

public theorem finiteIdeal_gaussianDifferentIdele :
    (finiteIdeleIdeal K (ideleFinitePart (gaussianDifferentIdele K)) : J) = D := by
  let f := finiteDifferentLift K
  have hf : ideleFinitePart (gaussianDifferentIdele K) = f := by
    apply Units.ext
    ext v
    rw [ideleFinitePart_apply]
    rfl
  rw [hf]
  dsimp only [f]
  rw [finiteDifferentLift_spec]
  rfl

/-- The different translation has norm the reciprocal absolute discriminant. -/
public theorem ideleNorm_gaussianDifferentIdele :
    ideleNorm (gaussianDifferentIdele K) = ((discr K).natAbs : ℝ)⁻¹ := by
  rw [ideleNorm_eq_archimedean_mul_absNorm_inv_finiteIdeleIdeal,
    finiteIdeal_gaussianDifferentIdele, map_inv₀,
    (FractionalIdeal.coeIdeal_absNorm (K := K)), absNorm_differentIdeal K, Rat.cast_inv, Rat.cast_natCast]
  have h (w : InfinitePlace K) : ((gaussianDifferentIdele K).val.1 w) = 1 := rfl
  simp [h]

/-- Over the rationals there is no translation in the reflected theta sum. -/
@[simp] public theorem gaussianDifferentIdele_rat : gaussianDifferentIdele ℚ = 1 := by
  have hd : differentIdeal ℤ (𝓞 ℚ) = ⊤ := Ideal.absNorm_eq_one_iff.mp (by
    rw [absNorm_differentIdeal ℚ, NumberField.discr_rat]; rfl)
  have h : differentUnit ℚ = 1 := Units.ext (by
    change ((differentIdeal ℤ (𝓞 ℚ) : Ideal (𝓞 ℚ)) : FractionalIdeal (𝓞 ℚ)⁰ ℚ) = 1
    rw [hd, FractionalIdeal.coeIdeal_top])
  simp only [gaussianDifferentIdele, finiteDifferentLift, h, ↓reduceIte]
  exact map_one _

private theorem ideleMixedPart_gaussianDifferentIdele : ideleMixedPart (gaussianDifferentIdele K) = 1 := by
  ext w <;> exact map_one _

/-- At the reflected idele, the same finite support test gives the trace-dual ideal. -/
public theorem ideleGaussianIdeal_reflect (g : I) :
    (ideleGaussianIdeal (gaussianDifferentIdele K * g⁻¹) : J) =
      FractionalIdeal.dual ℤ ℚ (ideleGaussianIdeal g : J) := by
  rw [fractionalIdeal_traceDual_eq, ideleGaussianIdeal, ideleGaussianIdeal, map_mul, map_mul, mul_inv,
    Units.val_mul, Units.val_inv_eq_inv_val, finiteIdeal_gaussianDifferentIdele]
  simp

public theorem ideleMixedPart_reflect (g : I) :
    ideleMixedPart (gaussianDifferentIdele K * g⁻¹) = ideleMixedPart g⁻¹ := by
  rw [map_mul, ideleMixedPart_gaussianDifferentIdele, one_mul]

end Masullo
