module

public import Theorems.IdeleLogSplit

import Lemmas.ArchimedeanLogRadius

/-!
# Uniform scalar section of the idelic norm

Definition A.2.2.3 and Lemma A.2.2.4, PDF p. 547, give an idele with
ordinary radius `t^(1/[K:ℚ])` at every infinite place and `1` at every
finite place. We construct it directly in log coordinates and compute
its norm from the local multiplicities.

For large-norm estimates, use this section in place of the diagonal
section of (A.2.2.11) used in Theorem 2.2.3.4(1). In the ordinary sup
norm of that proof, (2.2.3.10), PDF p. 84, does not give dilation by
`t`. The uniform scalar section gives dilation by `t^(1/[K:ℚ])`,
with the same finite part. The required decay exponent and lattice
majorant must still be supplied.
-/

open NumberField IsDedekindDomain

namespace Masullo

variable {K : Type*} [Field K] [NumberField K]

private noncomputable def scalarLogInput (w : InfinitePlace K) :
    Multiplicative ℝ →* Multiplicative ℝ where
  toFun x := Multiplicative.ofAdd ((w.mult : ℝ) * (x.toAdd / (Module.finrank ℚ K : ℝ)))
  map_one' := by simp
  map_mul' x y := by
    apply Multiplicative.toAdd.injective
    change (w.mult : ℝ) * ((x.toAdd + y.toAdd) / _) =
      (w.mult : ℝ) * (x.toAdd / _) + (w.mult : ℝ) * (y.toAdd / _)
    rw [add_div, mul_add]

private noncomputable def scalarLogCoordinate (w : InfinitePlace K) :
    Multiplicative ℝ →* w.Completion :=
  (completionLogRadius w).comp (scalarLogInput w)

private theorem continuous_scalarLogCoordinate (w : InfinitePlace K) :
    Continuous (scalarLogCoordinate w) :=
  (continuous_completionLogRadius w).comp (continuous_ofAdd.comp
    (continuous_const.mul (continuous_toAdd.div_const _)))

private noncomputable def scalarLogValue : Multiplicative ℝ →* AdeleRing (𝓞 K) K where
  toFun x := (fun w ↦ scalarLogCoordinate w x, 1)
  map_one' := Prod.ext (funext fun w ↦ (scalarLogCoordinate w).map_one) rfl
  map_mul' x y := Prod.ext (funext fun w ↦ (scalarLogCoordinate w).map_mul x y) (by
    change (1 : FiniteAdeleRing (𝓞 K) K) = 1 * 1
    rw [one_mul])

private theorem continuous_scalarLogValue :
    Continuous (scalarLogValue : Multiplicative ℝ → AdeleRing (𝓞 K) K) :=
  (continuous_pi continuous_scalarLogCoordinate).prodMk continuous_const

/-- The canonical section of Lemma A.2.2.4 on actual ideles, in logarithmic coordinates. -/
public noncomputable def ideleScalarLogSection : Multiplicative ℝ →ₜ* IdeleGroup (𝓞 K) K where
  toMonoidHom := scalarLogValue.toHomUnits
  continuous_toFun := Units.continuous_iff.mpr
    ⟨continuous_scalarLogValue, continuous_scalarLogValue.comp continuous_inv⟩

public theorem ideleScalarLogSection_infinite (x : Multiplicative ℝ) (w : InfinitePlace K) :
    InfinitePlace.Completion.extensionEmbedding w
        ((ideleScalarLogSection (K := K) x : AdeleRing (𝓞 K) K).1 w) =
      (Real.exp (x.toAdd / (Module.finrank ℚ K : ℝ)) : ℂ) := by
  change InfinitePlace.Completion.extensionEmbedding w (completionLogRadius w (scalarLogInput w x)) = _
  rw [extensionEmbedding_completionLogRadius]
  change (Real.exp ((w.mult : ℝ) * (x.toAdd / _) / (w.mult : ℝ)) : ℂ) = _
  rw [mul_comm, mul_div_cancel_right₀ _ (Nat.cast_ne_zero.mpr w.mult_ne_zero)]

public theorem ideleScalarLogSection_finite (x : Multiplicative ℝ)
    (w : HeightOneSpectrum (𝓞 K)) :
    (ideleScalarLogSection (K := K) x : AdeleRing (𝓞 K) K).2 w = 1 := by
  change (1 : FiniteAdeleRing (𝓞 K) K) w = 1
  rfl

public theorem ideleNorm_ideleScalarLogSection (x : Multiplicative ℝ) :
    ideleNorm (ideleScalarLogSection (K := K) x) = Real.exp x.toAdd := by
  rw [ideleNorm_apply, AdeleRing.norm_apply_of_isUnit (ideleScalarLogSection (K := K) x).isUnit]
  change (∏ w : InfinitePlace K, ‖(ideleScalarLogSection (K := K) x : AdeleRing (𝓞 K) K).1 w‖ ^ w.mult) *
    (∏ᶠ w : HeightOneSpectrum (𝓞 K), ‖(ideleScalarLogSection (K := K) x : AdeleRing (𝓞 K) K).2 w‖) = _
  simp only [ideleScalarLogSection_finite, norm_one, finprod_one, mul_one]
  have hloc (w : InfinitePlace K) :
      ‖(ideleScalarLogSection (K := K) x : AdeleRing (𝓞 K) K).1 w‖ ^ w.mult =
        Real.exp ((w.mult : ℝ) * (x.toAdd / (Module.finrank ℚ K : ℝ))) := by
    rw [← (InfinitePlace.Completion.isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _),
      ideleScalarLogSection_infinite, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _), Real.exp_nat_mul]
  simp_rw [hloc]
  rw [← Real.exp_sum, ← Finset.sum_mul, ← Nat.cast_sum, InfinitePlace.sum_mult_eq,
    mul_div_cancel₀ _ (Nat.cast_ne_zero.mpr (Module.finrank_pos (R := ℚ) (M := K)).ne')]

public theorem ideleLogNorm_scalarSection (x : Multiplicative ℝ) :
    ideleLogNorm (ideleScalarLogSection (K := K) x) = x := by
  apply Multiplicative.toAdd.injective
  rw [ideleLogNorm_apply, ideleNorm_ideleScalarLogSection, Real.log_exp]

end Masullo
