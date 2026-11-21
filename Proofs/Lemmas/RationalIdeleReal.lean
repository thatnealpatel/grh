module

public import Lemmas.FinitePlaceSupport

import Theorems.RationalIdeleNormalization

/-!
# The real coordinate of a rational idele

The absolute value of this coordinate gives the idelic norm after principal
rescaling to integral units at the finite places (Masullo, (A.2.2.2), p. 546).
-/

open NumberField IsDedekindDomain
open scoped BigOperators

namespace Masullo

/-- Identify the completion at the unique infinite place of `ℚ` with `ℝ`. -/
@[expose]
public noncomputable def rationalIdeleReal (a : IdeleGroup (𝓞 ℚ) ℚ) : ℝ :=
  InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace
    ((a : AdeleRing (𝓞 ℚ) ℚ).1 Rat.infinitePlace)

public theorem rationalIdeleReal_principal_mul (r : ℚˣ) (a : IdeleGroup (𝓞 ℚ) ℚ) :
    rationalIdeleReal (IdeleGroup.unitEmbedding (𝓞 ℚ) ℚ r * a) =
      ((r : ℚ) : ℝ) * rationalIdeleReal a := by
  let e := InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace
  change e ((algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) (r : ℚ)).1 Rat.infinitePlace *
    (a : AdeleRing (𝓞 ℚ) ℚ).1 Rat.infinitePlace) = _
  rw [map_mul, AdeleRing.algebraMap_fst_apply,
    ← InfinitePlace.Completion.WithAbs.ratCast_equiv _ (WithAbs.toAbs _ (r : ℚ)), map_ratCast]
  rfl

/-- The norm of a rational idele with integral-unit finite coordinates is its real absolute value. -/
public theorem ideleNorm_eq_abs_rationalIdeleReal (a : IdeleGroup (𝓞 ℚ) ℚ)
    (ha : ∀ v : HeightOneSpectrum (𝓞 ℚ), Valued.v ((a : AdeleRing (𝓞 ℚ) ℚ).2 v) = 1) :
    ideleNorm a = |rationalIdeleReal a| := by
  have hfin (v : HeightOneSpectrum (𝓞 ℚ)) : ‖(a : AdeleRing (𝓞 ℚ) ℚ).2 v‖ = 1 :=
    Valued.toNormedField.norm_eq_one_iff.mpr (ha v)
  rw [ideleNorm_apply, AdeleRing.norm_apply_of_isUnit a.isUnit]
  simp only [hfin, finprod_one, mul_one, Fintype.prod_subsingleton _ Rat.infinitePlace,
    Rat.isReal_infinitePlace.mult_eq_one, pow_one]
  exact (Isometry.norm_map_of_map_zero
    (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal Rat.isReal_infinitePlace)
    (map_zero _) _).symm

/-- One principal rescaling makes the finite coordinates integral units and
makes the real coordinate equal to the positive idelic norm. -/
public theorem exists_rational_principal_mul_norm_section (a : IdeleGroup (𝓞 ℚ) ℚ) :
    ∃ r : ℚˣ, rationalIdeleReal (IdeleGroup.unitEmbedding (𝓞 ℚ) ℚ r * a) = ideleNorm a ∧
      ∀ v : HeightOneSpectrum (𝓞 ℚ),
        Valued.v (((IdeleGroup.unitEmbedding (𝓞 ℚ) ℚ r * a : IdeleGroup (𝓞 ℚ) ℚ) :
          AdeleRing (𝓞 ℚ) ℚ).2 v) = 1 := by
  obtain ⟨r, hr⟩ := exists_rational_principal_mul_finite_valued_eq_one a
  let a' := IdeleGroup.unitEmbedding (𝓞 ℚ) ℚ r * a
  have hnorm : ideleNorm a' = ideleNorm a := by
    dsimp only [a']
    rw [map_mul, ideleNorm_apply (IdeleGroup.unitEmbedding (𝓞 ℚ) ℚ r)]
    change ‖algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) (r : ℚ)‖ * ideleNorm a = _
    rw [AdeleRing.norm_algebraMap_eq_one_of_ne_zero r.ne_zero, one_mul]
  have habs : |rationalIdeleReal a'| = ideleNorm a :=
    (ideleNorm_eq_abs_rationalIdeleReal a' hr).symm.trans hnorm
  rcases le_or_gt 0 (rationalIdeleReal a') with h | h
  · exact ⟨r, (abs_of_nonneg h).symm.trans habs, hr⟩
  · refine ⟨-r, ?_, fun v ↦ ?_⟩
    · rw [rationalIdeleReal_principal_mul, Units.val_neg, Rat.cast_neg, neg_mul,
        ← rationalIdeleReal_principal_mul, ← abs_of_neg h, habs]
    · change Valued.v (algebraMap ℚ (v.adicCompletion ℚ) ((-r : ℚˣ) : ℚ) *
          (a : AdeleRing (𝓞 ℚ) ℚ).2 v) = 1
      rw [Units.val_neg, map_neg, neg_mul, Valuation.map_neg]
      exact hr v

end Masullo
