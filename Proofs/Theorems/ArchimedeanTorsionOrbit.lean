module

public import Lemmas.ArchimedeanTorsionOrbit
public import Lemmas.IdeleArchimedeanCover

/-! # The pointwise torsion sector on the Archimedean norm-one group

Masullo Definition A.2.3.6, (A.2.3.13), PDF p. 549, uses the positive ray at a real
place and the half-open sector of width `2π/w` at a complex place. The proof of Lemma
A.2.3.8(2), PDF p. 551, uses this as a fundamental domain for torsion on the chosen
coordinate (provisional reading from the text and PDF layout). We justify this step by
applying the pointwise reduction in `Lemmas.ArchimedeanTorsionOrbit` to the nonzero
completion value of a norm-one adelic unit. The regulator box is not used in this step.
-/

open NumberField NumberField.InfinitePlace
open InfinitePlace.Completion

namespace Masullo

variable {K : Type*} [Field K] [NumberField K]

local notation "U∞" => (InfiniteAdeleRing K)ˣ
local notation "G∞" => archimedeanNormOne (K := K)

/-- The unrestricted pointwise sector condition at the chosen place of an Archimedean
norm-one unit. -/
@[expose] public noncomputable def archimedeanInTorsionSector (v : InfinitePlace K) (g : G∞) : Prop := by
  classical
  exact if hv : v.IsReal then 0 < extensionEmbeddingOfIsReal hv ((g : U∞).val v)
    else Complex.arg (extensionEmbedding v ((g : U∞).val v)) ∈
      Set.Ico 0 (2 * Real.pi / (NumberField.Units.torsionOrder K : ℝ))

/-- Each Archimedean norm-one unit has a unique torsion translate satisfying the sector
condition at the chosen place. -/
public theorem existsUnique_archimedeanTorsion_translate (v : InfinitePlace K) (g : G∞) :
    ∃! ζ : NumberField.Units.torsion K,
      archimedeanInTorsionSector v (archimedeanDiagonalUnit ζ.val * g) := by
  have hne : (g : U∞).val v ≠ 0 := ((Pi.isUnit_iff.mp (g : U∞).isUnit) v).ne_zero
  have hval (ζ : NumberField.Units.torsion K) :
      ((archimedeanDiagonalUnit ζ.val * g : G∞) : U∞).val v =
        (algebraMap K (InfiniteAdeleRing K) (ζ.val : K)) v * (g : U∞).val v := by
    rw [Subgroup.coe_mul, Units.val_mul, coe_archimedeanDiagonalUnit]
    rfl
  by_cases hv : v.IsReal
  · simpa only [archimedeanInTorsionSector, dite_eq_left hv, hval, map_mul,
      InfiniteAdeleRing.algebraMap_apply, extensionEmbeddingOfIsReal_coe,
      WithAbs.equiv_apply, WithAbs.ofAbs_toAbs] using
        existsUnique_torsion_real_pos hv ((map_ne_zero (extensionEmbeddingOfIsReal hv)).mpr hne)
  · simpa only [archimedeanInTorsionSector, dite_eq_right hv, hval, map_mul,
      InfiniteAdeleRing.algebraMap_apply, extensionEmbedding_coe, WithAbs.equiv_apply, WithAbs.ofAbs_toAbs] using
        existsUnique_torsion_complex_arg (v := v) ((map_ne_zero (extensionEmbedding v)).mpr hne)

end Masullo
