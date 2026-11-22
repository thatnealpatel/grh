module

public import Theorems.IdeleArchimedeanCover
public import Theorems.IdeleClassCompact
public import Theorems.IdeleClassSeparation

/-!
# Compact Hausdorff norm-one idele classes

Theorem A.1.4.3(1), PDF p. 542, concerns the norm-one subgroup of the actual
idele class group with the induced topology. For compactness, we combine
Masullo's logarithmic lattice reduction (Lemma A.2.3.8(1)–(2), pp. 550–551)
with the finite union over ideal classes (Proposition A.2.3.10(1)–(2), p. 552).
`archimedean_compact_cover` uses a closed log window with all signs and phases;
this gives the compact cover needed here without a disjoint angular section.
`compactSpace_ideleClassNormOne_of_archimedean_cover` implements the finite union
and its image under the quotient. Hausdorffness uses the product-formula
separation argument in `t2Space_ideleClassGroup`, independently of the cover.
-/

open IsDedekindDomain NumberField

namespace Masullo

variable {K : Type*} [Field K] [NumberField K]

/-- Masullo, Theorem A.1.4.3(1), on the actual idele class group of any number field. -/
public theorem compactHausdorff_ideleClassNormOne :
    CompactSpace (ideleClassNormOne (K := K)) ∧ T2Space (ideleClassNormOne (K := K)) := by
  have hT2 : T2Space (IdeleClassGroup (𝓞 K) K) := t2Space_ideleClassGroup
  refine ⟨?_, inferInstance⟩
  obtain ⟨C, hC, hcover⟩ := archimedean_compact_cover (K := K)
  refine compactSpace_ideleClassNormOne_of_archimedean_cover
    (((↑) : archimedeanNormOne (K := K) → (InfiniteAdeleRing K)ˣ) '' C)
    (hC.image continuous_subtype_val) ?_ ?_
  · rintro _ ⟨c, _, rfl⟩
    rw [← archimedeanNorm_apply]
    exact (mem_archimedeanNormOne _).mp c.property
  · intro g hg
    have hg' : g ∈ archimedeanNormOne := (mem_archimedeanNormOne g).mpr (by
      rw [archimedeanNorm_apply]
      exact hg)
    obtain ⟨u, c, hc, heq⟩ := hcover ⟨g, hg'⟩
    refine ⟨u, c, ⟨c, hc, rfl⟩, ?_⟩
    have hd : (archimedeanDiagonalUnit u : (InfiniteAdeleRing K)ˣ) =
        ideleInfinitePart (IdeleGroup.unitEmbedding (𝓞 K) K (Units.map (algebraMap (𝓞 K) K) u)) := by
      rw [coe_archimedeanDiagonalUnit, ideleInfinitePart_integralUnit]
      apply Units.ext
      exact (IsScalarTower.algebraMap_apply (𝓞 K) K (InfiniteAdeleRing K) (u : 𝓞 K)).symm
    have heq' := congrArg Subtype.val heq
    change g = (archimedeanDiagonalUnit u : (InfiniteAdeleRing K)ˣ) * c at heq'
    rwa [hd] at heq'

end Masullo
