module

public import Theorems.IdeleIdealClassStrict
import Mathlib.NumberTheory.NumberField.ClassNumber

/-!
# Compactness of the norm-one idele class group from an Archimedean cover

Masullo constructs the finite union (A.2.3.14), PDF p. 549, from norm-one
lifts of the ideal classes. Proposition A.2.3.10(1)–(2), p. 552, uses the
compact finite integral-unit factor and (A.2.3.28) to reduce coverage by
principal ideles to the Archimedean coverage of Lemma A.2.3.8(2), pp. 550–551.
For compactness we replace the relatively compact fundamental set by a compact
cover `W` and use only the norm-one infinite group in that reduction. The
empty-stage embedding implements the finite factor in the actual ideles.
The compactness assertion of Theorem A.1.4.3(1), p. 542, follows by taking the
image in the actual idele class group. We do not require disjointness or
nonempty interior and do not prove Hausdorffness here.
-/

open IsDedekindDomain NumberField Set

namespace Masullo

variable {K : Type*} [Field K] [NumberField K]

local notation "I" => IdeleGroup (𝓞 K) K
local notation "G" => IdeleClassGroup (𝓞 K) K
local notation "P" => ClassGroup (𝓞 K)
local notation "V" => HeightOneSpectrum (𝓞 K)

/-- The projection of an idele onto the units of its infinite factor. -/
public noncomputable def ideleInfinitePart : I →* (InfiniteAdeleRing K)ˣ :=
  Units.map (MonoidHom.fst (InfiniteAdeleRing K) (FiniteAdeleRing (𝓞 K) K))

/-- The Archimedean embedding of a global integral unit agrees with the infinite
projection of its diagonal principal idele. -/
public theorem ideleInfinitePart_integralUnit (u : (𝓞 K)ˣ) :
    ideleInfinitePart (IdeleGroup.unitEmbedding (𝓞 K) K (Units.map (algebraMap (𝓞 K) K) u)) =
      Units.map (algebraMap (𝓞 K) (InfiniteAdeleRing K)) u := by
  apply Units.ext
  change algebraMap K (InfiniteAdeleRing K) (algebraMap (𝓞 K) K (u : 𝓞 K)) = _
  exact IsScalarTower.algebraMap_apply (𝓞 K) K (InfiniteAdeleRing K) (u : 𝓞 K) |>.symm

private theorem integralUnit_mem_ideleFiniteUnits (u : (𝓞 K)ˣ) :
    IdeleGroup.unitEmbedding (𝓞 K) K (Units.map (algebraMap (𝓞 K) K) u) ∈ ideleFiniteUnits := by
  change _ ∈ (ideleFiniteUnits (K := K) : Set I)
  rw [← range_ideleFiniteStageEmbedding_empty, range_ideleFiniteStageEmbedding]
  intro v _
  have hv (z : 𝓞 K) := HeightOneSpectrum.coe_algebraMap_mem (R := 𝓞 K) (K := K) (v := v) z
  refine ⟨hv (u : 𝓞 K), ?_⟩
  rw [← map_inv, ← map_inv]
  exact hv (↑(u⁻¹) : 𝓞 K)

private noncomputable abbrev infiniteCoordinates :
    (InfiniteAdeleRing K)ˣ ≃ₜ* ((v : InfinitePlace K) → v.Completionˣ) :=
  ContinuousMulEquiv.piUnits

private theorem infiniteCoordinates_emptyStage (x : IdeleFiniteStage K ∅) :
    infiniteCoordinates (ideleInfinitePart (ideleFiniteStageEmbedding K ∅ x)) = x.1 := by
  funext v
  exact Units.ext (ideleFiniteStageEmbedding_infinite K ∅ x v)

/-- The product of `W` with all finite integral units, inside the actual ideles. -/
private def archWindow (W : Set (InfiniteAdeleRing K)ˣ) : Set I :=
  {g | ideleInfinitePart g ∈ W ∧ g ∈ ideleFiniteUnits}

private theorem isCompact_archWindow (W : Set (InfiniteAdeleRing K)ˣ) (hW : IsCompact W) :
    IsCompact (archWindow W) := by
  let B : Set (IdeleFiniteStage K ∅) := (infiniteCoordinates '' W) ×ˢ ({1} ×ˢ univ)
  let j := ideleFiniteStageEmbedding K ∅
  have hB : IsCompact B := by
    let (v : {v : V // v ∉ (∅ : Finset V)}) : CompactSpace (v.val.adicCompletionIntegers K)ˣ :=
      compactSpace_finiteCompletionIntegralUnits K v.val
    exact (hW.image infiniteCoordinates.continuous).prod (isCompact_singleton.prod isCompact_univ)
  have hstage (g : I) : g ∈ range j ↔ g ∈ ideleFiniteUnits :=
    Set.ext_iff.mp (range_ideleFiniteStageEmbedding_empty (K := K)) g
  have himage : j '' B = archWindow W := by
    ext g
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨?_, (hstage _).mp (mem_range_self x)⟩
      obtain ⟨w, hw, heq⟩ := hx.1
      exact infiniteCoordinates.injective (heq.trans (infiniteCoordinates_emptyStage x).symm) ▸ hw
    · rintro ⟨hg, hf⟩
      obtain ⟨x, rfl⟩ := (hstage g).mpr hf
      refine ⟨x, ⟨⟨_, hg, infiniteCoordinates_emptyStage x⟩, ?_, mem_univ _⟩, rfl⟩
      exact mem_singleton_iff.mpr (funext fun v ↦ (Finset.notMem_empty v.val v.property).elim)
  rw [← himage]
  exact hB.image (isOpenEmbedding_ideleFiniteStageEmbedding K ∅).continuous

/-- The global compact-cover step in the compactness assertion of Masullo,
Theorem A.1.4.3(1). The sole input beyond the number field is a compact set of
weighted-norm-one infinite units whose global integral-unit translates cover
all weighted-norm-one infinite units. -/
public theorem compactSpace_ideleClassNormOne_of_archimedean_cover
    (W : Set (InfiniteAdeleRing K)ˣ) (hW : IsCompact W)
    (hnorm : ∀ c ∈ W, ∏ w : InfinitePlace K, ‖(c : InfiniteAdeleRing K) w‖ ^ w.mult = 1)
    (hcover : ∀ g : (InfiniteAdeleRing K)ˣ,
      (∏ w : InfinitePlace K, ‖(g : InfiniteAdeleRing K) w‖ ^ w.mult) = 1 →
      ∃ (u : (𝓞 K)ˣ) (c : (InfiniteAdeleRing K)ˣ), c ∈ W ∧
        g = ideleInfinitePart
          (IdeleGroup.unitEmbedding (𝓞 K) K (Units.map (algebraMap (𝓞 K) K) u)) * c) :
    CompactSpace (ideleClassNormOne (K := K)) := by
  classical
  let q : I →* G := QuotientGroup.mk' (IdeleGroup.principalSubgroup (𝓞 K) K)
  have hprincipal (a : Kˣ) : q (IdeleGroup.unitEmbedding (𝓞 K) K a) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr ⟨a, rfl⟩
  -- (A.2.3.14): Take one norm-one lift per ideal class and translate the product window.
  choose r hr using ideleIdealClass_normOne_surjective (K := K)
  change ∀ p, ideleIdealClass (r p : I) = p at hr
  let S : Set I := ⋃ p : P, (fun b : I ↦ (r p : I) * b) '' archWindow W
  have hS : IsCompact S := isCompact_iUnion fun p ↦
    (isCompact_archWindow W hW).image (continuous_const.mul continuous_id)
  have himage : q '' S = (ideleClassNormOne (K := K) : Set G) := by
    ext c
    constructor
    · rintro ⟨_, hg, rfl⟩
      obtain ⟨p, hp⟩ := mem_iUnion.mp hg
      obtain ⟨b, hb, rfl⟩ := hp
      apply (mem_ideleClassNormOne _).mpr
      change ideleClassNorm (QuotientGroup.mk ((r p : I) * b)) = 1
      rw [ideleClassNorm_mk, map_mul, (mem_ideleNormOne _).mp (r p).property,
        ideleNorm_of_mem_ideleFiniteUnits hb.2, one_mul]
      exact hnorm _ hb.1
    · intro hc
      obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective c
      change q g = c at hg
      have hng : g ∈ ideleNormOne := by
        apply (mem_ideleNormOne g).mpr
        rw [← ideleClassNorm_mk, show (QuotientGroup.mk g : G) = c from hg]
        exact (mem_ideleClassNormOne c).mp hc
      -- (A.2.3.28): Remove the matching lift, then remove the principal factor.
      let p := ideleIdealClass g
      let x : ideleNormOne (K := K) := (r p)⁻¹ * ⟨g, hng⟩
      have hx : ideleIdealClass (x : I) = 1 := by
        change ideleIdealClass ((r p : I)⁻¹ * g) = 1
        rw [map_mul, map_inv, hr p]
        exact inv_mul_cancel p
      obtain ⟨a, u, hu, ha⟩ := (ideleIdealClass_normOne_eq_one_iff x).mp hx
      have hgu : g = (r p : I) * (IdeleGroup.unitEmbedding (𝓞 K) K a * (u : I)) := by
        rw [← ha]
        exact (mul_inv_cancel_left (r p : I) g).symm
      -- (A.2.3.25): At infinity use the cover; at finite places the inverse
      -- diagonal integral unit preserves the empty stage.
      have huArch : (∏ w : InfinitePlace K,
          ‖(ideleInfinitePart (u : I) : InfiniteAdeleRing K) w‖ ^ w.mult) = 1 :=
        (ideleNorm_of_mem_ideleFiniteUnits hu).symm.trans ((mem_ideleNormOne _).mp u.property)
      obtain ⟨t, w, hw, htw⟩ := hcover (ideleInfinitePart (u : I)) huArch
      let d := IdeleGroup.unitEmbedding (𝓞 K) K (Units.map (algebraMap (𝓞 K) K) t)
      let b := d⁻¹ * (u : I)
      have hb : b ∈ archWindow W := by
        have hbArch : ideleInfinitePart b = w := by
          change ideleInfinitePart (d⁻¹ * (u : I)) = w
          rw [map_mul, map_inv, htw, inv_mul_cancel_left]
        exact ⟨hbArch ▸ hw, ideleFiniteUnits.mul_mem
          (ideleFiniteUnits.inv_mem (integralUnit_mem_ideleFiniteUnits t)) hu⟩
      refine ⟨(r p : I) * b, mem_iUnion.mpr ⟨p, b, hb, rfl⟩, ?_⟩
      have hqd : q d = 1 := hprincipal _
      have hcancel : q (r p : I) * (1 * q (u : I)) = q (r p : I) * q (u : I) :=
        congrArg (q (r p : I) * ·) (one_mul (q (u : I)))
      calc
        q ((r p : I) * b) = q (r p : I) * q (u : I) := by
          simp only [b, map_mul, map_inv, hqd, inv_one]
          exact hcancel
        _ = q g := by
          rw [hgu, map_mul q, map_mul q, hprincipal]
          exact hcancel.symm
        _ = c := hg
  -- The subgroup has the topology induced from the actual quotient.
  have hq : Continuous q := QuotientGroup.continuous_mk
  exact isCompact_iff_compactSpace.mp (himage ▸ hS.image hq)

end Masullo
