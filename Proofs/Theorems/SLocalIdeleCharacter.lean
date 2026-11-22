module

public import Theorems.IdeleFiniteStageCharacter
public import Mathlib.Topology.Algebra.Group.Quotient
import Lemmas.FiniteCompletionCompact
import Theorems.IdeleClassSeparation

/-! # S-local descent of idelic characters

The quotient in §1.1.4 (second bullet, p. 12) is on the open stage of the
idele class group, not on the whole group. Section 2.3, p. 99, identifies
its kernel; §3.1.2.3, (3.1.2.6)–(3.1.2.9), p. 121, defines the resulting
character by inserting ones outside `S`. We use all infinite places and
index `S` in Lean by only its finite places.
-/

open IsDedekindDomain NumberField Topology

namespace Masullo

variable (K : Type*) [Field K] [NumberField K]

local notation "V" => HeightOneSpectrum (𝓞 K)
local notation "F" v => HeightOneSpectrum.adicCompletion K v
local notation "O" v => HeightOneSpectrum.adicCompletionIntegers K v
local notation "I" => IdeleGroup (𝓞 K) K
local notation "C" => IdeleClassGroup (𝓞 K) K
local notation "P" => IdeleGroup.principalSubgroup (𝓞 K) K

variable (S : Finset (HeightOneSpectrum (𝓞 K)))

/-- The units of the product of the completions at the places in `S`,
including every infinite place. The finite factors are full field units. -/
public abbrev SLocalIdeles (S : Finset (HeightOneSpectrum (𝓞 K))) :=
  ((v : InfinitePlace K) → v.Completionˣ) × ((v : {v : V // v ∈ S}) → (F v.val)ˣ)

/-- The product of integral units at the places not in `S`. -/
public abbrev OutsideSUnits (S : Finset (HeightOneSpectrum (𝓞 K))) := (v : {v : V // v ∉ S}) → (O v.val)ˣ

/-- Forget the outside-`S` factors. -/
public noncomputable def ideleStageProject : IdeleFiniteStage K S →* SLocalIdeles K S :=
  (MonoidHom.fst _ _).prod ((MonoidHom.fst _ _).comp (MonoidHom.snd _ _))

/-- Insert ones outside `S`, as in (3.1.2.8). -/
public noncomputable def ideleStageInsert : SLocalIdeles K S →* IdeleFiniteStage K S :=
  (MonoidHom.fst _ _).prod ((MonoidHom.snd _ _).prod (1 : _ →* OutsideSUnits K S))

/-- Insert the outside-`S` units into the stage with ones at the other places. -/
public noncomputable def ideleStageOutside : OutsideSUnits K S →* IdeleFiniteStage K S :=
  (1 : _ →* _).prod ((1 : _ →* _).prod (MonoidHom.id _))

/-- The principal relation on the stage is the preimage of the principal
ideles in the actual idele group. -/
public noncomputable def ideleStagePrincipal : Subgroup (IdeleFiniteStage K S) :=
  Subgroup.comap (ideleFiniteStageEmbedding K S) P

/-- The diagonal idele of a nonzero field element belongs to the stage precisely when the
unit and its inverse are integral at every finite place outside `S`.
Thus the principal elements of the stage are the diagonal `S`-units. -/
public theorem ideleStage_unitEmbedding_mem_range_iff (a : Kˣ) :
    IdeleGroup.unitEmbedding (𝓞 K) K a ∈ Set.range (ideleFiniteStageEmbedding K S) ↔
      ∀ v : V, v ∉ S → algebraMap K (F v) (a : K) ∈ (O v) ∧
        algebraMap K (F v) (↑(a⁻¹) : K) ∈ (O v) := by
  rw [range_ideleFiniteStageEmbedding]
  simp only [Set.mem_ofPred_eq, ← map_inv (IdeleGroup.unitEmbedding (𝓞 K) K)]
  rfl

/-- The principal relation in the stage consists exactly of the diagonals of
field elements satisfying the outside-`S` integrality conditions. -/
public theorem mem_ideleStagePrincipal_iff (x : IdeleFiniteStage K S) :
    x ∈ ideleStagePrincipal K S ↔ ∃ a : Kˣ,
      (∀ v : V, v ∉ S → algebraMap K (F v) (a : K) ∈ (O v) ∧
        algebraMap K (F v) (↑(a⁻¹) : K) ∈ (O v)) ∧
      IdeleGroup.unitEmbedding (𝓞 K) K a = ideleFiniteStageEmbedding K S x := by
  change (∃ a : Kˣ, IdeleGroup.unitEmbedding (𝓞 K) K a = _) ↔ _
  exact ⟨fun ⟨a, ha⟩ ↦ ⟨a, (ideleStage_unitEmbedding_mem_range_iff K S a).mp ⟨x, ha.symm⟩, ha⟩,
    fun ⟨a, _, ha⟩ ↦ ⟨a, ha⟩⟩

/-- The open stage modulo the diagonal `S`-units: the manuscript's `C_{F,S}`. -/
public abbrev IdeleStageClasses (S : Finset (HeightOneSpectrum (𝓞 K))) := IdeleFiniteStage K S ⧸ ideleStagePrincipal K S

/-- The local group `J_{F,S}`: the active factors modulo the projection
of the diagonal `S`-units. Both quotients carry the quotient topology. -/
public abbrev SLocalIdeleClasses (S : Finset (HeightOneSpectrum (𝓞 K))) :=
  SLocalIdeles K S ⧸ (ideleStagePrincipal K S).map (ideleStageProject K S)

local notation "A" => IdeleFiniteStage K S
local notation "B" => SLocalIdeles K S
local notation "N" => ideleStagePrincipal K S
local notation "p" => ideleStageProject K S
local notation "i" => ideleStageInsert K S
local notation "u" => ideleStageOutside K S
local notation "M" => Subgroup.map p N

private theorem isOpenQuotientMap_ideleStageProject : IsOpenQuotientMap p := by
  let e : A ≃ₜ B × OutsideSUnits K S := (Homeomorph.prodAssoc _ _ _).symm
  exact isOpenQuotientMap_fst.comp e.isOpenQuotientMap

private theorem continuous_ideleStageInsert : Continuous i :=
  continuous_fst.prodMk (continuous_snd.prodMk continuous_const)

private theorem continuous_ideleStageOutside : Continuous u :=
  continuous_const.prodMk (continuous_const.prodMk continuous_id)

/-- The map `C_{F,S} → C_F` induced by inclusion into the actual ideles. -/
public noncomputable def ideleStageToClass : IdeleStageClasses K S →ₜ* C where
  toMonoidHom := QuotientGroup.map N P (ideleFiniteStageEmbedding K S) le_rfl
  continuous_toFun := (QuotientGroup.isQuotientMap_mk N).continuous_iff.mpr
    (QuotientGroup.continuous_mk.comp (isOpenEmbedding_ideleFiniteStageEmbedding K S).continuous)

public theorem ideleStageToClass_mk (x : A) :
    ideleStageToClass K S (QuotientGroup.mk x) =
      QuotientGroup.mk (ideleFiniteStageEmbedding K S x) := by rfl

/-- The stage classes are an open subgroup of the actual idele class group.
No surjectivity onto all classes is asserted. -/
public theorem isOpenEmbedding_ideleStageToClass : IsOpenEmbedding (ideleStageToClass K S) := by
  refine IsOpenEmbedding.of_continuous_injective_isOpenMap (ideleStageToClass K S).continuous ?_ ?_
  · intro x y h
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective y
    rw [ideleStageToClass_mk, ideleStageToClass_mk, QuotientGroup.eq_iff_div_mem, ← map_div] at h
    exact QuotientGroup.eq_iff_div_mem.mpr h
  · exact IsOpenMap.of_comp QuotientGroup.continuous_mk QuotientGroup.mk_surjective
      (QuotientGroup.isOpenMap_coe.comp (isOpenEmbedding_ideleFiniteStageEmbedding K S).isOpenMap)

/-- The projection `C_{F,S} → J_{F,S}` on the quotients. -/
public noncomputable def ideleStageToLocal : IdeleStageClasses K S →ₜ* SLocalIdeleClasses K S where
  toMonoidHom := QuotientGroup.map N M p (fun x hx ↦ ⟨x, hx, rfl⟩)
  continuous_toFun := (QuotientGroup.isQuotientMap_mk N).continuous_iff.mpr
    (QuotientGroup.continuous_mk.comp (isOpenQuotientMap_ideleStageProject K S).continuous)

public theorem ideleStageToLocal_mk (x : A) :
    ideleStageToLocal K S (QuotientGroup.mk x) = QuotientGroup.mk (p x) := by rfl

/-- The displayed projection is an open topological quotient. -/
public theorem isOpenQuotientMap_ideleStageToLocal : IsOpenQuotientMap (ideleStageToLocal K S) := by
  have h : IsOpenQuotientMap (ideleStageToLocal K S ∘ (QuotientGroup.mk : A → IdeleStageClasses K S)) :=
    QuotientGroup.isOpenQuotientMap_mk.comp (isOpenQuotientMap_ideleStageProject K S)
  exact ⟨h.surjective.of_comp, (ideleStageToLocal K S).continuous,
    IsOpenMap.of_comp QuotientGroup.continuous_mk QuotientGroup.mk_surjective h.isOpenMap⟩

/-- The kernel is exactly the image in the stage classes of the outside-`S`
unit product, not the image of a sum of single-place groups. -/
public theorem ker_ideleStageToLocal : (ideleStageToLocal K S).toMonoidHom.ker =
    ((QuotientGroup.mk' N).comp u).range := by
  ext z
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective z
  change ideleStageToLocal K S (QuotientGroup.mk x) = 1 ↔ _
  rw [ideleStageToLocal_mk, QuotientGroup.eq_one_iff]
  constructor
  · rintro ⟨y, hy, he⟩
    have hproj : p (x / y) = 1 := by rw [map_div, he, div_self']
    have hz : u (x / y).2.2 = x / y := by
      exact Prod.ext (congrArg Prod.fst hproj).symm
        (Prod.ext (congrArg Prod.snd hproj).symm rfl)
    refine ⟨(x / y).2.2, ?_⟩
    change (QuotientGroup.mk (u (x / y).2.2) : IdeleStageClasses K S) = QuotientGroup.mk x
    rw [hz, QuotientGroup.mk_div, (QuotientGroup.eq_one_iff y).mpr hy, div_one]
  · rintro ⟨w, hw⟩
    change (QuotientGroup.mk (u w) : IdeleStageClasses K S) = QuotientGroup.mk x at hw
    have h := congrArg (ideleStageToLocal K S) hw
    rw [ideleStageToLocal_mk, ideleStageToLocal_mk] at h
    exact (QuotientGroup.eq_one_iff _).mp h.symm

/-- In the stage classes the outside-`S` image is compact, and closed
because the stage embeds in the Hausdorff idele class group. -/
public theorem isCompact_isClosed_ker_ideleStageToLocal :
    IsCompact ((ideleStageToLocal K S).toMonoidHom.ker : Set (IdeleStageClasses K S)) ∧
      IsClosed ((ideleStageToLocal K S).toMonoidHom.ker : Set (IdeleStageClasses K S)) := by
  let (v : {v : V // v ∉ S}) : CompactSpace (O v.val)ˣ :=
    compactSpace_finiteCompletionIntegralUnits K v.val
  let : T2Space C := t2Space_ideleClassGroup
  let : T2Space (IdeleStageClasses K S) := (isOpenEmbedding_ideleStageToClass K S).isEmbedding.t2Space
  rw [ker_ideleStageToLocal]
  have h : IsCompact (Set.range ((QuotientGroup.mk' N).comp u)) :=
    isCompact_range (QuotientGroup.continuous_mk.comp (continuous_ideleStageOutside K S))
  exact ⟨h, h.isClosed⟩

variable (χ : HeckeCharacter (𝓞 K) K) (hu : ∀ v ∉ S, χ.IsUnramifiedAt v)

include hu in
private theorem character_stage_project (x : A) :
    χ (ideleStageToClass K S (QuotientGroup.mk (i (p x)))) =
      χ (ideleStageToClass K S (QuotientGroup.mk x)) := by
  simp only [ideleStageToClass_mk]
  exact (ideleFiniteStage_character_factor K χ S hu (i (p x))).trans
    (ideleFiniteStage_character_factor K χ S hu x).symm

/-- The quasi-character of `J_{F,S}` induced by an idelic quasi-character
unramified outside `S`. On a representative this evaluates the character
on the idele with outside-`S` components set to one. -/
public noncomputable def sLocalCharacter : SLocalIdeleClasses K S →ₜ* ℂ where
  toMonoidHom := QuotientGroup.lift M
    (χ.toMonoidHom.comp ((ideleStageToClass K S).toMonoidHom.comp ((QuotientGroup.mk' N).comp i))) (by
      rintro _ ⟨x, hx, rfl⟩
      change χ (ideleStageToClass K S (QuotientGroup.mk (i (p x)))) = 1
      rw [character_stage_project K S χ hu, (QuotientGroup.eq_one_iff x).mpr hx, map_one, map_one])
  continuous_toFun := (QuotientGroup.isQuotientMap_mk M).continuous_iff.mpr
    (χ.continuous.comp ((ideleStageToClass K S).continuous.comp
      (QuotientGroup.continuous_mk.comp (continuous_ideleStageInsert K S))))

public theorem sLocalCharacter_mk (b : B) :
    sLocalCharacter K S χ hu (QuotientGroup.mk b) =
      χ (QuotientGroup.mk (ideleFiniteStageEmbedding K S (i b))) := by rfl

/-- Its pullback to `C_{F,S}` is the restriction of the original character. -/
public theorem sLocalCharacter_pullback (z : IdeleStageClasses K S) :
    sLocalCharacter K S χ hu (ideleStageToLocal K S z) = χ (ideleStageToClass K S z) := by
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective z
  rw [ideleStageToLocal_mk]
  exact character_stage_project K S χ hu x

include hu in
/-- The restricted character kills the full kernel of the stage projection. -/
public theorem character_eq_one_on_ideleStageToLocal_kernel (z : IdeleStageClasses K S)
    (hz : ideleStageToLocal K S z = 1) : χ (ideleStageToClass K S z) = 1 := by
  rw [← sLocalCharacter_pullback K S χ hu, hz, map_one]

include hu in
/-- There is exactly one continuous character with that pullback. -/
public theorem sLocalCharacter_existsUnique :
    ∃! ψ : SLocalIdeleClasses K S →ₜ* ℂ,
      ∀ z, ψ (ideleStageToLocal K S z) = χ (ideleStageToClass K S z) := by
  refine ⟨sLocalCharacter K S χ hu, sLocalCharacter_pullback K S χ hu, fun ψ hψ ↦ ?_⟩
  ext y
  obtain ⟨z, rfl⟩ := (isOpenQuotientMap_ideleStageToLocal K S).surjective y
  exact (hψ z).trans (sLocalCharacter_pullback K S χ hu z).symm

/-- Unitarity of the original character implies unitarity of the descent. -/
public theorem sLocalCharacter_unitary (hχ : ∀ c, ‖χ c‖ = 1) (y : SLocalIdeleClasses K S) :
    ‖sLocalCharacter K S χ hu y‖ = 1 := by
  obtain ⟨z, rfl⟩ := (isOpenQuotientMap_ideleStageToLocal K S).surjective y
  rw [sLocalCharacter_pullback]
  exact hχ _

end Masullo
