module

public import Lemmas.IdeleUnitWindow
import Theorems.IdeleClassSeparation
import Mathlib.Topology.LocalAtTarget

/-! # The principal quotient at norm one

The norm descends to actual idele classes ((A.1.3.6), PDF p. 542).
The orbits in Proposition A.2.3.10(2), (A.2.3.25)–(26), p. 552, are
therefore exactly the fibres of the restriction of the principal quotient.
We check this on the inherited subgroup topologies, not by assigning a
new quotient topology to the norm-one classes.
-/

open NumberField Set
open scoped Pointwise

namespace Masullo

variable {K : Type*} [Field K] [NumberField K]

local notation "I" => IdeleGroup (𝓞 K) K
local notation "C" => IdeleClassGroup (𝓞 K) K
local notation "I₁" => ideleNormOne (K := K)
local notation "C₁" => ideleClassNormOne (K := K)
local notation "P" => IdeleGroup.principalSubgroup (𝓞 K) K
local notation "d" => idelePrincipalNormOne (K := K)

/-- The actual principal quotient, restricted to the norm-one subgroups. -/
public noncomputable def ideleClassQuotientNormOne : I₁ →* C₁ where
  toFun g := ⟨QuotientGroup.mk (g : I), by
    exact (mem_ideleClassNormOne _).mpr (by
      rw [ideleClassNorm_mk]
      exact (mem_ideleNormOne _).mp g.property)⟩
  map_one' := Subtype.ext (QuotientGroup.mk_one P)
  map_mul' g h := Subtype.ext (QuotientGroup.mk_mul P (g : I) (h : I))

local notation "q₁" => ideleClassQuotientNormOne (K := K)

public theorem coe_ideleClassQuotientNormOne (g : I₁) :
    (q₁ g : C) = QuotientGroup.mk (g : I) := by
  unfold ideleClassQuotientNormOne
  rfl

/-- Restriction to the full preimage of norm-one classes preserves openness and
surjectivity. Both norm-one groups have their inherited topologies. -/
public theorem isOpenQuotientMap_ideleClassQuotientNormOne : IsOpenQuotientMap q₁ := by
  let π : I → C := QuotientGroup.mk
  have hpre : (I₁ : Set I) = π ⁻¹' (C₁ : Set C) := by
    ext g
    change g ∈ I₁ ↔ (QuotientGroup.mk g : C) ∈ C₁
    rw [mem_ideleNormOne, mem_ideleClassNormOne, ideleClassNorm_mk]
  have hπ : IsOpenQuotientMap π := QuotientGroup.isOpenQuotientMap_mk
  exact (hπ.restrictPreimage (C₁ : Set C)).comp (Homeomorph.setCongr hpre).isOpenQuotientMap

/-- Equality of actual norm-one classes is exactly the orbit relation for
left translation by the diagonal `Kˣ`. -/
public theorem ideleClassQuotientNormOne_eq_iff (x y : I₁) :
    q₁ x = q₁ y ↔ ∃ a : Kˣ, d a * x = y := by
  rw [← eq_comm, ← Subtype.coe_inj, coe_ideleClassQuotientNormOne,
    coe_ideleClassQuotientNormOne, QuotientGroup.eq_iff_div_mem]
  change (∃ a : Kˣ, IdeleGroup.unitEmbedding (𝓞 K) K a = (y : I) / (x : I)) ↔ _
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨a, Subtype.ext ((eq_div_iff_mul_eq').mp ((coe_idelePrincipalNormOne a).trans ha))⟩
  · rintro ⟨a, ha⟩
    refine ⟨a, eq_div_iff_mul_eq'.mpr ?_⟩
    rw [← coe_idelePrincipalNormOne]
    exact congrArg Subtype.val ha

/-- Each norm-one idele has an open neighborhood on which the quotient is
injective. This is the discrete-kernel input to measurable descent. -/
public theorem exists_open_injOn_ideleClassQuotientNormOne (x : I₁) :
    ∃ U : Set I₁, IsOpen U ∧ x ∈ U ∧ InjOn q₁ U := by
  have hdisc := discreteTopology_principalIdeles (K := K)
  have hopen : IsOpen ({1} : Set P) := isOpen_discrete _
  obtain ⟨O, hO, hOeq⟩ := isOpen_induced_iff.mp hopen
  have hO₁ : (1 : I) ∈ O := by
    change (1 : P) ∈ Subtype.val ⁻¹' O
    rw [hOeq]
    exact mem_singleton _
  have hdiff : Continuous (fun p : I₁ × I₁ ↦ (p.2 : I) / (p.1 : I)) :=
    (continuous_subtype_val.comp continuous_snd).div'
      (continuous_subtype_val.comp continuous_fst)
  have hxx : (x, x) ∈ (fun p : I₁ × I₁ ↦ (p.2 : I) / (p.1 : I)) ⁻¹' O := by
    simpa only [mem_preimage, div_self'] using hO₁
  obtain ⟨U, V, hU, hV, hxU, hxV, hUV⟩ := isOpen_prod_iff.mp (hO.preimage hdiff) x x hxx
  refine ⟨U ∩ V, hU.inter hV, ⟨hxU, hxV⟩, ?_⟩
  intro g hg h hh heq
  obtain ⟨a, ha⟩ := (ideleClassQuotientNormOne_eq_iff g h).mp heq
  have hd : (d a : I) = (h : I) / (g : I) :=
    eq_div_iff_mul_eq'.mpr (congrArg Subtype.val ha)
  let p : P := ⟨IdeleGroup.unitEmbedding (𝓞 K) K a, ⟨a, rfl⟩⟩
  have hp : p ∈ Subtype.val ⁻¹' O := by
    change IdeleGroup.unitEmbedding (𝓞 K) K a ∈ O
    rw [← coe_idelePrincipalNormOne, hd]
    exact hUV (show (g, h) ∈ U ×ˢ V from ⟨hg.1, hh.2⟩)
  have hp₁ : p = 1 := mem_singleton_iff.mp (hOeq ▸ hp)
  have hda : d a = 1 := Subtype.ext (congrArg (fun z : P ↦ (z : I)) hp₁)
  simpa only [hda, one_mul] using ha

end Masullo
