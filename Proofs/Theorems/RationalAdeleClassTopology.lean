module

public import Lemmas.RationalIntegralAdeles
public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import Mathlib.Topology.Algebra.Group.Quotient

import Mathlib.Topology.Algebra.ProperAction.Basic

/-!
# The additive adele class group over ℚ

The open integral-finite stage modulo its diagonal integers is isomorphic to
`𝔸_ℚ / ℚ` as a topological additive group. This is (A.1.2.2), p. 541, in
local product coordinates. The diagonal is discrete and closed, and the
quotient is compact Hausdorff as in (A.1.2.1) and Lemma A.1.2.1(1)–(2),
pp. 540–541.
-/

open NumberField IsDedekindDomain Set Function Topology
open scoped RestrictedProduct

namespace Masullo

local notation "A" => AdeleRing (𝓞 ℚ) ℚ
local notation "D" => rationalDiagonal
local notation "W" => rationalIntegralAdeles
local notation "Z" => rationalIntegralDiagonal
local notation "C" => A ⧸ D
local notation "ι" => algebraMap ℚ A
local notation "V" => HeightOneSpectrum (𝓞 ℚ)

private noncomputable def stageToClasses : W →+ C := (QuotientAddGroup.mk' D).comp (W).subtype

private theorem ker_stageToClasses : stageToClasses.ker = Z := by
  ext w
  change ((w : A) : C) = 0 ↔ w ∈ Z
  rw [QuotientAddGroup.eq_zero_iff, mem_rationalIntegralDiagonal_iff]
  constructor
  · rintro ⟨r, hr⟩
    have hint : algebraMap ℚ A r ∈ W := hr.symm ▸ w.property
    obtain ⟨z, rfl⟩ := (algebraMap_mem_rationalIntegralAdeles_iff r).mp hint
    exact ⟨z, hr.symm.trans (map_intCast (ι) _)⟩
  · rintro ⟨z, hz⟩
    exact ⟨(z : ℚ), (map_intCast (ι) _).trans hz.symm⟩

private theorem surjective_stageToClasses : Surjective stageToClasses := by
  intro c
  obtain ⟨a, rfl⟩ := QuotientAddGroup.mk_surjective c
  obtain ⟨q, hq⟩ := exists_rational_sub_mem_integral a
  refine ⟨⟨a - algebraMap ℚ A q, hq⟩, ?_⟩
  change ((a - algebraMap ℚ A q : A) : C) = (a : C)
  exact QuotientAddGroup.eq_iff_sub_mem.mpr (by simpa using (show -(algebraMap ℚ A q) ∈ D from
    (D).neg_mem ⟨q, rfl⟩))

private theorem isQuotientMap_stageToClasses : IsQuotientMap stageToClasses :=
  (QuotientAddGroup.isOpenMap_coe.comp (isOpen_rationalIntegralAdeles.isOpenEmbedding_subtypeVal.isOpenMap))
    |>.isQuotientMap (QuotientAddGroup.continuous_mk.comp continuous_subtype_val) surjective_stageToClasses

private noncomputable def stageQuotientEquiv : W ⧸ Z ≃+ C :=
  (QuotientAddGroup.quotientAddEquivOfEq ker_stageToClasses.symm).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective stageToClasses surjective_stageToClasses)

private theorem stageQuotientEquiv_mk (w : W) : stageQuotientEquiv (w : W ⧸ Z) = stageToClasses w := by
  change (QuotientAddGroup.quotientKerEquivOfSurjective stageToClasses surjective_stageToClasses)
    (QuotientAddGroup.quotientAddEquivOfEq ker_stageToClasses.symm (w : W ⧸ Z)) = _
  rw [QuotientAddGroup.quotientAddEquivOfEq_mk]
  rfl

/-- Inclusion of the integral-finite stage induces the topological isomorphism
    with the full rational adele class group. -/
public noncomputable def rationalAdeleQuotientEquiv : (W ⧸ Z) ≃ₜ+ C :=
  stageQuotientEquiv.toContinuousAddEquiv fun U ↦ by
    rw [← (QuotientAddGroup.isQuotientMap_mk Z).isOpen_preimage,
      ← isQuotientMap_stageToClasses.isOpen_preimage]
    have h : QuotientAddGroup.mk ⁻¹' (stageQuotientEquiv ⁻¹' U) = stageToClasses ⁻¹' U := by
      ext w
      simp only [mem_preimage, stageQuotientEquiv_mk]
    rw [h]

/-- The isomorphism sends a class in the integral-finite stage to the class of the same adele. -/
public theorem rationalAdeleQuotientEquiv_mk (w : W) :
    rationalAdeleQuotientEquiv (w : W ⧸ Z) = ((w : A) : C) := stageQuotientEquiv_mk w

/-- The diagonal rationals are discrete: Integers are the only diagonal elements of
    the integral-finite stage, and the real interval `(-1,1)` isolates zero there. -/
public theorem discreteTopology_rationalDiagonal : DiscreteTopology D := by
  rw [discreteTopology_iff_isOpen_singleton_zero]
  let U : Set A := (W : Set A) ∩ rationalAdeleReal ⁻¹' Ioo (-1 : ℝ) 1
  have hU : IsOpen U := isOpen_rationalIntegralAdeles.inter (isOpen_Ioo.preimage continuous_rationalAdeleReal)
  convert hU.preimage (continuous_subtype_val (p := (· ∈ D))) using 1
  ext d
  constructor
  · rintro (rfl : d = 0)
    change (0 : A) ∈ W ∧ rationalAdeleReal (0 : A) ∈ Ioo (-1 : ℝ) 1
    have h0 : rationalAdeleReal (0 : A) = 0 := by simpa using rationalAdeleReal_algebraMap 0
    simp [h0]
  · intro hd
    obtain ⟨q, hq⟩ := d.property
    change algebraMap ℚ A q = (d : A) at hq
    change (d : A) ∈ W ∧ rationalAdeleReal (d : A) ∈ Ioo (-1 : ℝ) 1 at hd
    obtain ⟨z, rfl⟩ := (algebraMap_mem_rationalIntegralAdeles_iff q).mp (hq.symm ▸ hd.1)
    have hz : (-1 : ℤ) < z ∧ z < 1 := by
      have hr : rationalAdeleReal (d : A) ∈ Ioo (-1 : ℝ) 1 := hd.2
      rw [← hq, rationalAdeleReal_algebraMap, Rat.cast_intCast] at hr
      change (-1 : ℝ) < (z : ℝ) ∧ (z : ℝ) < 1 at hr
      exact_mod_cast hr
    have hz0 : z = 0 := by omega
    exact mem_singleton_iff.mpr (Subtype.ext (hq.symm.trans (by simp [hz0])))

/-- The diagonal rationals form a closed additive subgroup. -/
public theorem isClosed_rationalDiagonal : IsClosed (D : Set A) := by
  let : T2Space (FiniteAdeleRing (𝓞 ℚ) ℚ) :=
    show T2Space (Πʳ v : V, [v.adicCompletion ℚ, v.adicCompletionIntegers ℚ]) from inferInstance
  let : T2Space (AdeleRing (𝓞 ℚ) ℚ) := by unfold AdeleRing InfiniteAdeleRing; infer_instance
  let := discreteTopology_rationalDiagonal
  exact AddSubgroup.isClosed_of_discreteTopology

/-- The additive rational adele class group with its quotient topology is Hausdorff. -/
public theorem t2Space_rationalAdeleClasses : T2Space C := by
  let := isClosed_rationalDiagonal
  infer_instance

/-- A closed real strip of length one in the integral-finite stage covers the quotient,
    making the additive rational adele class group compact. -/
public theorem compactSpace_rationalAdeleClasses : CompactSpace C := by
  let := compactSpace_rationalFiniteIntegers
  let e := rationalIntegralAdelesHomeomorph
  let X : Set (ℝ × ((v : V) → v.adicCompletionIntegers ℚ)) := Icc 0 1 ×ˢ univ
  let p : W → C := stageToClasses
  have hp : Continuous p := isQuotientMap_stageToClasses.continuous
  have hX : IsCompact X := isCompact_Icc.prod isCompact_univ
  refine ⟨?_⟩
  have hcover : (p ∘ e) '' X = univ := by
    apply eq_univ_of_forall
    intro c
    obtain ⟨w, hw⟩ := surjective_stageToClasses c
    obtain ⟨z, hz⟩ := exists_sub_intCast_real_mem_Ico (w : A)
    let i : W := ⟨(z : A), intCast_mem_rationalIntegralAdeles z⟩
    let w' := w - i
    have hi : stageToClasses i = 0 := by
      change ((z : A) : C) = 0
      rw [QuotientAddGroup.eq_zero_iff]
      exact ⟨(z : ℚ), map_intCast (ι) _⟩
    have hw' : p w' = c := by
      change stageToClasses (w - i) = c
      rw [map_sub, hw, hi, sub_zero]
    refine ⟨e.symm w', ⟨?_, mem_univ _⟩, ?_⟩
    · have he := rationalIntegralAdelesHomeomorph_real (e.symm w')
      rw [e.apply_symm_apply w'] at he
      rw [← he]
      exact ⟨hz.1, hz.2.le⟩
    · change p (e (e.symm w')) = c
      rw [e.apply_symm_apply, hw']
  rw [← hcover]
  exact hX.image (hp.comp e.continuous)

end Masullo
