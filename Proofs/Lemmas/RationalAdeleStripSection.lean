module

public import Theorems.RationalAdeleClassTopology
public import Theorems.RationalAdeleFundamentalDomain

/-! # The Borel section of the rational additive adele classes -/

open NumberField MeasureTheory Set Topology

namespace Masullo

local notation "A" => AdeleRing (𝓞 ℚ) ℚ
local notation "C" => A ⧸ rationalDiagonal
local notation "π" => (QuotientAddGroup.mk : A → C)

private theorem injOn_strip : InjOn π rationalAdeleUnitStrip := by
  intro x hx y hy he
  obtain ⟨q, hq⟩ := (QuotientAddGroup.eq_iff_sub_mem.mp he : x - y ∈ rationalDiagonal)
  change algebraMap ℚ A q = x - y at hq
  have hy' : x - algebraMap ℚ A q ∈ rationalAdeleUnitStrip := by
    rwa [hq, sub_sub_cancel]
  have hx' : x - algebraMap ℚ A 0 ∈ rationalAdeleUnitStrip := by simpa using hx
  obtain ⟨r, _, hr⟩ := existsUnique_rational_sub_mem_adeleUnitStrip x
  have hq0 := (hr q hy').trans (hr 0 hx').symm
  simpa [hq0, sub_eq_zero] using hq.symm

private theorem exists_strip_rep (c : C) : ∃ a ∈ rationalAdeleUnitStrip, π a = c := by
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective c
  obtain ⟨q, hq, _⟩ := existsUnique_rational_sub_mem_adeleUnitStrip x
  refine ⟨x - algebraMap ℚ A q, hq, ?_⟩
  apply QuotientAddGroup.eq_iff_sub_mem.mpr
  rw [sub_right_comm, sub_self, zero_sub, ← map_neg]
  exact ⟨-q, rfl⟩

/-- The unique representative with integral finite coordinates and real coordinate in `[0,1)`. -/
public noncomputable def rationalAdeleStripRep (c : C) : A := (exists_strip_rep c).choose

public theorem rationalAdeleStripRep_mem (c : C) : rationalAdeleStripRep c ∈ rationalAdeleUnitStrip :=
  (exists_strip_rep c).choose_spec.1

@[simp] public theorem mk_rationalAdeleStripRep (c : C) : π (rationalAdeleStripRep c) = c :=
  (exists_strip_rep c).choose_spec.2

public theorem rationalAdeleStripRep_mk_of_mem {a : A} (ha : a ∈ rationalAdeleUnitStrip) :
    rationalAdeleStripRep (π a) = a :=
  injOn_strip (rationalAdeleStripRep_mem _) ha (mk_rationalAdeleStripRep _)

private noncomputable def stripWindow (t : ℝ) : Set A :=
  (rationalIntegralAdeles : Set A) ∩ rationalAdeleReal ⁻¹' Icc 0 t

private theorem isCompact_stripWindow (t : ℝ) : IsCompact (stripWindow t) := by
  let := compactSpace_rationalFiniteIntegers
  let e := rationalAdeleIntegralEmbedding
  have he (x : ℝ × RationalFiniteIntegers) : rationalAdeleReal (e x) = x.1 :=
    rationalIntegralAdelesHomeomorph_real x
  have h : e '' (Icc (0 : ℝ) t ×ˢ (univ : Set RationalFiniteIntegers)) = stripWindow t := by
    ext a
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨(rationalIntegralAdelesHomeomorph x).property, by
        rw [mem_preimage, he]
        exact hx.1⟩
    · rintro ⟨ha, ht⟩
      let x := rationalIntegralAdelesHomeomorph.symm ⟨a, ha⟩
      have hx : e x = a := congrArg Subtype.val (rationalIntegralAdelesHomeomorph.apply_symm_apply ⟨a, ha⟩)
      exact ⟨x, ⟨by rwa [← he, hx], mem_univ _⟩, hx⟩
  rw [← h]
  exact (isCompact_Icc.prod isCompact_univ).image isOpenEmbedding_rationalAdeleIntegralEmbedding.continuous

private theorem stripWindow_subset {t : ℝ} (ht : t < 1) : stripWindow t ⊆ rationalAdeleUnitStrip :=
  fun _ h ↦ ⟨h.1, h.2.1, h.2.2.trans_lt ht⟩

set_option linter.concreteInstances false in
/-- The half-open strip section is Borel, by covering it with compact sub-strips
on which the projection is a closed embedding. -/
public theorem measurable_rationalAdeleStripRep
    [MeasurableSpace A] [BorelSpace A] [MeasurableSpace C] [BorelSpace C] :
    Measurable rationalAdeleStripRep := by
  let := t2Space_rationalAdeleClasses
  let Q := {q : ℚ // (q : ℝ) < 1}
  let p (q : Q) : stripWindow (q : ℚ) → C := π ∘ Subtype.val
  intro U hU
  have himage (q : Q) : MeasurableSet (p q '' (Subtype.val ⁻¹' U)) := by
    let := isCompact_iff_compactSpace.mp (isCompact_stripWindow (q : ℚ))
    have hp : Continuous (p q) := QuotientAddGroup.continuous_mk.comp continuous_subtype_val
    have hi : Function.Injective (p q) := fun x y hxy ↦ Subtype.ext
      (injOn_strip (stripWindow_subset q.property x.property) (stripWindow_subset q.property y.property) hxy)
    exact (hp.isClosedEmbedding hi).measurableEmbedding.measurableSet_image.mpr
      (measurable_subtype_coe hU)
  convert MeasurableSet.iUnion himage using 1
  ext c
  rw [mem_preimage, mem_iUnion]
  constructor
  · intro hc
    have hs := rationalAdeleStripRep_mem c
    obtain ⟨q, hq, hq1⟩ := exists_rat_btwn hs.2.2
    exact ⟨⟨q, hq1⟩, ⟨⟨_, hs.1, hs.2.1, hq.le⟩, hc, mk_rationalAdeleStripRep c⟩⟩
  · rintro ⟨q, x, hx, rfl⟩
    change rationalAdeleStripRep (π (x : A)) ∈ U
    rwa [rationalAdeleStripRep_mk_of_mem (stripWindow_subset q.property x.property)]

end Masullo
