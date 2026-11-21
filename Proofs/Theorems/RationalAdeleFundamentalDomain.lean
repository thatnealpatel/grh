module

public import Lemmas.RationalIntegralAdeles
public import Mathlib.MeasureTheory.Group.FundamentalDomain

/-!
# A fundamental domain for the additive rational diagonal

The half-open real strip with integral finite coordinates gives the disjoint
translate cover of Example A.2.1.3, (A.2.1.5)–(A.2.1.6), pp. 545–546.
Measurability does not choose or normalize a Haar measure.
-/

open NumberField MeasureTheory Set

namespace Masullo

local notation "A" => AdeleRing (𝓞 ℚ) ℚ
local notation "ι" => algebraMap ℚ A

/-- The strip `[0,1) × ∏ p, ℤ_p` in the actual additive restricted product. -/
@[expose]
public noncomputable def rationalAdeleUnitStrip : Set A :=
  (rationalIntegralAdeles : Set A) ∩ rationalAdeleReal ⁻¹' Ico 0 1

private theorem real_sub (a b : A) :
    rationalAdeleReal (a - b) = rationalAdeleReal a - rationalAdeleReal b := by
  simp only [rationalAdeleReal_apply]
  exact map_sub (InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace) _ _

/-- Every rational adele lies in exactly one diagonal rational translate of the strip. -/
public theorem existsUnique_rational_sub_mem_adeleUnitStrip (a : A) :
    ∃! q : ℚ, a - ι q ∈ rationalAdeleUnitStrip := by
  -- Clear the finite denominators, then reduce the real coordinate modulo one.
  obtain ⟨r, hr⟩ := exists_rational_sub_mem_integral a
  obtain ⟨z, hz⟩ := exists_sub_intCast_real_mem_Ico (a - ι r)
  have hbase : a - ι (r + (z : ℚ)) ∈ rationalAdeleUnitStrip := by
    rw [map_add, map_intCast, ← sub_sub]
    exact ⟨rationalIntegralAdeles.sub_mem hr (intCast_mem_rationalIntegralAdeles z), hz⟩
  refine ⟨r + (z : ℚ), hbase, ?_⟩
  intro q hq
  -- Two strip points differing by a diagonal rational differ by an integer.
  have hd : ι (q - (r + (z : ℚ))) = (a - ι (r + (z : ℚ))) - (a - ι q) := by
    rw [map_sub]
    abel
  have hi : ι (q - (r + (z : ℚ))) ∈ rationalIntegralAdeles := by
    rw [hd]
    exact rationalIntegralAdeles.sub_mem hbase.1 hq.1
  obtain ⟨n, hn⟩ := (algebraMap_mem_rationalIntegralAdeles_iff _).mp hi
  -- The difference of two real coordinates in `[0,1)` lies in `(-1,1)`.
  have he := congrArg rationalAdeleReal hd
  rw [rationalAdeleReal_algebraMap, hn, Rat.cast_intCast, real_sub] at he
  have hb : rationalAdeleReal (a - ι (r + (z : ℚ))) ∈ Ico (0 : ℝ) 1 := hbase.2
  have hq' : rationalAdeleReal (a - ι q) ∈ Ico (0 : ℝ) 1 := hq.2
  have hreal : (-1 : ℝ) < (n : ℝ) ∧ (n : ℝ) < 1 :=
    ⟨by linarith [hb.1, hq'.2], by linarith [hb.2, hq'.1]⟩
  have hint : (-1 : ℤ) < n ∧ n < 1 := by exact_mod_cast hreal
  have hn0 : n = 0 := by omega
  exact sub_eq_zero.mp (by simpa only [hn0, Int.cast_zero] using hn)

-- Borel measure spaces are supplied locally rather than installed as global instances.
set_option linter.concreteInstances false in
/-- The half-open strip is Borel measurable. -/
public theorem measurableSet_rationalAdeleUnitStrip [MeasurableSpace A] [BorelSpace A] :
    MeasurableSet rationalAdeleUnitStrip :=
  isOpen_rationalIntegralAdeles.measurableSet.inter
    (continuous_rationalAdeleReal.measurable measurableSet_Ico)

set_option linter.concreteInstances false in
/-- The strip is a measurable fundamental domain for the rational diagonal's
additive action, for any Borel measure on the adeles. -/
public theorem rationalAdeleUnitStrip_isAddFundamentalDomain [MeasurableSpace A] [BorelSpace A]
    (μ : Measure A) : IsAddFundamentalDomain rationalDiagonal rationalAdeleUnitStrip μ := by
  apply IsAddFundamentalDomain.mk' measurableSet_rationalAdeleUnitStrip.nullMeasurableSet
  intro a
  obtain ⟨q, hq, huniq⟩ := existsUnique_rational_sub_mem_adeleUnitStrip a
  refine ⟨⟨ι (-q), ⟨-q, rfl⟩⟩, ?_, ?_⟩
  · change ι (-q) + a ∈ rationalAdeleUnitStrip
    simpa only [map_neg, sub_eq_add_neg, add_comm] using hq
  · intro g hg
    obtain ⟨r, hr⟩ := g.property
    change ι r = (g : A) at hr
    change (g : A) + a ∈ rationalAdeleUnitStrip at hg
    have h : a - ι (-r) ∈ rationalAdeleUnitStrip := by
      rw [map_neg, sub_neg_eq_add, add_comm, hr]
      exact hg
    have he := huniq (-r) h
    apply Subtype.ext
    change (g : A) = ι (-q)
    rw [← hr, ← he, neg_neg]

end Masullo
