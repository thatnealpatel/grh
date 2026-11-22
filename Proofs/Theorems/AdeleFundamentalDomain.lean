module

public import Lemmas.AdeleIntegralCell

/-! # A Borel fundamental domain for the additive number-field diagonal

Definition A.2.1.1 and Lemma A.2.1.2(1), PDF p. 545, supply the product of
an Archimedean cell and the integral finite adeles, and its translate cover.
The display (A.2.1.1) indexes the Archimedean sum by `r₁ + r₂` and places an
absolute value on each coordinate. Instead use signed real coordinates in
`[0,1)^[K:ℚ]` in a full integral basis, as in the proof of Lemma A.2.4.2(2),
PDF p. 554. This gives one point per orbit, not just a covering. These
source readings are provisional (pinned Markdown and numbered PDF layout).
-/

open IsDedekindDomain MeasureTheory NumberField Set
open scoped Masullo.AdeleStage

namespace Masullo

noncomputable section

variable (K : Type*) [Field K] [NumberField K]

local notation "A" => AdeleRing (𝓞 K) K
local notation "A∞" => InfiniteAdeleRing K
local notation "ι" => algebraMap K A
local notation "j" => algebraMap (𝓞 K) K
local notation "Δ" => AdeleRing.principalSubgroup (𝓞 K) K

/-- The full-dimensional half-open cell at infinity times the integral finite adeles,
as a set in the actual adele ring. -/
@[expose] public def adeleIntegralCell : Set A :=
  adeleIntegerRectangle K (archimedeanIntegralCell K)

/-- Borel measurability in the actual restricted product, via its open integral stage. -/
public theorem measurableSet_adeleIntegralCell : MeasurableSet (adeleIntegralCell K) :=
  measurableSet_adeleIntegerRectangle K (measurableSet_archimedeanIntegralCell K)

/-- Every adele has a unique diagonal translation into the half-open cell. -/
public theorem existsUnique_sub_mem_adeleIntegralCell (a : A) :
    ∃! q : K, a - ι q ∈ adeleIntegralCell K := by
  -- First choose a finite reduction; its other choices are exactly the global integer shifts.
  obtain ⟨r, hr⟩ := exists_finiteIntegral_diagonalCoset K a
  -- Fix the remaining translation by reducing the infinite coordinate in the integral basis.
  obtain ⟨z, hz, huniq⟩ := existsUnique_sub_integer_mem_archimedeanIntegralCell K (a - ι r).1
  have hfst (w : 𝓞 K) : (a - ι (r + j w)).1 = (a - ι r).1 - algebraMap K A∞ (j w) := by
    rw [map_add, ← sub_sub]
    rfl
  refine ⟨r + j z, ⟨?_, (hr _).mpr ⟨z, add_sub_cancel_left _ _⟩⟩, ?_⟩
  · rw [hfst]
    exact hz
  · intro q hq
    obtain ⟨w, hw⟩ := (hr q).mp hq.2
    have hq' : q = r + j w := (sub_eq_iff_eq_add.mp hw).trans (add_comm _ _)
    have harch := hq.1
    rw [hq', hfst] at harch
    rw [hq', huniq w harch]

/-- The Borel cell is an additive fundamental domain for the actual principal subgroup;
no property of the measure is needed for this pointwise partition. -/
public theorem adeleIntegralCell_isAddFundamentalDomain (μ : Measure A) :
    IsAddFundamentalDomain Δ (adeleIntegralCell K) μ := by
  apply IsAddFundamentalDomain.mk' (measurableSet_adeleIntegralCell K).nullMeasurableSet
  intro a
  obtain ⟨q, hq, huniq⟩ := existsUnique_sub_mem_adeleIntegralCell K a
  refine ⟨⟨ι (-q), ⟨-q, rfl⟩⟩, ?_, ?_⟩
  · change ι (-q) + a ∈ adeleIntegralCell K
    simpa only [map_neg, sub_eq_add_neg, add_comm] using hq
  · intro g hg
    obtain ⟨r, hr⟩ := g.property
    change ι r = (g : A) at hr
    change (g : A) + a ∈ adeleIntegralCell K at hg
    have h : a - ι (-r) ∈ adeleIntegralCell K := by
      rw [map_neg, sub_neg_eq_add, add_comm, hr]
      exact hg
    have he := huniq (-r) h
    apply Subtype.ext
    change (g : A) = ι (-q)
    rw [← hr, ← he, neg_neg]

end

end Masullo
