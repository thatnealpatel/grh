module

public import Lemmas.SharedKnotCell
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Data.Finset.Sort
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Tactic.FunProp

/-!
# Finite price assembly for three additional real knots

Source: `ad99c73de5cb7499d2b39b752d418200cf6a3884:.godel/bob/three-midpoints-deletion-33.md:24–28`,
“Three real knots, including collisions.”
Owning check session: `01a20e74-7a96-7653-9648-0eb1c4d5d43d`.

Scope: the finite original slabs, with distinct added sites counted only in their strict
interiors. Each resulting subslab has its own probability law on the full atom interval.
The single-knot and measurable-release prices are local inputs, relative to the same
atom upper used in the unsplit price. For the measurable release the only input needed
is its restriction to finite ordered piecewise constant laws. The fixed term can include
the tail allowance; neither that allowance, the local price certificates, nor an upper
bound for unrestricted all-real profiles is proved here.
-/

@[expose] public section

namespace Masullo.ThreeKnotPrice

open Set MeasureTheory SplitAtomBernstein SharedKnotCell
open scoped BigOperators

noncomputable section

/-- Only distinct added sites in the strict slab interior create subslabs. -/
def interiorSites (sites : List ℝ) (l r : ℝ) : Finset ℝ := by
  classical
  exact sites.toFinset.filter fun x ↦ x ∈ Ioo l r

/-- The interior sites in the order of the refined mesh. -/
def slabKnots (sites : List ℝ) (l r : ℝ) : List ℝ := by
  classical
  exact (interiorSites sites l r).sort

/-- A knot of this slab is exactly a supplied site strictly between its endpoints. -/
theorem mem_slabKnots {sites : List ℝ} {l r x : ℝ} :
    x ∈ slabKnots sites l r ↔ x ∈ sites ∧ x ∈ Ioo l r := by
  classical
  simp [slabKnots, interiorSites]

/-- Including the original endpoints gives a strictly increasing mesh. -/
theorem slabKnots_ordered (sites : List ℝ) {l r : ℝ} (hlr : l < r) :
    (l :: (slabKnots sites l r ++ [r])).Pairwise (· < ·) := by
  classical
  rw [List.pairwise_cons, List.pairwise_append]
  refine ⟨?_, ?_, by simp, ?_⟩
  · intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact (mem_slabKnots.mp hx).2.1
    · rwa [List.mem_singleton.mp hx]
  · exact (Finset.sortedLT_sort _).pairwise
  · intro x hx y hy
    rw [List.mem_singleton.mp hy]
    exact (mem_slabKnots.mp hx).2.2

/-- Sum the primitive-difference mean scores over consecutive pairs in
`l :: (knots ++ [r])`, using the law of each ordered endpoint pair. -/
def piecewiseLawScore (p : ℝ → Primitive) (law : ℝ → ℝ → ProbabilityMeasure Atom)
    (r : ℝ) : ℝ → List ℝ → ℝ
  | l, [] => (halfScore (p l) (p r)).mean (law l r)
  | l, s :: knots => (halfScore (p l) (p s)).mean (law l s) + piecewiseLawScore p law r s knots

/-- Actual score of the refinement by the supplied real sites, not a score indexed
by a prescribed split count. -/
def refinedSlabScore (p : ℝ → Primitive) (law : ℝ → ℝ → ProbabilityMeasure Atom)
    (sites : List ℝ) (l r : ℝ) : ℝ :=
  piecewiseLawScore p law r l (slabKnots sites l r)

/-- With no interior site the original slab contributes its one law mean. -/
theorem refinedSlabScore_of_empty (p : ℝ → Primitive) (law : ℝ → ℝ → ProbabilityMeasure Atom)
    {sites : List ℝ} {l r : ℝ} (h : interiorSites sites l r = ∅) :
    refinedSlabScore p law sites l r = (halfScore (p l) (p r)).mean (law l r) := by
  classical
  simp [refinedSlabScore, slabKnots, h, piecewiseLawScore]

/-- At one interior site both half-scores use the very same real split. -/
theorem refinedSlabScore_of_singleton (p : ℝ → Primitive)
    (law : ℝ → ℝ → ProbabilityMeasure Atom) {sites : List ℝ} {l r s : ℝ}
    (h : interiorSites sites l r = {s}) :
    refinedSlabScore p law sites l r = splitLawScore p l r s (law l s) (law s r) := by
  classical
  simp [refinedSlabScore, slabKnots, h, piecewiseLawScore, splitLawScore]

variable {ι : Type*}

/-- No site is charged to two slabs, and deduplication precedes counting. -/
theorem sum_interiorSites_card_le (slabs : Finset ι) (left right : ι → ℝ) (sites : List ℝ)
    (hdisj : (slabs : Set ι).PairwiseDisjoint fun i ↦ Ioo (left i) (right i)) :
    (∑ i ∈ slabs, (interiorSites sites (left i) (right i)).card) ≤ sites.toFinset.card := by
  classical
  have hpair : (slabs : Set ι).PairwiseDisjoint fun i ↦ interiorSites sites (left i) (right i) := by
    intro i hi j hj hij
    apply Finset.disjoint_left.mpr
    intro x hxi hxj
    exact Set.disjoint_left.mp (hdisj hi hj hij)
      (Finset.mem_filter.mp hxi).2 (Finset.mem_filter.mp hxj).2
  rw [← Finset.card_biUnion hpair]
  apply Finset.card_le_card
  intro x hx
  obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hx
  exact (Finset.mem_filter.mp hi).1

/-- The legal extra-price rows: at most three distinct single splits, or one
released slab with no partner or with one different slab split once. -/
def extraPriceRows (slabs : Finset ι) (J D : ι → ℝ) : Finset ℝ := by
  classical
  exact ((slabs.powerset.filter fun s ↦ s.card ≤ 3).image fun s ↦ ∑ i ∈ s, J i) ∪
    slabs.biUnion fun i ↦ insert (D i) ((slabs.erase i).image fun j ↦ D i + J j)

/-- There are no extraneous rows, and a repeated value need occur only once. -/
theorem mem_extraPriceRows {slabs : Finset ι} {J D : ι → ℝ} {x : ℝ} :
    x ∈ extraPriceRows slabs J D ↔
      (∃ s ⊆ slabs, s.card ≤ 3 ∧ (∑ i ∈ s, J i) = x) ∨
      (∃ i ∈ slabs, x = D i ∨ ∃ j ∈ slabs, j ≠ i ∧ D i + J j = x) := by
  classical
  simp only [extraPriceRows, Finset.mem_union, Finset.mem_image, Finset.mem_filter,
    Finset.mem_powerset, Finset.mem_biUnion, Finset.mem_insert, Finset.mem_erase,
    and_assoc, and_comm, and_left_comm]

/-- Maximum over the legal rows. The empty single-split row makes the table
nonempty even if there are no slabs. -/
def extraPrice (slabs : Finset ι) (J D : ι → ℝ) : ℝ :=
  (extraPriceRows slabs J D).sup'
    ⟨0, mem_extraPriceRows.mpr (.inl ⟨∅, Finset.empty_subset _, by simp, by simp⟩)⟩ id

/-- A scalar upper certificate for the extra price must bound exactly the legal rows. -/
theorem extraPrice_le_iff (slabs : Finset ι) (J D : ι → ℝ) (B : ℝ) :
    extraPrice slabs J D ≤ B ↔ ∀ x ∈ extraPriceRows slabs J D, x ≤ B := by
  unfold extraPrice
  exact Finset.sup'_le_iff _ id

private theorem mean_le_of_atom_le (q : Score) (ν : ProbabilityMeasure Atom) (B : ℝ)
    (h : ∀ u : Atom, q.eval u ≤ B) : q.mean ν ≤ B := by
  have hc : Continuous q.eval := by
    unfold Score.eval Moment.eval
    fun_prop
  have hi : Integrable (fun u : Atom ↦ q.eval u) (ν : Measure Atom) :=
    integrableOn_univ.mp <|
      (hc.comp continuous_subtype_val).continuousOn.integrableOn_compact isCompact_univ
  simpa only [Score.mean, integral_const, probReal_univ, one_smul] using
    integral_mono hi (integrable_const B) h

private def debit (n : ℕ) (J D : ℝ) : ℝ :=
  if n = 0 then 0 else if n = 1 then J else D

private theorem card_active_le_sum (slabs : Finset ι) (n : ι → ℕ) :
    (slabs.filter fun i ↦ 0 < n i).card ≤ ∑ i ∈ slabs, n i := by
  rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  apply Finset.sum_le_sum
  intro i _
  split_ifs with hi
  · exact hi
  · exact Nat.zero_le _

private theorem sum_debit_eq_sum_active {slabs : Finset ι} {n : ι → ℕ} (J D : ι → ℝ)
    (h : ∀ i ∈ slabs, n i ≤ 1) :
    (∑ i ∈ slabs, debit (n i) (J i) (D i)) = ∑ i ∈ slabs.filter (fun i ↦ 0 < n i), J i := by
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i hi
  have hni := h i hi
  by_cases hzero : n i = 0
  · simp [debit, hzero]
  · have hone : n i = 1 := by omega
    simp [debit, hone]

private theorem sum_debit_mem_extraPriceRows (slabs : Finset ι) (n : ι → ℕ) (J D : ι → ℝ)
    (hbudget : (∑ i ∈ slabs, n i) ≤ 3) :
    (∑ i ∈ slabs, debit (n i) (J i) (D i)) ∈ extraPriceRows slabs J D := by
  classical
  apply mem_extraPriceRows.mpr
  by_cases h : ∀ i ∈ slabs, n i ≤ 1
  · rw [sum_debit_eq_sum_active J D h]
    exact .inl ⟨_, Finset.filter_subset _ _, (card_active_le_sum slabs n).trans hbudget, rfl⟩
  · push Not at h
    obtain ⟨i, hi, hni⟩ := h
    have hsum := Finset.sum_erase_add slabs n hi
    have hrest : (∑ j ∈ slabs.erase i, n j) ≤ 1 := by omega
    have hsmall (j : ι) (hj : j ∈ slabs.erase i) : n j ≤ 1 :=
      (Finset.single_le_sum (f := n) (fun k _ ↦ Nat.zero_le (n k)) hj).trans hrest
    rw [← Finset.sum_erase_add slabs (fun j ↦ debit (n j) (J j) (D j)) hi,
      sum_debit_eq_sum_active J D hsmall,
      show debit (n i) (J i) (D i) = D i by
        simp [debit, show n i ≠ 0 by omega, show n i ≠ 1 by omega]]
    let active := (slabs.erase i).filter fun j ↦ 0 < n j
    have hcard : active.card ≤ 1 := (card_active_le_sum (slabs.erase i) n).trans hrest
    change _ ∨ ∃ k ∈ slabs, (∑ j ∈ active, J j) + D i = D k ∨ _
    refine .inr ⟨i, hi, ?_⟩
    by_cases hzero : active.card = 0
    · left
      simp [Finset.card_eq_zero.mp hzero]
    · have hone : active.card = 1 := by omega
      obtain ⟨j, hj⟩ := Finset.card_eq_one.mp hone
      have hj' : j ∈ active := by simp [hj]
      obtain ⟨hne, hmem⟩ := Finset.mem_erase.mp (Finset.mem_filter.mp hj').1
      refine .inr ⟨j, hmem, hne, ?_⟩
      change D i + J j = (∑ k ∈ active, J k) + D i
      simp [hj, add_comm]

/-- At most three distinct supplied sites cost at most the largest legal extra
price above `fixed + ∑ i ∈ slabs, A i`. The atom, shared single-split, and
measurable-release inputs all refer to that same `A`. No sign assumptions are
needed: the empty single-split row and the release with no partner are included. -/
theorem refined_price_le (slabs : Finset ι) (left right : ι → ℝ) (sites : List ℝ)
    (hp : ∀ i ∈ slabs, left i < right i)
    (hdisj : (slabs : Set ι).PairwiseDisjoint fun i ↦ Ioo (left i) (right i))
    (hbudget : sites.toFinset.card ≤ 3) (p : ℝ → Primitive) (fixed : ℝ) (A J D : ι → ℝ)
    (hA : ∀ i ∈ slabs, ∀ u : Atom, (halfScore (p (left i)) (p (right i))).eval u ≤ A i)
    (hJ : ∀ i ∈ slabs, ∀ s ∈ Ioo (left i) (right i), ∀ νL νR : ProbabilityMeasure Atom,
      splitLawScore p (left i) (right i) s νL νR ≤ A i + J i)
    (hD : ∀ i ∈ slabs, ∀ knots : List ℝ,
      (left i :: (knots ++ [right i])).Pairwise (· < ·) →
      ∀ law : ℝ → ℝ → ProbabilityMeasure Atom,
        piecewiseLawScore p law (right i) (left i) knots ≤ A i + D i)
    (law : ι → ℝ → ℝ → ProbabilityMeasure Atom) :
    fixed + (∑ i ∈ slabs, refinedSlabScore p (law i) sites (left i) (right i)) ≤
      (fixed + ∑ i ∈ slabs, A i) + extraPrice slabs J D := by
  classical
  let n i := (interiorSites sites (left i) (right i)).card
  have htotal : (∑ i ∈ slabs, n i) ≤ 3 :=
    (sum_interiorSites_card_le slabs left right sites hdisj).trans hbudget
  have hlocal (i : ι) (hi : i ∈ slabs) :
      refinedSlabScore p (law i) sites (left i) (right i) ≤ A i + debit (n i) (J i) (D i) := by
    by_cases hzero : n i = 0
    · rw [refinedSlabScore_of_empty p (law i) (Finset.card_eq_zero.mp hzero)]
      simpa [debit, hzero] using
        mean_le_of_atom_le _ (law i (left i) (right i)) (A i) (hA i hi)
    · by_cases hone : n i = 1
      · obtain ⟨s, hs⟩ := Finset.card_eq_one.mp hone
        have hsin : s ∈ interiorSites sites (left i) (right i) := by simp [hs]
        rw [refinedSlabScore_of_singleton p (law i) hs]
        simpa [debit, hone] using
          hJ i hi s (Finset.mem_filter.mp hsin).2 (law i (left i) s) (law i s (right i))
      · simpa [debit, hzero, hone, refinedSlabScore] using
          hD i hi _ (slabKnots_ordered sites (hp i hi)) (law i)
  have hrow : (∑ i ∈ slabs, debit (n i) (J i) (D i)) ≤ extraPrice slabs J D :=
    Finset.le_sup' (f := id) (sum_debit_mem_extraPriceRows slabs n J D htotal)
  calc
    _ ≤ fixed + ∑ i ∈ slabs, (A i + debit (n i) (J i) (D i)) :=
      add_le_add_right (Finset.sum_le_sum hlocal) _
    _ = (fixed + ∑ i ∈ slabs, A i) + ∑ i ∈ slabs, debit (n i) (J i) (D i) := by
      rw [Finset.sum_add_distrib, add_assoc]
    _ ≤ _ := add_le_add_right hrow _

end

end Masullo.ThreeKnotPrice
