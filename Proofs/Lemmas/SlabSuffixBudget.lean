module

public import Mathlib.Data.Int.Basic
import Mathlib.Data.List.Basic

/-!
# Exact suffix budgets and tangent screening for integral slab edits

Source (at `85027edfee8ca3e2f0501950db1eb8c8c2ea4050`):
`.godel/bob/check-seven-knots-deletion-33.py:31–72` (`unpaid_patterns`, `screen`;
used at lines 87 and 102) and `.godel/bob/eight-piece-deletion-33.md:127–180`,
unchanged from `9af60873`
(route introduced in `f0f0e0d1`).
Owning check session: `01a20ec7-4115-7a16-8368-f5947df6f1f0`.

The input list is the order in which the first tangent visits the slab labels. The
Python dictionary supplies distinct labels; the sort key only chooses an order and
is not needed for the bound. The script's `choices` is a constant allowed list of
positive costs drawn from `{1, 2}`; we allow arbitrary positive integral costs and
lists that may vary by slab or be empty. Skips never appear in a pattern and cost
and score zero. The scores and the base are already rounded integers. The suffix
table is modeled by its entry recurrence; we do not formalize the Python caching,
the rounding enclosures, the encoding of real knots by edits, or any numerical
exclusion.
-/

@[expose] public section

namespace Masullo.SlabSuffixBudget

variable {ι : Type*}

/-- An edit is indexed by its positive integral cost. -/
abbrev Edit := {c : ℕ // 0 < c}

/-- Source order, listing only the edited slabs and their chosen costs. -/
abbrev Pattern (ι : Type*) := List (ι × Edit)

/-- Actual total charge of a pattern (no charge for omitted slabs). -/
def cost (p : Pattern ι) : ℕ := (p.map fun e ↦ e.2.val).sum

/-- Actual sum of the increments from one score table. -/
def score (s : ι → Edit → ℤ) (p : Pattern ι) : ℤ :=
  (p.map fun e ↦ s e.1 e.2).sum

/-- Feasibility independent of optimization and enumeration: the selected slab
labels form a sublist, each edit is allowed locally, and the total charge fits. -/
def Feasible (allowed : ι → List Edit) (slabs : List ι) (k : ℕ) (p : Pattern ι) : Prop :=
  (p.map Prod.fst).Sublist slabs ∧ (∀ e ∈ p, e.2 ∈ allowed e.1) ∧ cost p ≤ k

/-- The sublist condition gives at most one edit per distinct source slab. -/
theorem Feasible.nodup {allowed : ι → List Edit} {slabs : List ι} {k : ℕ} {p : Pattern ι}
    (hp : Feasible allowed slabs k p) (hs : slabs.Nodup) : (p.map Prod.fst).Nodup :=
  hp.1.nodup hs

/-- Skipping every slab always fits. -/
theorem feasible_nil (allowed : ι → List Edit) (slabs : List ι) (k : ℕ) :
    Feasible allowed slabs k [] := by
  simp [Feasible, cost]

/-- Skipping more slabs is allowed when a suffix (or any sublist) is enlarged. -/
theorem Feasible.of_sublist {allowed : ι → List Edit} {small large : List ι} {k : ℕ}
    {p : Pattern ι} (hp : Feasible allowed small k p) (h : small.Sublist large) :
    Feasible allowed large k p :=
  ⟨hp.1.trans h, hp.2⟩

/-- Exact skip-versus-affordable-edit decomposition. In the edit case the new
budget is the residual budget after paying the first charge. -/
theorem feasible_cons_iff {allowed : ι → List Edit} {t : ι} {ts : List ι} {k : ℕ}
    {p : Pattern ι} :
    Feasible allowed (t :: ts) k p ↔ Feasible allowed ts k p ∨
      ∃ c q, p = (t, c) :: q ∧ c ∈ allowed t ∧ c.val ≤ k ∧
        Feasible allowed ts (k - c.val) q := by
  constructor
  · rintro ⟨hs, ha, hk⟩
    rcases List.sublist_cons_iff.mp hs with hs | ⟨r, heq, htail⟩
    · exact Or.inl ⟨hs, ha, hk⟩
    · cases p with
      | nil => simp at heq
      | cons e q =>
        rcases e with ⟨u, c⟩
        change u :: q.map Prod.fst = t :: r at heq
        obtain ⟨hut, hqr⟩ := List.cons.inj heq
        subst u r
        change c.val + cost q ≤ k at hk
        exact Or.inr ⟨c, q, rfl, ha (t, c) List.mem_cons_self, by omega,
          htail, fun e he ↦ ha e (List.mem_cons_of_mem _ he), by omega⟩
  · rintro (hp | ⟨c, q, rfl, hc, hck, hq⟩)
    · exact hp.of_sublist ((List.Sublist.refl ts).cons t)
    · refine ⟨hq.1.cons_cons t, ?_, ?_⟩
      · intro e he
        rcases List.mem_cons.mp he with rfl | he
        · exact hc
        · exact hq.2.1 e he
      · have hqk := hq.2.2
        change c.val + cost q ≤ k
        omega

private theorem eq_nil_of_feasible_zero {allowed : ι → List Edit} {slabs : List ι}
    {p : Pattern ι} (hp : Feasible allowed slabs 0 p) : p = [] := by
  cases p with
  | nil => rfl
  | cons e q =>
    have h := hp.2.2
    change e.2.val + cost q ≤ 0 at h
    have := e.2.property
    omega

/-- Exact recurrence for a suffix-table entry: skip, or take an allowed edit
whose cost fits and use the residual-budget entry of the next row. -/
def suffixOpt (allowed : ι → List Edit) (s : ι → Edit → ℤ) : List ι → ℕ → ℤ
  | [], _ => 0
  | t :: ts, k =>
    let edits := (allowed t).filterMap fun c ↦
      if c.val ≤ k then some (s t c + suffixOpt allowed s ts (k - c.val)) else none
    (suffixOpt allowed s ts k :: edits).max (by simp)

/-- Every feasible pattern is bounded by the recurrence, and some feasible
pattern attains its value. The empty suffix and the skip branch are genuine
witnesses, including when no edit is affordable or scores are negative. -/
theorem suffixOpt_spec (allowed : ι → List Edit) (s : ι → Edit → ℤ)
    (slabs : List ι) (k : ℕ) :
    (∀ p, Feasible allowed slabs k p → score s p ≤ suffixOpt allowed s slabs k) ∧
      ∃ p, Feasible allowed slabs k p ∧ score s p = suffixOpt allowed s slabs k := by
  induction slabs generalizing k with
  | nil =>
    refine ⟨?_, ⟨[], feasible_nil allowed [] k, rfl⟩⟩
    intro p hp
    have := List.map_eq_nil_iff.mp (List.sublist_nil.mp hp.1)
    subst p
    exact Int.le_refl 0
  | cons t ts ih =>
    rw [suffixOpt]
    let skip := suffixOpt allowed s ts k
    let edit (c : Edit) := s t c + suffixOpt allowed s ts (k - c.val)
    let options := (allowed t).filterMap fun c ↦ if c.val ≤ k then some (edit c) else none
    change (∀ p, Feasible allowed (t :: ts) k p → score s p ≤ (skip :: options).max _) ∧
      ∃ p, Feasible allowed (t :: ts) k p ∧ score s p = (skip :: options).max _
    refine ⟨?_, ?_⟩
    · intro p hp
      rcases feasible_cons_iff.mp hp with hp | ⟨c, q, rfl, hc, hck, hq⟩
      · exact Int.le_trans ((ih k).1 p hp) (List.le_max_of_mem List.mem_cons_self)
      · have hm : edit c ∈ options := List.mem_filterMap.mpr ⟨c, hc, ite_eq_left hck⟩
        exact Int.le_trans (Int.add_le_add_left ((ih (k - c.val)).1 q hq) (s t c))
          (List.le_max_of_mem (List.mem_cons_of_mem _ hm))
    · rcases List.mem_cons.mp (List.max_mem (l := skip :: options) (by simp)) with hm | hm
      · obtain ⟨q, hq, hscore⟩ := (ih k).2
        exact ⟨q, feasible_cons_iff.mpr (Or.inl hq), hscore.trans hm.symm⟩
      · obtain ⟨c, hc, hm⟩ := List.mem_filterMap.mp hm
        split at hm
        next hck =>
          obtain ⟨q, hq, hscore⟩ := (ih (k - c.val)).2
          refine ⟨(t, c) :: q, feasible_cons_iff.mpr (Or.inr ⟨c, q, rfl, hc, hck, hq⟩), ?_⟩
          change s t c + score s q = _
          rw [hscore]
          exact (Option.some.inj hm)
        next => simp at hm

/-- With no remaining budget, the optimum is zero, even on a nonempty suffix. -/
theorem suffixOpt_zero (allowed : ι → List Edit) (s : ι → Edit → ℤ) (slabs : List ι) :
    suffixOpt allowed s slabs 0 = 0 := by
  obtain ⟨p, hp, hscore⟩ := (suffixOpt_spec allowed s slabs 0).2
  rw [eq_nil_of_feasible_zero hp] at hscore
  exact hscore.symm

/-- Starting further into the list cannot increase the optimum at the same
budget. No ordering assumption on scores or score-to-cost ratios is used. -/
theorem suffixOpt_le_of_sublist {allowed : ι → List Edit} {s : ι → Edit → ℤ}
    {small large : List ι} (h : small.Sublist large) (k : ℕ) :
    suffixOpt allowed s small k ≤ suffixOpt allowed s large k := by
  obtain ⟨p, hp, hs⟩ := (suffixOpt_spec allowed s small k).2
  rw [← hs]
  exact (suffixOpt_spec allowed s large k).1 p (hp.of_sublist h)

/-- If the current price plus the suffix bound is strictly below cutoff, no
feasible continuation reaches cutoff. Equality does not permit pruning. -/
theorem prune_prefix_cutoff {allowed : ι → List Edit} {s : ι → Edit → ℤ}
    {slabs : List ι} {k : ℕ} {value cutoff : ℤ}
    (h : value + suffixOpt allowed s slabs k < cutoff)
    {p : Pattern ι} (hp : Feasible allowed slabs k p) : value + score s p < cutoff :=
  Int.lt_of_le_of_lt (Int.add_le_add_left ((suffixOpt_spec allowed s slabs k).1 p hp) value) h

/-- The `break` at start index `j` excludes every feasible continuation from
*any* later start `j'`, not just branches whose first edit is at `j`. -/
theorem prune_later_start {allowed : ι → List Edit} {s : ι → Edit → ℤ}
    {slabs : List ι} {k j : ℕ} {value cutoff : ℤ}
    (h : value + suffixOpt allowed s (slabs.drop j) k < cutoff) :
    ∀ j' ≥ j, ∀ p, Feasible allowed (slabs.drop j') k p → value + score s p < cutoff := by
  intro j' hj p hp
  have hsub : (slabs.drop j').Sublist (slabs.drop j) := by
    have hdrop := List.drop_sublist (j' - j) (slabs.drop j)
    rwa [List.drop_drop, Nat.add_sub_of_le hj] at hdrop
  exact prune_prefix_cutoff h (hp.of_sublist hsub)

/-- A tangent has its own unsplit base and its own integral increments. -/
structure Tangent (ι : Type*) where
  base : ℤ
  increment : ι → Edit → ℤ

/-- Price a pattern on this tangent alone. -/
def Tangent.price (table : Tangent ι) (p : Pattern ι) : ℤ :=
  table.base + score table.increment p

/-- The running value for a prefix plus the continuation score is exactly the
price of the concatenated pattern, in the same tangent. -/
theorem Tangent.price_append (table : Tangent ι) (p q : Pattern ι) :
    table.price (p ++ q) = table.price p + score table.increment q := by
  simp [Tangent.price, score, List.sum_append, Int.add_assoc]

private def keepEmpty (cutoff value : ℤ) : List (Pattern ι) :=
  if cutoff ≤ value then [[]] else []

/-- The loop over first-edit sites of a nonempty continuation. Its right-hand
recursive call moves to the next possible start at the same budget and value;
the outer guard breaks the whole loop. Each edit branch first visits its empty
continuation, then runs the loop on the suffix after that edit. -/
private def prunedStarts (allowed : ι → List Edit) (s : ι → Edit → ℤ) (cutoff : ℤ) :
    List ι → ℕ → ℤ → List (Pattern ι)
  | [], _, _ => []
  | t :: ts, k, value =>
    if k = 0 ∨ value + suffixOpt allowed s (t :: ts) k < cutoff then []
    else
      ((allowed t).flatMap fun c ↦
        if c.val ≤ k then
          let v := value + s t c
          if cutoff ≤ v + suffixOpt allowed s ts (k - c.val) then
            (keepEmpty cutoff v ++ prunedStarts allowed s cutoff ts (k - c.val) v).map
              ((t, c) :: ·)
          else []
        else []) ++ prunedStarts allowed s cutoff ts k value

private theorem mem_keepEmpty_append_iff {allowed : ι → List Edit} {s : ι → Edit → ℤ}
    {slabs : List ι} {k : ℕ} {cutoff value : ℤ} {starts : List (Pattern ι)}
    (hstarts : ∀ p, p ∈ starts ↔ p ≠ [] ∧ Feasible allowed slabs k p ∧
      cutoff ≤ value + score s p) {p : Pattern ι} :
    p ∈ keepEmpty cutoff value ++ starts ↔
      Feasible allowed slabs k p ∧ cutoff ≤ value + score s p := by
  cases p <;> by_cases h : cutoff ≤ value <;>
    simp [keepEmpty, h, hstarts, feasible_nil, score]

private theorem mem_prunedStarts_iff (allowed : ι → List Edit) (s : ι → Edit → ℤ)
    (cutoff : ℤ) (slabs : List ι) (k : ℕ) (value : ℤ) (p : Pattern ι) :
    p ∈ prunedStarts allowed s cutoff slabs k value ↔
      p ≠ [] ∧ Feasible allowed slabs k p ∧ cutoff ≤ value + score s p := by
  induction slabs generalizing k value p with
  | nil =>
    simp only [prunedStarts, List.not_mem_nil, false_iff]
    exact fun ⟨hne, hp, _⟩ ↦ hne (List.map_eq_nil_iff.mp (List.sublist_nil.mp hp.1))
  | cons t ts ih =>
    by_cases hz : k = 0
    · subst k
      rw [prunedStarts, ite_eq_left (Or.inl rfl)]
      simp only [List.not_mem_nil, false_iff]
      exact fun ⟨hne, hp, _⟩ ↦ hne (eq_nil_of_feasible_zero hp)
    by_cases hb : value + suffixOpt allowed s (t :: ts) k < cutoff
    · rw [prunedStarts, ite_eq_left (Or.inr hb)]
      simp only [List.not_mem_nil, false_iff]
      exact fun ⟨_, hp, hcut⟩ ↦ Int.not_le_of_gt (prune_prefix_cutoff hb hp) hcut
    rw [prunedStarts, ite_eq_right (not_or.mpr ⟨hz, hb⟩)]
    simp only [List.mem_append, List.mem_flatMap, ih k value p]
    constructor
    · rintro (⟨c, hc, hbranch⟩ | ⟨hne, hp, hcut⟩)
      · split at hbranch
        next hck =>
          split at hbranch
          next =>
            obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hbranch
            obtain ⟨hqf, hqcut⟩ := (mem_keepEmpty_append_iff (ih _ _)).mp hq
            refine ⟨List.cons_ne_nil _ _, ?_, ?_⟩
            · exact feasible_cons_iff.mpr (Or.inr ⟨c, q, rfl, hc, hck, hqf⟩)
            · simpa only [score, List.map_cons, List.sum_cons, Int.add_assoc] using hqcut
          next => simp at hbranch
        next => simp at hbranch
      · exact ⟨hne, feasible_cons_iff.mpr (Or.inl hp), hcut⟩
    · rintro ⟨hne, hp, hcut⟩
      rcases feasible_cons_iff.mp hp with hp | ⟨c, q, rfl, hc, hck, hq⟩
      · exact Or.inr ⟨hne, hp, hcut⟩
      · have hqcut : cutoff ≤ (value + s t c) + score s q := by
          simpa only [score, List.map_cons, List.sum_cons, Int.add_assoc] using hcut
        have hbound := Int.le_trans hqcut
          (Int.add_le_add_left ((suffixOpt_spec allowed s ts _).1 q hq) (value + s t c))
        refine Or.inl ⟨c, hc, ?_⟩
        simp only [ite_eq_left hck, ite_eq_left hbound, List.mem_map]
        exact ⟨q, (mem_keepEmpty_append_iff (ih _ _)).mpr ⟨hq, hqcut⟩, rfl⟩

/-- The first tangent's cutoff enumerator. As in `visit`, the current pattern
(here the empty prefix at entry) is considered before the remaining edits. -/
@[no_expose] def unpaidPatterns (allowed : ι → List Edit) (table : Tangent ι) (cutoff : ℤ)
    (slabs : List ι) (k : ℕ) : List (Pattern ι) :=
  keepEmpty cutoff table.base ++ prunedStarts allowed table.increment cutoff slabs k table.base

/-- The pruned enumerator keeps exactly all feasible patterns at or above the
cutoff on the first tangent, including exact-budget and exact-cutoff ties.
This is a membership criterion, not an assertion about output order or multiplicity. -/
theorem mem_unpaidPatterns_iff {allowed : ι → List Edit} {table : Tangent ι} {cutoff : ℤ}
    {slabs : List ι} {k : ℕ} {p : Pattern ι} :
    p ∈ unpaidPatterns allowed table cutoff slabs k ↔
      Feasible allowed slabs k p ∧ cutoff ≤ table.price p :=
  mem_keepEmpty_append_iff (mem_prunedStarts_iff allowed table.increment cutoff slabs k table.base)

private def rescreen (cutoff : ℤ) : List (Pattern ι) → List (Tangent ι) → List (Pattern ι)
  | pending, [] => pending
  | pending, table :: tables =>
    rescreen cutoff (pending.filter fun p ↦ decide (cutoff ≤ table.price p)) tables

private theorem mem_rescreen_iff (cutoff : ℤ) (pending : List (Pattern ι))
    (tables : List (Tangent ι)) (p : Pattern ι) :
    p ∈ rescreen cutoff pending tables ↔ p ∈ pending ∧ ∀ t ∈ tables, cutoff ≤ t.price p := by
  induction tables generalizing pending with
  | nil => simp [rescreen]
  | cons t ts ih =>
    rw [rescreen, ih]
    simp only [List.mem_filter, decide_eq_true_eq, List.forall_mem_cons, and_assoc]

/-- Generate candidates on the first tangent, then successively re-filter the
same patterns on the supplied subsequent tables. All tables price the same slab
labels and allowed edit costs; `others` is the sequence actually visited after
the first table (the price entries processed by the source's `zip`). -/
@[no_expose] def screen (allowed : ι → List Edit) (first : Tangent ι) (others : List (Tangent ι))
    (cutoff : ℤ) (slabs : List ι) (k : ℕ) : List (Pattern ι) :=
  rescreen cutoff (unpaidPatterns allowed first cutoff slabs k) others

/-- Surviving `screen` means feasibility and passing every table separately:
there is no addition of prices across tangents. -/
theorem mem_screen_iff {allowed : ι → List Edit} {first : Tangent ι} {others : List (Tangent ι)}
    {cutoff : ℤ} {slabs : List ι} {k : ℕ} {p : Pattern ι} :
    p ∈ screen allowed first others cutoff slabs k ↔
      Feasible allowed slabs k p ∧ ∀ table ∈ first :: others, cutoff ≤ table.price p := by
  simp only [screen, mem_rescreen_iff, mem_unpaidPatterns_iff, List.forall_mem_cons, and_assoc]

end Masullo.SlabSuffixBudget
