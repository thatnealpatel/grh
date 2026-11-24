module

public import Lemmas.CrossedDirectionCover
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Order.Hom.Set

/-!
# The crossed split menu, counted by radical

Source: `b6920957:.godel/alice/crossed-gap-filters.md:24`, step 3, before scalar
recovery. This is the finite count on the actual eligible split menu: the
parameters `eligible`, `X`, `K`, and `V` retain their meaning in
`CrossedDirectionCover.admissibleSplits`. With `V > 1` and a total prime
multiplicity bound `E` on a fiber, each prime in the radical has a side and a
positive exponent. The exponents, in increasing prime order, give a subset of
`{1, …, E}` by taking partial sums. The count sums over the radicals that
actually occur. If `V ≤ 1`, the menu is already `{(1, 1)}`. There is no
asymptotic estimate or count for scalar recovery here.

Owning check session: `01a20b48-5cad-74c3-865b-b625005166b3`.
-/

namespace CrossedSplitCount

open CrossedDirectionCover UniqueFactorizationMonoid

/-- The actual admissible splits whose product has radical `r`. -/
@[expose] public noncomputable def radicalFiber (eligible : ℕ → Prop) (X K V : ℝ) (r : ℕ) :
    Finset (ℕ × ℕ) :=
  (admissibleSplits eligible X K V).filter fun b => radical (b.1 * b.2) = r

/-- The radicals of products of actual admissible splits. -/
@[expose] public noncomputable def radicalMenu (eligible : ℕ → Prop) (X K V : ℝ) : Finset ℕ :=
  (admissibleSplits eligible X K V).image fun b => radical (b.1 * b.2)

/-- Sum of the entries strictly before the natural index `j`. -/
private def partialSum {k : ℕ} (a : Fin k → ℕ) (j : ℕ) : ℕ :=
  ∑ i ∈ Finset.univ.filter (fun i : Fin k => i.val < j), a i

private theorem partialSum_succ {k : ℕ} (a : Fin k → ℕ) (i : Fin k) :
    partialSum a (i.val + 1) = a i + partialSum a i.val := by
  have hs : Finset.univ.filter (fun j : Fin k => j.val < i.val + 1) =
      insert i (Finset.univ.filter fun j : Fin k => j.val < i.val) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, ← Fin.val_inj]
    omega
  unfold partialSum
  rw [hs, Finset.sum_insert]
  simp

private theorem partialSum_mono {k : ℕ} (a : Fin k → ℕ) : Monotone (partialSum a) := by
  intro i j hij
  apply Finset.sum_le_sum_of_subset
  intro t ht
  obtain ⟨htU, htI⟩ := Finset.mem_filter.mp ht
  exact Finset.mem_filter.mpr ⟨htU, htI.trans_le hij⟩

private theorem partialSum_strict {k : ℕ} {a : Fin k → ℕ} (ha : ∀ i, 0 < a i) :
    StrictMono (fun i : Fin k => partialSum a (i.val + 1)) := by
  intro i j hij
  have h := partialSum_mono a (show i.val + 1 ≤ j.val from hij)
  change partialSum a (i.val + 1) < partialSum a (j.val + 1)
  rw [partialSum_succ a j]
  have := ha j
  omega

private def cuts {k : ℕ} (a : Fin k → ℕ) : Finset ℕ :=
  Finset.univ.image fun i : Fin k => partialSum a (i.val + 1)

-- This also covers `k = 0`: the image of `Fin 0` is the empty set of cuts.
private theorem cuts_mem {k E : ℕ} {a : Fin k → ℕ} (ha : ∀ i, 0 < a i)
    (hE : ∑ i, a i ≤ E) : cuts a ∈ (Finset.Icc 1 E).powersetCard k := by
  apply Finset.mem_powersetCard.mpr
  constructor
  · intro t ht
    unfold cuts at ht
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ht
    refine Finset.mem_Icc.mpr ⟨?_, ?_⟩
    · rw [partialSum_succ]
      have := ha i
      omega
    · unfold partialSum
      exact (Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)).trans hE
  · rw [cuts, Finset.card_image_of_injective _ (partialSum_strict ha).injective,
      Finset.card_univ, Fintype.card_fin]

private theorem eq_of_cuts_eq {k : ℕ} {a b : Fin k → ℕ} (ha : ∀ i, 0 < a i)
    (hb : ∀ i, 0 < b i) (h : cuts a = cuts b) : a = b := by
  have hrange (v : Fin k → ℕ) : Set.range (fun i : Fin k => partialSum v (i.val + 1)) =
      (cuts v : Set ℕ) := by
    ext t
    simp [cuts]
  -- The unordered set of cuts determines their increasing enumeration.
  have he := (partialSum_strict ha).eq_of_range_eq (partialSum_strict hb)
    (by rw [hrange, hrange, h])
  funext i
  have hnext := congrFun he i
  change partialSum a (i.val + 1) = partialSum b (i.val + 1) at hnext
  rw [partialSum_succ, partialSum_succ] at hnext
  have hprev : partialSum a i.val = partialSum b i.val := by
    by_cases hi : i.val = 0
    · simp [hi, partialSum]
    · let j : Fin k := ⟨i.val - 1, by have := i.isLt; omega⟩
      have hj : j.val + 1 = i.val := by dsimp [j]; omega
      simpa only [hj] using congrFun he j
  omega

/-- The usual total prime multiplicity is the sum of exponents over the support. -/
private theorem sum_factorization (n : ℕ) :
    ∑ p ∈ n.primeFactors, n.factorization p = n.primeFactorsList.length := by
  rw [← Multiset.coe_card]
  simpa only [Multiset.coe_count, Nat.primeFactorsList_count_eq] using
    Multiset.sum_count_eq_card (s := n.primeFactors) (m := (n.primeFactorsList : Multiset ℕ))
      (fun p hp => List.mem_toFinset.mpr (Multiset.mem_coe.mp hp))

private theorem factorization_zero_of_coprime {a b : ℕ} (h : a.Coprime b) (p : ℕ) :
    a.factorization p = 0 ∨ b.factorization p = 0 := by
  by_cases hp : p.Prime
  · by_cases ha : p ∣ a
    · right
      apply Nat.factorization_eq_zero_of_not_dvd
      intro hb
      exact hp.not_dvd_one (h.gcd_eq_one ▸ Nat.dvd_gcd ha hb)
    · exact Or.inl (Nat.factorization_eq_zero_of_not_dvd ha)
  · exact Or.inl ((Nat.factorization_eq_zero_iff a p).mpr (Or.inl hp))

/-- One side bit and the total exponent at each support prime determine both factors. -/
private theorem eq_of_split_data {a b : ℕ × ℕ} {s : Finset ℕ}
    (ha₁ : a.1 ≠ 0) (ha₂ : a.2 ≠ 0) (hb₁ : b.1 ≠ 0) (hb₂ : b.2 ≠ 0)
    (ha : a.1.Coprime a.2) (hb : b.1.Coprime b.2)
    (hsa : (a.1 * a.2).primeFactors = s) (hsb : (b.1 * b.2).primeFactors = s)
    (he : ∀ p ∈ s, (a.1 * a.2).factorization p = (b.1 * b.2).factorization p)
    (hs : ∀ p ∈ s, decide (a.1.factorization p = 0) = decide (b.1.factorization p = 0)) :
    a = b := by
  have h (p : ℕ) : a.1.factorization p = b.1.factorization p ∧
      a.2.factorization p = b.2.factorization p := by
    by_cases hp : p ∈ s
    · have he' := he p hp
      simp only [Nat.factorization_mul ha₁ ha₂, Nat.factorization_mul hb₁ hb₂,
        Finsupp.add_apply] at he'
      have hs' : a.1.factorization p = 0 ↔ b.1.factorization p = 0 :=
        decide_eq_decide.mp (hs p hp)
      by_cases hpa : a.1.factorization p = 0
      · have hpb := hs'.mp hpa
        constructor <;> omega
      · have hpa' := (factorization_zero_of_coprime ha p).resolve_left hpa
        have hpb' := (factorization_zero_of_coprime hb p).resolve_left (hpa ∘ hs'.mpr)
        constructor <;> omega
    · have hza : (a.1 * a.2).factorization p = 0 := Finsupp.notMem_support_iff.mp (by
        simpa only [Nat.support_factorization, hsa] using hp)
      have hzb : (b.1 * b.2).factorization p = 0 := Finsupp.notMem_support_iff.mp (by
        simpa only [Nat.support_factorization, hsb] using hp)
      rw [Nat.factorization_mul ha₁ ha₂, Finsupp.add_apply] at hza
      rw [Nat.factorization_mul hb₁ hb₂, Finsupp.add_apply] at hzb
      constructor <;> omega
  exact Prod.ext (Nat.eq_of_factorization_eq ha₁ hb₁ fun p => (h p).1)
    (Nat.eq_of_factorization_eq ha₂ hb₂ fun p => (h p).2)

/-- At a fixed radical `r`, write `ω(r) = r.primeFactors.card`. If every product
in the fiber has at most `E` prime factors with multiplicity, the fiber has at
most `2^ω(r) * choose E ω(r)` admissible ordered splits. -/
public theorem card_radicalFiber_le {eligible : ℕ → Prop} {X K V : ℝ} {r E : ℕ}
    (hX : 1 < X) (hV : 1 < V)
    (hE : ∀ b ∈ radicalFiber eligible X K V r, (b.1 * b.2).primeFactorsList.length ≤ E) :
    (radicalFiber eligible X K V r).card ≤
      2 ^ r.primeFactors.card * Nat.choose E r.primeFactors.card := by
  classical
  let F := radicalFiber eligible X K V r
  let k := r.primeFactors.card
  let e := r.primeFactors.orderIsoOfFin (k := k) rfl
  let prime (i : Fin k) : ℕ := (e i).val
  have hsplit (b : F) : b.val.1 ≠ 0 ∧ b.val.2 ≠ 0 ∧ b.val.1.Coprime b.val.2 := by
    have hb := (mem_admissibleSplits hX).mp (Finset.mem_filter.mp b.property).1
    rw [ite_eq_left hV] at hb
    exact ⟨hb.1.ne', hb.2.1.ne', hb.2.2.1⟩
  have hsupport (b : F) : (b.val.1 * b.val.2).primeFactors = r.primeFactors := by
    rw [← Nat.primeFactors_radical, (Finset.mem_filter.mp b.property).2]
  let exp (b : F) (i : Fin k) : ℕ := (b.val.1 * b.val.2).factorization (prime i)
  -- The bit is true exactly when the prime is assigned to the second factor.
  let side (b : F) (i : Fin k) : Bool := decide (b.val.1.factorization (prime i) = 0)
  have hpos (b : F) (i : Fin k) : 0 < exp b i := by
    have hi : prime i ∈ (b.val.1 * b.val.2).primeFactors := (hsupport b).symm ▸ (e i).property
    obtain ⟨hp, hd, hn⟩ := Nat.mem_primeFactors.mp hi
    exact hp.factorization_pos_of_dvd hn hd
  have hsum (b : F) : ∑ i, exp b i ≤ E := by
    let f (p : ℕ) := (b.val.1 * b.val.2).factorization p
    calc
      ∑ i, exp b i = ∑ p : r.primeFactors, f p.val := e.toEquiv.sum_comp (fun p => f p.val)
      _ = ∑ p ∈ r.primeFactors, f p := Finset.sum_coe_sort _ _
      _ = (b.val.1 * b.val.2).primeFactorsList.length := by
        rw [← hsupport b]
        exact sum_factorization _
      _ ≤ E := hE b.val b.property
  let code (b : F) : (Fin k → Bool) × ↥((Finset.Icc 1 E).powersetCard k) :=
    (side b, ⟨cuts (exp b), cuts_mem (hpos b) (hsum b)⟩)
  have hinj : Function.Injective code := by
    intro a b h
    have he : exp a = exp b := eq_of_cuts_eq (hpos a) (hpos b)
      (congrArg (fun c => c.2.val) h)
    have hs : side a = side b := congrArg Prod.fst h
    obtain ⟨ha₁, ha₂, ha⟩ := hsplit a
    obtain ⟨hb₁, hb₂, hb⟩ := hsplit b
    apply Subtype.ext
    apply eq_of_split_data ha₁ ha₂ hb₁ hb₂ ha hb (hsupport a) (hsupport b)
    · intro p hp
      obtain ⟨i, hi⟩ := e.surjective ⟨p, hp⟩
      have hpi : prime i = p := congrArg Subtype.val hi
      simpa only [exp, hpi] using congrFun he i
    · intro p hp
      obtain ⟨i, hi⟩ := e.surjective ⟨p, hp⟩
      have hpi : prime i = p := congrArg Subtype.val hi
      simpa only [side, hpi] using congrFun hs i
  have hcard := Fintype.card_le_of_injective code hinj
  rw [Fintype.card_prod, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin,
    Fintype.card_coe, Fintype.card_coe, Finset.card_powersetCard, Nat.card_Icc,
    Nat.add_sub_cancel] at hcard
  exact hcard

/-- Sum the fiber bounds over the radicals actually present in the large-`V`
menu. In the small-`V` branch the menu is exactly the singleton `(1, 1)`,
independently of the prime multiplicity budget. -/
public theorem card_admissibleSplits_le {eligible : ℕ → Prop} {X K V : ℝ} {E : ℕ}
    (hX : 1 < X)
    (hE : 1 < V → ∀ b ∈ admissibleSplits eligible X K V, (b.1 * b.2).primeFactorsList.length ≤ E) :
    (admissibleSplits eligible X K V).card ≤
      if 1 < V then
        ∑ r ∈ radicalMenu eligible X K V, 2 ^ r.primeFactors.card * Nat.choose E r.primeFactors.card
      else 1 := by
  classical
  by_cases hV : 1 < V
  · rw [ite_eq_left hV]
    let M := admissibleSplits eligible X K V
    let R := radicalMenu eligible X K V
    let F := radicalFiber eligible X K V
    have hcover : R.biUnion F = M := by
      ext b
      constructor
      · intro hb
        obtain ⟨r, _, hr⟩ := Finset.mem_biUnion.mp hb
        exact (Finset.mem_filter.mp hr).1
      · intro hb
        exact Finset.mem_biUnion.mpr ⟨radical (b.1 * b.2),
          Finset.mem_image.mpr ⟨b, hb, rfl⟩, Finset.mem_filter.mpr ⟨hb, rfl⟩⟩
    have hdisj : (R : Set ℕ).PairwiseDisjoint F := by
      intro r _ s _ hrs
      apply Finset.disjoint_left.mpr
      intro b hr hs
      exact hrs ((Finset.mem_filter.mp hr).2.symm.trans (Finset.mem_filter.mp hs).2)
    calc
      M.card = ∑ r ∈ R, (F r).card := hcover ▸ Finset.card_biUnion hdisj
      _ ≤ ∑ r ∈ R, 2 ^ r.primeFactors.card * Nat.choose E r.primeFactors.card :=
        Finset.sum_le_sum fun r _ => card_radicalFiber_le hX hV
          (fun b hb => hE hV b (Finset.mem_filter.mp hb).1)
  · have hsingleton : admissibleSplits eligible X K V = {(1, 1)} := by
      ext b
      rw [mem_admissibleSplits hX, ite_eq_right hV, Finset.mem_singleton]
    simp [hV, hsingleton]

end CrossedSplitCount
