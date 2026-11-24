module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.Data.Finset.Sort
public import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Order.Prod.Lex.Basic
import Mathlib.Data.Nat.Find
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The ordered full-power crossing for ordinary ratio labels

Source: `cab410b8:.godel/alice/ordinary-outside-radical.md:7–19`, retained as a
separate label price in `35960cb0:.godel/alice/two-ratio-radical.md:20`.
For a fixed inside pool `P`, sort the outside primes of `N*M` by decreasing
multiplicity, then by increasing prime. When `1 ≤ U` and the full outside
product exceeds `U`, stop at the first **full prime power** making the product
strictly greater than `U`. The radical price charges only the logarithm of the
crossing prime on top of the weighted prefix bound. The label records the
numerator and denominator parts separately, both inside `P` and at the stop.
For `U < 1` there is no crossing or outside label. We take the uniform
normalized determinant bound and the crossing availability as inputs; the
asymptotic width, dyadic bins, and Rankin count are not formalized here.

Owning check session: `01a20d17-2b2a-7097-a6d0-937638b43d97`.
-/

namespace OrderedRadicalCrossing

/-- The part of `n` supported on `S`, with each selected prime's full multiplicity. -/
@[expose] public def primePart (S : Finset ℕ) (n : ℕ) : ℕ :=
  ∏ p ∈ S, p ^ n.factorization p

/-- The outside support for the fixed inside pool `P`. -/
@[expose] public def outsidePrimes (P : Finset ℕ) (n : ℕ) : Finset ℕ :=
  n.primeFactors \ P

private def sortKey (n : ℕ) : ℕ ↪ (ℕᵒᵈ ×ₗ ℕ) where
  toFun p := toLex (OrderDual.toDual (n.factorization p), p)
  inj' := by
    intro p r h
    exact congrArg (fun k : ℕᵒᵈ ×ₗ ℕ ↦ (ofLex k).2) h

private def sortedKeys (P : Finset ℕ) (n : ℕ) : List (ℕᵒᵈ ×ₗ ℕ) :=
  ((outsidePrimes P n).map (sortKey n)).sort

/-- The outside primes in decreasing multiplicity, breaking ties by increasing prime. -/
public def orderedOutside (P : Finset ℕ) (n : ℕ) : List ℕ :=
  (sortedKeys P n).map fun k ↦ (ofLex k).2

private theorem mem_sortedKeys {P : Finset ℕ} {n : ℕ} {k : ℕᵒᵈ ×ₗ ℕ} :
    k ∈ sortedKeys P n ↔ ∃ p ∈ outsidePrimes P n, sortKey n p = k := by
  rw [sortedKeys, Finset.mem_sort, Finset.mem_map]

private theorem orderedOutside_toFinset (P : Finset ℕ) (n : ℕ) :
    (orderedOutside P n).toFinset = outsidePrimes P n := by
  ext p
  rw [List.mem_toFinset, orderedOutside, List.mem_map]
  constructor
  · rintro ⟨k, hk, rfl⟩
    obtain ⟨a, ha, rfl⟩ := mem_sortedKeys.mp hk
    exact ha
  · intro hp
    exact ⟨sortKey n p, mem_sortedKeys.mpr ⟨p, hp, rfl⟩, rfl⟩

private theorem orderedOutside_nodup (P : Finset ℕ) (n : ℕ) :
    (orderedOutside P n).Nodup := by
  apply List.Nodup.map_on _ (Finset.sort_nodup _ _)
  intro x hx y hy hxy
  obtain ⟨p, _, rfl⟩ := mem_sortedKeys.mp hx
  obtain ⟨p', _, rfl⟩ := mem_sortedKeys.mp hy
  exact congrArg (sortKey n) (show p = p' from hxy)

private theorem orderedOutside_pairwise (P : Finset ℕ) (n : ℕ) :
    (orderedOutside P n).Pairwise (fun p r ↦
      n.factorization r < n.factorization p ∨
      n.factorization p = n.factorization r ∧ p ≤ r) := by
  rw [orderedOutside, List.pairwise_map]
  refine (Finset.pairwise_sort _ _).imp_of_mem ?_
  intro x y hx hy hxy
  obtain ⟨p, _, rfl⟩ := mem_sortedKeys.mp hx
  obtain ⟨r, _, rfl⟩ := mem_sortedKeys.mp hy
  exact Prod.Lex.le_iff.mp hxy

/-- The sorted list contains the actual outside support, without repetition, in the
specified multiplicity order. -/
public theorem orderedOutside_spec (P : Finset ℕ) (n : ℕ) :
    (orderedOutside P n).toFinset = outsidePrimes P n ∧ (orderedOutside P n).Nodup ∧
      (orderedOutside P n).Pairwise (fun p r ↦ n.factorization r < n.factorization p ∨
        n.factorization p = n.factorization r ∧ p ≤ r) :=
  ⟨orderedOutside_toFinset P n, orderedOutside_nodup P n, orderedOutside_pairwise P n⟩

/-- The primes in the first `k` entries of the ordered outside support. -/
@[expose] public def prefixPrimes (P : Finset ℕ) (n k : ℕ) : Finset ℕ :=
  ((orderedOutside P n).take k).toFinset

private theorem prefix_subset (P : Finset ℕ) (n k : ℕ) :
    prefixPrimes P n k ⊆ outsidePrimes P n := by
  rw [← orderedOutside_toFinset]
  exact fun _ hp ↦ List.mem_toFinset.mpr (List.mem_of_mem_take (List.mem_toFinset.mp hp))

private theorem part_ne_zero {S : Finset ℕ} {n : ℕ} (hS : S ⊆ n.primeFactors) :
    primePart S n ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun _ hp ↦
    pow_ne_zero _ (Nat.prime_of_mem_primeFactors (hS hp)).ne_zero

private theorem primeFactors_part {S : Finset ℕ} {n : ℕ} (hS : S ⊆ n.primeFactors) :
    (primePart S n).primeFactors = S := by
  induction S using Finset.induction_on with
  | empty => simp [primePart]
  | @insert p T hpT ih =>
    have hp := hS (Finset.mem_insert_self p T)
    have hT : T ⊆ n.primeFactors := fun _ hr ↦ hS (Finset.mem_insert_of_mem hr)
    have hep : n.factorization p ≠ 0 :=
      Finsupp.mem_support_iff.mp (by rwa [Nat.support_factorization])
    have hprime := Nat.prime_of_mem_primeFactors hp
    rw [primePart, Finset.prod_insert hpT]
    change (p ^ n.factorization p * primePart T n).primeFactors = insert p T
    rw [Nat.primeFactors_mul (pow_ne_zero _ hprime.ne_zero) (part_ne_zero hT),
      Nat.primeFactors_prime_pow hep hprime, ih hT, Finset.singleton_union]

private theorem part_dvd {S : Finset ℕ} {n : ℕ} (hn : n ≠ 0) : primePart S n ∣ n := by
  have hfull : primePart n.primeFactors n = n := by
    simpa only [primePart, Finsupp.prod, Nat.support_factorization] using
      Nat.prod_factorization_pow_eq_self hn
  have hinter : primePart (S ∩ n.primeFactors) n = primePart S n := by
    apply Finset.prod_subset Finset.inter_subset_left
    intro p hp hpn
    have h : p ∉ n.primeFactors := fun hm ↦ hpn (Finset.mem_inter.mpr ⟨hp, hm⟩)
    have hzero : n.factorization p = 0 :=
      Finsupp.notMem_support_iff.mp (by rwa [Nat.support_factorization])
    rw [hzero, pow_zero]
  calc
    primePart S n = primePart (S ∩ n.primeFactors) n := hinter.symm
    _ ∣ primePart n.primeFactors n :=
      Finset.prod_dvd_prod_of_subset _ _ (fun p ↦ p ^ n.factorization p) Finset.inter_subset_right
    _ = n := hfull

private theorem part_mul (S : Finset ℕ) {N M : ℕ} (hN : N ≠ 0) (hM : M ≠ 0) :
    primePart S (N * M) = primePart S N * primePart S M := by
  simp only [primePart, Nat.factorization_mul hN hM, Finsupp.add_apply, pow_add,
    Finset.prod_mul_distrib]

/-- The least crossing length in the available crossing branch, and zero when
`U < 1` or the whole outside product cannot cross. -/
public noncomputable def stopIndex (P : Finset ℕ) (n : ℕ) (U : ℝ) : ℕ := by
  classical
  exact if h : 1 ≤ U ∧ ∃ k, k ≤ (orderedOutside P n).length ∧
      U < (primePart (prefixPrimes P n k) n : ℝ) then Nat.find h.2 else 0

/-- The primes whose full powers are disclosed at the stop (empty for `U < 1`). -/
@[expose] public noncomputable def stoppedPrimes (P : Finset ℕ) (n : ℕ) (U : ℝ) : Finset ℕ :=
  prefixPrimes P n (stopIndex P n U)

private theorem stopIndex_spec {P : Finset ℕ} {n : ℕ} {U : ℝ} (hU : 1 ≤ U)
    (havailable : U < (primePart (outsidePrimes P n) n : ℝ)) :
    stopIndex P n U ≤ (orderedOutside P n).length ∧
      U < (primePart (stoppedPrimes P n U) n : ℝ) ∧
      ∀ j < stopIndex P n U, (primePart (prefixPrimes P n j) n : ℝ) ≤ U := by
  classical
  have hex : ∃ k, k ≤ (orderedOutside P n).length ∧
      U < (primePart (prefixPrimes P n k) n : ℝ) :=
    ⟨_, le_rfl, by simpa only [prefixPrimes, List.take_length, orderedOutside_toFinset]⟩
  have hf := Nat.find_spec hex
  simp only [stoppedPrimes, stopIndex, dite_eq_left (And.intro hU hex)]
  exact ⟨hf.1, hf.2, fun j hj ↦ le_of_not_gt fun h ↦
    Nat.find_min hex hj ⟨(Nat.le_of_lt hj).trans hf.1, h⟩⟩

/-- A subunit threshold does not disclose a crossing power. -/
public theorem stoppedPrimes_of_lt_one {P : Finset ℕ} {n : ℕ} {U : ℝ} (hU : U < 1) :
    stoppedPrimes P n U = ∅ := by
  classical
  simp [stoppedPrimes, stopIndex, hU.not_ge, prefixPrimes]

open UniqueFactorizationMonoid

private theorem log_radical_part {S : Finset ℕ} {n : ℕ} (hS : S ⊆ n.primeFactors) :
    Real.log ((radical (primePart S n) : ℕ) : ℝ) = ∑ p ∈ S, Real.log (p : ℝ) := by
  rw [Nat.radical_eq_prod_primeFactors, primeFactors_part hS, Nat.cast_prod, Real.log_prod]
  exact fun _ hp ↦ Nat.cast_ne_zero.mpr (Nat.prime_of_mem_primeFactors (hS hp)).ne_zero

private theorem log_part {S : Finset ℕ} {n : ℕ} (hS : S ⊆ n.primeFactors) :
    Real.log (primePart S n : ℝ) = ∑ p ∈ S, (n.factorization p : ℝ) * Real.log (p : ℝ) := by
  simp only [primePart, Nat.cast_prod, Nat.cast_pow]
  rw [Real.log_prod]
  · simp only [Real.log_pow]
  · exact fun _ hp ↦ pow_ne_zero _
      (Nat.cast_ne_zero.mpr (Nat.prime_of_mem_primeFactors (hS hp)).ne_zero)

-- Cross-multiply the prefix/suffix comparison, so an empty prefix needs no division.
private theorem weighted_prefix (A B : Finset ℕ) (e : ℕ → ℕ)
    (horder : ∀ a ∈ A, ∀ b ∈ B, e b ≤ e a) :
    (∑ a ∈ A, Real.log (a : ℝ)) * (∑ b ∈ B, (e b : ℝ) * Real.log (b : ℝ)) ≤
      (∑ a ∈ A, (e a : ℝ) * Real.log (a : ℝ)) * (∑ b ∈ B, Real.log (b : ℝ)) := by
  rw [Finset.sum_mul_sum, Finset.sum_mul_sum]
  refine Finset.sum_le_sum fun a ha ↦ Finset.sum_le_sum fun b hb ↦ ?_
  have he : (e b : ℝ) ≤ e a := by exact_mod_cast horder a ha b hb
  calc
    Real.log (a : ℝ) * ((e b : ℝ) * Real.log (b : ℝ)) =
        (Real.log (a : ℝ) * Real.log (b : ℝ)) * (e b : ℝ) := by ring
    _ ≤ (Real.log (a : ℝ) * Real.log (b : ℝ)) * (e a : ℝ) :=
      mul_le_mul_of_nonneg_left he
        (mul_nonneg (Real.log_natCast_nonneg a) (Real.log_natCast_nonneg b))
    _ = ((e a : ℝ) * Real.log (a : ℝ)) * Real.log (b : ℝ) := by ring

private theorem prefix_log_le {P : Finset ℕ} {n k : ℕ} {U : ℝ} (hU : 1 ≤ U)
    (havailable : U < (primePart (outsidePrimes P n) n : ℝ))
    (hpre : (primePart (prefixPrimes P n k) n : ℝ) ≤ U) :
    Real.log ((radical (primePart (prefixPrimes P n k) n) : ℕ) : ℝ) ≤
      (Real.log ((radical (primePart (outsidePrimes P n) n) : ℕ) : ℝ) /
        Real.log (primePart (outsidePrimes P n) n : ℝ)) * Real.log U := by
  let L := orderedOutside P n
  let A := prefixPrimes P n k
  let B := (L.drop k).toFinset
  have hsplit : L.take k ++ L.drop k = L := List.take_append_drop k L
  have hAB : A ∪ B = outsidePrimes P n := by
    change (L.take k).toFinset ∪ (L.drop k).toFinset = _
    rw [← List.toFinset_append, hsplit]
    exact orderedOutside_toFinset P n
  have hdisj : Disjoint A B := by
    have hn : L.Nodup := orderedOutside_nodup P n
    rw [← hsplit, List.nodup_append] at hn
    exact Finset.disjoint_left.mpr fun a ha hb ↦
      hn.2.2 a (List.mem_toFinset.mp ha) a (List.mem_toFinset.mp hb) rfl
  have horder : ∀ a ∈ A, ∀ b ∈ B, n.factorization b ≤ n.factorization a := by
    have hL := orderedOutside_pairwise P n
    change L.Pairwise _ at hL
    rw [← hsplit, List.pairwise_append] at hL
    intro a ha b hb
    exact (hL.2.2 a (List.mem_toFinset.mp ha) b (List.mem_toFinset.mp hb)).elim
      Nat.le_of_lt (fun h ↦ h.1.ge)
  have hA : A ⊆ n.primeFactors := (prefix_subset P n k).trans Finset.sdiff_subset
  have hO : outsidePrimes P n ⊆ n.primeFactors := Finset.sdiff_subset
  have htotal := Real.log_pos (hU.trans_lt havailable)
  have hprefix : Real.log (primePart A n : ℝ) ≤ Real.log U :=
    Real.log_le_log (Nat.cast_pos.mpr (Nat.pos_of_ne_zero (part_ne_zero hA))) hpre
  have hratio : 0 ≤ Real.log ((radical (primePart (outsidePrimes P n) n) : ℕ) : ℝ) /
      Real.log (primePart (outsidePrimes P n) n : ℝ) :=
    div_nonneg (Real.log_natCast_nonneg _) htotal.le
  change _ ≤ _ * Real.log U
  calc
    Real.log ((radical (primePart A n) : ℕ) : ℝ) ≤
        (Real.log ((radical (primePart (outsidePrimes P n) n) : ℕ) : ℝ) /
          Real.log (primePart (outsidePrimes P n) n : ℝ)) * Real.log (primePart A n : ℝ) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ htotal, log_radical_part hA, log_radical_part hO,
        log_part hA, log_part hO, ← hAB, Finset.sum_union hdisj, Finset.sum_union hdisj]
      nlinarith only [weighted_prefix A B n.factorization horder]
    _ ≤ _ := mul_le_mul_of_nonneg_left hprefix hratio

private theorem prefix_succ {P : Finset ℕ} {n i : ℕ} (hi : i < (orderedOutside P n).length) :
    prefixPrimes P n (i + 1) = insert (orderedOutside P n)[i] (prefixPrimes P n i) ∧
      (orderedOutside P n)[i] ∉ prefixPrimes P n i := by
  have ht : (orderedOutside P n).take (i + 1) =
      (orderedOutside P n).take i ++ [(orderedOutside P n)[i]] := by
    rw [List.take_add_one, List.getElem?_eq_getElem hi]
    rfl
  have hn := (List.take_sublist (i + 1) (orderedOutside P n)).nodup (orderedOutside_nodup P n)
  rw [ht, List.nodup_append] at hn
  refine ⟨?_, fun hm ↦ hn.2.2 _ (List.mem_toFinset.mp hm) _ (by simp) rfl⟩
  simp only [prefixPrimes, ht, List.toFinset_append, List.toFinset_cons, List.toFinset_nil,
    Finset.insert_empty, Finset.union_singleton]

/-- The actual first full-power crossing, with its immediate predecessor and
crossing prime. Earlier products may equal `U`; only a strict excess stops the
prefix. The additive loss in the log radical is one log prime, not a log power. -/
public theorem first_crossing {P : Finset ℕ} {n : ℕ} {U : ℝ} (hU : 1 ≤ U)
    (havailable : U < (primePart (outsidePrimes P n) n : ℝ)) :
    ∃ i : Fin (orderedOutside P n).length,
      stopIndex P n U = i.val + 1 ∧
      stoppedPrimes P n U = insert (orderedOutside P n)[i.val] (prefixPrimes P n i.val) ∧
      (∀ j < stopIndex P n U, (primePart (prefixPrimes P n j) n : ℝ) ≤ U) ∧
      U < (primePart (stoppedPrimes P n U) n : ℝ) ∧
      Real.log ((radical (primePart (stoppedPrimes P n U) n) : ℕ) : ℝ) ≤
        (Real.log ((radical (primePart (outsidePrimes P n) n) : ℕ) : ℝ) /
          Real.log (primePart (outsidePrimes P n) n : ℝ)) * Real.log U +
          Real.log ((orderedOutside P n)[i.val] : ℝ) := by
  obtain ⟨hcap, hcross, hbefore⟩ := stopIndex_spec hU havailable
  have hnonzero : stopIndex P n U ≠ 0 := by
    intro heq
    have hlt : U < 1 := by simpa [stoppedPrimes, heq, prefixPrimes, primePart] using hcross
    exact hlt.not_ge hU
  let i := stopIndex P n U - 1
  have hi : stopIndex P n U = i + 1 := by dsimp [i]; omega
  have hilt : i < (orderedOutside P n).length := by omega
  obtain ⟨hnext, hnew⟩ := prefix_succ hilt
  have hstop : stoppedPrimes P n U = insert (orderedOutside P n)[i] (prefixPrimes P n i) := by
    rw [stoppedPrimes, hi, hnext]
  refine ⟨⟨i, hilt⟩, hi, hstop, hbefore, hcross, ?_⟩
  have hS : stoppedPrimes P n U ⊆ n.primeFactors :=
    (prefix_subset P n (stopIndex P n U)).trans Finset.sdiff_subset
  have hA : prefixPrimes P n i ⊆ n.primeFactors :=
    (prefix_subset P n i).trans Finset.sdiff_subset
  have hpre := prefix_log_le hU havailable (hbefore i (by omega))
  rw [log_radical_part hS, hstop, Finset.sum_insert hnew, ← log_radical_part hA, add_comm]
  exact add_le_add_left hpre _

/-- The two signs are recorded separately, both inside `P` and at the outside stop. -/
public structure SignedLabel where
  insideNum : ℕ
  insideDen : ℕ
  stoppedNum : ℕ
  stoppedDen : ℕ

/-- Encode the signed full powers, not just their radicals. -/
@[expose] public noncomputable def signedLabel (P : Finset ℕ) (U : ℝ) (N M : ℕ) : SignedLabel :=
  let S := stoppedPrimes P (N * M) U
  ⟨primePart P N, primePart P M, primePart S N, primePart S M⟩

/-- Product of the two full inside parts, the normalization factor `m`. -/
@[expose] public def insideProduct (P : Finset ℕ) (N M : ℕ) : ℕ :=
  primePart P N * primePart P M

/-- The signed integer determinant of two numerator/denominator pairs. -/
@[expose] public def determinant (N₁ M₁ N₂ M₂ : ℕ) : ℤ :=
  (N₁ : ℤ) * M₂ - (N₂ : ℤ) * M₁

private theorem part_union {S T : Finset ℕ} {n : ℕ} (hd : Disjoint S T) :
    primePart (S ∪ T) n = primePart S n * primePart T n :=
  Finset.prod_union hd

private theorem stopped_disjoint (P : Finset ℕ) (n : ℕ) (U : ℝ) :
    Disjoint P (stoppedPrimes P n U) :=
  Finset.disjoint_left.mpr fun _ hp hs ↦
    (Finset.mem_sdiff.mp (prefix_subset P n (stopIndex P n U) hs)).2 hp

private theorem matching_parts_dvd_det {S T : Finset ℕ} {N₁ M₁ N₂ M₂ : ℕ}
    (hN₁ : N₁ ≠ 0) (hM₁ : M₁ ≠ 0) (hN₂ : N₂ ≠ 0) (hM₂ : M₂ ≠ 0)
    (hN : primePart S N₁ = primePart T N₂) (hM : primePart S M₁ = primePart T M₂) :
    ((primePart S (N₁ * M₁) : ℕ) : ℤ) ∣ determinant N₁ M₁ N₂ M₂ := by
  rw [part_mul S hN₁ hM₁, determinant]
  apply dvd_sub
  · rw [← Nat.cast_mul]
    exact Int.natCast_dvd_natCast.mpr (Nat.mul_dvd_mul (part_dvd hN₁) (hM ▸ part_dvd hM₂))
  · rw [← Nat.cast_mul]
    exact Int.natCast_dvd_natCast.mpr (Nat.mul_dvd_mul (hN ▸ part_dvd hN₂) (part_dvd hM₁))

/-- Equal signed labels give the product of the inside and stopped full powers
as a divisor of the signed integer determinant, even if the two stops were
computed separately. -/
public theorem signedLabel_dvd_determinant {P : Finset ℕ} {U : ℝ} {N₁ M₁ N₂ M₂ : ℕ}
    (hN₁ : N₁ ≠ 0) (hM₁ : M₁ ≠ 0) (hN₂ : N₂ ≠ 0) (hM₂ : M₂ ≠ 0)
    (hlabel : signedLabel P U N₁ M₁ = signedLabel P U N₂ M₂) :
    ((insideProduct P N₁ M₁ * primePart (stoppedPrimes P (N₁ * M₁) U) (N₁ * M₁) : ℕ) : ℤ)
      ∣ determinant N₁ M₁ N₂ M₂ := by
  let S := stoppedPrimes P (N₁ * M₁) U
  let T := stoppedPrimes P (N₂ * M₂) U
  have hs : Disjoint P S := stopped_disjoint P (N₁ * M₁) U
  have ht : Disjoint P T := stopped_disjoint P (N₂ * M₂) U
  have hN : primePart (P ∪ S) N₁ = primePart (P ∪ T) N₂ := by
    rw [part_union hs, part_union ht]
    exact congrArg₂ (· * ·) (congrArg SignedLabel.insideNum hlabel)
      (congrArg SignedLabel.stoppedNum hlabel)
  have hM : primePart (P ∪ S) M₁ = primePart (P ∪ T) M₂ := by
    rw [part_union hs, part_union ht]
    exact congrArg₂ (· * ·) (congrArg SignedLabel.insideDen hlabel)
      (congrArg SignedLabel.stoppedDen hlabel)
  have h := matching_parts_dvd_det hN₁ hM₁ hN₂ hM₂ hN hM
  rwa [part_union hs, part_mul P hN₁ hM₁] at h

private theorem eq_of_det_eq_zero {N₁ M₁ N₂ M₂ : ℕ}
    (hM₁ : 0 < M₁) (hred₁ : N₁.Coprime M₁) (hred₂ : N₂.Coprime M₂)
    (hdet : determinant N₁ M₁ N₂ M₂ = 0) : N₁ = N₂ ∧ M₁ = M₂ := by
  have hz : (N₁ : ℤ) * M₂ = (N₂ : ℤ) * M₁ := sub_eq_zero.mp hdet
  have hprod : N₁ * M₂ = N₂ * M₁ := by exact_mod_cast hz
  have h12 : M₁ ∣ M₂ := hred₁.symm.dvd_of_dvd_mul_left (by
    rw [hprod]
    exact Nat.dvd_mul_left M₁ N₂)
  have h21 : M₂ ∣ M₁ := hred₂.symm.dvd_of_dvd_mul_left (by
    rw [← hprod]
    exact Nat.dvd_mul_left M₂ N₁)
  have hm := Nat.dvd_antisymm h12 h21
  exact ⟨Nat.eq_of_mul_eq_mul_right hM₁ (by simpa only [hm] using hprod), hm⟩

/-- Separation of reduced positive ratios by Alice's signed label. It suffices
that `q` is coprime to the first candidate's product, and that this candidate
has enough outside product to cross when `1 ≤ U`. For `U < 1` the outside
part is `1`, so the inside parts alone already force equality. -/
public theorem signedLabel_separates {P : Finset ℕ} {U : ℝ} {q N₁ M₁ N₂ M₂ : ℕ}
    (hq : 0 < q) (hN₁ : 0 < N₁) (hM₁ : 0 < M₁) (hN₂ : 0 < N₂) (hM₂ : 0 < M₂)
    (hred₁ : N₁.Coprime M₁) (hred₂ : N₂.Coprime M₂)
    (hqcop : q.Coprime (N₁ * M₁)) (hqdet : (q : ℤ) ∣ determinant N₁ M₁ N₂ M₂)
    (havailable : 1 ≤ U → U < (primePart (outsidePrimes P (N₁ * M₁)) (N₁ * M₁) : ℝ))
    (hbound : |(determinant N₁ M₁ N₂ M₂ : ℝ)| / ((q : ℝ) * insideProduct P N₁ M₁) ≤ U)
    (hlabel : signedLabel P U N₁ M₁ = signedLabel P U N₂ M₂) :
    determinant N₁ M₁ N₂ M₂ = 0 ∧ N₁ = N₂ ∧ M₁ = M₂ := by
  let n := N₁ * M₁
  let S := stoppedPrimes P n U
  let m := insideProduct P N₁ M₁
  let v := primePart S n
  let Δ := determinant N₁ M₁ N₂ M₂
  have hn : 0 < n := Nat.mul_pos hN₁ hM₁
  have hmprod : m = primePart P n := (part_mul P hN₁.ne' hM₁.ne').symm
  have hmv : m * v = primePart (P ∪ S) n := by
    rw [part_union (stopped_disjoint P n U), ← hmprod]
  have hmn : m ∣ n := hmprod ▸ part_dvd hn.ne'
  have hmvdiv : m * v ∣ n := hmv ▸ part_dvd hn.ne'
  have hstop : U < (v : ℝ) := by
    by_cases hU : 1 ≤ U
    · obtain ⟨_, _, _, _, hcross, _⟩ := first_crossing hU (havailable hU)
      exact hcross
    · have he := stoppedPrimes_of_lt_one (P := P) (n := n) (not_le.mp hU)
      simpa [v, S, he, primePart] using (not_le.mp hU : U < (1 : ℝ))
  have hdiv : ((m * v : ℕ) : ℤ) ∣ Δ :=
    signedLabel_dvd_determinant hN₁.ne' hM₁.ne' hN₂.ne' hM₂.ne' hlabel
  have hqmv : q * (m * v) ∣ Δ.natAbs :=
    (hqcop.of_dvd_right hmvdiv).mul_dvd_of_dvd_of_dvd
      (Int.natCast_dvd.mp hqdet) (Int.natCast_dvd.mp hdiv)
  have hqm : 0 < (q : ℝ) * (m : ℝ) := mul_pos (Nat.cast_pos.mpr hq)
    (Nat.cast_pos.mpr (Nat.pos_of_dvd_of_pos hmn hn))
  have hzero : Δ = 0 := by
    by_contra hne
    have hloNat := Nat.le_of_dvd (Int.natAbs_pos.mpr hne) hqmv
    have hlo : (q : ℝ) * ((m : ℝ) * (v : ℝ)) ≤ (Δ.natAbs : ℝ) := by
      exact_mod_cast hloNat
    rw [Nat.cast_natAbs, Int.cast_abs, ← mul_assoc] at hlo
    have hhi : |(Δ : ℝ)| ≤ U * ((q : ℝ) * (m : ℝ)) := (div_le_iff₀ hqm).mp hbound
    have hlt := mul_lt_mul_of_pos_right hstop hqm
    rw [mul_comm (v : ℝ)] at hlt
    exact (hhi.trans_lt hlt).not_ge hlo
  exact ⟨hzero, eq_of_det_eq_zero hM₁ hred₁ hred₂ hzero⟩

end OrderedRadicalCrossing
