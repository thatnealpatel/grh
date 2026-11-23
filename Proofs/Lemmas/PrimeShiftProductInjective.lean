module

public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Algebra.BigOperators.Group.Multiset.Basic
import Mathlib.Data.Multiset.Filter
import Mathlib.Data.Nat.Factors

/-!
# Fixed-shift prime ratio products are injective

Formalizes the finite decoding step of `db760d6f:.godel/bob/dyadic-prime-pair-moments.md`
(lines 9–15) and `ec81e8cb:.godel/bob/last-slot-residues.md` (lines 11–15), also used
for net signed multiplicities in `454c049f:.godel/bob/tuple-redraw-cost.md` (line 21).
The scope is one fixed positive shift, with arbitrary finite multiplicities and possible
overlaps between starts and endpoints. The factorial-weighted enumeration is not included.

Owning check session: `01a208d1-f4a1-7e74-9d68-6b0dfb6d9df9`.
-/

namespace PrimeShiftProductInjective

private theorem eq_of_prime_prod_eq (s t : Multiset ℕ) :
    s.prod = t.prod → (∀ p ∈ s, p.Prime) → (∀ p ∈ t, p.Prime) → s = t := by
  refine Quotient.inductionOn₂ s t ?_
  intro l r hprod hl hr
  apply Multiset.coe_eq_coe.mpr
  exact (Nat.primeFactorsList_unique (n := r.prod) hprod hl).trans
    (Nat.primeFactorsList_unique (n := r.prod) rfl hr).symm

private theorem count_shift (s : Multiset ℕ) (d n : ℕ) :
    (s.map (fun p => p + d)).count n = if d ≤ n then s.count (n - d) else 0 := by
  by_cases h : d ≤ n
  · rw [ite_eq_left h, Multiset.count_map, Multiset.count_eq_card_filter_eq]
    congr 1
    apply Multiset.filter_congr
    intro p _
    exact ⟨fun he => Nat.add_right_cancel ((Nat.sub_add_cancel h).trans he),
      fun he => (Nat.sub_add_cancel h).symm.trans (congrArg (· + d) he)⟩
  · rw [ite_eq_right h, Multiset.count_eq_zero]
    intro hn
    obtain ⟨p, _, rfl⟩ := Multiset.mem_map.mp hn
    exact h (Nat.le_add_left d p)

/-- Two finite multisets of prime starts for the same positive shift are equal if their
products of `(p + d) / p` agree. The hypothesis is written with natural cross multiplication:
the product of the shifted starts from `s` is multiplied by the product of the starts from `t`,
and conversely. Each denominator is a product of nonzero primes (or `1` if empty), so no
information is lost by cross multiplication. -/
public theorem eq_of_cross_mul_eq {d : ℕ} {s t : Multiset ℕ} (hd : 0 < d)
    (hs : ∀ p ∈ s, p.Prime ∧ (p + d).Prime)
    (ht : ∀ p ∈ t, p.Prime ∧ (p + d).Prime)
    (hprod : (s.map (fun p => p + d)).prod * t.prod =
      (t.map (fun p => p + d)).prod * s.prod) : s = t := by
  have prime_add_map (u v : Multiset ℕ)
      (hu : ∀ p ∈ u, p.Prime ∧ (p + d).Prime)
      (hv : ∀ p ∈ v, p.Prime ∧ (p + d).Prime) :
      ∀ p ∈ u.map (fun q => q + d) + v, p.Prime := by
    intro p hp
    rcases Multiset.mem_add.mp hp with hp | hp
    · obtain ⟨q, hq, rfl⟩ := Multiset.mem_map.mp hp
      exact (hu q hq).2
    · exact (hv p hp).1
  have hbalance : s.map (fun p => p + d) + t = t.map (fun p => p + d) + s :=
    eq_of_prime_prod_eq _ _ (by simpa only [Multiset.prod_add] using hprod)
      (prime_add_map s t hs ht) (prime_add_map t s ht hs)
  -- At `n`, the incoming multiplicity comes from the strictly smaller start `n - d`, if any.
  apply Multiset.ext.mpr
  intro n
  induction n using Nat.strong_induction_on with
  | ind n ih =>
      have hc := congrArg (Multiset.count n) hbalance
      simp only [Multiset.count_add, count_shift] at hc
      by_cases h : d ≤ n
      · simp only [ite_eq_left h, ih (n - d) (Nat.sub_lt (lt_of_lt_of_le hd h) hd)] at hc
        exact (Nat.add_left_cancel hc).symm
      · simpa only [ite_eq_right h, Nat.zero_add] using hc.symm

end PrimeShiftProductInjective
