module

public import Lemmas.CrossedSplitCount

/-!
# The occupied crossed-direction budget from an eligible-prime cutoff

Source: `b6920957:.godel/alice/crossed-gap-filters.md:13–30`, especially step 3
before scalar recovery. Keep the occupied directions and the actual admissible
split and radical menus. In the large-`V` branch each split product is at most
`X * V` and each prime factor is at least `ℓ`; counting factors with repetition,
`X * V < ℓ ^ (E + 1)` therefore limits their number to `E`. The small-`V`
menu has only the unit split and needs no power bound. This is a finite
occupied-direction bound, not a smooth-radical count or scalar recovery.

Owning check session: `01a20b8b-65a1-7430-ae92-47e2bde881a8`.
-/

namespace CrossedDirectionBudget

open CrossedDirectionCover CrossedSplitCount UniqueFactorizationMonoid

private theorem pow_length_le_cast_prod {ℓ : ℝ} (hℓ : 0 ≤ ℓ) (l : List ℕ)
    (h : ∀ p ∈ l, ℓ ≤ (p : ℝ)) : ℓ ^ l.length ≤ (l.prod : ℝ) := by
  induction l with
  | nil => simp
  | cons p l ih =>
    simp only [List.mem_cons, forall_eq_or_imp] at h
    rw [List.length_cons, pow_succ', List.prod_cons, Nat.cast_mul]
    exact mul_le_mul h.1 (ih h.2) (pow_nonneg hℓ _) (Nat.cast_nonneg p)

/-- Bound the occupied signed directions using all admissible radicals, with one
side bit per support prime and a total multiplicity budget deduced from `ℓ`.
At `V ≤ 1` there are at most two directions, independently of the power bound. -/
public theorem card_le_radicalMenu_budget {eligible : ℕ → Prop} {X K V ℓ : ℝ} {E : ℕ}
    {d F₁ F₂ : ℤ} {S : Finset (ℤ × ℤ)} (hd : 0 < d) (hX : 1 < X) (hK : 1 ≤ K)
    (hcoeff : IsCoprime F₁ d ∧ IsCoprime F₂ d)
    (hrows : ∀ n ∈ S, n.1 ≠ 0 ∧ n.2 ≠ 0 ∧ IsCoprime n.1 n.2 ∧
      IsCoprime n.1 d ∧ IsCoprime n.2 d ∧ (F₂ * n.1 ≡ F₁ * n.2 [ZMOD d]))
    (hdet : ∀ x ∈ S, ∀ y ∈ S,
      |((x.1 * y.2 - y.1 * x.2 : ℤ) : ℝ)| ≤ (d : ℝ) * V / 2)
    (hdata : ∀ n ∈ S, ∃ M A : ℕ, IsEligiblePart eligible (n.1 * n.2).natAbs M ∧
      (∀ p : ℕ, p.Prime → p ∣ M → (p : ℝ) ≤ X) ∧
      K ≤ ((M / radical M : ℕ) : ℝ) ∧ A ∣ M ∧ (1 < V → V ≤ (A : ℝ)))
    (hseed : 1 < K → X ^ 2 * K ^ 2 ≤ V)
    (hℓ : 2 ≤ ℓ) (hfloor : ∀ p : ℕ, p.Prime → eligible p → ℓ ≤ (p : ℝ))
    (hbudget : 1 < V → X * V < ℓ ^ (E + 1)) :
    S.card ≤ if 1 < V then
      2 * ∑ r ∈ radicalMenu eligible X K V, 2 ^ r.primeFactors.card * Nat.choose E r.primeFactors.card
    else 2 := by
  have hcover := CrossedDirectionCover.card_le_twice_admissibleSplits
    hd hX hK hcoeff hrows hdet hdata hseed
  have hlength (hV : 1 < V) (b : ℕ × ℕ) (hb : b ∈ admissibleSplits eligible X K V) :
      (b.1 * b.2).primeFactorsList.length ≤ E := by
    have hb' := (mem_admissibleSplits hX).mp hb
    rw [ite_eq_left hV] at hb'
    obtain ⟨h₁, h₂, _, _, hcap, _, heligible⟩ := hb'
    have hm : b.1 * b.2 ≠ 0 := mul_ne_zero h₁.ne' h₂.ne'
    have hfactor (p : ℕ) (hp : p ∈ (b.1 * b.2).primeFactorsList) : ℓ ≤ (p : ℝ) := by
      obtain ⟨hp', hpdiv⟩ := (Nat.mem_primeFactorsList hm).mp hp
      exact hfloor p hp' (heligible p hp' hpdiv).1
    have hprod := pow_length_le_cast_prod (zero_le_two.trans hℓ) _ hfactor
    rw [Nat.prod_primeFactorsList hm] at hprod
    apply le_of_not_gt
    intro hE
    have hpow := pow_le_pow_right₀ (one_le_two.trans hℓ) (Nat.succ_le_of_lt hE)
    exact (hbudget hV).not_ge (hpow.trans (hprod.trans hcap))
  have hcount := CrossedSplitCount.card_admissibleSplits_le hX hlength
  by_cases hV : 1 < V
  · rw [ite_eq_left hV] at hcount ⊢
    exact hcover.trans (Nat.mul_le_mul_left 2 hcount)
  · rw [ite_eq_right hV] at hcount ⊢
    exact hcover.trans (by simpa only [mul_one] using Nat.mul_le_mul_left 2 hcount)

end CrossedDirectionBudget
