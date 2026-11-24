module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Finite-alphabet rounding with weighted prefix error

Source: `daee96a:.godel/bob/endpoint-convolution-lift.md`, lines 22–44.
This formalizes the finite accumulator construction and partial summation in
line 26, used in the translated measurements in lines 28–44. At each position
we add its probability vector and choose an atom of maximal resulting
residual, subtracting one at that atom. The choices work jointly for every
real observable and every real weight sequence. There is no prime asymptotic
or analytic normalization in this finite bound.

Owning check session: `01a20d17-2b2a-7097-a6d0-937638b43d97`.
-/

namespace FiniteAlphabetRounding

open scoped BigOperators Classical

variable {A : Type*}

/-- Demand minus the number of selections of `a` among the first `k` positions. -/
@[expose] public noncomputable def prefixResidual {n k : ℕ} (p : Fin n → A → ℝ)
    (s : Fin n → A) (hk : k ≤ n) (a : A) : ℝ :=
  ∑ i : Fin k, (p (i.castLE hk) a - if a = s (i.castLE hk) then 1 else 0)

/-- Absolute terminal weight plus the variation between adjacent weights, or zero
when there are no weights. -/
@[expose] public noncomputable def weightVariation : {n : ℕ} → (Fin n → ℝ) → ℝ
  | 0, _ => 0
  | n + 1, w => |w (Fin.last n)| + ∑ i : Fin n, |w i.succ - w i.castSucc|

private theorem sum_prefix_succ {n k : ℕ} (g : Fin n → ℝ) (hk : k + 1 ≤ n) :
    (∑ i : Fin (k + 1), g (i.castLE hk)) =
      (∑ i : Fin k, g (i.castLE ((Nat.le_succ k).trans hk))) + g ⟨k, hk⟩ := by
  rw [Fin.sum_univ_castSucc]
  rfl

private theorem prefixResidual_succ {n k : ℕ} (p : Fin n → A → ℝ) (s : Fin n → A)
    (hk : k + 1 ≤ n) (a : A) :
    prefixResidual p s hk a = prefixResidual p s ((Nat.le_succ k).trans hk) a +
      (p ⟨k, hk⟩ a - if a = s ⟨k, hk⟩ then 1 else 0) :=
  sum_prefix_succ (fun i ↦ p i a - if a = s i then 1 else 0) hk

private theorem prefixResidual_snoc {n k : ℕ} (p : Fin (n + 1) → A → ℝ)
    (s : Fin n → A) (a b : A) (hk : k ≤ n) :
    prefixResidual p (Fin.snoc (α := fun _ ↦ A) s a) (hk.trans (Nat.le_succ n)) b =
      prefixResidual (fun i ↦ p i.castSucc) s hk b := by
  unfold prefixResidual
  apply Finset.sum_congr rfl
  intro i _
  change p (i.castLE hk).castSucc b -
    (if b = Fin.snoc (α := fun _ ↦ A) s a (i.castLE hk).castSucc then 1 else 0) = _
  rw [Fin.snoc_castSucc]

variable [Fintype A]

private theorem exists_selection_invariant [Nonempty A] {n : ℕ} (p : Fin n → A → ℝ)
    (hp : ∀ i a, 0 ≤ p i a) (hmass : ∀ i, ∑ a, p i a = 1) :
    ∃ s : Fin n → A, ∀ (k : ℕ) (hk : k ≤ n),
      (∑ a, prefixResidual p s hk a = 0) ∧ ∀ a, -1 < prefixResidual p s hk a := by
  induction n with
  | zero =>
    refine ⟨Fin.elim0, ?_⟩
    intro k hk
    have : k = 0 := Nat.eq_zero_of_le_zero hk
    subst k
    simp [prefixResidual]
  | succ n ih =>
    let p' (i : Fin n) := p i.castSucc
    obtain ⟨s, hs⟩ := ih p' (fun i a ↦ hp i.castSucc a) (fun i ↦ hmass i.castSucc)
    let q (a : A) := prefixResidual p' s (le_refl n) a + p (Fin.last n) a
    obtain ⟨hsum, hlower⟩ := hs n (le_refl n)
    have hqsum : ∑ a, q a = 1 := by
      simp only [q, Finset.sum_add_distrib, hsum, hmass, zero_add]
    have hqlower (b : A) : -1 < q b :=
      (hlower b).trans_le (le_add_of_nonneg_right (hp (Fin.last n) b))
    obtain ⟨a, _, hmax⟩ := Finset.exists_max_image Finset.univ q Finset.univ_nonempty
    have ha : 0 < q a := by
      by_contra! h
      have : ∑ b, q b ≤ 0 :=
        Finset.sum_nonpos fun b hb ↦ (hmax b hb).trans h
      linarith
    let s' : Fin (n + 1) → A := Fin.snoc (α := fun _ ↦ A) s a
    have hfull (b : A) :
        prefixResidual p s' (le_refl (n + 1)) b = q b - (if b = a then 1 else 0) := by
      rw [prefixResidual_succ, prefixResidual_snoc]
      change prefixResidual p' s (le_refl n) b +
        (p (Fin.last n) b -
          (if b = Fin.snoc (α := fun _ ↦ A) s a (Fin.last n) then 1 else 0)) = _
      rw [Fin.snoc_last, ← add_sub_assoc]
    refine ⟨s', fun k hk ↦ ?_⟩
    by_cases hk' : k ≤ n
    · simpa only [s', prefixResidual_snoc p s a _ hk'] using hs k hk'
    · have : k = n + 1 := Nat.le_antisymm hk (Nat.succ_le_of_lt (Nat.lt_of_not_ge hk'))
      subst k
      constructor
      · simp [hfull, Finset.sum_sub_distrib, hqsum]
      · intro b
        rw [hfull]
        by_cases hb : b = a
        · subst b
          simp only [ite_true]
          linarith
        · simpa only [ite_eq_right hb, sub_zero] using hqlower b

private theorem abs_le_card [Nonempty A] (r : A → ℝ) (hsum : ∑ a, r a = 0)
    (hlower : ∀ a, -1 < r a) (a : A) : |r a| ≤ (Fintype.card A : ℝ) := by
  have hone : (1 : ℝ) ≤ Fintype.card A := by
    exact_mod_cast (Fintype.card_pos (α := A) : 1 ≤ Fintype.card A)
  have hsplit : (∑ b ∈ Finset.univ.erase a, r b) + r a = 0 :=
    (Finset.sum_erase_add _ _ (Finset.mem_univ a)).trans hsum
  have hrest : -((Finset.univ.erase a).card : ℝ) ≤ ∑ b ∈ Finset.univ.erase a, r b := by
    simpa using (Finset.sum_le_sum (s := Finset.univ.erase a)
      (f := fun _ ↦ (-1 : ℝ)) (g := r) fun b _ ↦ (hlower b).le)
  have hcard : ((Finset.univ.erase a).card : ℝ) ≤ Fintype.card A := by
    exact_mod_cast (Finset.card_erase_le (s := Finset.univ) (a := a))
  exact abs_le.mpr ⟨by linarith [hlower a], by linarith⟩

private theorem scalar_prefix_eq {n k : ℕ} (p : Fin n → A → ℝ) (s : Fin n → A)
    (hk : k ≤ n) (f : A → ℝ) :
    (∑ a, prefixResidual p s hk a * f a) =
      ∑ i : Fin k, ((∑ a, p (i.castLE hk) a * f a) - f (s (i.castLE hk))) := by
  simp only [prefixResidual, Finset.sum_mul, sub_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_sub_distrib]
  simp [ite_mul]

-- The successor of position `i` indexes the prefix including that position.
private theorem sum_by_parts {n : ℕ} (w e : Fin (n + 1) → ℝ) (t : Fin (n + 2) → ℝ)
    (hzero : t 0 = 0) (hdiff : ∀ i, e i = t i.succ - t i.castSucc) :
    (∑ i, w i * e i) = w (Fin.last n) * t (Fin.last (n + 1)) +
      ∑ i : Fin n, (w i.castSucc - w i.succ) * t i.castSucc.succ := by
  simp only [hdiff, mul_sub, Finset.sum_sub_distrib]
  rw [Fin.sum_univ_castSucc (f := fun i ↦ w i * t i.succ),
    Fin.sum_univ_succ (f := fun i ↦ w i * t i.castSucc)]
  change (∑ i : Fin n, w i.castSucc * t i.castSucc.succ) +
    w (Fin.last n) * t (Fin.last (n + 1)) -
    (w 0 * t 0 + ∑ i : Fin n, w i.succ * t i.castSucc.succ) = _
  simp only [hzero, mul_zero, zero_add, sub_mul, Finset.sum_sub_distrib]
  ring

private theorem abs_weighted_sum_le {n : ℕ} (w e : Fin (n + 1) → ℝ) (t : Fin (n + 2) → ℝ)
    (C : ℝ) (hzero : t 0 = 0) (hdiff : ∀ i, e i = t i.succ - t i.castSucc)
    (ht : ∀ k, |t k| ≤ C) : |∑ i, w i * e i| ≤ C * weightVariation w := by
  rw [sum_by_parts w e t hzero hdiff]
  calc
    _ ≤ |w (Fin.last n) * t (Fin.last (n + 1))| +
        ∑ i : Fin n, |(w i.castSucc - w i.succ) * t i.castSucc.succ| :=
      (abs_add_le _ _).trans (add_le_add le_rfl (Finset.abs_sum_le_sum_abs _ _))
    _ ≤ |w (Fin.last n)| * C + ∑ i : Fin n, |w i.succ - w i.castSucc| * C := by
      simp only [abs_mul]
      refine add_le_add (mul_le_mul_of_nonneg_left (ht _) (abs_nonneg _)) ?_
      apply Finset.sum_le_sum
      intro i _
      rw [abs_sub_comm (w i.castSucc) (w i.succ)]
      exact mul_le_mul_of_nonneg_left (ht _) (abs_nonneg _)
    _ = C * weightVariation w := by
      rw [← Finset.sum_mul, ← add_mul, mul_comm]
      rfl

/-- One selection controls each coordinate at every prefix and, for the same
selection, the weighted discrepancy for every real observable and weight vector.
The weighted discrepancy and its bound are both zero when `n = 0`. -/
public theorem exists_rounding [Nonempty A] {n : ℕ} (p : Fin n → A → ℝ)
    (hp : ∀ i a, 0 ≤ p i a) (hmass : ∀ i, ∑ a, p i a = 1) :
    ∃ s : Fin n → A,
      (∀ (k : ℕ) (hk : k ≤ n) (a : A), |prefixResidual p s hk a| ≤ (Fintype.card A : ℝ)) ∧
      ∀ (f : A → ℝ) (w : Fin n → ℝ),
        |(∑ i, w i * f (s i)) - ∑ i, w i * (∑ a, p i a * f a)| ≤
          (Fintype.card A : ℝ) * (∑ a, |f a|) * weightVariation w := by
  obtain ⟨s, hs⟩ := exists_selection_invariant p hp hmass
  have hcoord k hk a := abs_le_card (prefixResidual p s (k := k) hk) (hs k hk).1 (hs k hk).2 a
  refine ⟨s, hcoord, fun f w ↦ ?_⟩
  cases n with
  | zero => simp [weightVariation]
  | succ n =>
    let e (i : Fin (n + 1)) := (∑ a, p i a * f a) - f (s i)
    let t (k : Fin (n + 2)) := ∑ i : Fin k.val, e (i.castLE (Nat.le_of_lt_succ k.isLt))
    have hzero : t 0 = 0 := by
      change (∑ i : Fin 0, e (i.castLE (Nat.zero_le _))) = 0
      simp
    have hdiff (i : Fin (n + 1)) : e i = t i.succ - t i.castSucc := by
      have hstep : t i.succ = t i.castSucc + e i := sum_prefix_succ e i.isLt
      rw [hstep, add_sub_cancel_left]
    have ht (k : Fin (n + 2)) : |t k| ≤ (Fintype.card A : ℝ) * ∑ a, |f a| := by
      let hk : k.val ≤ n + 1 := Nat.le_of_lt_succ k.isLt
      change |∑ i : Fin k.val, ((∑ a, p (i.castLE hk) a * f a) - f (s (i.castLE hk)))| ≤ _
      rw [← scalar_prefix_eq p s hk f]
      calc
        _ ≤ ∑ a, |prefixResidual p s hk a * f a| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ a, (Fintype.card A : ℝ) * |f a| := by
          apply Finset.sum_le_sum
          intro a _
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_right (hcoord _ hk a) (abs_nonneg _)
        _ = _ := (Finset.mul_sum _ _ _).symm
    have hw : (∑ i, w i * e i) =
        (∑ i, w i * (∑ a, p i a * f a)) - ∑ i, w i * f (s i) := by
      simp only [e, mul_sub, Finset.sum_sub_distrib]
    rw [abs_sub_comm, ← hw]
    exact abs_weighted_sum_le w e t _ hzero hdiff ht

end FiniteAlphabetRounding
