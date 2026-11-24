module

public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Finset.Sort
import Mathlib.Data.ZMod.Basic

/-!
# Finite branch-evaluation determinant divisor

Source: `85027edf:.godel/alice/prescribed-product-jets.md:52`.
Direct consumers: `e2145667:.godel/alice/through-point-components.md:25–41`
(ordinary multiple points and one-coordinate cubic fibers).
Owning check session: `01a20ee2-df11-780c-9cc1-8715404fb242`.

For a square integer matrix with `a` columns, put `N = a.choose 2`. At each exact prime
power `q = p ^ g.factorization p` of a positive natural number `g`, the input is an
entrywise congruence modulo `q ^ N`. The representative for column `j` is the value at
`t j` of a single finite vector polynomial with integer coefficients, with `q ∣ t j`.
The truncation length, coefficient representatives, and parameter vector are local to the
prime and the chosen branch class; within that class all columns use the same coefficients.
These finite congruences suffice for `g ^ N` to divide the integer determinant. No branch
existence, convergence, second-coordinate congruence, or occupancy bound is asserted.

For `g = 1` the prime conditions are vacuous; for `a = 0` or `a = 1` the divisor is `1`.
-/

open scoped BigOperators Matrix

namespace BranchEvaluationDivisor

private theorem choose_two_le_sum_degrees {a d : ℕ} {e : Fin a → Fin d}
    (he : Function.Injective e) : a.choose 2 ≤ ∑ j, (e j : ℕ) := by
  let s := Finset.univ.image (fun j ↦ (e j : ℕ))
  have he' : Function.Injective (fun j ↦ (e j : ℕ)) := Fin.val_injective.comp he
  have hs : s.card = a := by
    simp [s, Finset.card_image_of_injective _ he']
  let v := s.orderEmbOfFin hs
  have index_le_of_strictMono {n : ℕ} (f : Fin n → ℕ) (hf : StrictMono f)
      (i : Fin n) : (i : ℕ) ≤ f i := by
    cases n with
    | zero => exact i.elim0
    | succ n =>
      induction i using Fin.induction with
      | zero => exact Nat.zero_le _
      | succ i ih => exact Nat.succ_le_of_lt (lt_of_le_of_lt ih (hf Fin.castSucc_lt_succ))
  calc
    a.choose 2 = ∑ i : Fin a, (i : ℕ) := by
      rw [Nat.choose_two_right, ← Finset.sum_range_id]
      exact (Fin.sum_univ_eq_sum_range (fun i : ℕ ↦ i) a).symm
    _ ≤ ∑ i, v i := Finset.sum_le_sum (fun i _ ↦ index_le_of_strictMono v v.strictMono i)
    _ = ∑ x ∈ s, x := by
      rw [← Finset.image_orderEmbOfFin_univ s hs, Finset.sum_image v.injective.injOn]
    _ = ∑ i, (e i : ℕ) := Finset.sum_image he'.injOn

private theorem pow_choose_two_dvd_det_evaluation {a d q : ℕ}
    (c : Fin d → Fin a → ℤ) (t : Fin a → ℤ) (ht : ∀ j, (q : ℤ) ∣ t j) :
    (↑(q ^ a.choose 2) : ℤ) ∣ (Matrix.of fun i j ↦ ∑ n : Fin d, t j ^ (n : ℕ) * c n i).det := by
  classical
  -- Transposition makes the evaluation columns the arguments of the row determinant.
  rw [Nat.cast_pow, ← Matrix.det_transpose]
  let D := (Matrix.detRowAlternating (n := Fin a) (R := ℤ)).toMultilinearMap
  have hrows : (fun j i ↦ ∑ n : Fin d, t j ^ (n : ℕ) * c n i) =
      (fun j ↦ ∑ n : Fin d, t j ^ (n : ℕ) • c n) := by
    funext j i
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  change (q : ℤ) ^ a.choose 2 ∣ D (fun j i ↦ ∑ n : Fin d, t j ^ (n : ℕ) * c n i)
  rw [hrows, D.map_sum]
  apply Finset.dvd_sum
  intro e _
  rw [D.map_smul_univ]
  by_cases he : Function.Injective e
  · -- Distinct chosen degrees contribute at least `a.choose 2` powers of `q`.
    have hprod : (q : ℤ) ^ (∑ j, (e j : ℕ)) ∣ ∏ j, t j ^ (e j : ℕ) := by
      rw [← Finset.prod_pow_eq_pow_sum]
      exact Finset.prod_dvd_prod_of_dvd _ _ (fun j _ ↦ pow_dvd_pow_of_dvd (ht j) _)
    exact dvd_mul_of_dvd_left ((pow_dvd_pow _ (choose_two_le_sum_degrees he)).trans hprod) _
  · -- A repeated degree gives two identical coefficient vectors.
    obtain ⟨i, j, hij, hne⟩ := Function.not_injective_iff.mp he
    have hz : D (fun j ↦ c (e j)) = 0 :=
      Matrix.detRowAlternating.map_eq_zero_of_eq _ (congrArg c hij) hne
    rw [hz, smul_zero]
    exact dvd_zero _

/-- A finite congruence to common polynomial evaluations at `q`-divisible parameters gives
`q ^ a.choose 2` in the determinant. No primality assumption on `q` is needed. -/
public theorem pow_choose_two_dvd_det_of_local_congruence {a d q : ℕ}
    (A : Matrix (Fin a) (Fin a) ℤ) (c : Fin d → Fin a → ℤ) (t : Fin a → ℤ)
    (ht : ∀ j, (q : ℤ) ∣ t j)
    (hA : ∀ i j, A i j ≡ (∑ n : Fin d, t j ^ (n : ℕ) * c n i) [ZMOD ↑(q ^ a.choose 2)]) :
    (↑(q ^ a.choose 2) : ℤ) ∣ A.det := by
  let B : Matrix (Fin a) (Fin a) ℤ := Matrix.of fun i j ↦ ∑ n : Fin d, t j ^ (n : ℕ) * c n i
  have hB : (↑(q ^ a.choose 2) : ℤ) ∣ B.det := pow_choose_two_dvd_det_evaluation c t ht
  let ρ := Int.castRingHom (ZMod (q ^ a.choose 2))
  have hmap : ρ.mapMatrix A = ρ.mapMatrix B := by
    ext i j
    exact (ZMod.intCast_eq_intCast_iff _ _ _).mpr (hA i j)
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
  change ρ A.det = 0
  rw [ρ.map_det, hmap, ← ρ.map_det]
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hB

/-- Assemble the finite branch congruences at the exact prime powers of a positive natural
number `g`. The witnesses for the finite polynomial and parameters can vary with the prime. -/
public theorem pow_choose_two_dvd_det_of_prime_power_congruences {a g : ℕ}
    (hg : g ≠ 0) (A : Matrix (Fin a) (Fin a) ℤ)
    (h : ∀ p ∈ g.primeFactors,
      ∃ (d : ℕ) (c : Fin d → Fin a → ℤ) (t : Fin a → ℤ),
        (∀ j, (↑(p ^ g.factorization p) : ℤ) ∣ t j) ∧
        (∀ i j, A i j ≡ (∑ n : Fin d, t j ^ (n : ℕ) * c n i)
          [ZMOD ↑((p ^ g.factorization p) ^ a.choose 2)])) :
    (↑(g ^ a.choose 2) : ℤ) ∣ A.det := by
  -- Assemble the local divisibilities on the natural absolute value of the determinant.
  apply Int.natCast_dvd.mpr
  by_cases hdet : A.det.natAbs = 0
  · simp [hdet]
  apply (Nat.factorization_le_iff_dvd (pow_ne_zero _ hg) hdet).mp
  intro p
  rw [Nat.factorization_pow, Finsupp.smul_apply, nsmul_eq_mul, Nat.cast_id]
  by_cases hp : p ∈ g.primeFactors
  · obtain ⟨d, c, t, ht, hA⟩ := h p hp
    have hlocal := Int.natCast_dvd.mp (pow_choose_two_dvd_det_of_local_congruence A c t ht hA)
    rw [← pow_mul, Nat.mul_comm] at hlocal
    exact ((Nat.prime_of_mem_primeFactors hp).pow_dvd_iff_le_factorization hdet).mp hlocal
  · have hp0 : g.factorization p = 0 := by
      rwa [← Nat.support_factorization, Finsupp.mem_support_iff, not_ne_iff] at hp
    simp [hp0]

end BranchEvaluationDivisor
