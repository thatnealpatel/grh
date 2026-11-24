module

public import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Finset.Max

/-!
# Sparse missing-divisor routing

Source: `fea7eb0b:.godel/alice/sharp-sparse-harmonics.md:9–25` (selection and
quotient bound, lines 11–19). Consumer:
`3d2886df:.godel/bob/noisy-sparse-harmonics.md:11–16`. The scope is unchanged
from pin `3d2886df` at base `1de21475`.

Only queries above the cutoff with at least one missing divisor are assigned.
Each such query is sent to its largest missing divisor, and the budget leaves
an unassigned missing order. The argument does not bound the query orders.
This is the combinatorial input to the grid argument, not a claim about the
shifted-grid mean or noisy minimax.

Owning check session: `01a20c3b-0de7-75d0-b4f0-194be0854305`.
-/

namespace Masullo

/-- Compare the two exact cofactors of a positive common multiple. The smaller
cofactor leaves a product gap of at least one copy of `n`. -/
private theorem quotient_mul_gap_ge {j n m N : ℕ} (hj : 0 < j) (hnm : n < m)
    (hmN : m ≤ N) (hnd : n ∣ j) (hmd : m ∣ j) : N ≤ (j / n) * (N - n) := by
  have hndiv : (j / n) * n = j := Nat.div_mul_cancel hnd
  have hmdiv : (j / m) * m = j := Nat.div_mul_cancel hmd
  have hmpos : 0 < j / m := Nat.div_pos (Nat.le_of_dvd hj hmd) (by omega)
  have hlt : (j / m) * n < (j / m) * m := Nat.mul_lt_mul_of_pos_left hnm hmpos
  have hsucc : j / m + 1 ≤ j / n :=
    Nat.lt_of_mul_lt_mul_right ((hlt.trans_eq hmdiv).trans_eq hndiv.symm)
  have hstep : (j / m + 1) * n ≤ j := (Nat.mul_le_mul_right n hsucc).trans_eq hndiv
  have hgap : n ≤ (j / m) * (m - n) := by
    rw [Nat.mul_sub_left_distrib, hmdiv]
    rw [Nat.add_mul, Nat.one_mul] at hstep
    omega
  have hgap' : n ≤ (j / m) * (N - n) :=
    hgap.trans (Nat.mul_le_mul_left _ (Nat.sub_le_sub_right hmN n))
  calc
    N = n + (N - n) := by omega
    _ ≤ (j / m + 1) * (N - n) := by
      rw [Nat.add_mul, Nat.one_mul]
      exact Nat.add_le_add_right hgap' _
    _ ≤ (j / n) * (N - n) := Nat.mul_le_mul_right _ hsucc

/-- For a budget of at most `N - 1` positive query orders, there is a missing
order `n` in `[1,N]`. If `4 * n > 3 * N`, every query divisible by `n` is above
`N` and has a larger missing divisor in `[1,N]`. For `n < N`, the exact
cofactor `j / n` is at least `1 + n / (N - n)` with rational division on the
right, stated by cross multiplication. If `n = N`, no query is divisible by `n`. -/
public theorem exists_sparse_missing_divisor {N : ℕ} (hN : 1 ≤ N)
    (J : Finset ℕ) (hJpos : ∀ j ∈ J, 0 < j) (hJcard : J.card ≤ N - 1) :
    ∃ n : ℕ, 1 ≤ n ∧ n ≤ N ∧ n ∉ J ∧
      (3 * N < 4 * n → ∀ j ∈ J, n ∣ j →
        N < j ∧ (∃ m : ℕ, n < m ∧ m ≤ N ∧ m ∉ J ∧ m ∣ j) ∧
          (n < N → N ≤ (j / n) * (N - n))) ∧
      (n = N → ∀ j ∈ J, ¬ n ∣ j) := by
  let I := Finset.Icc 1 N
  let M := I \ J
  let H := J \ I -- For positive queries, this is exactly the set of orders above `N`.
  have hIcard : I.card = N := by simp [I]
  have hMcard : M.card = N - (J ∩ I).card := by
    dsimp only [M]
    rw [Finset.card_sdiff, hIcard]
  have hHcard : H.card = J.card - (J ∩ I).card := by
    dsimp only [H]
    rw [Finset.card_sdiff, Finset.inter_comm I J]
  have hcommon : (J ∩ I).card ≤ J.card := Finset.card_le_card Finset.inter_subset_left
  have hHM : H.card < M.card := by
    rw [hHcard, hMcard]
    omega
  let D (j : ℕ) := M.filter fun m ↦ m ∣ j
  let R := H.filter fun j ↦ (D j).Nonempty
  let route (q : {j // j ∈ R}) : ℕ := (D q.val).max' (Finset.mem_filter.mp q.property).2
  let A := R.attach.image route
  have hAH : A.card ≤ H.card := by
    calc
      A.card ≤ R.attach.card := Finset.card_image_le
      _ = R.card := Finset.card_attach
      _ ≤ H.card := Finset.card_filter_le _ _
  obtain ⟨n, hnM, hnA⟩ := Finset.exists_mem_notMem_of_card_lt_card (hAH.trans_lt hHM)
  obtain ⟨hnI, hnJ⟩ := Finset.mem_sdiff.mp hnM
  obtain ⟨hnpos, hnN⟩ := Finset.mem_Icc.mp hnI
  have hroute (hnlarge : 3 * N < 4 * n) (j : ℕ) (hj : j ∈ J) (hnj : n ∣ j) :
      N < j ∧ ∃ m ∈ M, n < m ∧ m ∣ j := by
    have hdiv : (j / n) * n = j := Nat.div_mul_cancel hnj
    have hqpos : 0 < j / n := Nat.div_pos (Nat.le_of_dvd (hJpos j hj) hnj) hnpos
    have hqne : j / n ≠ 1 := by
      intro hq
      rw [hq, Nat.one_mul] at hdiv
      exact hnJ (hdiv.symm ▸ hj)
    have hq : 2 ≤ j / n := by omega
    have hjhigh : N < j :=
      (show N < 2 * n by omega).trans_le ((Nat.mul_le_mul_right n hq).trans_eq hdiv)
    have hjH : j ∈ H := Finset.mem_sdiff.mpr ⟨hj, fun hjI ↦
      (not_le_of_gt hjhigh) (Finset.mem_Icc.mp hjI).2⟩
    have hnD : n ∈ D j := Finset.mem_filter.mpr ⟨hnM, hnj⟩
    let q : {j // j ∈ R} := ⟨j, Finset.mem_filter.mpr ⟨hjH, ⟨n, hnD⟩⟩⟩
    have hqA : route q ∈ A := Finset.mem_image_of_mem route (Finset.mem_attach R q)
    have hqD : route q ∈ D j := Finset.max'_mem _ _
    have hnle : n ≤ route q := Finset.le_max' _ _ hnD
    have hne : n ≠ route q := fun heq ↦ hnA (heq.symm ▸ hqA)
    obtain ⟨hmM, hmj⟩ := Finset.mem_filter.mp hqD
    exact ⟨hjhigh, route q, hmM, lt_of_le_of_ne hnle hne, hmj⟩
  refine ⟨n, hnpos, hnN, hnJ, ?_, ?_⟩
  · intro hnlarge j hj hnj
    obtain ⟨hjhigh, m, hmM, hnm, hmj⟩ := hroute hnlarge j hj hnj
    obtain ⟨hmI, hmJ⟩ := Finset.mem_sdiff.mp hmM
    have hmN := (Finset.mem_Icc.mp hmI).2
    exact ⟨hjhigh, ⟨m, hnm, hmN, hmJ, hmj⟩,
      fun _ ↦ quotient_mul_gap_ge (hJpos j hj) hnm hmN hnj hmj⟩
  · intro hn_eq j hj hnj
    obtain ⟨_, m, hmM, hnm, _⟩ := hroute (by omega) j hj hnj
    have hmN := (Finset.mem_Icc.mp (Finset.mem_sdiff.mp hmM).1).2
    omega

end Masullo
