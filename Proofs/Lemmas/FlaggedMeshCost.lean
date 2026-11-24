module

public import Lemmas.SignedCubeCellScreen
public import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Flagged-mesh fine-node cost

Source: `dcc11ec5:.godel/bob/signed-gap-cube-screen.md:66` ("Use and cost").
Consumer: `.godel/bob/retained-shell-screen.md:27–37`, the finite accounting
for tests at both endpoints of each fine subcell on the genuine inner shell.
Owning check session: `01a20e21-be35-7bb8-b792-768105414492`.

This is the finite incidence bound for the cube screen, with the original
normalized surviving sum, whole-cell flags, and `V = X^k`, `m = k` in the
source specialization. Shared endpoints contribute no length, but a node
shared by different flagged cells is counted once in each cell. An absent,
unflagged, or singleton clipped last cell is allowed. No estimate of the
signed statistic at a fine node, cap conclusion, or asymptotic cost is proved.
-/

open MeasureTheory Set
open scoped BigOperators

namespace Masullo.FlaggedMeshCost

open SignedCubeCellScreen
open SignedCubeShell

/-- The strict flag rule of the whole-cell screen, as a finite set of indices. -/
@[expose] public noncomputable def flaggedCells {ι : Type*} (cells : Finset ι)
    (q : ι → ℝ) (δ : ℝ) : Finset ι := by
  classical
  exact cells.filter (fun i => δ / 2 < q i)

public theorem mem_flaggedCells {ι : Type*} {cells : Finset ι} {q : ι → ℝ} {δ : ℝ} {i : ι} :
    i ∈ flaggedCells cells q δ ↔ i ∈ cells ∧ δ / 2 < q i := by
  classical
  exact Finset.mem_filter

private theorem width_nonneg (c : Cell) : 0 ≤ c.width := sub_nonneg.mpr c.left_le_right

private theorem flaggedCellUnion_eq_biUnion {ι : Type*} (cells : Finset ι) (cell : ι → Cell)
    (q : ι → ℝ) (δ : ℝ) :
    flaggedCellUnion cells cell q δ = ⋃ i ∈ flaggedCells cells q δ, (cell i).interval := by
  ext u
  simp only [flaggedCellUnion, mem_ofPred_eq, mem_iUnion, mem_flaggedCells]
  constructor
  · rintro ⟨i, hi, hq, hu⟩
    exact ⟨i, ⟨hi, hq⟩, hu⟩
  · rintro ⟨i, ⟨hi, hq⟩, hu⟩
    exact ⟨i, hi, hq, hu⟩

/-- Disjoint open interiors suffice for additivity of the actual closed-cell
union: removing the two endpoints of each cell changes it only on a null set. -/
public theorem volume_flaggedCellUnion_eq {ι : Type*} (cells : Finset ι) (cell : ι → Cell)
    (q : ι → ℝ) (δ : ℝ)
    (hdisj : (↑cells : Set ι).PairwiseDisjoint (fun i => Ioo (cell i).left (cell i).right)) :
    volume (flaggedCellUnion cells cell q δ) =
      ENNReal.ofReal (∑ i ∈ flaggedCells cells q δ, (cell i).width) := by
  have hae (i : ι) : (cell i).interval =ᵐ[volume] Ioo (cell i).left (cell i).right :=
    Ioo_ae_eq_Icc.symm
  rw [flaggedCellUnion_eq_biUnion, measure_biUnion_finset₀,
    ENNReal.ofReal_sum_of_nonneg (fun i _ => width_nonneg (cell i))]
  · exact Finset.sum_congr rfl (fun i _ => Real.volume_Icc)
  · intro i hi j hj hij
    exact (hdisj (mem_flaggedCells.mp hi).1 (mem_flaggedCells.mp hj).1 hij).aedisjoint.congr
      (hae i) (hae j)
  · exact fun _ _ => measurableSet_Icc.nullMeasurableSet

/-- The number of equal fine subintervals. It is zero exactly for a singleton
when the step bound is positive. -/
@[expose] public noncomputable def fineSubdivisionCount (c : Cell) (ℓ : ℝ) : ℕ :=
  ⌈c.width / ℓ⌉₊

/-- Include both endpoints; a singleton has just one node. -/
@[expose] public noncomputable def fineNodeCount (c : Cell) (ℓ : ℝ) : ℕ :=
  fineSubdivisionCount c ℓ + 1

/-- The genuine ordinate of each uniform fine node. In the singleton case the
sole index is zero and the expression gives the cell's left endpoint. -/
@[expose] public noncomputable def fineNode (c : Cell) (ℓ : ℝ) (j : Fin (fineNodeCount c ℓ)) : ℝ :=
  c.left + (j.val : ℝ) * (c.width / (fineSubdivisionCount c ℓ : ℝ))

private theorem width_div_le_subdivisionCount (c : Cell) (ℓ : ℝ) :
    c.width / ℓ ≤ (fineSubdivisionCount c ℓ : ℝ) := Nat.le_ceil _

/-- A zero-width cell has exactly one node. -/
public theorem fineNodeCount_of_width_eq_zero (c : Cell) (ℓ : ℝ) (hc : c.width = 0) :
    fineNodeCount c ℓ = 1 := by
  simp [fineNodeCount, fineSubdivisionCount, hc]

public theorem fineNode_zero (c : Cell) (ℓ : ℝ) :
    fineNode c ℓ (0 : Fin (fineSubdivisionCount c ℓ + 1)) = c.left := by
  simp [fineNode]

public theorem fineNode_last (c : Cell) {ℓ : ℝ} (hℓ : 0 < ℓ) :
    fineNode c ℓ (Fin.last (fineSubdivisionCount c ℓ)) = c.right := by
  let n := fineSubdivisionCount c ℓ
  change c.left + (n : ℝ) * (c.width / (n : ℝ)) = c.right
  by_cases hn : n = 0
  · have hdiv : c.width / ℓ ≤ 0 := by
      simpa [show fineSubdivisionCount c ℓ = 0 from hn] using width_div_le_subdivisionCount c ℓ
    have hw : c.width ≤ 0 := by simpa using (div_le_iff₀ hℓ).mp hdiv
    have hzero : c.width = 0 := le_antisymm hw (width_nonneg c)
    have heq : c.right = c.left := sub_eq_zero.mp hzero
    simp [hzero, heq]
  · have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
    rw [mul_comm, div_mul_cancel₀ _ hn', Cell.width, add_sub_cancel]

/-- The node indices are in increasing order, with no duplication within a cell. -/
public theorem fineNode_strictMono (c : Cell) {ℓ : ℝ} (hℓ : 0 < ℓ) :
    StrictMono (fineNode c ℓ) := by
  intro i j hij
  have hij' : i.val < j.val := hij
  have hn : 0 < fineSubdivisionCount c ℓ := by
    have := j.isLt
    change j.val < fineSubdivisionCount c ℓ + 1 at this
    omega
  have hw : 0 < c.width := by
    by_contra! hw
    exact hn.ne' (Nat.ceil_eq_zero.mpr (div_nonpos_of_nonpos_of_nonneg hw hℓ.le))
  exact add_lt_add_right
    (mul_lt_mul_of_pos_right (Nat.cast_lt.mpr hij') (div_pos hw (Nat.cast_pos.mpr hn))) _

/-- Every fine node lies in its original closed cell. -/
public theorem fineNode_mem_interval (c : Cell) {ℓ : ℝ} (hℓ : 0 < ℓ)
    (j : Fin (fineNodeCount c ℓ)) : fineNode c ℓ j ∈ c.interval := by
  have hm := (fineNode_strictMono c hℓ).monotone
  let hj : Fin (fineSubdivisionCount c ℓ + 1) := j
  change c.left ≤ fineNode c ℓ hj ∧ fineNode c ℓ hj ≤ c.right
  rw [← fineNode_zero c ℓ, ← fineNode_last c hℓ]
  exact ⟨hm (Fin.zero_le hj), hm (Fin.le_last hj)⟩

/-- Consecutive fine nodes are at most the positive prescribed step apart. -/
public theorem fineNode_succ_sub_le (c : Cell) {ℓ : ℝ} (hℓ : 0 < ℓ)
    (j : Fin (fineSubdivisionCount c ℓ)) :
    fineNode c ℓ j.succ - fineNode c ℓ j.castSucc ≤ ℓ := by
  have hn : (0 : ℝ) < fineSubdivisionCount c ℓ := Nat.cast_pos.mpr (Nat.zero_lt_of_lt j.isLt)
  have hs : c.width / (fineSubdivisionCount c ℓ : ℝ) ≤ ℓ := by
    apply (div_le_iff₀ hn).mpr
    rw [mul_comm]
    exact (div_le_iff₀ hℓ).mp (width_div_le_subdivisionCount c ℓ)
  calc
    _ = c.width / (fineSubdivisionCount c ℓ : ℝ) := by
      simp only [fineNode, Fin.val_succ, Fin.val_castSucc, Nat.cast_succ]
      ring
    _ ≤ ℓ := hs

/-- Incidences, not distinct ordinates across the entire mesh. -/
@[expose] public noncomputable def flaggedNodeIncidences {ι : Type*} (cells : Finset ι)
    (cell : ι → Cell) (q : ι → ℝ) (δ ℓ : ℝ) : ℕ :=
  ∑ i ∈ flaggedCells cells q δ, fineNodeCount (cell i) ℓ

private theorem fullCell_card_mul_le {ι : Type*} (flags : Finset ι) (cell : ι → Cell)
    (last : Option ι) {V : ℝ} (hV : 0 < V)
    (hfull : ∀ i ∈ flags, some i ≠ last → (cell i).width = V) :
    ((flags.card : ℝ) - 1) * V ≤ ∑ i ∈ flags, (cell i).width := by
  classical
  let full := flags.filter (fun i => some i ≠ last)
  have hcount : flags.card ≤ full.card + 1 := by
    have hclipped : (flags.filter (fun i => ¬(some i ≠ last))).card ≤ 1 := by
      apply Finset.card_le_one.mpr
      intro i hi j hj
      have hi' := not_not.mp (Finset.mem_filter.mp hi).2
      have hj' := not_not.mp (Finset.mem_filter.mp hj).2
      exact Option.some.inj (hi'.trans hj'.symm)
    have hsplit := Finset.card_filter_add_card_filter_not (s := flags) (fun i => some i ≠ last)
    change full.card + (flags.filter (fun i => ¬(some i ≠ last))).card = flags.card at hsplit
    omega
  have hcount' : (flags.card : ℝ) ≤ (full.card : ℝ) + 1 := by exact_mod_cast hcount
  calc
    _ ≤ (full.card : ℝ) * V := mul_le_mul_of_nonneg_right (by linarith) hV.le
    _ = ∑ i ∈ full, (cell i).width := by
      rw [← nsmul_eq_mul, ← Finset.sum_const]
      refine Finset.sum_congr rfl (fun i hi => ?_)
      obtain ⟨hi', hn⟩ := Finset.mem_filter.mp hi
      exact (hfull i hi' hn).symm
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun i _ _ => width_nonneg (cell i))

/-- From a bound on the measured union (not on an assumed sum of widths),
bound the flag count and fine-node incidences. The exceptional index need not
be present or flagged; its width upper bound is not needed for the accounting. -/
public theorem flaggedMesh_cost {ι : Type*} (cells : Finset ι) (cell : ι → Cell)
    (q : ι → ℝ) {δ V ℓ B : ℝ} (last : Option ι) (hV : 0 < V) (hℓ : 0 < ℓ)
    (hdisj : (↑cells : Set ι).PairwiseDisjoint (fun i => Ioo (cell i).left (cell i).right))
    (hfull : ∀ i ∈ cells, some i ≠ last → (cell i).width = V)
    (hB : 0 ≤ B) (hvol : volume (flaggedCellUnion cells cell q δ) ≤ ENNReal.ofReal B) :
    ((flaggedCells cells q δ).card : ℝ) ≤ B / V + 1 ∧
      (flaggedNodeIncidences cells cell q δ ℓ : ℝ) ≤ B / ℓ + 2 * (B / V + 1) := by
  let flags := flaggedCells cells q δ
  have hsum : (∑ i ∈ flags, (cell i).width) ≤ B := by
    rw [volume_flaggedCellUnion_eq cells cell q δ hdisj] at hvol
    exact (ENNReal.ofReal_le_ofReal_iff hB).mp hvol
  have hcount : (flags.card : ℝ) ≤ B / V + 1 := by
    have hmul := (fullCell_card_mul_le flags cell last hV
      (fun i hi => hfull i (mem_flaggedCells.mp hi).1)).trans hsum
    have := (le_div_iff₀ hV).mpr hmul
    linarith
  refine ⟨hcount, ?_⟩
  change ((∑ i ∈ flags, fineNodeCount (cell i) ℓ : ℕ) : ℝ) ≤ _
  rw [Nat.cast_sum]
  calc
    _ ≤ ∑ i ∈ flags, ((cell i).width / ℓ + 2) := by
      refine Finset.sum_le_sum (fun i _ => ?_)
      have hc := Nat.ceil_lt_add_one (div_nonneg (width_nonneg (cell i)) hℓ.le)
      simp only [fineNodeCount, fineSubdivisionCount, Nat.cast_succ]
      linarith
    _ = (∑ i ∈ flags, (cell i).width) / ℓ + 2 * (flags.card : ℝ) := by
      rw [Finset.sum_add_distrib, ← Finset.sum_div, Finset.sum_const, nsmul_eq_mul, mul_comm _ 2]
    _ ≤ _ := add_le_add (div_le_div_of_nonneg_right hsum hℓ.le)
      (mul_le_mul_of_nonneg_left hcount (by norm_num))

/-- The finite real upper bound from the existing screen, taken at moment `m = k`. -/
@[expose] public noncomputable def cubeScreenBudget (G H k : ℕ) (t δ : ℝ) : ℝ :=
  8 * Real.pi * t * (((4 * (k : ℝ) - 2) ^ (4 * 2 ^ k) *
    (4 * 2 ^ k : ℝ) ^ (k + 2)) /
    (((2 * G + 1 : ℕ) : ℝ) * G * (H : ℝ) ^ k * (δ / 4) ^ 2)) ^ k

/-- Apply the signed-cube screen to the source mesh on `[t + ℓ, 5t/4 - ℓ]`.
The full cells have width `X^k`, with at most one clipped last cell. The
estimate and width hypotheses are those of the actual normalized cube screen. -/
public theorem flaggedCubeMesh_cost {ι : Type*} {G H k : ℕ} (d : ℤ) (a : Fin G → ℤ → ℝ)
    {X t δ ℓ : ℝ} (hG : 0 < G) (hH : 0 < H) (hd : 0 ≤ d) (hX : 1 ≤ X)
    (hk : 1 ≤ k) (ht : X ^ (k * (4 * 2 ^ k)) < t) (hδ : 0 < δ) (hℓ : 0 < ℓ)
    (ha : ∀ g p, 0 ≤ a g p ∧ a g p ≤ 1)
    (haL : ∀ g p, a g p ≠ 0 → Real.exp (-8) * X ≤ (p : ℝ))
    (haX : ∀ g p, a g p ≠ 0 → ((p + (g.val : ℤ) + 1 + d : ℤ) : ℝ) ≤ X)
    (cells : Finset ι) (cell : ι → Cell) (q : ι → ℝ) (last : Option ι)
    (hinside : ∀ i ∈ cells, (cell i).interval ⊆ Icc (t + ℓ) (5 * t / 4 - ℓ))
    (hdisj : (↑cells : Set ι).PairwiseDisjoint (fun i => Ioo (cell i).left (cell i).right))
    (hfull : ∀ i ∈ cells, some i ≠ last → (cell i).width = X ^ k)
    (_hclipped : ∀ i ∈ cells, some i = last → (cell i).width ≤ X ^ k)
    (hwidth : ∀ i ∈ cells, frequencyBound d H k X * (cell i).width ≤ δ / 4)
    (herror : ∀ i ∈ cells,
      |(survivingSum d (cubeWeight (H := H) (k := k) a) (cell i).midpoint).re - q i| ≤ δ / 16) :
    ((flaggedCells cells q δ).card : ℝ) ≤ cubeScreenBudget G H k t δ / X ^ k + 1 ∧
      (flaggedNodeIncidences cells cell q δ ℓ : ℝ) ≤
        cubeScreenBudget G H k t δ / ℓ + 2 * (cubeScreenBudget G H k t δ / X ^ k + 1) := by
  have hX' : 0 < X := zero_lt_one.trans_le hX
  have ht' : 0 < t := (pow_pos hX' _).trans ht
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hbase : 0 ≤ 4 * (k : ℝ) - 2 := by linarith
  have hB : 0 ≤ cubeScreenBudget G H k t δ := by
    unfold cubeScreenBudget
    positivity
  have houter (i : ι) (hi : i ∈ cells) : (cell i).interval ⊆ Icc t (5 * t / 4) := by
    intro u hu
    obtain ⟨hl, hr⟩ := hinside i hi hu
    exact ⟨by linarith, by linarith⟩
  have hvol := (flaggedCellUnion_screen d a hG hH hd hX hk ht hδ ha haL haX
    cells cell q houter hwidth herror).2.2
  exact flaggedMesh_cost cells cell q last (pow_pos hX' _) hℓ hdisj hfull hB hvol

end Masullo.FlaggedMeshCost
