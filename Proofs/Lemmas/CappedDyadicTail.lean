module

public import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Capped dyadic tail bound

A two-sided height count and a pointwise amplitude bound on each dyadic band
control the absolute capped tail. The sum is over indices, not absolute heights:
distinct zeros with the same absolute height still contribute separately.
-/

open scoped BigOperators

namespace Masullo

/-- The strict lower and closed upper bounds assign an internal cutoff to the
band ending there, and exclude `|t| = 8192` altogether. -/
public def cappedDyadicBand (j : ℕ) (t : ℝ) : Prop :=
  (8192 : ℝ) * 2 ^ j < |t| ∧ |t| ≤ 8192 * 2 ^ (j + 1)

/-- Each height of the strict tail lies in exactly one band. -/
public theorem existsUnique_cappedDyadicBand {t : ℝ} (ht : 8192 < |t|) :
    ∃! j, cappedDyadicBand j t := by
  classical
  have hmono : Monotone (fun j : ℕ ↦ (8192 : ℝ) * 2 ^ j) := by
    intro i j hij
    have hpow : StrictMono (fun n : ℕ ↦ (2 : ℝ) ^ n) :=
      pow_right_strictMono₀ (by norm_num)
    exact mul_le_mul_of_nonneg_left (hpow.monotone hij) (by norm_num)
  have hex : ∃ j : ℕ, |t| ≤ (8192 : ℝ) * 2 ^ (j + 1) := by
    obtain ⟨j, hj⟩ := pow_unbounded_of_one_lt (|t| / 8192) (show (1 : ℝ) < 2 by norm_num)
    refine ⟨j, ?_⟩
    exact ((div_lt_iff₀ (by norm_num : (0 : ℝ) < 8192)).mp hj).le.trans (by
      rw [mul_comm ((2 : ℝ) ^ j)]
      exact hmono (Nat.le_succ j))
  refine ⟨Nat.find hex, ⟨?_, Nat.find_spec hex⟩, ?_⟩
  · cases h : Nat.find hex with
    | zero => simpa using ht
    | succ j => exact lt_of_not_ge (Nat.find_min hex (h ▸ Nat.lt_succ_self j))
  · intro k hk
    refine le_antisymm ?_ (Nat.find_min' hex hk.2)
    apply le_of_not_gt
    intro h
    exact (not_lt_of_ge ((Nat.find_spec hex).trans (hmono h))) hk.1

private theorem cappedDyadicBand_linear_le (j : ℕ) : (12 : ℝ) + j ≤ 12 * 2 ^ j := by
  induction j with
  | zero => norm_num
  | succ j ih =>
    rw [Nat.cast_succ, pow_succ]
    have hpow : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
    linarith

/-- The strict capped tail of nonnegative terms is summable and has the stated
bound. A count for every finite subset of a band suffices; the index type need
not carry an enumeration or a decidable equality. -/
public theorem cappedDyadicTail_bound {ι : Type*} (height weight amplitude : ι → ℝ)
    (htail : ∀ i, 8192 < |height i|) (hw : ∀ i, 0 ≤ weight i) (ha : ∀ i, 0 ≤ amplitude i)
    (hcount : ∀ (j : ℕ) (A : Finset ι), (∀ i ∈ A, cappedDyadicBand j (height i)) →
      (∑ i ∈ A, weight i) ≤ 163840 * 2 ^ j * (12 + (j : ℝ)))
    (hamp : ∀ j i, cappedDyadicBand j (height i) →
      amplitude i ≤ (2 / 10 ^ 13 : ℝ) * (1 / 1024 : ℝ) ^ j) :
    Summable (fun i ↦ weight i * amplitude i) ∧
      (∑' i, weight i * amplitude i) ≤ (425984 : ℝ) / 10 ^ 12 ∧
      (425984 : ℝ) / 10 ^ 12 < 1 / 1000 := by
  classical
  let band (i : ι) : ℕ := Classical.choose (existsUnique_cappedDyadicBand (htail i)).exists
  have hband (i : ι) : cappedDyadicBand (band i) (height i) :=
    Classical.choose_spec (existsUnique_cappedDyadicBand (htail i)).exists
  let B (j : ℕ) : ℝ := 163840 * (2 / 10 ^ 13) * 12 * (1 / 256) ^ j
  have hB : HasSum B (163840 * (2 / 10 ^ 13) * 12 * (1 - 1 / 256)⁻¹) :=
    (hasSum_geometric_of_lt_one (r := 1 / 256) (by norm_num) (by norm_num)).mul_left _
  have hblock (j : ℕ) (A : Finset ι) (hA : ∀ i ∈ A, band i = j) :
      (∑ i ∈ A, weight i * amplitude i) ≤ B j := by
    have hj (i : ι) (hi : i ∈ A) : cappedDyadicBand j (height i) := hA i hi ▸ hband i
    let q : ℝ := (2 / 10 ^ 13 : ℝ) * (1 / 1024 : ℝ) ^ j
    have hq : 0 ≤ q := by dsimp [q]; positivity
    calc
      _ ≤ ∑ i ∈ A, weight i * q :=
        Finset.sum_le_sum fun i hi ↦ mul_le_mul_of_nonneg_left (hamp j i (hj i hi)) (hw i)
      _ = (∑ i ∈ A, weight i) * q := by rw [Finset.sum_mul]
      _ ≤ (163840 * 2 ^ j * (12 + (j : ℝ))) * q :=
        mul_le_mul_of_nonneg_right (hcount j A hj) hq
      _ ≤ (163840 * 2 ^ j * (12 * 2 ^ j)) * q := by
        apply mul_le_mul_of_nonneg_right _ hq
        exact mul_le_mul_of_nonneg_left (cappedDyadicBand_linear_le j) (by positivity)
      _ = B j := by
        have hbase : (2 * 2 * (1 / 1024) : ℝ) = 1 / 256 := by norm_num
        have hpow : (2 : ℝ) ^ j * 2 ^ j * (1 / 1024) ^ j = (1 / 256) ^ j := by
          rw [← mul_pow, ← mul_pow, hbase]
        dsimp only [B, q]
        rw [← hpow]
        ring
  have hfinite (A : Finset ι) : (∑ i ∈ A, weight i * amplitude i) ≤ (425984 : ℝ) / 10 ^ 12 := by
    calc
      _ = ∑ j ∈ A.image band, ∑ i ∈ A with band i = j, weight i * amplitude i :=
        (Finset.sum_fiberwise_of_maps_to (fun _ hi ↦ Finset.mem_image_of_mem band hi) _).symm
      _ ≤ ∑ j ∈ A.image band, B j :=
        Finset.sum_le_sum fun j _ ↦ hblock j _ (fun i hi ↦ (Finset.mem_filter.mp hi).2)
      _ ≤ ∑' j, B j := hB.summable.sum_le_tsum _ (fun j _ ↦ by dsimp [B]; positivity)
      _ ≤ _ := by rw [hB.tsum_eq]; norm_num
  have hnonneg (i : ι) : 0 ≤ weight i * amplitude i := mul_nonneg (hw i) (ha i)
  have hs := summable_of_sum_le hnonneg hfinite
  exact ⟨hs, hs.tsum_le_of_sum_le hfinite, by norm_num⟩

/-- Version for a supplied finite enumeration of every band. Membership is
exactly the height predicate, so no index in a band can be omitted. -/
public theorem cappedDyadicTail_bound_of_bands {ι : Type*} (height weight amplitude : ι → ℝ)
    (htail : ∀ i, 8192 < |height i|) (hw : ∀ i, 0 ≤ weight i) (ha : ∀ i, 0 ≤ amplitude i)
    (bands : ℕ → Finset ι) (hmem : ∀ j i, i ∈ bands j ↔ cappedDyadicBand j (height i))
    (hcount : ∀ j, (∑ i ∈ bands j, weight i) ≤ 163840 * 2 ^ j * (12 + (j : ℝ)))
    (hamp : ∀ j i, cappedDyadicBand j (height i) →
      amplitude i ≤ (2 / 10 ^ 13 : ℝ) * (1 / 1024 : ℝ) ^ j) :
    Summable (fun i ↦ weight i * amplitude i) ∧
      (∑' i, weight i * amplitude i) ≤ (425984 : ℝ) / 10 ^ 12 ∧
      (425984 : ℝ) / 10 ^ 12 < 1 / 1000 := by
  refine cappedDyadicTail_bound height weight amplitude htail hw ha (fun j A hA ↦ ?_) hamp
  exact (Finset.sum_le_sum_of_subset_of_nonneg (fun i hi ↦ (hmem j i).2 (hA i hi))
    (fun i _ _ ↦ hw i)).trans (hcount j)

end Masullo
