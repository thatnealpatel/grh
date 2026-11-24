module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Interval
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Powerset
import Mathlib.Tactic.NormNum

/-!
# A finite separating family of masks

Source: `.godel/alice/three-local-directions.md:28–42` at scan pin `1730648dc8b4`,
the mask-family step in the partially supported lift. This proves the exact
finite selection bound for a given family of required/forbidden pairs. It does
not count the arithmetic prescriptions or prove the subsequent lift price.

Owning check session: `01a20dea-9bff-7af6-950c-47bd0e521e1e`.
-/

open scoped BigOperators

namespace Masullo.PuncturedMaskFamily

variable {α : Type*} [Fintype α]

section

variable [DecidableEq α]

private def badMasks (J F : Finset α) : Finset (Finset α) := (Finset.Icc J Fᶜ)ᶜ

private theorem mem_badMasks {J F T : Finset α} :
    T ∈ badMasks J F ↔ ¬(J ⊆ T ∧ Disjoint T F) := by
  simp only [badMasks, Finset.mem_compl, Finset.mem_Icc, le_compl_iff_disjoint_right]

private theorem card_badMasks_le (J F : Finset α) {m : ℕ}
    (hJF : Disjoint J F) (hm : J.card + F.card ≤ m) :
    ((badMasks J F).card : ℝ) ≤ (Fintype.card (Finset α) : ℝ) * (1 - ((2 : ℝ) ^ m)⁻¹) := by
  have hsub : J ⊆ Fᶜ := le_compl_iff_disjoint_right.mpr hJF
  have hJ : J.card ≤ Fᶜ.card := Finset.card_le_card hsub
  have hF : F.card ≤ Fintype.card α := Finset.card_le_univ _
  have hwidth : Fintype.card α ≤ Fᶜ.card - J.card + m := by
    rw [Finset.card_compl] at hJ ⊢
    omega
  have hone : (1 : ℝ) ≤ 2 := by norm_num
  -- In the interval of good masks, only the coordinates of `Fᶜ \ J` are free.
  have hgood : (Fintype.card (Finset α) : ℝ) * ((2 : ℝ) ^ m)⁻¹ ≤
      ((Finset.Icc J Fᶜ).card : ℝ) := by
    apply (mul_inv_le_iff₀ (pow_pos (zero_lt_one.trans_le hone) m)).mpr
    rw [Fintype.card_finset, Finset.card_Icc_finset hsub]
    norm_num only [Nat.cast_pow, Nat.cast_ofNat]
    rw [← pow_add]
    exact pow_le_pow_right₀ hone hwidth
  rw [badMasks, Finset.card_compl, Nat.cast_sub (Finset.card_le_univ _), mul_sub, mul_one]
  exact sub_le_sub_left hgood _

end

/-- If `P * (1 - 2⁻ᵐ)^k < 1`, at most `k` masks suffice to contain the required set
and avoid the forbidden set for each of at most `P` prescriptions of width at most `m`. -/
public theorem exists_separating_masks (pairs : Finset (Finset α × Finset α))
    {P m k : ℕ} (_hk : 1 ≤ k) (hP : pairs.card ≤ P)
    (hdisj : ∀ p ∈ pairs, Disjoint p.1 p.2)
    (hwidth : ∀ p ∈ pairs, p.1.card + p.2.card ≤ m)
    (hprob : (P : ℝ) * (1 - ((2 : ℝ) ^ m)⁻¹) ^ k < 1) :
    ∃ masks : Finset (Finset α), masks.card ≤ k ∧
      ∀ p ∈ pairs, ∃ T ∈ masks, p.1 ⊆ T ∧ Disjoint T p.2 := by
  classical
  let q : ℝ := 1 - ((2 : ℝ) ^ m)⁻¹
  let D : ℝ := Fintype.card (Finset α)
  have hq : 0 ≤ q := sub_nonneg.mpr (inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num)))
  have hDk : 0 < D ^ k := pow_pos (Nat.cast_pos.mpr Fintype.card_pos) k
  -- A tuple misses a prescription exactly when every slot is a bad mask for it.
  let badTuples (p : Finset α × Finset α) : Finset (Fin k → Finset α) :=
    Fintype.piFinset fun _ => badMasks p.1 p.2
  have hslot (p) (hp : p ∈ pairs) : ((badTuples p).card : ℝ) ≤ D ^ k * q ^ k := by
    have hcard : (badTuples p).card = (badMasks p.1 p.2).card ^ k := by
      simp [badTuples, Fintype.card_piFinset]
    rw [hcard, Nat.cast_pow, ← mul_pow]
    exact pow_le_pow_left₀ (Nat.cast_nonneg _) (card_badMasks_le _ _ (hdisj p hp) (hwidth p hp)) k
  have htotal : ((Finset.univ : Finset (Fin k → Finset α)).card : ℝ) = D ^ k := by
    rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Nat.cast_pow]
  have hbad : ((pairs.biUnion badTuples).card : ℝ) ≤ D ^ k * ((P : ℝ) * q ^ k) := by
    calc
      _ ≤ ∑ p ∈ pairs, ((badTuples p).card : ℝ) := by
        rw [← Nat.cast_sum]
        exact Nat.cast_le.mpr Finset.card_biUnion_le
      _ ≤ ∑ _p ∈ pairs, D ^ k * q ^ k := Finset.sum_le_sum hslot
      _ = (pairs.card : ℝ) * (D ^ k * q ^ k) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (P : ℝ) * (D ^ k * q ^ k) :=
        mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hP) (mul_nonneg hDk.le (pow_nonneg hq _))
      _ = _ := by ac_rfl
  have hstrict : ((pairs.biUnion badTuples).card : ℝ) <
      ((Finset.univ : Finset (Fin k → Finset α)).card : ℝ) := by
    rw [htotal]
    simpa only [mul_one] using hbad.trans_lt (mul_lt_mul_of_pos_left hprob hDk)
  have hnot : ¬ (Finset.univ : Finset (Fin k → Finset α)) ⊆ pairs.biUnion badTuples :=
    fun h => (Nat.cast_lt.mp hstrict).not_ge (Finset.card_le_card h)
  obtain ⟨t, -, ht⟩ := Finset.not_subset.mp hnot
  -- The image removes repeated masks without losing any witness.
  refine ⟨Finset.univ.image t, Finset.card_image_le.trans_eq (by simp), ?_⟩
  intro p hp
  by_contra hnone
  refine ht (Finset.mem_biUnion.mpr ⟨p, hp, Fintype.mem_piFinset.mpr ?_⟩)
  intro i
  exact mem_badMasks.mpr fun hhit =>
    hnone ⟨t i, Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩, hhit⟩

end Masullo.PuncturedMaskFamily
