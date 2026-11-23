module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-! # The central-slice obstruction for positive tuple weights

Source: `db760d6f:.godel/bob/dyadic-prime-pair-moments.md`, lines 21–29 (the
central-cell argument for the signed test (1)). Application:
`ec81e8cb:.godel/bob/last-slot-residues.md`, lines 47–51.
Owning check session: `01a208d1-f4a1-7e74-9d68-6b0dfb6d9df9`.

For a fixed prime shift in the source, take the atoms to be the labeled ordered
`h`-tuples of starts, with weight `∏ i, w (p i)` and frequency `∑ i, λ (p i)`.
In particular, the indices are not quotiented by frequency or by permutation.
The total mass is `A_d^h`; normalizing each start's weight by `A_d` as in the
last-slot note rescales every pair mass by `A_d^(-2h)`. The finite estimate applies
once the cell cover and the bound on the full exact-zero mass are supplied. Its
central slice belongs to the positive part of the signed test; an upper bound on
mass discarded by the last-slot gate is a separate input for retaining this slice.
The estimates below give neither a count of mass-rich shifts nor an asymptotic or
a sign for the full signed sum.
-/

open scoped BigOperators

namespace Masullo.PositiveTupleCore

/-- The triangular cosine multiplier on the window `t * |ν| < 2π`. -/
@[expose] public noncomputable def multiplier (t ν : ℝ) : ℝ :=
  (1 - t * |ν| / (2 * Real.pi)) * Real.cos (t * ν)

/-- All ordered pairs at frequency difference zero, including distinct atom indices
whose frequencies agree. -/
@[expose] public noncomputable def zeroMass {ι : Type*} (A : Finset ι)
    (frequency weight : ι → ℝ) : ℝ := by
  classical
  exact ∑ p ∈ (A ×ˢ A).filter (fun p ↦ frequency p.1 = frequency p.2), weight p.1 * weight p.2

/-- The signed weighted mass on the central slice `0 < t * |ν| ≤ 1/2`. -/
@[expose] public noncomputable def centralMass {ι : Type*} (A : Finset ι)
    (frequency weight : ι → ℝ) (t : ℝ) : ℝ := by
  classical
  exact ∑ p ∈ (A ×ˢ A).filter (fun p ↦
      0 < t * |frequency p.1 - frequency p.2| ∧ t * |frequency p.1 - frequency p.2| ≤ 1 / 2),
    weight p.1 * weight p.2 * multiplier t (frequency p.1 - frequency p.2)

/-- The sum of absolute contributions on the whole nonzero window `0 < t * |ν| < 2π`.
This is not the absolute value of the signed sum. -/
@[expose] public noncomputable def absoluteTest {ι : Type*} (A : Finset ι)
    (frequency weight : ι → ℝ) (t : ℝ) : ℝ := by
  classical
  exact ∑ p ∈ (A ×ˢ A).filter (fun p ↦
      0 < t * |frequency p.1 - frequency p.2| ∧ t * |frequency p.1 - frequency p.2| < 2 * Real.pi),
    |weight p.1 * weight p.2 * multiplier t (frequency p.1 - frequency p.2)|

private theorem half_le_multiplier {t ν : ℝ} (ht : 0 < t) (hν : t * |ν| ≤ 1 / 2) :
    1 / 2 ≤ multiplier t ν := by
  have habs : |t * ν| ≤ 1 / 2 := by simpa only [abs_mul, abs_of_pos ht] using hν
  have hsq : (t * ν) ^ 2 ≤ (1 / 2 : ℝ) ^ 2 := by
    rw [← sq_abs (t * ν)]
    exact pow_le_pow_left₀ (abs_nonneg _) habs 2
  have hcos : 7 / 8 ≤ Real.cos (t * ν) := by
    linarith only [hsq, Real.one_sub_sq_div_two_le_cos (x := t * ν)]
  have hfrac : t * |ν| / (2 * Real.pi) ≤ 1 / 4 := by
    apply (div_le_iff₀ (mul_pos two_pos Real.pi_pos)).2
    linarith only [hν, Real.pi_gt_three]
  have htri : 3 / 4 ≤ 1 - t * |ν| / (2 * Real.pi) := by linarith only [hfrac]
  calc
    (1 / 2 : ℝ) ≤ (3 / 4) * (7 / 8) := by norm_num
    _ ≤ multiplier t ν :=
      mul_le_mul htri hcos (by norm_num) ((by norm_num : (0 : ℝ) ≤ 3 / 4).trans htri)

private theorem mass_sq_div_card_le_sameCell {ι κ : Type*} [DecidableEq κ]
    (A : Finset ι) (C : Finset κ)
    (hC : C.Nonempty) (assign : ι → κ) (hassign : ∀ i ∈ A, assign i ∈ C) (weight : ι → ℝ) :
    (∑ i ∈ A, weight i) ^ 2 / (C.card : ℝ) ≤
      ∑ p ∈ (A ×ˢ A).filter (fun p ↦ assign p.1 = assign p.2), weight p.1 * weight p.2 := by
  classical
  let fiber (c : κ) := A.filter (fun i ↦ assign i = c)
  let m (c : κ) := ∑ i ∈ fiber c, weight i
  let same := (A ×ˢ A).filter (fun p ↦ assign p.1 = assign p.2)
  have hm : ∑ c ∈ C, m c = ∑ i ∈ A, weight i := Finset.sum_fiberwise_of_maps_to hassign weight
  have hfiber (c : κ) : same.filter (fun p ↦ assign p.1 = c) = fiber c ×ˢ fiber c := by
    ext p
    simp only [same, fiber, Finset.mem_filter, Finset.mem_product]
    constructor
    · rintro ⟨⟨⟨hi, hj⟩, heq⟩, hc⟩
      exact ⟨⟨hi, hc⟩, ⟨hj, heq.symm.trans hc⟩⟩
    · rintro ⟨⟨hi, hic⟩, ⟨hj, hjc⟩⟩
      exact ⟨⟨⟨hi, hj⟩, hic.trans hjc.symm⟩, hic⟩
  have hm2 : (∑ c ∈ C, m c ^ 2) = ∑ p ∈ same, weight p.1 * weight p.2 := calc
    _ = ∑ c ∈ C, ∑ p ∈ same with assign p.1 = c, weight p.1 * weight p.2 := by
      apply Finset.sum_congr rfl
      intro c _
      rw [hfiber, Finset.sum_product, pow_two]
      simp only [m]
      rw [Finset.sum_mul]
      simp only [Finset.mul_sum]
    _ = _ := Finset.sum_fiberwise_of_maps_to
      (fun p hp ↦ hassign p.1 (Finset.mem_product.mp (Finset.mem_filter.mp hp).1).1) _
  have hN : (0 : ℝ) < C.card := by exact_mod_cast Finset.card_pos.mpr hC
  have hcs : (∑ c ∈ C, m c) ^ 2 ≤ (C.card : ℝ) * (∑ c ∈ C, m c ^ 2) := by
    simpa using Finset.sum_mul_sq_le_sq_mul_sq C (fun _ ↦ (1 : ℝ)) m
  exact (div_le_iff₀ hN).2 (by simpa only [hm, hm2, mul_comm] using hcs)

/-- If the atom frequencies are covered by a nonempty finite family of cells of
absolute diameter at most `1 / (2 * t)`, the central slice has at least half the
cell Cauchy–Schwarz budget after removing the exact-zero mass. The cells may overlap.
In particular this applies to the one-sided tuple frequencies in the source;
the bound only uses differences and does not require their nonnegativity. -/
public theorem centralMass_lower_bound {ι κ : Type*} (A : Finset ι) (frequency weight : ι → ℝ)
    (hw : ∀ i ∈ A, 0 ≤ weight i) {t : ℝ} (ht : 0 < t)
    (C : Finset κ) (hC : C.Nonempty) (cell : κ → Set ℝ)
    (hcover : ∀ i ∈ A, ∃ c ∈ C, frequency i ∈ cell c)
    (hdiam : ∀ c ∈ C, ∀ x ∈ cell c, ∀ y ∈ cell c, |x - y| ≤ 1 / (2 * t)) :
    ((∑ i ∈ A, weight i) ^ 2 / (C.card : ℝ) - zeroMass A frequency weight) / 2 ≤
      centralMass A frequency weight t := by
  classical
  let fallback : κ := Classical.choose hC
  -- Choose just one covering cell per atom, so overlaps cannot inflate the pair mass.
  let assign (i : ι) : κ := if hi : i ∈ A then (hcover i hi).choose else fallback
  have ha (i : ι) (hi : i ∈ A) : assign i ∈ C ∧ frequency i ∈ cell (assign i) := by
    simpa only [assign, dite_eq_left hi] using (hcover i hi).choose_spec
  let P := A ×ˢ A
  let same := P.filter (fun p ↦ assign p.1 = assign p.2)
  let ν (p : ι × ι) := frequency p.1 - frequency p.2
  let w (p : ι × ι) := weight p.1 * weight p.2
  let z (p : ι × ι) := frequency p.1 = frequency p.2
  let central := P.filter (fun p ↦ 0 < t * |ν p| ∧ t * |ν p| ≤ 1 / 2)
  have hwP (p : ι × ι) (hp : p ∈ P) : 0 ≤ w p :=
    mul_nonneg (hw p.1 (Finset.mem_product.mp hp).1) (hw p.2 (Finset.mem_product.mp hp).2)
  have hcs : (∑ i ∈ A, weight i) ^ 2 / (C.card : ℝ) ≤ ∑ p ∈ same, w p :=
    mass_sq_div_card_le_sameCell A C hC assign (fun i hi ↦ (ha i hi).1) weight
  have hzero : ∑ p ∈ same.filter z, w p ≤ zeroMass A frequency weight := by
    change ∑ p ∈ same.filter z, w p ≤ ∑ p ∈ P.filter z, w p
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro p hp
      rcases Finset.mem_filter.mp hp with ⟨hs, hz⟩
      exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hs).1, hz⟩
    · exact fun p hp _ ↦ hwP p (Finset.mem_filter.mp hp).1
  have hnear : same.filter (fun p ↦ ¬z p) ⊆ central := by
    intro p hp
    rcases Finset.mem_filter.mp hp with ⟨hs, hne⟩
    rcases Finset.mem_filter.mp hs with ⟨hP, heq⟩
    rcases Finset.mem_product.mp hP with ⟨hi, hj⟩
    have hν : |ν p| ≤ 1 / (2 * t) :=
      hdiam (assign p.1) (ha p.1 hi).1 (frequency p.1) (ha p.1 hi).2 (frequency p.2)
        (heq.symm ▸ (ha p.2 hj).2)
    have hscaled : |ν p| * (2 * t) ≤ 1 := (le_div_iff₀ (mul_pos two_pos ht)).1 hν
    exact Finset.mem_filter.mpr
      ⟨hP, mul_pos ht (abs_pos.mpr (sub_ne_zero.mpr hne)), by nlinarith only [hscaled]⟩
  have hcentral : ∑ p ∈ same.filter (fun p ↦ ¬z p), w p ≤ 2 * centralMass A frequency weight t := by
    change _ ≤ 2 * ∑ p ∈ central, w p * multiplier t (ν p)
    calc
      _ ≤ ∑ p ∈ central, w p :=
        Finset.sum_le_sum_of_subset_of_nonneg hnear (fun p hp _ ↦ hwP p (Finset.mem_filter.mp hp).1)
      _ ≤ _ := by
        rw [Finset.mul_sum]
        apply Finset.sum_le_sum
        intro p hp
        rcases Finset.mem_filter.mp hp with ⟨hP, _, hpν⟩
        have h := mul_le_mul_of_nonneg_left (half_le_multiplier ht hpν) (hwP p hP)
        linarith only [h]
  have hsplit := Finset.sum_filter_add_sum_filter_not same z w
  linarith only [hcs, hzero, hcentral, hsplit]

/-- The same budget lower-bounds the termwise absolute test on the full nonzero
window. In particular, summing absolute contributions cannot exploit cancellation
between the central slice and the negative portion of the multiplier. -/
public theorem absoluteTest_lower_bound {ι κ : Type*} (A : Finset ι) (frequency weight : ι → ℝ)
    (hw : ∀ i ∈ A, 0 ≤ weight i) {t : ℝ} (ht : 0 < t)
    (C : Finset κ) (hC : C.Nonempty) (cell : κ → Set ℝ)
    (hcover : ∀ i ∈ A, ∃ c ∈ C, frequency i ∈ cell c)
    (hdiam : ∀ c ∈ C, ∀ x ∈ cell c, ∀ y ∈ cell c, |x - y| ≤ 1 / (2 * t)) :
    ((∑ i ∈ A, weight i) ^ 2 / (C.card : ℝ) - zeroMass A frequency weight) / 2 ≤
      absoluteTest A frequency weight t := by
  refine (centralMass_lower_bound A frequency weight hw ht C hC cell hcover hdiam).trans ?_
  classical
  unfold centralMass absoluteTest
  refine (Finset.sum_le_sum (fun _ _ ↦ le_abs_self _)).trans ?_
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ ↦ abs_nonneg _)
  intro p hp
  rcases Finset.mem_filter.mp hp with ⟨hP, hpos, hbound⟩
  exact Finset.mem_filter.mpr ⟨hP, hpos, hbound.trans_lt (by linarith only [Real.pi_gt_three])⟩

end Masullo.PositiveTupleCore
