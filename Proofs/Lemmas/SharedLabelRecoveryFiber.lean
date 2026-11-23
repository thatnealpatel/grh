module

public import Lemmas.SignedRowRecovery
public import Mathlib.NumberTheory.Divisors
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Data.Int.Interval
import Mathlib.RingTheory.Int.Basic
import Mathlib.Tactic.Linarith

/-!
# Off-diagonal shared-label recovery fibers

Source: `fd54047c:.godel/alice/shared-row-labels.md`, lines 11–17, as used in
`d15218cc:.godel/alice/overlapping-lift-count.md`, lines 54–56.
Owning check session: `01a20938-230d-71be-9082-772ff1e0dec6`.

This is the exact finite price at one fixed list and one fixed off-diagonal
product `w = hᵢ yⱼ`. It counts distinct original primitive columns, not
realizations, using the original signed row at position `i` for column recovery.
Neither product needs to be squarefree. No smoothness, fixed-mask, or
asymptotic estimates are included.
-/

open scoped BigOperators

namespace SharedLabelRecoveryFiber

/-- A realization at two list positions, with original row `(Fi * hi, yi)`
used for recovery and `Fj * hj` the first coordinate at the second position.
`p` is the original column, not a pair of label factors. -/
public structure Realization (q Fi Fj w : ℕ) (H Z W : ℝ) (p : ℕ × ℕ) where
  hi : ℕ
  hj : ℕ
  yi : ℕ
  yj : ℕ
  t : ℤ
  gap : ℤ
  cross_product : hi * yj = w
  xi_pos : 0 < Fi * hi
  xj_pos : 0 < Fj * hj
  yi_pos : 0 < yi
  det : (Fi : ℤ) * w - (Fj : ℤ) * (hj * yi : ℕ) = (q : ℤ) * t
  tag_width : |(t : ℝ)| ≤ W
  c_pos : 0 < p.1
  d_pos : 0 < p.2
  primitive : p.1.Coprime p.2
  d_le : (p.2 : ℝ) ≤ Z
  not_dvd_xi : ¬ q ∣ Fi * hi
  signed_row : (p.1 : ℤ) * (Fi * hi : ℕ) - (p.2 : ℤ) * yi = (q : ℤ) * gap
  gap_bound : |(gap : ℝ)| ≤ H
  cutoff : 4 * H * Z ≤ ((Fi * hi : ℕ) : ℝ)

private theorem Realization.column_eq {q Fi Fj w : ℕ} {H Z W : ℝ} {p p' : ℕ × ℕ}
    (hq : q.Prime) (a : Realization q Fi Fj w H Z W p)
    (b : Realization q Fi Fj w H Z W p') (hhi : a.hi = b.hi) (hyi : a.yi = b.yi) :
    p = p' := by
  have hrow' : (p'.1 : ℤ) * (Fi * a.hi : ℕ) - (p'.2 : ℤ) * a.yi = (q : ℤ) * b.gap := by
    rw [hhi, hyi]
    exact b.signed_row
  obtain ⟨hc, hd⟩ := SignedRowRecovery.primitiveColumn_eq_of_signed_gaps
    hq a.not_dvd_xi a.xi_pos a.yi_pos a.c_pos a.d_pos b.c_pos b.d_pos
    a.primitive b.primitive a.d_le b.d_le a.signed_row hrow'
    a.gap_bound b.gap_bound a.cutoff
  exact Prod.ext hc hd

/-- The signed determinant tags in the width window whose numerator is
positive and exactly divisible by `Fj`. -/
public noncomputable def admissibleTags (q Fi Fj w : ℕ) (W : ℝ) : Finset ℤ :=
  (Finset.Icc (-⌊W⌋) ⌊W⌋).filter fun t ↦
    0 < (Fi : ℤ) * w - (q : ℤ) * t ∧ (Fj : ℤ) ∣ (Fi : ℤ) * w - (q : ℤ) * t

public theorem mem_admissibleTags {q Fi Fj w : ℕ} {W : ℝ} {t : ℤ} :
    t ∈ admissibleTags q Fi Fj w W ↔
      |(t : ℝ)| ≤ W ∧ 0 < (Fi : ℤ) * w - (q : ℤ) * t ∧
        (Fj : ℤ) ∣ (Fi : ℤ) * w - (q : ℤ) * t := by
  simp only [admissibleTags, Finset.mem_filter, Finset.mem_Icc, abs_le]
  rw [neg_le, Int.le_floor, Int.le_floor, Int.cast_neg, neg_le]

/-- For an admissible tag, the exact positive quotient, as a natural number. -/
@[expose] public def recoveryQuotient (q Fi Fj w : ℕ) (t : ℤ) : ℕ :=
  (((Fi : ℤ) * w - (q : ℤ) * t) / (Fj : ℤ)).toNat

public theorem recoveryQuotient_pos {q Fi Fj w : ℕ} {W : ℝ} {t : ℤ}
    (ht : t ∈ admissibleTags q Fi Fj w W) : 0 < recoveryQuotient q Fi Fj w t := by
  obtain ⟨_, hpos, hdvd⟩ := mem_admissibleTags.mp ht
  have h := Int.ediv_pos_of_pos_of_dvd hpos (Int.natCast_nonneg Fj) hdvd
  unfold recoveryQuotient
  omega

/-- Each half of the signed width window contains at most one admissible tag. -/
public theorem card_admissibleTags_le_two {q Fi Fj w : ℕ} {W : ℝ}
    (hcop : q.Coprime Fj) (hwidth : W < (Fj : ℝ)) :
    (admissibleTags q Fi Fj w W).card ≤ 2 := by
  let side (t : ℤ) : Fin 2 := if 0 ≤ t then 1 else 0
  rw [← Fintype.card_fin 2, ← Finset.card_univ]
  refine Finset.card_le_card_of_injOn side (fun _ _ ↦ Finset.mem_univ _) ?_
  intro a ha b hb hside
  by_contra hab
  obtain ⟨haW, _, haD⟩ := mem_admissibleTags.mp ha
  obtain ⟨hbW, _, hbD⟩ := mem_admissibleTags.mp hb
  have hqmul : (Fj : ℤ) ∣ (q : ℤ) * (b - a) := by
    convert dvd_sub haD hbD using 1
    ring
  have hcopZ : IsCoprime (Fj : ℤ) (q : ℤ) :=
    Int.isCoprime_iff_nat_coprime.mpr (by simpa using hcop.symm)
  have hspacing : (Fj : ℤ) ≤ |b - a| :=
    Int.le_of_dvd (abs_pos.mpr (sub_ne_zero.mpr (Ne.symm hab)))
      ((dvd_abs _ _).mpr (hcopZ.dvd_of_dvd_mul_left hqmul))
  have hspacingR : (Fj : ℝ) ≤ |(b : ℝ) - (a : ℝ)| := by exact_mod_cast hspacing
  have hnear : |(b : ℝ) - (a : ℝ)| ≤ W := by
    rw [abs_le] at haW hbW ⊢
    by_cases ha0 : 0 ≤ a <;> by_cases hb0 : 0 ≤ b
    · have haR : (0 : ℝ) ≤ a := by exact_mod_cast ha0
      have hbR : (0 : ℝ) ≤ b := by exact_mod_cast hb0
      exact ⟨by linarith [haW.2], by linarith [hbW.2]⟩
    · simp [side, ha0, hb0] at hside
    · simp [side, ha0, hb0] at hside
    · have haR : (a : ℝ) < 0 := by exact_mod_cast lt_of_not_ge ha0
      have hbR : (b : ℝ) < 0 := by exact_mod_cast lt_of_not_ge hb0
      exact ⟨by linarith [hbW.1], by linarith [haW.1]⟩
  exact (not_lt_of_ge (hspacingR.trans hnear)) hwidth

private theorem Realization.numerator_eq {q Fi Fj w : ℕ} {H Z W : ℝ} {p : ℕ × ℕ}
    (a : Realization q Fi Fj w H Z W p) :
    (Fi : ℤ) * w - (q : ℤ) * a.t = (Fj : ℤ) * (a.hj * a.yi : ℕ) := by
  rw [← a.det, sub_sub_cancel]

private theorem Realization.tag_mem {q Fi Fj w : ℕ} {H Z W : ℝ} {p : ℕ × ℕ}
    (a : Realization q Fi Fj w H Z W p) : a.t ∈ admissibleTags q Fi Fj w W := by
  refine mem_admissibleTags.mpr ⟨a.tag_width, ?_, ⟨_, a.numerator_eq⟩⟩
  rw [a.numerator_eq]
  have hF : (0 : ℤ) < Fj := by exact_mod_cast Nat.pos_of_mul_pos_right a.xj_pos
  have hprod : 0 < a.hj * a.yi := Nat.mul_pos (Nat.pos_of_mul_pos_left a.xj_pos) a.yi_pos
  exact mul_pos hF (by exact_mod_cast hprod)

private theorem Realization.quotient_eq {q Fi Fj w : ℕ} {H Z W : ℝ} {p : ℕ × ℕ}
    (a : Realization q Fi Fj w H Z W p) : recoveryQuotient q Fi Fj w a.t = a.hj * a.yi := by
  have hF : (Fj : ℤ) ≠ 0 := by exact_mod_cast (Nat.pos_of_mul_pos_right a.xj_pos).ne'
  rw [recoveryQuotient, Int.ediv_eq_of_eq_mul_right hF a.numerator_eq, Int.toNat_natCast]

/-- At fixed off-diagonal product `w` for the chosen positions of a fixed list,
there are at most two admissible tags. The number of distinct columns is bounded
by the divisor count of `w` times the sum of divisor counts of the exact quotients.
A column may have several witnesses; only one witness per column is used. -/
public theorem offDiagonal_recovery_bounds {labels : List ℕ} {i j : Fin labels.length}
    (_hij : i ≠ j) {q w : ℕ} {H Z W : ℝ}
    (hq : q.Prime) (hcop : q.Coprime (labels.get j)) (hW : W < (labels.get j : ℝ))
    (hw : 0 < w) (columns : Finset (ℕ × ℕ))
    (hreal : ∀ p ∈ columns, Nonempty (Realization q (labels.get i) (labels.get j) w H Z W p)) :
    (admissibleTags q (labels.get i) (labels.get j) w W).card ≤ 2 ∧
      columns.card ≤ w.divisors.card *
        ∑ t ∈ admissibleTags q (labels.get i) (labels.get j) w W,
          (recoveryQuotient q (labels.get i) (labels.get j) w t).divisors.card := by
  refine ⟨card_admissibleTags_le_two hcop hW, ?_⟩
  let Fi := labels.get i
  let Fj := labels.get j
  let T := admissibleTags q Fi Fj w W
  let row (p : ↥columns) : Realization q Fi Fj w H Z W p :=
    Classical.choice (hreal p p.property)
  let code (p : ↥columns) : Σ _ : ℤ, ℕ × ℕ := ⟨(row p).t, (row p).hi, (row p).yi⟩
  let fiber (t : ℤ) := w.divisors ×ˢ (recoveryQuotient q Fi Fj w t).divisors
  calc
    columns.card = columns.attach.card := Finset.card_attach.symm
    _ ≤ (T.sigma fiber).card := by
      refine Finset.card_le_card_of_injOn code ?_ ?_
      · intro p _
        refine Finset.mem_sigma.mpr ⟨(row p).tag_mem, Finset.mem_product.mpr ⟨?_, ?_⟩⟩
        · exact Nat.mem_divisors.mpr ⟨⟨(row p).yj, (row p).cross_product.symm⟩, hw.ne'⟩
        · apply Nat.mem_divisors.mpr
          refine ⟨?_, (recoveryQuotient_pos (row p).tag_mem).ne'⟩
          change (row p).yi ∣ recoveryQuotient q Fi Fj w (row p).t
          rw [(row p).quotient_eq]
          exact Nat.dvd_mul_left _ _
      · intro a _ b _ hab
        apply Subtype.ext
        exact Realization.column_eq hq (row a) (row b)
          (congrArg (fun v : Σ _ : ℤ, ℕ × ℕ ↦ v.2.1) hab)
          (congrArg (fun v : Σ _ : ℤ, ℕ × ℕ ↦ v.2.2) hab)
    _ = _ := by
      rw [Finset.card_sigma, Finset.mul_sum]
      simp only [T, fiber, Fi, Fj, Finset.card_product]

end SharedLabelRecoveryFiber
