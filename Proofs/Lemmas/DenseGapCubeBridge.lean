module

public import Lemmas.RetainedSignedCap
public import Lemmas.DeletedCubePhaseAverage
public import Lemmas.SignedCubeCellScreen
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The finite dense-gap prime-pool bridge

Source: `dcc11ec5bbd653cbb1068ea454799744de33fb73`,
`.godel/bob/signed-gap-cube-screen.md:5–9,26–48,66`.
Owning check session: `01a20db3-6987-747d-9d8d-903a502adedd`.

Use the actual lower-first dense pairs, with their original weights and
angular phase. Reindex each gap fibre on the full cycle, apply differencing
on the full gap and ordered-draw domains, and use the integer-lift statistic
with the original divisor after deletion. The shift room, separation,
deletion loss, cell width and midpoint error are finite budgets. This proves
the signed bound on cleared cells only, not a flagged-node or asymptotic cap.
-/

open scoped BigOperators

namespace Masullo.DenseGapCubeBridge

open RetainedSignedCap (IsPrimePool densePairs gap farPairs weight frequency Q weight_bounds)
open TriangularCubeDeletion (Start survivingAverage cyclic_iteratedDifference_deletion_bound)
open TriangularGapDifferencing (averagedDifference intervalDraw cyclic_iteratedDifference_bound)
open DeletedCubePhaseAverage (gapPairFrequency gapPhase survivingAverage_eq_survivingSum)
open SignedCubeShell (survivingSum cubeWeight)
open SignedBlockIntervalMoment (phase)
open SignedCubeCellScreen (Cell frequencyBound cell_midpoint_screen)

variable {S : Finset ℕ} {X : ℝ} {d n H k : ℕ}

/-- The very same set of pairs as in `RetainedSignedCap.Q`. -/
public noncomputable abbrev pairs (S : Finset ℕ) (X : ℝ) (n : ℕ) : Finset (ℕ × ℕ) :=
  densePairs S (n * (Real.log X)^2) (X / (n * (Real.log X)^4))

private theorem mem_pairs {pq : ℕ × ℕ} (hpq : pq ∈ pairs S X n) :
    pq.1 ∈ S ∧ pq.2 ∈ S ∧ (n : ℝ) * (Real.log X)^2 < (pq.2 : ℝ) - pq.1 := by
  simpa only [farPairs, Finset.mem_filter, Finset.mem_product, and_assoc] using
    (Finset.mem_filter.mp (show pq ∈ (farPairs S (n * (Real.log X)^2)).filter _ from hpq)).1

private theorem lower_first {pq : ℕ × ℕ} (hpq : pq ∈ pairs S X n) : pq.1 < pq.2 := by
  have h := (mem_pairs hpq).2.2
  have hnonneg : 0 ≤ (n : ℝ) * (Real.log X)^2 := by positivity
  exact_mod_cast sub_pos.mp (hnonneg.trans_lt h)

private theorem floor_pos (h : IsPrimePool S X d) : 0 < ⌊X⌋₊ :=
  Nat.le_floor (by simpa using h.one_lt.le)

private theorem le_floor_of_mem (h : IsPrimePool S X d) {p : ℕ} (hp : p ∈ S) : p ≤ ⌊X⌋₊ :=
  Nat.le_floor (h.band p hp).2.2.1.2

private theorem pair_gap_range (h : IsPrimePool S X d) {pq : ℕ × ℕ} (hpq : pq ∈ pairs S X n) :
    1 ≤ gap pq ∧ gap pq ≤ ⌊X⌋₊ := by
  have hp := lower_first hpq
  have hq := le_floor_of_mem h (mem_pairs hpq).2.1
  unfold gap
  omega

/-- The original complex pair term, without the opposite-order factor two. -/
@[expose] public noncomputable def pairTerm (X : ℝ) (d : ℕ) (u : ℝ) (pq : ℕ × ℕ) : ℂ :=
  (↑(weight X d pq.1 * weight X d pq.2) : ℂ) *
    phase (u * (frequency d pq.1 - frequency d pq.2))

/-- The exact complex dense gap group `P_g`, including the factor two. Gap
labels run over `1, …, ⌊X⌋₊`; a gap without dense pairs has zero group sum. -/
@[expose] public noncomputable def gapGroup (S : Finset ℕ) (X : ℝ) (d n : ℕ) (u : ℝ)
    (g : Fin ⌊X⌋₊) : ℂ :=
  2 * ∑ pq ∈ (pairs S X n).filter (fun pq ↦ gap pq = g.val + 1), pairTerm X d u pq

/-- The original logarithmic weight bound `W`. -/
@[expose] public noncomputable def weightScale (X : ℝ) : ℝ := 8 * (Real.log X)^2 / X

private theorem weightScale_pos (h : IsPrimePool S X d) : 0 < weightScale X := by
  have hX : 0 < X := zero_lt_one.trans h.one_lt
  have hD := Real.log_pos h.one_lt
  unfold weightScale
  positivity

/-- The normalized amplitude, with the strict far and dense masks inherited
from `densePairs`. The upper start is formed in the integers, not modulo
`2⌊X⌋₊+1`. No starts outside the representative interval are admitted. -/
@[expose] public noncomputable def amplitude (S : Finset ℕ) (X : ℝ) (d n : ℕ)
    (g : Fin ⌊X⌋₊) (p : ℤ) : ℝ :=
  let q := p.toNat + (g.val + 1)
  if 0 ≤ p ∧ p < ((2 * ⌊X⌋₊ + 1 : ℕ) : ℤ) ∧ (p.toNat, q) ∈ pairs S X n then
    weight X d p.toNat * weight X d q / weightScale X ^ 2
  else 0

private theorem mem_of_amplitude_ne_zero {g : Fin ⌊X⌋₊} {p : ℤ}
    (hp : amplitude S X d n g p ≠ 0) :
    0 ≤ p ∧ p < ((2 * ⌊X⌋₊ + 1 : ℕ) : ℤ) ∧
      (p.toNat, p.toNat + (g.val + 1)) ∈ pairs S X n := by
  unfold amplitude at hp
  dsimp only at hp
  split at hp
  · assumption
  · exact (hp rfl).elim

private theorem amplitude_bounds (h : IsPrimePool S X d) (g : Fin ⌊X⌋₊) (p : ℤ) :
    0 ≤ amplitude S X d n g p ∧ amplitude S X d n g p ≤ 1 := by
  unfold amplitude
  dsimp only
  split_ifs with hm
  · have hp := weight_bounds h (mem_pairs hm.2.2).1
    have hq := weight_bounds h (mem_pairs hm.2.2).2.1
    have hW := weightScale_pos h
    refine ⟨div_nonneg (mul_nonneg hp.1 hq.1) (sq_nonneg _), (div_le_iff₀ (sq_pos_of_pos hW)).2 ?_⟩
    rw [one_mul, pow_two]
    exact mul_le_mul hp.2 hq.2 hq.1 hW.le
  · exact ⟨le_rfl, zero_le_one⟩

private theorem amplitude_lower (h : IsPrimePool S X d) (g : Fin ⌊X⌋₊) (p : ℤ)
    (hp : amplitude S X d n g p ≠ 0) : Real.exp (-8) * X ≤ (p : ℝ) := by
  have hm := mem_of_amplitude_ne_zero hp
  have hb := (h.band _ (mem_pairs hm.2.2).1).2.2.1.1
  have hcast := congrArg (fun z : ℤ ↦ (z : ℝ)) (Int.toNat_of_nonneg hm.1)
  rw [Int.cast_natCast] at hcast
  rwa [hcast] at hb

private theorem frequency_eq_ratio (d p : ℕ) (hp : 0 < p) :
    frequency d p = Real.log (((p + d : ℕ) : ℝ) / (p : ℝ)) := by
  have hp' : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  unfold frequency
  rw [Nat.cast_add, add_div, div_self hp']

private theorem cyclic_pair_frequency (h : IsPrimePool S X d)
    (g : Fin ⌊X⌋₊) (p : Start ⌊X⌋₊)
    (hp : (p.val, p.val + (g.val + 1)) ∈ pairs S X n) :
    gapPairFrequency (d : ℤ) g p.val =
      frequency d p.val - frequency d (p.val + (g.val + 1)) := by
  have hpos := (h.band _ (mem_pairs hp).1).1.pos
  have hq : 0 < p.val + (g.val + 1) := by omega
  rw [frequency_eq_ratio d _ hpos, frequency_eq_ratio d _ hq]
  simp only [gapPairFrequency, Int.cast_add, Int.cast_natCast, Int.cast_one, Nat.cast_add,
    Nat.cast_one, add_assoc]

-- Reindex on each fibre. The inverse of a dense pair is the residue of its
-- lower start; its representative is unchanged by the pool's upper band.
private theorem sum_cyclic_pairs (h : IsPrimePool S X d) (g : Fin ⌊X⌋₊) (F : ℕ × ℕ → ℂ) :
    (∑ p : Start ⌊X⌋₊,
      if (p.val, p.val + (g.val + 1)) ∈ pairs S X n then F (p.val, p.val + (g.val + 1)) else 0) =
    ∑ pq ∈ (pairs S X n).filter (fun pq ↦ gap pq = g.val + 1), F pq := by
  classical
  rw [← Finset.sum_filter]
  refine Finset.sum_bij (fun p _ ↦ (p.val, p.val + (g.val + 1))) ?_ ?_ ?_ (fun _ _ ↦ rfl)
  · intro p hp
    refine Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hp).2, ?_⟩
    simp [gap]
  · intro p _ q _ he
    exact ZMod.val_injective _ (congrArg Prod.fst he)
  · intro pq hpq
    obtain ⟨hm, hg⟩ := Finset.mem_filter.mp hpq
    have hlo := lower_first hm
    have hhi := le_floor_of_mem h (mem_pairs hm).1
    have hrep : (pq.1 : Start ⌊X⌋₊).val = pq.1 := ZMod.val_natCast_of_lt (by omega)
    have hpair : (pq.1, pq.1 + (g.val + 1)) = pq := by
      refine Prod.ext rfl ?_
      unfold gap at hg
      dsimp
      omega
    refine ⟨(pq.1 : Start ⌊X⌋₊), Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
    · simpa only [hrep, hpair] using hm
    · simpa only [hrep] using hpair

private theorem scaled_gapPhase (h : IsPrimePool S X d) (u : ℝ)
    (g : Fin ⌊X⌋₊) (p : Start ⌊X⌋₊) :
    (↑(weightScale X ^ 2) : ℂ) * gapPhase (d : ℤ) (amplitude S X d n) u g p =
      if (p.val, p.val + (g.val + 1)) ∈ pairs S X n then
        pairTerm X d u (p.val, p.val + (g.val + 1)) else 0 := by
  have hrep : (p.val : ℤ) < ((2 * ⌊X⌋₊ + 1 : ℕ) : ℤ) := by exact_mod_cast ZMod.val_lt p
  have hw := (weightScale_pos h).ne'
  rw [gapPhase, amplitude]
  simp only [Int.toNat_natCast, Int.natCast_nonneg, hrep, true_and]
  split_ifs with hp
  · rw [cyclic_pair_frequency h g p hp, pairTerm, ← mul_assoc, ← Complex.ofReal_mul]
    congr 2
    field_simp
  · simp

/-- Every complex group is exactly the full cyclic start sum of the masked
phase, scaled by the original weight normalization and opposite-order factor. -/
public theorem gapGroup_eq_cyclic_sum (h : IsPrimePool S X d) (u : ℝ) (g : Fin ⌊X⌋₊) :
    gapGroup S X d n u g =
      2 * (↑(weightScale X ^ 2) : ℂ) *
        ∑ p : Start ⌊X⌋₊, gapPhase (d : ℤ) (amplitude S X d n) u g p := by
  rw [gapGroup]
  conv_rhs => rw [mul_assoc, Finset.mul_sum]
  simp_rw [scaled_gapPhase h]
  rw [sum_cyclic_pairs h]

-- The image is exactly the full gap interval; empty fibres contribute zero.
private theorem sum_gap_fibres (h : IsPrimePool S X d) (F : ℕ × ℕ → ℂ) :
    (∑ g : Fin ⌊X⌋₊, ∑ pq ∈ (pairs S X n).filter (fun pq ↦ gap pq = g.val + 1), F pq) =
      ∑ pq ∈ pairs S X n, F pq := by
  let j (g : Fin ⌊X⌋₊) : ℕ := g.val + 1
  have hj : Set.InjOn j ↑(Finset.univ : Finset (Fin ⌊X⌋₊)) := by
    intro a _ b _ hab
    apply Fin.ext
    dsimp [j] at hab
    omega
  have hmaps (pq : ℕ × ℕ) (hpq : pq ∈ pairs S X n) :
      gap pq ∈ Finset.univ.image j := by
    obtain ⟨hlo, hhi⟩ := pair_gap_range h hpq
    refine Finset.mem_image.mpr ⟨⟨gap pq - 1, by omega⟩, Finset.mem_univ _, ?_⟩
    dsimp [j]
    omega
  calc
    _ = ∑ l ∈ Finset.univ.image j, ∑ pq ∈ (pairs S X n).filter (fun pq ↦ gap pq = l), F pq :=
      (Finset.sum_image hj).symm
    _ = _ := Finset.sum_fiberwise_of_maps_to hmaps F

/-- The retained signed sum is exactly the sum of the real parts of the
original complex groups. Neither the pairs nor the gap threshold change. -/
public theorem Q_eq_sum_re_gapGroup (h : IsPrimePool S X d) (u : ℝ) :
    Q S X d n u = ∑ g, (gapGroup S X d n u g).re := by
  calc
    _ = (2 * ∑ pq ∈ pairs S X n, pairTerm X d u pq : ℂ).re := by
      rw [Q, show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num, Complex.re_ofReal_mul, Complex.re_sum]
      congr 1
      refine Finset.sum_congr rfl fun pq _ ↦ ?_
      rw [pairTerm, Complex.re_ofReal_mul, phase, Complex.exp_ofReal_mul_I_re]
    _ = (∑ g, gapGroup S X d n u g).re := by
      simp only [gapGroup, ← Finset.mul_sum, sum_gap_fibres h]
    _ = _ := Complex.re_sum _ _

/-- Sum of absolute complex group sums, not the sum of individual pair norms. -/
@[expose] public noncomputable def groupMass (S : Finset ℕ) (X : ℝ) (d n : ℕ) (u : ℝ) : ℝ :=
  ∑ g, ‖gapGroup S X d n u g‖

/-- The dense group mass dominates the absolute value of the signed target. -/
public theorem abs_Q_le_groupMass (h : IsPrimePool S X d) (u : ℝ) :
    |Q S X d n u| ≤ groupMass S X d n u := by
  rw [Q_eq_sum_re_gapGroup h, groupMass]
  exact (Finset.abs_sum_le_sum_abs _ _).trans
    (Finset.sum_le_sum fun _ _ ↦ Complex.abs_re_le_norm _)

/-- The normalization for passing from the complex group mass to the mean of
cyclic start means: opposite order, all starts, all gaps, and weight scale. -/
@[expose] public noncomputable def gapNormalizer (X : ℝ) : ℝ :=
  2 * (↑(2 * ⌊X⌋₊ + 1 : ℕ) : ℝ) * (⌊X⌋₊ : ℝ) * weightScale X ^ 2

private theorem gapNormalizer_pos (h : IsPrimePool S X d) : 0 < gapNormalizer X := by
  have hg := floor_pos h
  have hw := weightScale_pos h
  unfold gapNormalizer
  positivity

private theorem norm_gapGroup (h : IsPrimePool S X d) (u : ℝ) (g : Fin ⌊X⌋₊) :
    ‖gapGroup S X d n u g‖ =
      (2 * (↑(2 * ⌊X⌋₊ + 1 : ℕ) : ℝ) * weightScale X ^ 2) *
        ‖𝔼 p : Start ⌊X⌋₊, gapPhase (d : ℤ) (amplitude S X d n) u g p‖ := by
  have hN : (↑(2 * ⌊X⌋₊ + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  rw [gapGroup_eq_cyclic_sum h, Finset.expect_eq_sum_div_card, Finset.card_univ, ZMod.card]
  simp only [Start, norm_mul, norm_div, Complex.norm_natCast, Complex.norm_ofNat, Complex.norm_real,
    Real.norm_of_nonneg (sq_nonneg (weightScale X))]
  field_simp

/-- The original Cauchy input is exactly the mass of the complex dense groups
with denominator `2 N G W²`, including all zero gap and start labels. -/
public theorem mean_norm_eq_groupMass_div (h : IsPrimePool S X d) (u : ℝ) :
    (𝔼 g, ‖𝔼 p : Start ⌊X⌋₊, gapPhase (d : ℤ) (amplitude S X d n) u g p‖) =
      groupMass S X d n u / gapNormalizer X := by
  have hG : (⌊X⌋₊ : ℝ) ≠ 0 := by have := floor_pos h; positivity
  have hN : (↑(2 * ⌊X⌋₊ + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  have hW := (weightScale_pos h).ne'
  rw [groupMass, Finset.expect_eq_sum_div_card, Finset.card_univ, Fintype.card_fin, gapNormalizer]
  simp_rw [norm_gapGroup h, ← Finset.mul_sum]
  field_simp

private theorem gapNormalizer_le (h : IsPrimePool S X d) :
    gapNormalizer X ≤ 400 * (Real.log X)^4 := by
  have hX : 0 < X := zero_lt_one.trans h.one_lt
  have hG : (⌊X⌋₊ : ℝ) ≤ X := Nat.floor_le hX.le
  have hN : (↑(2 * ⌊X⌋₊ + 1 : ℕ) : ℝ) ≤ 3 * X := by
    push_cast
    linarith [h.one_lt]
  calc
    gapNormalizer X ≤ 2 * (3 * X) * X * weightScale X ^ 2 := by
      unfold gapNormalizer
      gcongr
    _ = 384 * (Real.log X)^4 := by
      unfold weightScale
      field_simp
      ring
    _ ≤ _ := by
      gcongr
      norm_num

private theorem amplitude_band (h : IsPrimePool S X d)
    (hroom : (k : ℝ) * ((H : ℝ) - 1) ≤ Real.exp (-8) * X)
    (g : Fin ⌊X⌋₊) (p : ℤ) (ha : amplitude S X d n g p ≠ 0) :
    (k : ℤ) * ((H : ℤ) - 1) ≤ p ∧
    p + (k : ℤ) * ((H : ℤ) - 1) < ((2 * ⌊X⌋₊ + 1 : ℕ) : ℤ) ∧
    p + (g.val : ℤ) + 1 + d < ((2 * ⌊X⌋₊ + 1 : ℕ) : ℤ) := by
  have hm := mem_of_amplitude_ne_zero ha
  have hp := (mem_pairs hm.2.2).1
  have hq := (h.band _ (mem_pairs hm.2.2).2.1).2.2.2.2
  have hT : (k : ℤ) * ((H : ℤ) - 1) ≤ p := by
    exact_mod_cast hroom.trans (amplitude_lower h g p ha)
  have hpF : (p.toNat : ℤ) ≤ (⌊X⌋₊ : ℤ) := by exact_mod_cast le_floor_of_mem h hp
  rw [Int.toNat_of_nonneg hm.1] at hpF
  have hqF : (↑(p.toNat + (g.val + 1) + d : ℕ) : ℤ) ≤ (⌊X⌋₊ : ℤ) := by
    exact_mod_cast Nat.le_floor hq
  push_cast at hqF
  rw [Int.toNat_of_nonneg hm.1] at hqF
  refine ⟨hT, ?_, ?_⟩ <;> push_cast <;> omega

private theorem amplitude_prime (h : IsPrimePool S X d) (g : Fin ⌊X⌋₊) (p : ℤ)
    (ha : amplitude S X d n g p ≠ 0) (e b : Bool) :
    (p + (if e then (g.val : ℤ) + 1 else 0) + (if b then (d : ℤ) else 0)).toNat.Prime := by
  have hm := mem_of_amplitude_ne_zero ha
  obtain ⟨hp, hq, _⟩ := mem_pairs hm.2.2
  have hp' := Int.toNat_of_nonneg hm.1
  have hq' : (↑(p.toNat + (g.val + 1) : ℕ) : ℤ) = p + (g.val : ℤ) + 1 := by
    push_cast
    rw [hp']
    omega
  cases e <;> cases b <;> simp only [Bool.false_eq_true, ↓reduceIte, add_zero, ← add_assoc]
  · exact (h.band _ hp).1
  · rw [← hp', ← Int.natCast_add, Int.toNat_natCast]
    exact (h.band _ hp).2.1
  · rw [← hq', Int.toNat_natCast]
    exact (h.band _ hq).1
  · rw [← hq', ← Int.natCast_add, Int.toNat_natCast]
    exact (h.band _ hq).2.1

private theorem norm_gapPhase_le_one (h : IsPrimePool S X d) (u : ℝ)
    (g : Fin ⌊X⌋₊) (p : Start ⌊X⌋₊) :
    ‖gapPhase (d : ℤ) (amplitude S X d n) u g p‖ ≤ 1 := by
  obtain ⟨hlo, hhi⟩ := amplitude_bounds (n := n) h g p.val
  rwa [gapPhase, norm_mul, phase, Complex.norm_exp_ofReal_mul_I, mul_one,
    Complex.norm_real, Real.norm_of_nonneg hlo]

private theorem gapPhase_separation (h : IsPrimePool S X d)
    (hsep : (d : ℝ) ≤ (n : ℝ) * (Real.log X)^2) (u : ℝ)
    (g : Fin ⌊X⌋₊) (p : Start ⌊X⌋₊)
    (hp : gapPhase (d : ℤ) (amplitude S X d n) u g p ≠ 0) :
    0 < (d : ℤ) ∧ (d : ℤ) < (g.val : ℤ) + 1 := by
  have ha : amplitude S X d n g p.val ≠ 0 := by
    intro hz
    exact hp (by rw [gapPhase, hz, Complex.ofReal_zero, zero_mul])
  have hf := (mem_pairs (mem_of_amplitude_ne_zero ha).2.2).2.2
  simp only [Int.toNat_natCast, Nat.cast_add, Nat.cast_one] at hf
  have hs : (d : ℝ) < (g.val : ℝ) + 1 := by linarith
  exact ⟨by exact_mod_cast h.shift_pos, by exact_mod_cast hs⟩

/-- The arithmetic scale in the dense-gap test, with `a₀ = 1/16`. -/
@[expose] public noncomputable def delta (X : ℝ) (k : ℕ) : ℝ :=
  ((1 / 16 : ℝ)^2 / (800 * (Real.log X)^4)) ^ (2 ^ k)

private theorem delta_pos (h : IsPrimePool S X d) : 0 < delta X k := by
  have hD := Real.log_pos h.one_lt
  unfold delta
  positivity

/-- The normalized surviving prime-cube statistic, evaluated with the
concrete dense-pair amplitude on the full ordered-draw domain. -/
@[expose] public noncomputable def survivingDenseSum (S : Finset ℕ) (X : ℝ) (d n H k : ℕ)
    (u : ℝ) : ℂ :=
  survivingSum (d : ℤ) (cubeWeight (H := H) (k := k) (amplitude S X d n)) u

/-- The finite arithmetic implication of (1). Separation is supplied by the
strict far mask and `d ≤ n (log X)²`; the shift room is supplied by the
original prime band and the displacement bound `k(H-1)`. The deletion cost
is charged only after all differences, without changing the divisor. -/
public theorem three_quarters_delta_le_re_survivingDenseSum (h : IsPrimePool S X d)
    (_hn : 1 ≤ n) (hH : 1 ≤ H) (hk : 1 ≤ k)
    (hsep : (d : ℝ) ≤ (n : ℝ) * (Real.log X)^2)
    (hroom : (k : ℝ) * ((H : ℝ) - 1) ≤ Real.exp (-8) * X)
    (hdel : (4 * 2 ^ k : ℝ)^2 / (H : ℝ) ≤ delta X k / 4)
    (u : ℝ) (hmass : (1 / 16 : ℝ)^2 / 2 ≤ groupMass S X d n u) :
    3 * delta X k / 4 ≤ (survivingDenseSum S X d n H k u).re := by
  let : Nonempty (Fin ⌊X⌋₊) := ⟨⟨0, floor_pos h⟩⟩
  have hD := (Real.log_pos h.one_lt).ne'
  let B : ℝ := (1 / 16 : ℝ)^2 / (800 * (Real.log X)^4)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  let f := gapPhase (d : ℤ) (amplitude S X d n) u
  have hmean : B ≤ 𝔼 g, ‖𝔼 p, f g p‖ := by
    change B ≤ 𝔼 g, ‖𝔼 p, gapPhase (d : ℤ) (amplitude S X d n) u g p‖
    rw [mean_norm_eq_groupMass_div h]
    apply (le_div_iff₀ (gapNormalizer_pos h)).2
    calc
      B * gapNormalizer X ≤ B * (400 * (Real.log X)^4) :=
        mul_le_mul_of_nonneg_left (gapNormalizer_le h) hB
      _ = (1 / 16 : ℝ)^2 / 2 := by dsimp [B]; field_simp; ring
      _ ≤ _ := hmass
  have hC := (cyclic_iteratedDifference_bound hH hk f).2
  have hA : delta X k ≤ (averagedDifference (intervalDraw (2 * ⌊X⌋₊ + 1) H) f k).re :=
    (pow_le_pow_left₀ hB hmean _).trans hC
  have hcost := (cyclic_iteratedDifference_deletion_bound (H := H) (k := k) (d : ℤ) f
    (norm_gapPhase_le_one h u) (gapPhase_separation h hsep u)).trans hdel
  have hre := (Complex.re_le_norm _).trans hcost
  have hlift : survivingAverage (H := H) (d : ℤ) f k = survivingDenseSum S X d n H k u := by
    apply survivingAverage_eq_survivingSum hH (d : ℤ) (Int.natCast_nonneg _) (amplitude S X d n)
    · intro g p _ _ hp
      exact amplitude_band h hroom g p hp
    · intro g p _ _ hp e b
      exact amplitude_prime h g p hp e b
  rw [Complex.sub_re, hlift] at hre
  linarith

/-- A cleared cell has small absolute value of the actual retained signed
sum at every point, including the endpoints. The midpoint estimate can
clear at equality; the strict upper bound comes from `cell_midpoint_screen`. -/
public theorem abs_Q_lt_of_cleared_cell (h : IsPrimePool S X d)
    (hn : 1 ≤ n) (hH : 1 ≤ H) (hk : 1 ≤ k)
    (hsep : (d : ℝ) ≤ (n : ℝ) * (Real.log X)^2)
    (hroom : (k : ℝ) * ((H : ℝ) - 1) ≤ Real.exp (-8) * X)
    (hdel : (4 * 2 ^ k : ℝ)^2 / (H : ℝ) ≤ delta X k / 4)
    (c : Cell) (q : ℝ)
    (hwidth : frequencyBound (d : ℤ) H k X * c.width ≤ delta X k / 4)
    (herror : |(survivingDenseSum S X d n H k c.midpoint).re - q| ≤ delta X k / 16)
    (hclear : q ≤ delta X k / 2) {u : ℝ} (hu : u ∈ c.interval) :
    |Q S X d n u| < (1 / 16 : ℝ)^2 / 2 := by
  have hs : (survivingDenseSum S X d n H k u).re < 3 * delta X k / 4 :=
    (cell_midpoint_screen (d : ℤ) (amplitude S X d n) (floor_pos h) hH (Int.natCast_nonneg _)
      (zero_lt_one.trans h.one_lt) (delta_pos h) (amplitude_bounds h) (amplitude_lower h)
      c q hwidth herror hu).1 hclear
  refine (abs_Q_le_groupMass h u).trans_lt (lt_of_not_ge fun hm ↦ ?_)
  exact hs.not_ge (three_quarters_delta_le_re_survivingDenseSum h hn hH hk hsep hroom hdel u hm)

end Masullo.DenseGapCubeBridge
