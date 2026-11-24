module

public import Lemmas.ShortCellSelbergOffDiagonal
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Basic.Complex.BigOperators
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Finite short-cell Gram assembly

Source: `8058479edd84:.godel/bob/short-cell-weil-list.md:17–27,37,45–53`, unchanged
at scan pin `7817ec43`. This is the positive-width finite cell estimate behind
(2), with the integer Gram bounds as inputs. Prime ownership is represented by
an injective map of the assigned finite set into the integer support. The
normalized estimate supplies a cell density budget for
`ShortCellTrace.mul_cellBudget_of_div` or, after clearing the width,
`ShortCellTrace.integral_trace_le`. It makes no claim about a prime asymptotic,
a character-sum saving, or moments at width zero.

Owning check session: `01a20fda-fdc5-7fd5-bef7-0dc0da54e6c0`.
-/

open Finset
open scoped ComplexConjugate

namespace ShortCellGramAssembly

variable {ι α : Type*} [Fintype ι]

/-- The integer-support Gram matrix, with conjugation on the second row. -/
@[expose] public noncomputable def gram (S : Finset ℤ) (W : ℤ → ℝ) (χ : ι → ℤ → ℂ)
    (i j : ι) : ℂ :=
  ∑ n ∈ S, (W n : ℂ) * χ i n * conj (χ j n)

/-- The assigned cell moment with density normalization. -/
@[expose] public noncomputable def moment (P : Finset α) (point : α ↪ ℤ) (w : α → ℝ)
    (ξ : α → ℂ) (χ : ι → ℤ → ℂ) (h : ℝ) (i : ι) : ℂ :=
  (∑ p ∈ P, (w p : ℂ) * ξ p * χ i (point p)) / (h : ℂ)

omit [Fintype ι] in
private theorem gram_diag_norm (S : Finset ℤ) {W : ℤ → ℝ} (χ : ι → ℤ → ℂ)
    (hW : ∀ n ∈ S, 0 ≤ W n) (i : ι) :
    ‖gram S W χ i i‖ = ∑ n ∈ S, W n * ‖χ i n‖ ^ 2 := by
  have heq : gram S W χ i i = ((∑ n ∈ S, W n * ‖χ i n‖ ^ 2 : ℝ) : ℂ) := by
    rw [gram, Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun n _ ↦ ?_
    rw [mul_assoc, Complex.mul_conj, ← Complex.sq_norm, Complex.ofReal_mul]
  rw [heq, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Finset.sum_nonneg fun n hn ↦ mul_nonneg (hW n hn) (sq_nonneg _))]

private theorem off_pair_sum [Nonempty ι] [DecidableEq ι] (a : ι → ℝ) :
    ∑ i, ∑ j ∈ (Finset.univ : Finset ι).erase i, (a i + a j) / 2 =
      ((Fintype.card ι - 1 : ℕ) : ℝ) * ∑ i, a i := by
  classical
  let c : ℝ := ((Fintype.card ι - 1 : ℕ) : ℝ)
  have hc : c = (Fintype.card ι : ℝ) - 1 := by
    simp only [c, Nat.cast_sub (Nat.succ_le_of_lt Fintype.card_pos), Nat.cast_one]
  have hrow (i : ι) : (∑ _j ∈ (Finset.univ : Finset ι).erase i, a i) = c * a i := by
    rw [Finset.sum_const, nsmul_eq_mul, Finset.card_erase_of_mem (Finset.mem_univ i),
      Finset.card_univ]
  have hcol (i : ι) : (∑ j ∈ (Finset.univ : Finset ι).erase i, a j) = (∑ j, a j) - a i :=
    eq_sub_of_add_eq (Finset.sum_erase_add _ a (Finset.mem_univ i))
  have hcols : (∑ i, ∑ j ∈ (Finset.univ : Finset ι).erase i, a j) = c * ∑ j, a j := by
    simp only [hcol, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hc]
    ring
  calc
    _ = ((∑ i, ∑ j ∈ (Finset.univ : Finset ι).erase i, a i) +
        (∑ i, ∑ j ∈ (Finset.univ : Finset ι).erase i, a j)) / 2 := by
      simp only [← Finset.sum_div, Finset.sum_add_distrib]
    _ = _ := by
      simp only [hrow, hcols, ← Finset.mul_sum]
      change (_ + _) / 2 = c * _
      ring

private theorem gram_form_le [Nonempty ι] (S : Finset ℤ) {W : ℤ → ℝ} (χ : ι → ℤ → ℂ)
    {D E : ℝ} (hW : ∀ n ∈ S, 0 ≤ W n) (hE : 0 ≤ E)
    (hdiag : ∀ i, ∑ n ∈ S, W n * ‖χ i n‖ ^ 2 ≤ D)
    (hoff : ∀ i j, i ≠ j → ‖gram S W χ i j‖ ≤ E) (v : ι → ℂ) :
    (∑ n ∈ S, W n * ‖∑ i, conj (v i) * χ i n‖ ^ 2) ≤
      (D + ((Fintype.card ι - 1 : ℕ) : ℝ) * E) * ∑ i, ‖v i‖ ^ 2 := by
  classical
  let F (n : ℤ) : ℂ := ∑ i, conj (v i) * χ i n
  let Q : ℝ := ∑ n ∈ S, W n * ‖F n‖ ^ 2
  have hQ : 0 ≤ Q := Finset.sum_nonneg fun n hn ↦ mul_nonneg (hW n hn) (sq_nonneg _)
  have hterm (n : ℤ) : ((W n * ‖F n‖ ^ 2 : ℝ) : ℂ) =
      ∑ i, ∑ j, (conj (v i) * v j) * ((W n : ℂ) * χ i n * conj (χ j n)) := by
    rw [Complex.ofReal_mul, Complex.sq_norm, ← Complex.mul_conj]
    simp only [F, map_sum, map_mul, Complex.conj_conj]
    rw [Finset.sum_mul_sum]
    simp only [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ by ring
  have hexpand : (Q : ℂ) = ∑ i, ∑ j, conj (v i) * v j * gram S W χ i j := by
    simp only [Q, Complex.ofReal_sum, hterm]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [Finset.sum_comm]
    simp only [Finset.mul_sum, gram]
  let a (i : ι) : ℝ := ‖v i‖ ^ 2
  let T (i j : ι) : ℝ := ‖conj (v i) * v j * gram S W χ i j‖
  have hTi (i : ι) : T i i ≤ D * a i := by
    dsimp only [T, a]
    rw [norm_mul, norm_mul, Complex.norm_conj, ← pow_two, gram_diag_norm S χ hW, mul_comm]
    exact mul_le_mul_of_nonneg_right (hdiag i) (sq_nonneg _)
  have hTij {i j : ι} (hij : i ≠ j) : T i j ≤ E * ((a i + a j) / 2) := by
    calc
      T i j = (‖v i‖ * ‖v j‖) * ‖gram S W χ i j‖ := by
        simp only [T, norm_mul, Complex.norm_conj]
      _ ≤ (‖v i‖ * ‖v j‖) * E :=
        mul_le_mul_of_nonneg_left (hoff i j hij) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      _ ≤ E * ((a i + a j) / 2) := by
        rw [mul_comm]
        apply mul_le_mul_of_nonneg_left _ hE
        dsimp only [a]
        nlinarith only [sq_nonneg (‖v i‖ - ‖v j‖)]
  change Q ≤ (D + _) * ∑ i, a i
  calc
    Q = ‖(Q : ℂ)‖ := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hQ]
    _ ≤ ∑ i, ∑ j, T i j := by
      rw [hexpand]
      exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun _ _ ↦ norm_sum_le _ _)
    _ ≤ ∑ i, (D * a i + ∑ j ∈ (Finset.univ : Finset ι).erase i, E * ((a i + a j) / 2)) := by
      refine Finset.sum_le_sum fun i _ ↦ ?_
      rw [← Finset.sum_erase_add _ (T i) (Finset.mem_univ i), add_comm]
      exact add_le_add (hTi i) (Finset.sum_le_sum fun j hj ↦ hTij (Finset.mem_erase.mp hj).1.symm)
    _ = _ := by
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum, off_pair_sum]
      ring

private theorem weighted_cs (P : Finset α) {w : α → ℝ} {ξ f : α → ℂ}
    (hw : ∀ p ∈ P, 0 ≤ w p) (hξ : ∀ p ∈ P, ‖ξ p‖ ≤ 1) :
    ‖∑ p ∈ P, (w p : ℂ) * ξ p * f p‖ ^ 2 ≤
      (∑ p ∈ P, w p) * ∑ p ∈ P, w p * ‖f p‖ ^ 2 := by
  refine (pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2).trans ?_
  refine Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul P hw
    (fun p hp ↦ mul_nonneg (hw p hp) (sq_nonneg _)) (fun p hp ↦ ?_)
  have ht : ‖(w p : ℂ) * ξ p * f p‖ ≤ w p * ‖f p‖ := by
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hw p hp)]
    exact mul_le_mul_of_nonneg_right (mul_le_of_le_one_right (hw p hp) (hξ p hp)) (norm_nonneg _)
  calc
    _ ≤ (w p * ‖f p‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) ht 2
    _ = _ := by ring

private theorem unnormalized_le [Nonempty ι] (S : Finset ℤ) (P : Finset α) (point : α ↪ ℤ)
    {w : α → ℝ} {W : ℤ → ℝ} {ξ : α → ℂ} (χ : ι → ℤ → ℂ) {L D E : ℝ}
    (hsub : P.map point ⊆ S) (hw : ∀ p ∈ P, 0 ≤ w p ∧ w p ≤ L)
    (hξ : ∀ p ∈ P, ‖ξ p‖ ≤ 1) (hW : ∀ n ∈ S, 0 ≤ W n) (hWP : ∀ p ∈ P, W (point p) = 1)
    (hD : 0 ≤ D) (hE : 0 ≤ E) (hdiag : ∀ i, ∑ n ∈ S, W n * ‖χ i n‖ ^ 2 ≤ D)
    (hoff : ∀ i j, i ≠ j → ‖gram S W χ i j‖ ≤ E) :
    (∑ i, ‖∑ p ∈ P, (w p : ℂ) * ξ p * χ i (point p)‖ ^ 2) ≤
      (∑ p ∈ P, w p) * L * (D + ((Fintype.card ι - 1 : ℕ) : ℝ) * E) := by
  classical
  obtain rfl | ⟨p, hp⟩ := P.eq_empty_or_nonempty
  · simp
  have hL : 0 ≤ L := (hw p hp).1.trans (hw p hp).2
  let u (i : ι) : ℂ := ∑ p ∈ P, (w p : ℂ) * ξ p * χ i (point p)
  let Q : ℝ := ∑ i, ‖u i‖ ^ 2
  let B : ℝ := ∑ p ∈ P, w p
  let K : ℝ := D + ((Fintype.card ι - 1 : ℕ) : ℝ) * E
  let F (n : ℤ) : ℂ := ∑ i, conj (u i) * χ i n
  have hQ : 0 ≤ Q := Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
  have hB : 0 ≤ B := Finset.sum_nonneg fun p hp ↦ (hw p hp).1
  change Q ≤ B * L * K
  rcases hQ.eq_or_lt with hzero | hpos
  · rw [← hzero]
    dsimp only [K]
    positivity
  -- Enlarge the support of the positive square, before expanding the Gram form.
  have hdom : (∑ p ∈ P, w p * ‖F (point p)‖ ^ 2) ≤ L * (∑ n ∈ S, W n * ‖F n‖ ^ 2) := by
    calc
      _ ≤ ∑ p ∈ P, L * (W (point p) * ‖F (point p)‖ ^ 2) := by
        refine Finset.sum_le_sum fun p hp ↦ ?_
        rw [hWP p hp, one_mul]
        exact mul_le_mul_of_nonneg_right (hw p hp).2 (sq_nonneg _)
      _ = L * (∑ n ∈ P.map point, W n * ‖F n‖ ^ 2) := by
        rw [Finset.mul_sum, Finset.sum_map]
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum_of_subset_of_nonneg hsub fun n hn _ ↦
          mul_nonneg (hW n hn) (sq_nonneg _)) hL
  have hpair : (Q : ℂ) = ∑ p ∈ P, (w p : ℂ) * ξ p * F (point p) := by
    calc
      _ = ∑ i, conj (u i) * u i := by
        simp only [Q, Complex.ofReal_sum, Complex.sq_norm, ← Complex.mul_conj, mul_comm]
      _ = ∑ i, ∑ p ∈ P, conj (u i) * ((w p : ℂ) * ξ p * χ i (point p)) :=
        Finset.sum_congr rfl fun _ _ ↦ Finset.mul_sum _ _ _
      _ = ∑ p ∈ P, ∑ i, conj (u i) * ((w p : ℂ) * ξ p * χ i (point p)) := Finset.sum_comm
      _ = _ := by
        refine Finset.sum_congr rfl fun p _ ↦ ?_
        rw [show F (point p) = ∑ i, conj (u i) * χ i (point p) from rfl, Finset.mul_sum]
        exact Finset.sum_congr rfl fun _ _ ↦ by ring
  apply le_of_mul_le_mul_of_pos_right _ hpos
  calc
    Q * Q = ‖(Q : ℂ)‖ ^ 2 := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hQ, pow_two]
    _ ≤ B * (∑ p ∈ P, w p * ‖F (point p)‖ ^ 2) := by
      rw [hpair]
      exact weighted_cs P (fun p hp ↦ (hw p hp).1) hξ
    _ ≤ B * (L * (∑ n ∈ S, W n * ‖F n‖ ^ 2)) := mul_le_mul_of_nonneg_left hdom hB
    _ ≤ B * (L * (K * Q)) := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left (gram_form_le S χ hW hE hdiag hoff u) hL) hB
    _ = _ := by ring

/-- Finite cell bound for complex rows. The assigned points can be an arbitrary
subset of the integer support, in particular an ownership fibre of primes.
The bound only uses integer Gram inputs, and holds also for empty assignments
and vanishing weights. The row index has cardinality `N ≥ 1`. -/
public theorem sum_norm_moment_sq_le [Nonempty ι] (S : Finset ℤ) (P : Finset α)
    (point : α ↪ ℤ) {w : α → ℝ} {W : ℤ → ℝ} {ξ : α → ℂ} (χ : ι → ℤ → ℂ)
    {h L D E : ℝ} (hh : 0 < h) (hsub : P.map point ⊆ S)
    (hw : ∀ p ∈ P, 0 ≤ w p ∧ w p ≤ L) (hξ : ∀ p ∈ P, ‖ξ p‖ ≤ 1)
    (hW : ∀ n ∈ S, 0 ≤ W n) (hWP : ∀ p ∈ P, W (point p) = 1)
    (hD : 0 ≤ D) (hE : 0 ≤ E) (hdiag : ∀ i, ∑ n ∈ S, W n * ‖χ i n‖ ^ 2 ≤ D)
    (hoff : ∀ i j, i ≠ j → ‖gram S W χ i j‖ ≤ E) :
    (∑ i, ‖moment P point w ξ χ h i‖ ^ 2) ≤
      ((∑ p ∈ P, w p) / h) * (L / h) * (D + ((Fintype.card ι - 1 : ℕ) : ℝ) * E) := by
  simp only [moment, Complex.norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hh,
    div_pow, ← Finset.sum_div]
  refine (div_le_div_of_nonneg_right
    (unnormalized_le S P point χ hsub hw hξ hW hWP hD hE hdiag hoff) (sq_nonneg h)).trans_eq ?_
  rw [pow_two, ← div_div]
  ring

open SelbergIntervalDiagonal ShortCellSelbergOffDiagonal

private theorem natCast_Ioc (a h : ℕ) :
    (Ioc a (a + h)).map (Nat.castEmbedding : ℕ ↪ ℤ) = Ioc (a : ℤ) ((a : ℤ) + h) := by
  ext n
  simp only [Finset.mem_map, Finset.mem_Ioc, Nat.castEmbedding_apply]
  constructor
  · rintro ⟨m, hm, rfl⟩
    exact_mod_cast hm
  · intro hn
    have hnn : 0 ≤ n := (Int.natCast_nonneg a).trans hn.1.le
    have he := Int.toNat_of_nonneg hnn
    refine ⟨n.toNat, ?_, he⟩
    have hm : (a : ℤ) < (n.toNat : ℤ) ∧ (n.toNat : ℤ) ≤ (a : ℤ) + h := by
      simpa only [he] using hn
    exact_mod_cast hm

private theorem weight_eq_one_at_prime {z : ℤ} (hz : 1 ≤ z) {p : ℕ} (hp : p.Prime)
    (hpz : z < (p : ℤ)) : weight z (p : ℤ) = 1 := by
  have heq : (cutoff z).filter (fun k ↦ k ∣ p) = {1} := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨hk, hkp⟩
      rcases (Nat.dvd_prime hp).mp hkp with h | rfl
      · exact h
      · exact (not_lt_of_ge ((mem_cutoff hz).mp hk).2 hpz).elim
    · rintro rfl
      exact ⟨(mem_cutoff hz).mpr (by simpa using hz), one_dvd _⟩
  rw [weight_natCast, heq, Finset.sum_singleton, lambda_one hz, one_pow]

/-- Log-prime specialization for a cell `(a, a+h]` with natural endpoints.
Only the assigned primes must exceed the Selberg cutoff. The diagonal is
supplied by `SelbergIntervalDiagonal.interval_error_le`; the remaining bound
`E` is on integer off-diagonal entries for the pinned Selberg square. In
particular those entries are the sums of the pair rows to which
`ShortCellSelbergOffDiagonal.weighted_sum_norm_le` can be applied. -/
public theorem sum_norm_log_moment_sq_le_selberg [Nonempty ι] (P : Finset α)
    (prime : α ↪ ℕ) (χ : ι → ℤ → ℂ) {ξ : α → ℂ} {z : ℤ} {a h : ℕ} {E : ℝ}
    (hz : 1 ≤ z) (hh : 0 < h)
    (hP : ∀ p ∈ P, (prime p).Prime ∧ prime p ∈ Ioc a (a + h) ∧ z < (prime p : ℤ))
    (hξ : ∀ p ∈ P, ‖ξ p‖ ≤ 1)
    (hχ : ∀ i n, n ∈ Ioc (a : ℤ) ((a : ℤ) + h) → ‖χ i n‖ ≤ 1)
    (hE : 0 ≤ E)
    (hoff : ∀ i j, i ≠ j →
      ‖gram (Ioc (a : ℤ) ((a : ℤ) + h)) (weight z) χ i j‖ ≤ E) :
    (∑ i, ‖moment P (prime.trans (Nat.castEmbedding : ℕ ↪ ℤ))
      (fun p ↦ Real.log (prime p : ℝ)) ξ χ (h : ℝ) i‖ ^ 2) ≤
      ((∑ p ∈ P, Real.log (prime p : ℝ)) / (h : ℝ)) *
        (Real.log ((a + h : ℕ) : ℝ) / (h : ℝ)) *
        ((h : ℝ) / J z + (z : ℝ) ^ 2 + ((Fintype.card ι - 1 : ℕ) : ℝ) * E) := by
  let S : Finset ℤ := Ioc (a : ℤ) ((a : ℤ) + h)
  let point := prime.trans (Nat.castEmbedding : ℕ ↪ ℤ)
  have hsub : P.map point ⊆ S := by
    intro n hn
    obtain ⟨p, hp, rfl⟩ := Finset.mem_map.mp hn
    rw [show S = _ from (natCast_Ioc a h).symm]
    exact Finset.mem_map.mpr ⟨prime p, (hP p hp).2.1, rfl⟩
  have hw (p : α) (hp : p ∈ P) :
      0 ≤ Real.log (prime p : ℝ) ∧ Real.log (prime p : ℝ) ≤ Real.log ((a + h : ℕ) : ℝ) := by
    obtain ⟨hpp, hcell, _⟩ := hP p hp
    have hp₁ : 1 < (prime p : ℝ) := by exact_mod_cast hpp.one_lt
    exact ⟨Real.log_nonneg hp₁.le, Real.log_le_log (zero_lt_one.trans hp₁)
      (by exact_mod_cast (Finset.mem_Ioc.mp hcell).2)⟩
  have hW (n : ℤ) : 0 ≤ weight z n := sq_nonneg _
  have hJ := J_pos hz
  have hmass : (∑ n ∈ S, weight z n) ≤ (h : ℝ) / J z + (z : ℝ) ^ 2 := by
    rw [show S = _ from (natCast_Ioc a h).symm, Finset.sum_map]
    simp only [Nat.castEmbedding_apply, weight_natCast]
    linarith only [le_of_abs_le (interval_error_le hz a h)]
  refine sum_norm_moment_sq_le S P point χ (by exact_mod_cast hh) hsub hw hξ
    (fun n _ ↦ hW n) (fun p hp ↦ weight_eq_one_at_prime hz (hP p hp).1 (hP p hp).2.2)
    (by positivity) hE (fun i ↦ ?_) hoff
  refine (Finset.sum_le_sum fun n hn ↦ ?_).trans hmass
  calc
    weight z n * ‖χ i n‖ ^ 2 ≤ weight z n * 1 ^ 2 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hχ i n hn) 2) (hW n)
    _ = weight z n := by rw [one_pow, mul_one]

end ShortCellGramAssembly
