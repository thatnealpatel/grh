module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fin.Tuple.Basic

/-!
# Triangular differencing of finite gap means

Source: `dcc11ec5bbd653cbb1068ea454799744de33fb73:.godel/bob/signed-gap-cube-screen.md`,
“Differencing the original sum”, through the lower bound `A_k ≥ δ` used in (1).
Owning check session: `01a20a16-7036-75bb-8ab9-3bc3a536b6e9`.

The average is over all gaps and cyclic starts, including zeros of the input, and
all ordered pairs of independent interval draws in each slot. Translation is
used on the start variable alone. Neither the correlation identity nor the
inequality needs the source's pointwise unit bound or any no-wrap assumption.
The prime support, repeated-vertex deletion, and frequency estimates are outside
this module.
-/

open scoped BigOperators ComplexConjugate

namespace Masullo.TriangularGapDifferencing

variable {G B P : Type*} [AddCommGroup P]

/-- The shifted value is the unconjugated factor. -/
@[expose] public def difference (h : P) (F : P → ℂ) (p : P) : ℂ :=
  F (p + h) * conj (F p)

/-- Apply the first pair's difference first and the last pair's difference last. -/
@[expose] public def iteratedDifference (shift : B → P) (F : P → ℂ) :
    (k : ℕ) → (Fin k → B × B) → P → ℂ
  | 0, _ => F
  | k + 1, b =>
    difference (shift (b (Fin.last k)).1 - shift (b (Fin.last k)).2)
      (iteratedDifference shift F k (Fin.init b))

variable [Fintype G] [Fintype B] [Fintype P]

/-- The normalized complex average, with a separate uniform average over gaps,
ordered tuples of draw pairs, and starts. -/
@[expose] public noncomputable def averagedDifference (shift : B → P) (f : G → P → ℂ)
    (k : ℕ) : ℂ :=
  𝔼 g, 𝔼 b : Fin k → B × B, 𝔼 p, iteratedDifference shift (f g) k b p

private theorem expect_prod {α β M : Type*} [Fintype α] [Fintype β]
    [AddCommMonoid M] [Module ℚ≥0 M] (f : α × β → M) :
    (𝔼 x, f x) = 𝔼 a, 𝔼 b, f (a, b) := by
  rw [← Finset.expect_product', Finset.univ_product_univ]

private theorem expect_snoc {α M : Type*} [Fintype α] [AddCommMonoid M]
    [Module ℚ≥0 M] {k : ℕ} (f : (Fin (k + 1) → α) → M) :
    (𝔼 b, f b) = 𝔼 a : Fin k → α, 𝔼 x : α, f (Fin.snoc a x) := by
  let e : ((Fin k → α) × α) ≃ (Fin (k + 1) → α) :=
    (Equiv.prodComm _ _).trans (Fin.snocEquiv fun _ => α)
  rw [← Fintype.expect_equiv e (fun x => f (Fin.snoc x.1 x.2)) f (fun _ => rfl), expect_prod]

private theorem expect_translate (h : P) (F : P → ℂ) :
    (𝔼 p, F (p + h)) = 𝔼 p, F p :=
  Fintype.expect_equiv (Equiv.addRight h) _ _ (fun _ => rfl)

private theorem conj_expect {α : Type*} [Fintype α] (F : α → ℂ) :
    conj (𝔼 a, F a) = 𝔼 a, conj (F a) := by
  simp only [Finset.expect, map_smul, map_sum]

private theorem expect_sq {α : Type*} [Fintype α] [Nonempty α] (F : α → ℝ) :
    (𝔼 a, F a) ^ 2 ≤ 𝔼 a, F a ^ 2 := by
  simpa [Fintype.expect_const] using
    Finset.expect_mul_sq_le_sq_mul_sq Finset.univ (fun _ : α => (1 : ℝ)) F

private noncomputable def shiftEnergy (shift : B → P) (F : P → ℂ) : ℝ :=
  𝔼 p, ‖𝔼 b, F (p + shift b)‖ ^ 2

/-- Expand the square using two draws and translate `p` by the second draw.
The two draw indices stay fixed in this reindexing. -/
private theorem correlation_eq_shiftEnergy (shift : B → P) (F : P → ℂ) :
    (𝔼 b : B × B, 𝔼 p, difference (shift b.1 - shift b.2) F p) =
      (shiftEnergy shift F : ℂ) := by
  rw [expect_prod]
  simp only [shiftEnergy, Complex.ofReal_expect, Complex.sq_norm, ← Complex.mul_conj,
    conj_expect, Finset.expect_mul_expect]
  conv_rhs =>
    rw [Finset.expect_comm Finset.univ Finset.univ]
    enter [2, b]
    rw [Finset.expect_comm Finset.univ Finset.univ]
  refine Finset.expect_congr rfl fun b _ => Finset.expect_congr rfl fun b' _ => ?_
  refine Fintype.expect_equiv (Equiv.subRight (shift b')) _ _ fun p => ?_
  change F (p + (shift b - shift b')) * conj (F p) =
    F (p - shift b' + shift b) * conj (F (p - shift b' + shift b'))
  rw [sub_add_cancel, sub_add_eq_add_sub, add_sub_assoc]

private theorem norm_expect_sq_le_shiftEnergy [Nonempty B] (shift : B → P) (F : P → ℂ) :
    ‖𝔼 p, F p‖ ^ 2 ≤ shiftEnergy shift F := by
  have hmean : (𝔼 p, 𝔼 b, F (p + shift b)) = 𝔼 p, F p := by
    rw [Finset.expect_comm]
    simp only [expect_translate, Fintype.expect_const]
  rw [← hmean]
  exact (pow_le_pow_left₀ (norm_nonneg _) (RCLike.norm_expect_le (K := ℂ)) 2).trans
    (expect_sq _)

private theorem averagedDifference_succ_eq (shift : B → P) (f : G → P → ℂ) (k : ℕ) :
    averagedDifference shift f (k + 1) =
      (↑(𝔼 g, 𝔼 a : Fin k → B × B,
        shiftEnergy shift (iteratedDifference shift (f g) k a)) : ℂ) := by
  simp only [averagedDifference, Complex.ofReal_expect]
  refine Finset.expect_congr rfl fun g _ => ?_
  rw [expect_snoc]
  refine Finset.expect_congr rfl fun a _ => ?_
  simpa only [iteratedDifference, Fin.init_snoc, Fin.snoc_last] using
    correlation_eq_shiftEnergy shift (iteratedDifference shift (f g) k a)

private noncomputable def meanNorm (shift : B → P) (f : G → P → ℂ) (k : ℕ) : ℝ :=
  𝔼 g, 𝔼 a : Fin k → B × B, ‖𝔼 p, iteratedDifference shift (f g) k a p‖

private theorem re_le_meanNorm (shift : B → P) (f : G → P → ℂ) (k : ℕ) :
    (averagedDifference shift f k).re ≤ meanNorm shift f k := by
  rw [averagedDifference, meanNorm, Complex.re_expect]
  refine Finset.expect_le_expect fun g _ => ?_
  rw [Complex.re_expect]
  exact Finset.expect_le_expect fun _ _ => Complex.re_le_norm _

private theorem meanNorm_sq_le_re_succ [Nonempty G] [Nonempty B]
    (shift : B → P) (f : G → P → ℂ) (k : ℕ) :
    meanNorm shift f k ^ 2 ≤ (averagedDifference shift f (k + 1)).re := by
  rw [averagedDifference_succ_eq, Complex.ofReal_re, meanNorm]
  refine (expect_sq _).trans (Finset.expect_le_expect fun g _ => ?_)
  refine (expect_sq _).trans (Finset.expect_le_expect fun a _ => ?_)
  exact norm_expect_sq_le_shiftEnergy shift (iteratedDifference shift (f g) k a)

/-- The unrotated average after `k ≥ 1` differences is real, and its real part
bounds the `2^k`-th power of the mean of the gapwise absolute start means.
In each slot the shift is the difference of two independent draws from `B`. -/
public theorem iteratedDifference_bound [Nonempty G] [Nonempty B]
    (shift : B → P) (f : G → P → ℂ) {k : ℕ} (hk : 1 ≤ k) :
    (averagedDifference shift f k).im = 0 ∧
      (𝔼 g, ‖𝔼 p, f g p‖) ^ (2 ^ k) ≤ (averagedDifference shift f k).re := by
  have hnonneg : 0 ≤ 𝔼 g, ‖𝔼 p, f g p‖ :=
    Finset.expect_nonneg fun _ _ => norm_nonneg _
  have hbound (j : ℕ) :
      (𝔼 g, ‖𝔼 p, f g p‖) ^ (2 ^ (j + 1)) ≤ (averagedDifference shift f (j + 1)).re := by
    induction j with
    | zero =>
      simpa [meanNorm, iteratedDifference, Fintype.expect_const] using
        meanNorm_sq_le_re_succ shift f 0
    | succ j ih =>
      rw [pow_succ (2 : ℕ), pow_mul]
      exact (pow_le_pow_left₀ (pow_nonneg hnonneg _)
        (ih.trans (re_le_meanNorm shift f (j + 1))) 2).trans
        (meanNorm_sq_le_re_succ shift f (j + 1))
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk)
  exact ⟨by rw [averagedDifference_succ_eq, Complex.ofReal_im], hbound j⟩

/-- Label the integers `1, …, H` by `Fin H`, then reduce into the group of starts.
The law remains uniform on the labels, even if reduction is not injective. -/
@[expose] public def intervalDraw (N H : ℕ) (b : Fin H) : ZMod N :=
  ((b.val + 1 : ℕ) : ZMod N)

/-- Cyclic interval-draw case. In the source, `G` is the set of integers from
`1` to `⌊X⌋` and `N = 2 * ⌊X⌋ + 1`. Each pair gives the reduction of the
integer difference `b_i - b'_i`, not a uniform draw from `ZMod N`. -/
public theorem cyclic_iteratedDifference_bound [Nonempty G] {N H k : ℕ} [NeZero N]
    (hH : 1 ≤ H) (hk : 1 ≤ k) (f : G → ZMod N → ℂ) :
    (averagedDifference (intervalDraw N H) f k).im = 0 ∧
      (𝔼 g, ‖𝔼 p, f g p‖) ^ (2 ^ k) ≤
        (averagedDifference (intervalDraw N H) f k).re := by
  let : Nonempty (Fin H) := ⟨⟨0, hH⟩⟩
  exact iteratedDifference_bound (intervalDraw N H) f hk

end Masullo.TriangularGapDifferencing
