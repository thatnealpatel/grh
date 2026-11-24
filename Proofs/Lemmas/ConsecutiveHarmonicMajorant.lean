module

public import Lemmas.ConsecutiveHarmonicGrid
import all Lemmas.ConsecutiveHarmonicGrid
import Mathlib.Algebra.Polynomial.Sequence
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic

/-!
# An attaining majorant for the consecutive harmonics

Source: `8fde6138dc2ec249c6560b66ca0976aa8ea34dab:.godel/bob/initial-harmonic-budget.md:13`.
The majorant is used at `fea7eb0:.godel/alice/sharp-sparse-harmonics.md:38` for the consecutive
zero-moment upper bound. Here we prove global majorization of `|sin (s/2)|`,
contact at every shifted grid node, and the exact constant coefficient. We use
a Newton interpolation remainder instead of differentiating the square root.
No claim is made about the cost of the nonconstant coefficients.

Owning check session: `01a20b48-5cad-74c3-865b-b625005166b3`.
-/

open scoped BigOperators
open Polynomial

namespace Masullo.ConsecutiveHarmonicMajorant

open ConsecutiveHarmonicGrid (node average_abs_sin average_cos_sin_eq_zero)

/-- The remainder factors are built from nonnegative constants by sums and
multiplication by reciprocals of `z + b`, with `b > 0`. -/
private inductive PositiveRational : (ℝ → ℝ) → Prop
  | const (c : ℝ) (hc : 0 ≤ c) : PositiveRational (fun _ ↦ c)
  | add {f g} : PositiveRational f → PositiveRational g → PositiveRational (fun z ↦ f z + g z)
  | div {f} (b : ℝ) (hb : 0 < b) : PositiveRational f →
      PositiveRational (fun z ↦ f z / (z + b))

private theorem PositiveRational.nonneg {f : ℝ → ℝ} (hf : PositiveRational f)
    {z : ℝ} (hz : 0 ≤ z) : 0 ≤ f z := by
  induction hf with
  | const _ hc => exact hc
  | add _ _ ihf ihg => exact add_nonneg ihf ihg
  | div b hb _ ih => exact div_nonneg ih (by linarith)

-- The minus divided difference in the variable z² stays in the same class.
-- Formulate it as a factorization so repeated interpolation nodes are allowed.
private theorem PositiveRational.factor {f : ℝ → ℝ} (hf : PositiveRational f)
    {a : ℝ} (ha : 0 < a) :
    ∃ g, PositiveRational g ∧ ∀ z, 0 ≤ z → f z - f a = (a ^ 2 - z ^ 2) * g z := by
  induction hf with
  | const c hc => exact ⟨fun _ ↦ 0, .const 0 le_rfl, by simp⟩
  | @add f₁ f₂ hf₁ hf₂ ih₁ ih₂ =>
    obtain ⟨g₁, hg₁, h₁⟩ := ih₁
    obtain ⟨g₂, hg₂, h₂⟩ := ih₂
    refine ⟨fun z ↦ g₁ z + g₂ z, .add hg₁ hg₂, fun z hz ↦ ?_⟩
    dsimp
    linear_combination h₁ z hz + h₂ z hz
  | @div f b hb hf ih =>
    obtain ⟨g, hg, h⟩ := ih
    have hc : 0 ≤ f a / (a + b) := div_nonneg (hf.nonneg ha.le) (by positivity)
    refine ⟨fun z ↦ g z / (z + b) + f a / (a + b) / (z + b) / (z + a),
      .add (.div b hb hg) (.div a ha (.div b hb (.const _ hc))), fun z hz ↦ ?_⟩
    have hza : 0 < z + a := by positivity
    have hzb : 0 < z + b := by positivity
    have hab : 0 < a + b := by positivity
    dsimp
    rw [sub_eq_iff_eq_add.mp (h z hz)]
    field_simp
    ring

private noncomputable def nodeProduct (a : ℕ → ℝ) (m : ℕ) : ℝ[X] :=
  ∏ j ∈ Finset.range m, C (1 / 2 : ℝ) * (X - C (1 - 2 * a j ^ 2))

private theorem nodeProduct_degree (a : ℕ → ℝ) (m : ℕ) :
    (nodeProduct a m).natDegree ≤ m := by
  unfold nodeProduct
  refine (Polynomial.natDegree_prod_le _ _).trans ?_
  calc
    _ ≤ ∑ _j ∈ Finset.range m, (1 : ℕ) := Finset.sum_le_sum fun j _ ↦
      (Polynomial.natDegree_C_mul_le _ _).trans_eq (Polynomial.natDegree_X_sub_C _)
    _ = m := by simp

private theorem nodeProduct_eval (a : ℕ → ℝ) (m : ℕ) (z : ℝ) :
    (nodeProduct a m).eval (1 - 2 * z ^ 2) = ∏ j ∈ Finset.range m, (a j ^ 2 - z ^ 2) := by
  rw [nodeProduct, Polynomial.eval_prod]
  apply Finset.prod_congr rfl
  intro j _
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_sub, Polynomial.eval_X]
  ring

-- Newton interpolation in the variable 1 - 2z². Adding a node subtracts the
-- value of the old remainder factor there, times the old node product.
private theorem interpolation_remainder (a : ℕ → ℝ) (m : ℕ)
    (ha : ∀ j < m + 1, 0 < a j) :
    ∃ (P : ℝ[X]) (g : ℝ → ℝ), P.natDegree ≤ m ∧ PositiveRational g ∧
      ∀ z, 0 ≤ z → z = P.eval (1 - 2 * z ^ 2) -
        (∏ j ∈ Finset.range (m + 1), (a j ^ 2 - z ^ 2)) * g z := by
  induction m with
  | zero =>
    have ha₀ := ha 0 (by omega)
    refine ⟨C (a 0), fun z ↦ 1 / (z + a 0), by simp,
      .div _ ha₀ (.const 1 zero_le_one), fun z hz ↦ ?_⟩
    have hza : 0 < z + a 0 := by positivity
    simp only [Nat.zero_add, Polynomial.eval_C, Finset.prod_range_one]
    field_simp
    ring
  | succ m ih =>
    obtain ⟨P, g, hP, hg, hrem⟩ := ih fun j hj ↦ ha j (by omega)
    have ha' := ha (m + 1) (by omega)
    obtain ⟨g', hg', hfactor⟩ := hg.factor ha'
    refine ⟨P - C (g (a (m + 1))) * nodeProduct a (m + 1), g', ?_, hg', fun z hz ↦ ?_⟩
    · apply (Polynomial.natDegree_sub_le _ _).trans (max_le _ _)
      · omega
      · exact (Polynomial.natDegree_C_mul_le _ _).trans (nodeProduct_degree a (m + 1))
    · rw [Finset.prod_range_succ (fun j ↦ a j ^ 2 - z ^ 2) (m + 1),
        Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C, nodeProduct_eval]
      have h := sub_eq_iff_eq_add.mp (hfactor z hz)
      have hremz := hrem z hz
      rw [h] at hremz
      exact hremz.trans (by ring)

private theorem grid_value_pos {n j : ℕ} (hn : 2 ≤ n) (hj : j < n) :
    0 < |Real.sin (node n j / 2)| := by
  obtain ⟨hlo, hhi⟩ := ConsecutiveHarmonicGrid.node_mem_Ioo hn hj
  exact abs_pos.mpr (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)).ne'

private theorem grid_value_reflect {n j : ℕ} (hn : 2 ≤ n) (hj : j < n) :
    |Real.sin (node n (n - 1 - j) / 2)| = |Real.sin (node n j / 2)| := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hj' : ((n - 1 - j : ℕ) : ℝ) = (n : ℝ) - 1 - (j : ℝ) := by
    rw [Nat.cast_sub (by omega : j ≤ n - 1), Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one]
  have hreflect : node n (n - 1 - j) / 2 = Real.pi - node n j / 2 := by
    unfold node
    rw [hj']
    field_simp
    ring
  rw [hreflect, Real.sin_pi_sub]

private theorem grid_value_center {n m : ℕ} (hn : n = 2 * m + 1) :
    |Real.sin (node n m / 2)| = 1 := by
  have hn' : (n : ℝ) = 2 * (m : ℝ) + 1 := by exact_mod_cast hn
  have hn₀ : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hcenter : node n m / 2 = Real.pi / 2 := by
    unfold node
    rw [← hn']
    field_simp
  simp [hcenter, Real.sin_pi_div_two]

-- Reflected nodes have equal values: their factors contribute a square. The
-- only possible unpaired node is s = π, with factor 1 - z².
private theorem grid_product_nonneg {n : ℕ} (hn : 2 ≤ n) {z : ℝ}
    (hz : 0 ≤ z) (hz₁ : z ≤ 1) :
    0 ≤ ∏ j ∈ Finset.range n, (|Real.sin (node n j / 2)| ^ 2 - z ^ 2) := by
  let f (j : ℕ) := |Real.sin (node n j / 2)| ^ 2 - z ^ 2
  change 0 ≤ ∏ j ∈ Finset.range n, f j
  let m := n / 2
  let r := n % 2
  have hsplit : n = (m + r) + m := by dsimp [m, r]; omega
  have hr : r = 0 ∨ r = 1 := by dsimp [r]; omega
  have hlast : (∏ j ∈ Finset.range m, f (m + r + j)) = ∏ j ∈ Finset.range m, f j := calc
    _ = ∏ j ∈ Finset.range m, f (m + r + (m - 1 - j)) :=
      (Finset.prod_range_reflect (fun j ↦ f (m + r + j)) m).symm
    _ = _ := by
      apply Finset.prod_congr rfl
      intro j hj
      have hj' := Finset.mem_range.mp hj
      have hidx : m + r + (m - 1 - j) = n - 1 - j := by omega
      simp only [hidx, f, grid_value_reflect hn (by omega : j < n)]
  have hmid : 0 ≤ ∏ j ∈ Finset.range r, f (m + j) := by
    rcases hr with hr | hr
    · simp [hr]
    · have hm := grid_value_center (n := n) (m := m) (by omega)
      simp only [hr, Finset.prod_range_one, add_zero, f, hm, one_pow]
      nlinarith [mul_nonneg (sub_nonneg.mpr hz₁) (show 0 ≤ 1 + z by positivity)]
  rw [hsplit, Finset.prod_range_add f (m + r) m, hlast, Finset.prod_range_add f m r,
    mul_right_comm]
  exact mul_nonneg (mul_self_nonneg _) hmid

private theorem cos_eq_one_sub (s : ℝ) : Real.cos s = 1 - 2 * |Real.sin (s / 2)| ^ 2 := by
  calc
    Real.cos s = Real.cos (2 * (s / 2)) := congrArg Real.cos (by ring)
    _ = 1 - 2 * |Real.sin (s / 2)| ^ 2 := by
      rw [Real.cos_two_mul, sq_abs]
      nlinarith [Real.sin_sq_add_cos_sq (s / 2)]

private theorem exists_polynomial {n : ℕ} (hn : 2 ≤ n) :
    ∃ P : ℝ[X], P.natDegree < n ∧
      (∀ s : ℝ, |Real.sin (s / 2)| ≤ P.eval (Real.cos s)) ∧
      (∀ j < n, P.eval (Real.cos (node n j)) = |Real.sin (node n j / 2)|) := by
  let a (j : ℕ) := |Real.sin (node n j / 2)|
  have hn' : n - 1 + 1 = n := by omega
  obtain ⟨P, g, hP, hg, hrem⟩ := interpolation_remainder a (n - 1)
    (by rw [hn']; exact fun _ hj ↦ grid_value_pos hn hj)
  rw [hn'] at hrem
  have h (s : ℝ) :
      |Real.sin (s / 2)| = P.eval (Real.cos s) -
        (∏ j ∈ Finset.range n, (a j ^ 2 - |Real.sin (s / 2)| ^ 2)) * g |Real.sin (s / 2)| := by
    simpa only [← cos_eq_one_sub s] using hrem _ (abs_nonneg (Real.sin (s / 2)))
  refine ⟨P, by omega, fun s ↦ ?_, fun j hj ↦ ?_⟩
  · have hz := abs_nonneg (Real.sin (s / 2))
    have hnonneg := mul_nonneg (grid_product_nonneg hn hz (Real.abs_sin_le_one (s / 2)))
      (hg.nonneg hz)
    exact (h s).le.trans (sub_le_self _ hnonneg)
  · have hzero : (∏ i ∈ Finset.range n, (a i ^ 2 - a j ^ 2)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_range.mpr hj) (sub_self _)
    simpa only [← show a j = |Real.sin (node n j / 2)| from rfl, hzero, zero_mul, sub_zero]
      using (h (node n j)).symm

private theorem exists_cosine_expansion {P : ℝ[X]} {n : ℕ} (hP : P.natDegree < n) :
    ∃ (c : ℝ) (d : ℕ → ℝ), ∀ s : ℝ,
      P.eval (Real.cos s) = c + ∑ k ∈ Finset.Ico 1 n, d k * Real.cos ((k : ℝ) * s) := by
  let S : Polynomial.Sequence ℝ :=
    ⟨fun k ↦ Chebyshev.T ℝ (k : ℤ), fun k ↦ by simp⟩
  have hspan := S.span_degreeLT (m := n) fun k _ ↦
    isUnit_iff_ne_zero.mpr (Polynomial.leadingCoeff_ne_zero.mpr (S.ne_zero k))
  have hset : Set.range (fun i : Fin n ↦ S (i : ℕ)) = S '' Set.Iio n := by
    ext Q
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨i, i.isLt, rfl⟩
    · rintro ⟨k, hk, rfl⟩
      exact ⟨⟨k, hk⟩, rfl⟩
  have hmem : P ∈ Submodule.span ℝ (Set.range (fun i : Fin n ↦ S (i : ℕ))) := by
    rw [hset, hspan, Polynomial.mem_degreeLT]
    exact Polynomial.degree_le_natDegree.trans_lt (by exact_mod_cast hP)
  obtain ⟨b, hb⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hmem
  let d (k : ℕ) : ℝ := if hk : k < n then b ⟨k, hk⟩ else 0
  have hzero : 0 ∈ Finset.range n := Finset.mem_range.mpr (by omega)
  have herase : (Finset.range n).erase 0 = Finset.Ico 1 n := by
    ext k
    simp only [Finset.mem_erase, Finset.mem_range, Finset.mem_Ico]
    omega
  refine ⟨d 0, d, fun s ↦ ?_⟩
  let f (k : ℕ) := d k * Real.cos ((k : ℝ) * s)
  calc
    P.eval (Real.cos s) = ∑ i : Fin n, (b i • S (i : ℕ)).eval (Real.cos s) := by
      simpa only [Polynomial.eval_finsetSum] using congrArg (Polynomial.eval (Real.cos s)) hb.symm
    _ = ∑ i : Fin n, f i := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Polynomial.smul_eq_C_mul, Polynomial.eval_mul, Polynomial.eval_C]
      change b i * (Chebyshev.T ℝ ((i : ℕ) : ℤ)).eval (Real.cos s) = f i
      rw [Chebyshev.T_real_cos, Int.cast_natCast]
      simp [f, d, i.isLt]
    _ = ∑ k ∈ Finset.range n, f k := Fin.sum_univ_eq_sum_range f n
    _ = d 0 + ∑ k ∈ Finset.Ico 1 n, f k := by
      rw [← Finset.sum_erase_add _ f hzero, herase, add_comm]
      simp [f]

/-- For `n ≥ 2`, the consecutive harmonics of frequencies `1 ≤ k < n` admit
an even majorant on all of `ℝ` with constant term `1 / (n sin (π/(2n)))`
and equality at every node of the shifted grid. -/
public theorem exists_majorant {n : ℕ} (hn : 2 ≤ n) :
    ∃ d : ℕ → ℝ,
      (∀ s : ℝ, |Real.sin (s / 2)| ≤
        1 / ((n : ℝ) * Real.sin (Real.pi / (2 * (n : ℝ)))) +
          ∑ k ∈ Finset.Ico 1 n, d k * Real.cos ((k : ℝ) * s)) ∧
      (∀ j < n, 1 / ((n : ℝ) * Real.sin (Real.pi / (2 * (n : ℝ)))) +
          ∑ k ∈ Finset.Ico 1 n, d k * Real.cos ((k : ℝ) * node n j) =
        |Real.sin (node n j / 2)|) := by
  obtain ⟨P, hP, hmajor, hcontact⟩ := exists_polynomial hn
  obtain ⟨c, d, hcos⟩ := exists_cosine_expansion hP
  have hnode (j : ℕ) (hj : j < n) :
      c + ∑ k ∈ Finset.Ico 1 n, d k * Real.cos ((k : ℝ) * node n j) =
        |Real.sin (node n j / 2)| := (hcos _).symm.trans (hcontact j hj)
  have hn₀ : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hmode (k : ℕ) (hk : k ∈ Finset.Ico 1 n) :
      (∑ j ∈ Finset.range n, d k * Real.cos ((k : ℝ) * node n j)) = 0 := by
    obtain ⟨hk₁, hkn⟩ := Finset.mem_Ico.mp hk
    have hc := (div_eq_zero_iff.mp (average_cos_sin_eq_zero hn (by omega) hkn).1).resolve_right hn₀
    rw [← Finset.mul_sum, hc, mul_zero]
  have hsum : (∑ j ∈ Finset.range n, |Real.sin (node n j / 2)|) = (n : ℝ) * c := calc
    _ = ∑ j ∈ Finset.range n, (c + ∑ k ∈ Finset.Ico 1 n, d k * Real.cos ((k : ℝ) * node n j)) :=
      Finset.sum_congr rfl fun j hj ↦ (hnode j (Finset.mem_range.mp hj)).symm
    _ = _ := by
      rw [Finset.sum_add_distrib, Finset.sum_comm, Finset.sum_eq_zero hmode]
      simp [nsmul_eq_mul]
  have hc : 1 / ((n : ℝ) * Real.sin (Real.pi / (2 * (n : ℝ)))) = c := by
    rw [← average_abs_sin hn, hsum, mul_comm, mul_div_cancel_right₀ _ hn₀]
  refine ⟨d, fun s ↦ ?_, fun j hj ↦ ?_⟩
  · rw [hc, ← hcos]
    exact hmajor s
  · rw [hc]
    exact hnode j hj

end Masullo.ConsecutiveHarmonicMajorant
