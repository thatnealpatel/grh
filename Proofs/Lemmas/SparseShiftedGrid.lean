module

public import Lemmas.ConsecutiveHarmonicGrid
import all Lemmas.ConsecutiveHarmonicGrid -- unfold the accepted grid node
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.RingTheory.RootsOfUnity.Complex

/-!
# Sparse queried moments on an independently shifted grid

Source: `fea7eb0b:.godel/alice/sharp-sparse-harmonics.md:13–38`, “Pay for the shifts.”
Use: `059232cf:.godel/bob/noisy-sparse-harmonics.md:11–16` uses the resulting
exact-zero witness as a mixture of grid translates. The obligation at pin
`059232cff7d3894d8545eb11ffccf9cd2fec1646` is unchanged from `e96c4611`.
Here we prove the moment conditions and the product lower bound for that mixture,
not the comparison with `C_N` or the noisy or unrestricted minimax bounds.

Owning check session: `01a20c71-faab-7613-8747-63acf6b0d98e`.
-/

open scoped BigOperators

namespace Masullo.SparseShiftedGrid

open ConsecutiveHarmonicGrid (node)

/-- Only queries divisible by the grid size require a shift. -/
@[expose] public def shiftedQueries (n : ℕ) (J : Finset ℕ) : Finset ℕ :=
  J.filter (fun j ↦ n ∣ j)

/-- The radius of the fair two-point shift for query `j`. -/
@[expose] public noncomputable def radius (j : ℕ) : ℝ := Real.pi / (2 * (j : ℝ))

/-- The total shift when precisely the indices in `P ⊆ K` take the plus sign. -/
@[expose] public noncomputable def translation (K P : Finset ℕ) : ℝ :=
  ∑ j ∈ K, if j ∈ P then radius j else -radius j

/-- Expectation for the mixture of translates of the uniform odd `π/n` grid.
The powerset indexes each independent fair sign assignment once, and `range n`
indexes each grid node once for each assignment. Coincident outcomes are counted
with multiplicity. We evaluate on the real lifts, without selecting representatives. -/
@[expose] public noncomputable def average {A : Type*} [Field A] [CharZero A]
    (n : ℕ) (K : Finset ℕ) (f : ℝ → A) : A :=
  (∑ P ∈ K.powerset, ∑ l ∈ Finset.range n, f (node n l + translation K P)) /
    (2 : A) ^ K.card / (n : A)

private noncomputable def shiftAverage {A : Type*} [Field A] [CharZero A]
    (K : Finset ℕ) (f : ℝ → A) (s : ℝ) : A :=
  (∑ P ∈ K.powerset, f (s + translation K P)) / (2 : A) ^ K.card

private theorem average_eq_grid_average {A : Type*} [Field A] [CharZero A]
    (n : ℕ) (K : Finset ℕ) (f : ℝ → A) :
    average n K f = (∑ l ∈ Finset.range n, shiftAverage K f (node n l)) / (n : A) := by
  rw [average, Finset.sum_comm]
  simp only [shiftAverage, div_eq_mul_inv, Finset.sum_mul]

/-- The mixture has mass one; in particular the normalization retains multiplicity. -/
public theorem average_const_one {A : Type*} [Field A] [CharZero A]
    {n : ℕ} (hn : 0 < n) (K : Finset ℕ) : average n K (fun _ ↦ (1 : A)) = 1 := by
  have hn' : (n : A) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have hK : (2 : A) ^ K.card ≠ 0 := pow_ne_zero _ (by norm_num)
  rw [average_eq_grid_average]
  simp [shiftAverage, Finset.card_powerset, nsmul_eq_mul, hK, hn']

private theorem translation_insert_neg {j : ℕ} {K P : Finset ℕ}
    (hj : j ∉ K) (hP : P ⊆ K) :
    translation (insert j K) P = translation K P - radius j := by
  simp only [translation, Finset.sum_insert hj, ite_eq_right (fun h ↦ hj (hP h))]
  ring

private theorem translation_insert_pos {j : ℕ} {K P : Finset ℕ} (hj : j ∉ K) :
    translation (insert j K) (insert j P) = translation K P + radius j := by
  simp only [translation, Finset.sum_insert hj, Finset.mem_insert_self, ite_true]
  rw [add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  have hkj : k ≠ j := by rintro rfl; exact hj hk
  simp only [Finset.mem_insert, hkj, false_or]

private theorem shiftAverage_empty {A : Type*} [Field A] [CharZero A] (f : ℝ → A) (s : ℝ) :
    shiftAverage ∅ f s = f s := by
  simp [shiftAverage, translation]

private theorem shiftAverage_insert {A : Type*} [Field A] [CharZero A]
    {j : ℕ} {K : Finset ℕ} (hj : j ∉ K) (f : ℝ → A) (s : ℝ) :
    shiftAverage (insert j K) f s =
      (shiftAverage K f (s - radius j) + shiftAverage K f (s + radius j)) / 2 := by
  rw [shiftAverage, Finset.sum_powerset_insert hj, Finset.card_insert_of_notMem hj, pow_succ]
  have hneg : (∑ P ∈ K.powerset, f (s + translation (insert j K) P)) =
      ∑ P ∈ K.powerset, f (s - radius j + translation K P) := by
    refine Finset.sum_congr rfl fun P hP ↦ ?_
    rw [translation_insert_neg hj (Finset.mem_powerset.mp hP)]
    congr 1
    ring
  have hpos : (∑ P ∈ K.powerset, f (s + translation (insert j K) (insert j P))) =
      ∑ P ∈ K.powerset, f (s + radius j + translation K P) := by
    refine Finset.sum_congr rfl fun P _ ↦ ?_
    rw [translation_insert_pos hj]
    congr 1
    ring
  rw [hneg, hpos]
  simp only [shiftAverage, ← add_div, div_div]

private noncomputable def mode (j : ℕ) (s : ℝ) : ℂ :=
  Complex.exp (↑((j : ℝ) * s) * Complex.I)

private theorem mode_add (j : ℕ) (s t : ℝ) : mode j (s + t) = mode j s * mode j t := by
  simp only [mode, mul_add, Complex.ofReal_add, add_mul, Complex.exp_add]

private noncomputable def multiplier (j k : ℕ) : ℂ :=
  (mode j (-radius k) + mode j (radius k)) / 2

private theorem shiftAverage_mode (K : Finset ℕ) (j : ℕ) (s : ℝ) :
    shiftAverage K (mode j) s = mode j s * ∏ k ∈ K, multiplier j k := by
  induction K using Finset.induction_on generalizing s with
  | empty => simp [shiftAverage_empty]
  | @insert k K hk ih =>
    rw [shiftAverage_insert hk, ih, ih, sub_eq_add_neg, mode_add, mode_add,
      Finset.prod_insert hk, multiplier]
    ring

private theorem multiplier_self {j : ℕ} (hj : 0 < j) : multiplier j j = 0 := by
  have hj' : (j : ℝ) ≠ 0 := (Nat.cast_pos.mpr hj).ne'
  have hangle : (j : ℝ) * radius j = Real.pi / 2 := by
    unfold radius
    field_simp
  have hpos : mode j (radius j) = Complex.I := by
    rw [mode, hangle, Complex.ofReal_div, Complex.ofReal_ofNat, Complex.exp_pi_div_two_mul_I]
  have hneg : mode j (-radius j) = -Complex.I := by
    rw [mode, mul_neg, Complex.ofReal_neg, neg_mul, Complex.exp_neg, ← mode, hpos, Complex.inv_I]
  rw [multiplier, hpos, hneg, neg_add_cancel, zero_div]

-- The grid annihilates every nonmultiple, not just frequencies below `n`.
private theorem grid_sum_mode_eq_zero {n j : ℕ} (hn : 0 < n) (hj : ¬ n ∣ j) :
    (∑ l ∈ Finset.range n, mode j (node n l)) = 0 := by
  let ω : ℂ := 2 * ↑Real.pi * Complex.I / (n : ℂ)
  let ζ : ℂ := Complex.exp ω
  have hroot : IsPrimitiveRoot ζ n := Complex.isPrimitiveRoot_exp n hn.ne'
  have hpow : (ζ ^ j) ^ n = 1 := by
    rw [← pow_mul, Nat.mul_comm j n, pow_mul, hroot.pow_eq_one, one_pow]
  have hgeom : (∑ l ∈ Finset.range n, (ζ ^ j) ^ l) = 0 := by
    have h := geom_sum_mul (ζ ^ j) n
    rw [hpow, sub_self] at h
    exact (mul_eq_zero.mp h).resolve_right
      (sub_ne_zero.mpr (fun h ↦ hj (hroot.dvd_of_pow_eq_one j h)))
  have hfactor (l : ℕ) :
      mode j (node n l) = mode j (Real.pi / (n : ℝ)) * (ζ ^ j) ^ l := by
    have harg : (↑((j : ℝ) * node n l) : ℂ) * Complex.I =
        ↑((j : ℝ) * (Real.pi / (n : ℝ))) * Complex.I + (l : ℂ) * ((j : ℂ) * ω) := by
      unfold node ω
      push_cast
      ring
    simp only [mode, ζ, harg, Complex.exp_add, Complex.exp_nat_mul]
  simp only [hfactor, ← Finset.mul_sum, hgeom, mul_zero]

private theorem average_mode_eq_zero {n j : ℕ} {J : Finset ℕ}
    (hn : 0 < n) (hj : 0 < j) (hjJ : j ∈ J) : average n (shiftedQueries n J) (mode j) = 0 := by
  rw [average_eq_grid_average]
  simp only [shiftAverage_mode, ← Finset.sum_mul]
  by_cases hdvd : n ∣ j
  · have hk : j ∈ shiftedQueries n J := Finset.mem_filter.mpr ⟨hjJ, hdvd⟩
    rw [Finset.prod_eq_zero hk (multiplier_self hj), mul_zero, zero_div]
  · rw [grid_sum_mode_eq_zero hn hdvd, zero_mul, zero_div]

private noncomputable def envelope (s : ℝ) : ℝ := |Real.sin (s / 2)|

private theorem radius_half (j : ℕ) : radius j / 2 = Real.pi / (4 * (j : ℝ)) := by
  unfold radius
  ring

private theorem cos_radius_nonneg {j : ℕ} (hj : 0 < j) : 0 ≤ Real.cos (radius j / 2) := by
  have hj' : 1 ≤ (j : ℝ) := Nat.one_le_cast.mpr hj
  rw [radius_half]
  apply Real.cos_nonneg_of_mem_Icc
  refine ⟨?_, div_le_div_of_nonneg_left Real.pi_pos.le (by norm_num) (by linarith)⟩
  have hd : 0 ≤ Real.pi / (4 * (j : ℝ)) := by positivity
  linarith [Real.pi_pos]

-- The absolute-value estimate holds on all real lifts, even across a wrap.
private theorem pair_envelope_ge (s d : ℝ) (hc : 0 ≤ Real.cos (d / 2)) :
    envelope s * Real.cos (d / 2) ≤ (envelope (s - d) + envelope (s + d)) / 2 := by
  have hsin : Real.sin ((s - d) / 2) + Real.sin ((s + d) / 2) =
      2 * (Real.sin (s / 2) * Real.cos (d / 2)) := by
    rw [show (s - d) / 2 = s / 2 - d / 2 by ring,
      show (s + d) / 2 = s / 2 + d / 2 by ring, Real.sin_sub, Real.sin_add]
    ring
  have h := abs_add_le (Real.sin ((s - d) / 2)) (Real.sin ((s + d) / 2))
  rw [hsin, abs_mul, abs_mul, abs_of_nonneg hc, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)] at h
  exact (le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).2 (by simpa [envelope, mul_comm] using h)

private theorem shiftAverage_envelope_ge (K : Finset ℕ) (hK : ∀ j ∈ K, 0 < j) (s : ℝ) :
    envelope s * (∏ j ∈ K, Real.cos (radius j / 2)) ≤ shiftAverage K envelope s := by
  induction K using Finset.induction_on generalizing s with
  | empty => simp [shiftAverage_empty]
  | @insert j K hj ih =>
    have hK' (k : ℕ) (hk : k ∈ K) : 0 < k := hK k (Finset.mem_insert_of_mem hk)
    have hc := cos_radius_nonneg (hK j (Finset.mem_insert_self _ _))
    let p := ∏ k ∈ K, Real.cos (radius k / 2)
    have hp : 0 ≤ p := Finset.prod_nonneg fun k hk ↦ cos_radius_nonneg (hK' k hk)
    rw [Finset.prod_insert hj, shiftAverage_insert hj]
    calc
      _ = (envelope s * Real.cos (radius j / 2)) * p := by rw [mul_assoc]
      _ ≤ ((envelope (s - radius j) + envelope (s + radius j)) / 2) * p :=
        mul_le_mul_of_nonneg_right (pair_envelope_ge s (radius j) hc) hp
      _ = (envelope (s - radius j) * p + envelope (s + radius j) * p) / 2 := by ring
      _ ≤ _ := div_le_div_of_nonneg_right
        (add_le_add (ih hK' (s - radius j)) (ih hK' (s + radius j))) (by norm_num)

private theorem grid_average_envelope {n : ℕ} (hn : 0 < n) :
    (∑ l ∈ Finset.range n, envelope (node n l)) / (n : ℝ) =
      1 / ((n : ℝ) * Real.sin (Real.pi / (2 * (n : ℝ)))) := by
  by_cases h : n = 1
  · subst n
    simp [envelope, node, Real.sin_pi_div_two]
  · exact ConsecutiveHarmonicGrid.average_abs_sin (by omega)

private theorem average_envelope_ge {n : ℕ} (hn : 0 < n) (K : Finset ℕ)
    (hK : ∀ j ∈ K, 0 < j) :
    (1 / ((n : ℝ) * Real.sin (Real.pi / (2 * (n : ℝ))))) *
        (∏ j ∈ K, Real.cos (Real.pi / (4 * (j : ℝ)))) ≤ average n K envelope := by
  rw [average_eq_grid_average, ← grid_average_envelope hn, div_mul_eq_mul_div, Finset.sum_mul]
  simp only [← radius_half]
  exact div_le_div_of_nonneg_right
    (Finset.sum_le_sum fun l _ ↦ shiftAverage_envelope_ge K hK (node n l)) (Nat.cast_nonneg n)

/-- The explicit shifted-grid law kills all queried complex moments and retains
at least the original grid mean `C_n` times the product of the cosine factors. -/
public theorem annihilates_and_mean_ge {n : ℕ} (hn : 0 < n) (J : Finset ℕ)
    (hJ : ∀ j ∈ J, 0 < j) :
    (∀ j ∈ J, average n (shiftedQueries n J)
      (fun s ↦ Complex.exp (↑((j : ℝ) * s) * Complex.I)) = 0) ∧
    (1 / ((n : ℝ) * Real.sin (Real.pi / (2 * (n : ℝ))))) *
        (∏ j ∈ shiftedQueries n J, Real.cos (Real.pi / (4 * (j : ℝ)))) ≤
      average n (shiftedQueries n J) (fun s ↦ |Real.sin (s / 2)|) := by
  refine ⟨fun j hj ↦ average_mode_eq_zero hn (hJ j hj) hj, ?_⟩
  exact average_envelope_ge hn (shiftedQueries n J) fun j hj ↦ hJ j (Finset.mem_filter.mp hj).1

end Masullo.SparseShiftedGrid
