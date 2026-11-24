module

public import Lemmas.ConsecutiveHarmonicGrid
import all Lemmas.ConsecutiveHarmonicGrid -- unfold the shifted node in the cosine bound
public import Mathlib.Data.Nat.Dist
import Mathlib.Algebra.BigOperators.Field

/-!
# Sharp threshold for a zero prefix of longer cosine moments

Source: `3d2886df57b8eae8638274327fc4ea62d473ccc0:.godel/bob/finite-cutoff-budget.md`,
lines 11–38, “A signed test, and a matching law”; used in the zero-longer-measurements
comparison in `.godel/bob/long-cutoff-moments.md` at the same revision.

The exclusion is at the level of necessary Toeplitz positivity. The converse
constructs the boundary cosine law on the shifted grid, including at equality.
This is an exact statement about the normalized angular moment model, not a
claim that any prime or divisor measurements realize the law.

Owning check session: `01a20c3b-0de7-75d0-b4f0-194be0854305`.
-/

open scoped BigOperators

namespace Masullo.ZeroPrefixCosine

/-- The spacing parameter of the sine test and the half-step of the grid. -/
@[expose] public noncomputable def angle (n : ℕ) : ℝ := Real.pi / ((n : ℝ) + 2)

/-- Largest magnitude of the negative first cosine moment in the zero-prefix model. -/
@[expose] public noncomputable def threshold (n : ℕ) : ℝ := 1 / (2 * Real.cos (angle n))

/-- The `k`-th cosine moment of a finite weighted angle law. -/
@[expose] public noncomputable def moment {ι : Type*} (s : Finset ι) (w θ : ι → ℝ) (k : ℕ) : ℝ :=
  ∑ l ∈ s, w l * Real.cos ((k : ℝ) * θ l)

/-- Positivity of the real Toeplitz form indexed by `0, …, n`. -/
@[expose] public def ToeplitzPositive (n : ℕ) (m : ℕ → ℝ) : Prop :=
  ∀ v : ℕ → ℝ, 0 ≤ ∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n + 1),
    v i * v j * m (Nat.dist i j)

private theorem cos_dist (x : ℝ) (i j : ℕ) :
    Real.cos ((Nat.dist i j : ℝ) * x) =
      Real.cos ((i : ℝ) * x) * Real.cos ((j : ℝ) * x) +
      Real.sin ((i : ℝ) * x) * Real.sin ((j : ℝ) * x) := by
  rcases le_total i j with h | h
  · rw [Nat.dist_eq_sub_of_le h, Nat.cast_sub h, sub_mul, Real.cos_sub]
    ring
  · rw [Nat.dist_comm i j, Nat.dist_eq_sub_of_le h, Nat.cast_sub h, sub_mul, Real.cos_sub]

/-- Arbitrary finite nonnegative angle data give a positive Toeplitz form. -/
public theorem toeplitzPositive_moment {ι : Type*} (n : ℕ) (s : Finset ι) (w θ : ι → ℝ)
    (hw : ∀ l ∈ s, 0 ≤ w l) : ToeplitzPositive n (moment s w θ) := by
  intro v
  let r := Finset.range (n + 1)
  change 0 ≤ ∑ i ∈ r, ∑ j ∈ r, v i * v j * moment s w θ (Nat.dist i j)
  have hswap :
      (∑ i ∈ r, ∑ j ∈ r, v i * v j * moment s w θ (Nat.dist i j)) =
        ∑ l ∈ s, w l * ∑ i ∈ r, ∑ j ∈ r,
          (v i * v j * Real.cos ((Nat.dist i j : ℝ) * θ l)) := by
    simp only [moment, Finset.mul_sum]
    calc
      _ = ∑ i ∈ r, ∑ l ∈ s, ∑ j ∈ r,
          v i * v j * (w l * Real.cos ((Nat.dist i j : ℝ) * θ l)) := by
            exact Finset.sum_congr rfl (fun i _ ↦ Finset.sum_comm)
      _ = _ := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun l _ ↦ Finset.sum_congr rfl fun i _ ↦
          Finset.sum_congr rfl fun j _ ↦ ?_
        ring
  rw [hswap]
  refine Finset.sum_nonneg fun l hl ↦ mul_nonneg (hw l hl) ?_
  let c (i : ℕ) := v i * Real.cos ((i : ℝ) * θ l)
  let d (i : ℕ) := v i * Real.sin ((i : ℝ) * θ l)
  calc
    0 ≤ (∑ i ∈ r, c i) ^ 2 + (∑ i ∈ r, d i) ^ 2 := by positivity
    _ = ∑ i ∈ r, ∑ j ∈ r, v i * v j * Real.cos ((Nat.dist i j : ℝ) * θ l) := by
      simp only [pow_two, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
      rw [cos_dist]
      dsimp only [c, d]
      ring

private theorem angle_pos (n : ℕ) : 0 < angle n :=
  div_pos Real.pi_pos (by positivity)

private theorem angle_lt_half_pi {n : ℕ} (hn : 1 ≤ n) : angle n < Real.pi / 2 := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  unfold angle
  apply (div_lt_div_iff₀ (by positivity) (by norm_num : (0 : ℝ) < 2)).2
  nlinarith only [mul_pos Real.pi_pos hn']

private theorem cos_angle_pos {n : ℕ} (hn : 1 ≤ n) : 0 < Real.cos (angle n) :=
  Real.cos_pos_of_mem_Ioo ⟨by linarith [angle_pos n, Real.pi_pos], angle_lt_half_pi hn⟩

private theorem sine_recurrence (α : ℝ) (i : ℕ) :
    Real.sin ((i : ℝ) * α) + Real.sin (((i : ℝ) + 2) * α) =
      2 * Real.cos α * Real.sin (((i : ℝ) + 1) * α) := by
  rw [show (i : ℝ) * α = ((i : ℝ) + 1) * α - α by ring,
    show ((i : ℝ) + 2) * α = ((i : ℝ) + 1) * α + α by ring,
    Real.sin_sub, Real.sin_add]
  ring

private theorem sine_row {n : ℕ} {m : ℕ → ℝ} (h0 : m 0 = 1)
    (hz : ∀ k : ℕ, 2 ≤ k → k ≤ n → m k = 0) {i : ℕ} (hi : i ≤ n) :
    let v (j : ℕ) := Real.sin (((j : ℝ) + 1) * angle n)
    (∑ j ∈ Finset.range (n + 1), v j * m (Nat.dist i j)) =
      (1 + 2 * Real.cos (angle n) * m 1) * v i := by
  dsimp only
  let α := angle n
  let v (j : ℕ) := Real.sin (((j : ℝ) + 1) * α)
  let r := Finset.range (n + 1)
  change (∑ j ∈ r, v j * m (Nat.dist i j)) = (1 + 2 * Real.cos α * m 1) * v i
  have hentry (j : ℕ) (hj : j ∈ r) :
      v j * m (Nat.dist i j) =
        (if j = i then v i else 0) + (if j = i + 1 then v (i + 1) * m 1 else 0) +
          (if j + 1 = i then v (i - 1) * m 1 else 0) := by
    have hj' : j < n + 1 := Finset.mem_range.mp hj
    by_cases h : j = i
    · subst j
      simp [h0]
    by_cases h' : j = i + 1
    · subst j
      rw [show Nat.dist i (i + 1) = 1 by unfold Nat.dist; omega]
      simp [show i + 1 + 1 ≠ i by omega]
    by_cases h'' : j + 1 = i
    · subst i
      rw [show Nat.dist (j + 1) j = 1 by unfold Nat.dist; omega]
      simp [show j ≠ j + 1 + 1 by omega]
    have hdist₁ : 2 ≤ Nat.dist i j := by unfold Nat.dist; omega
    have hdist₂ : Nat.dist i j ≤ n := by unfold Nat.dist; omega
    simp [h, h', h'', hz _ hdist₁ hdist₂]
  have hr (j : ℕ) : j ∈ r ↔ j < n + 1 := Finset.mem_range
  have hdiag : (∑ j ∈ r, if j = i then v i else 0) = v i := by
    simp [hr, show i < n + 1 by omega]
  -- The two off-diagonal sums are the two shifts of the sine vector. The
  -- missing entries at the endpoints have sine values `sin 0` and `sin π`.
  have hright :
      (∑ j ∈ r, if j = i + 1 then v (i + 1) * m 1 else 0) =
        Real.sin (((i : ℝ) + 2) * α) * m 1 := by
    simp only [Finset.sum_ite_eq', hr]
    by_cases hin : i + 1 < n + 1
    · rw [ite_eq_left hin]
      have hc : ((↑(i + 1) : ℝ) + 1) = (i : ℝ) + 2 := by push_cast; ring
      simp only [v, hc]
    · have hin' : i = n := by omega
      subst i
      have hangle : ((n : ℝ) + 2) * α = Real.pi :=
        mul_div_cancel₀ _ (by positivity : (n : ℝ) + 2 ≠ 0)
      simp [hangle]
  have hleft :
      (∑ j ∈ r, if j + 1 = i then v (i - 1) * m 1 else 0) =
        Real.sin ((i : ℝ) * α) * m 1 := by
    cases i with
    | zero => simp
    | succ k =>
      have hk : k < n + 1 := by omega
      simp [hr, hk, v]
  rw [Finset.sum_congr rfl hentry, Finset.sum_add_distrib, Finset.sum_add_distrib,
    hdiag, hright, hleft]
  calc
    _ = v i + (Real.sin ((i : ℝ) * α) + Real.sin (((i : ℝ) + 2) * α)) * m 1 := by ring
    _ = _ := by
      rw [sine_recurrence]
      change v i + (2 * Real.cos α * v i) * m 1 = _
      ring

/-- The sine test excludes a first moment below `-threshold n` for every positive
Toeplitz prefix with unit mass and vanishing moments at orders `2, …, n`. -/
public theorem first_ge_of_toeplitzPositive {n : ℕ} (hn : 1 ≤ n) {m : ℕ → ℝ}
    (hT : ToeplitzPositive n m) (h0 : m 0 = 1)
    (hz : ∀ k : ℕ, 2 ≤ k → k ≤ n → m k = 0) : -threshold n ≤ m 1 := by
  let v (i : ℕ) := Real.sin (((i : ℝ) + 1) * angle n)
  let r := Finset.range (n + 1)
  let C := 2 * Real.cos (angle n)
  have hC : 0 < C := mul_pos (by norm_num) (cos_angle_pos hn)
  have htest : 0 ≤ (1 + C * m 1) * ∑ i ∈ r, v i ^ 2 := by
    refine (hT v).trans_eq ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i hi ↦ ?_
    simp only [mul_assoc, ← Finset.mul_sum]
    have hi' : i ≤ n := by have := Finset.mem_range.mp hi; omega
    rw [sine_row h0 hz hi']
    change v i * ((1 + C * m 1) * v i) = (1 + C * m 1) * v i ^ 2
    ring
  -- The positive norm of this unnormalized sine vector is enough for the test.
  have hv0 : 0 < v 0 := by
    simpa [v] using Real.sin_pos_of_pos_of_lt_pi (angle_pos n)
      (by linarith [angle_lt_half_pi hn, Real.pi_pos])
  have hnorm : 0 < ∑ i ∈ r, v i ^ 2 :=
    (sq_pos_of_pos hv0).trans_le (Finset.single_le_sum (fun i _ ↦ sq_nonneg (v i))
      (Finset.mem_range.mpr (Nat.zero_lt_succ n)))
  have hlin : 0 ≤ 1 + C * m 1 := by
    by_contra! hh
    exact (not_lt_of_ge htest) (mul_neg_of_neg_of_pos hh hnorm)
  change -(1 / C) ≤ m 1
  rw [neg_le, le_div_iff₀ hC]
  linarith only [hlin, mul_comm C (m 1)]

open ConsecutiveHarmonicGrid (node)

private theorem grid_cos_le {n l : ℕ} (hl : l < n + 2) :
    Real.cos (node (n + 2) l) ≤ Real.cos (angle n) := by
  let α := angle n
  let θ := node (n + 2) l
  have hα : 0 < α := angle_pos n
  have hθ : θ = (2 * (l : ℝ) + 1) * α := by
    simp [θ, α, node, angle, mul_div_assoc]
  have hmul : ((n : ℝ) + 2) * α = Real.pi :=
    mul_div_cancel₀ _ (by positivity : (n : ℝ) + 2 ≠ 0)
  have hmin : α ≤ θ := by
    rw [hθ]
    calc
      α = 1 * α := (one_mul _).symm
      _ ≤ (2 * (l : ℝ) + 1) * α := by
        have hl₀ : 0 ≤ (l : ℝ) := by positivity
        exact mul_le_mul_of_nonneg_right (by linarith only [hl₀]) hα.le
  have hmax : θ ≤ 2 * Real.pi - α := by
    have hl' : (l : ℝ) + 1 ≤ (n : ℝ) + 2 := by
      exact_mod_cast (show l + 1 ≤ n + 2 by omega)
    rw [hθ]
    calc
      _ ≤ (2 * ((n : ℝ) + 2) - 1) * α :=
        mul_le_mul_of_nonneg_right (by linarith only [hl']) hα.le
      _ = _ := by linarith only [hmul]
  change Real.cos θ ≤ Real.cos α
  by_cases h : θ ≤ Real.pi
  · exact Real.cos_le_cos_of_nonneg_of_le_pi hα.le h hmin
  · rw [← Real.cos_two_pi_sub θ]
    exact Real.cos_le_cos_of_nonneg_of_le_pi hα.le (by linarith) (by linarith)

private theorem grid_sum_cos_eq_zero {n k : ℕ} (hk : 0 < k) (hkn : k < n + 2) :
    (∑ l ∈ Finset.range (n + 2), Real.cos ((k : ℝ) * node (n + 2) l)) = 0 := by
  have h := (ConsecutiveHarmonicGrid.average_cos_sin_eq_zero (by omega) hk hkn).1
  have hN : ((n + 2 : ℕ) : ℝ) ≠ 0 := by positivity
  calc
    _ = (_ / ((n + 2 : ℕ) : ℝ)) * ((n + 2 : ℕ) : ℝ) := (div_mul_cancel₀ _ hN).symm
    _ = 0 := by rw [h, zero_mul]

private theorem cos_product (x : ℝ) {k : ℕ} (hk : 1 ≤ k) :
    2 * Real.cos x * Real.cos ((k : ℝ) * x) =
      Real.cos (((k + 1 : ℕ) : ℝ) * x) + Real.cos (((k - 1 : ℕ) : ℝ) * x) := by
  push_cast [Nat.cast_sub hk]
  rw [add_mul, sub_mul, one_mul, Real.cos_add, Real.cos_sub]
  ring

/-- Each node in the shifted grid of size `n+2` gets weight `(1-2a cos θ)/(n+2)`. -/
@[expose] public noncomputable def tiltedWeight (n : ℕ) (a : ℝ) (l : ℕ) : ℝ :=
  (1 - 2 * a * Real.cos (node (n + 2) l)) / ((n + 2 : ℕ) : ℝ)

/-- The tilted grid is a probability law with exact first moment `-a` and zero
moments at orders `2, …, n`, even for `a = threshold n`. -/
public theorem tiltedGrid_spec {n : ℕ} (hn : 1 ≤ n) {a : ℝ} (ha : 0 ≤ a)
    (hab : a ≤ threshold n) :
    (∀ l ∈ Finset.range (n + 2), 0 ≤ tiltedWeight n a l) ∧
    (∑ l ∈ Finset.range (n + 2), tiltedWeight n a l) = 1 ∧
    ∀ k : ℕ, 1 ≤ k → k ≤ n →
      moment (Finset.range (n + 2)) (tiltedWeight n a) (node (n + 2)) k =
        if k = 1 then -a else 0 := by
  let r := Finset.range (n + 2)
  let N : ℝ := ((n + 2 : ℕ) : ℝ)
  let θ := node (n + 2)
  have hN : 0 < N := by dsimp [N]; positivity
  have hfreq {k : ℕ} (hk : 0 < k) (hkn : k < n + 2) :
      (∑ l ∈ r, Real.cos ((k : ℝ) * θ l)) = 0 := grid_sum_cos_eq_zero hk hkn
  have hfreq₁ : (∑ l ∈ r, Real.cos (θ l)) = 0 := by
    simpa using (hfreq (k := 1) (by omega) (by omega))
  have hones : (∑ _l ∈ r, (1 : ℝ)) = N := by simp [r, N]
  have hnorm : 2 * a * Real.cos (angle n) ≤ 1 := by
    have hC : 0 < 2 * Real.cos (angle n) := mul_pos (by norm_num) (cos_angle_pos hn)
    have := (le_div_iff₀ hC).1 hab
    linarith only [this, show a * (2 * Real.cos (angle n)) = 2 * a * Real.cos (angle n) by ring]
  refine ⟨?_, ?_, ?_⟩
  · intro l hl
    have hcos : Real.cos (θ l) ≤ Real.cos (angle n) := grid_cos_le (Finset.mem_range.mp hl)
    exact div_nonneg (sub_nonneg.mpr ((mul_le_mul_of_nonneg_left hcos (by positivity)).trans
      hnorm)) hN.le
  · change (∑ l ∈ r, (1 - 2 * a * Real.cos (θ l)) / N) = 1
    rw [← Finset.sum_div, Finset.sum_sub_distrib, ← Finset.mul_sum, hones, hfreq₁,
      mul_zero, sub_zero, div_self hN.ne']
  · intro k hk hkn
    -- Tilting shifts each mode by one in either direction. Only the downward
    -- shift of mode 1 survives, with frequency zero and grid sum `N`.
    have hterm (l : ℕ) : tiltedWeight n a l * Real.cos ((k : ℝ) * θ l) =
        (Real.cos ((k : ℝ) * θ l) - a * (Real.cos (((k + 1 : ℕ) : ℝ) * θ l) +
          Real.cos (((k - 1 : ℕ) : ℝ) * θ l))) / N := by
      rw [← cos_product (θ l) hk]
      change (1 - 2 * a * Real.cos (θ l)) / N * Real.cos ((k : ℝ) * θ l) = _
      ring
    unfold moment
    rw [Finset.sum_congr rfl (fun l _ ↦ hterm l), ← Finset.sum_div,
      Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_add_distrib,
      hfreq (k := k) (by omega) (by omega), hfreq (k := k + 1) (by omega) (by omega)]
    by_cases h : k = 1
    · subst k
      simp only [Nat.sub_self, Nat.cast_zero, zero_mul, Real.cos_zero, zero_add, zero_sub]
      change -(a * ∑ _l ∈ r, (1 : ℝ)) / N = -a
      rw [hones, neg_div, mul_div_cancel_right₀ _ hN.ne']
    · rw [hfreq (k := k - 1) (by omega) (by omega)]
      simp [h]

/-- Every finite probability law with the specified prefix satisfies the sharp bound. -/
public theorem le_threshold_of_moment {ι : Type*} {n : ℕ} (hn : 1 ≤ n) {a : ℝ}
    {s : Finset ι} {w θ : ι → ℝ} (hw : ∀ l ∈ s, 0 ≤ w l)
    (hmass : (∑ l ∈ s, w l) = 1) (hfirst : moment s w θ 1 ≤ -a)
    (hz : ∀ k : ℕ, 2 ≤ k → k ≤ n → moment s w θ k = 0) : a ≤ threshold n := by
  have h0 : moment s w θ 0 = 1 := by simpa [moment] using hmass
  have h := first_ge_of_toeplitzPositive hn (toeplitzPositive_moment n s w θ hw) h0 hz
  simpa only [neg_le_neg_iff] using h.trans hfirst

/-- A finite cosine probability law with first moment at most `-a` and zero moments
at orders `2, …, n` exists exactly up to the threshold, inclusive. -/
public theorem exists_law_iff {n : ℕ} (hn : 1 ≤ n) {a : ℝ} (ha : 0 ≤ a) :
    (∃ (d : ℕ) (w θ : ℕ → ℝ),
      (∀ l ∈ Finset.range d, 0 ≤ w l) ∧ (∑ l ∈ Finset.range d, w l) = 1 ∧
      moment (Finset.range d) w θ 1 ≤ -a ∧
      (∀ k : ℕ, 2 ≤ k → k ≤ n → moment (Finset.range d) w θ k = 0)) ↔
        a ≤ threshold n := by
  constructor
  · rintro ⟨d, w, θ, hw, hmass, hfirst, hz⟩
    exact le_threshold_of_moment hn hw hmass hfirst hz
  · intro hab
    obtain ⟨hw, hmass, hmoment⟩ := tiltedGrid_spec hn ha hab
    refine ⟨n + 2, tiltedWeight n a, node (n + 2), hw, hmass, ?_, ?_⟩
    · simpa using (hmoment 1 le_rfl hn).le
    · intro k hk hkn
      simpa [show k ≠ 1 by omega] using hmoment k (by omega) hkn

end Masullo.ZeroPrefixCosine
