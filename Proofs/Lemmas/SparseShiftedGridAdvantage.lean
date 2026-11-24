module

public import Lemmas.SparseShiftedGrid
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# The large missing-divisor branch for sparse harmonic queries

Source: `fea7eb0b:.godel/alice/sharp-sparse-harmonics.md:13–38`.
Consumer: `3d2886df:.godel/bob/noisy-sparse-harmonics.md:11–16` reuses the
explicit mixture of grid translates as its exact-zero witness.

At pin `e97a8a47`, take the missing order supplied by
`Masullo.exists_sparse_missing_divisor` and assume `3 * N < 4 * n`.
We compare the shift product with `C_N / C_n`, with no frequency cap, and use
that comparison for the existing law. We do not prove the small branch,
near-zero arc mass, or a minimax claim.

Owning check session: `01a20e90-1953-703f-a5c5-0300053aba36`.
-/

open scoped BigOperators

namespace Masullo.SparseShiftedGrid

/-- The unshifted odd-grid mean `C_n` in the source normalization. -/
@[expose] public noncomputable def gridMean (n : ℕ) : ℝ :=
  1 / ((n : ℝ) * Real.sin (Real.pi / (2 * (n : ℝ))))

-- The finite sum is dominated by the telescoping differences of 1 / (k - 1).
private theorem inverse_square_sum_le (Q : Finset ℕ) {a : ℕ} (ha : 2 ≤ a)
    (hQ : ∀ k ∈ Q, a ≤ k) :
    (∑ k ∈ Q, (1 : ℝ) / (k : ℝ)^2) ≤ 1 / ((a : ℝ) - 1) := by
  by_cases he : Q.Nonempty
  · let b := Q.max' he + 1
    have hab : a ≤ b := (hQ _ (Q.max'_mem he)).trans (Nat.le_succ _)
    have hsub : Q ⊆ Finset.Ico a b := fun k hk ↦
      Finset.mem_Ico.mpr ⟨hQ k hk, Nat.lt_succ_of_le (Q.le_max' k hk)⟩
    let f (k : ℕ) : ℝ := 1 / ((k : ℝ) - 1)
    calc
      _ ≤ ∑ k ∈ Finset.Ico a b, (1 : ℝ) / (k : ℝ)^2 :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ ↦ by positivity
      _ ≤ ∑ k ∈ Finset.Ico a b, (f k - f (k + 1)) := by
        refine Finset.sum_le_sum fun k hk ↦ ?_
        have hk2 : (2 : ℝ) ≤ (k : ℝ) := by
          exact_mod_cast ha.trans (Finset.mem_Ico.mp hk).1
        have hk0 : (0 : ℝ) < k := by linarith
        have hk1 : (0 : ℝ) < (k : ℝ) - 1 := by linarith
        have hstep : f (k + 1) = 1 / (k : ℝ) := by simp [f, Nat.cast_add]
        have htel : 1 / ((k : ℝ) - 1) - 1 / (k : ℝ) = 1 / (((k : ℝ) - 1) * (k : ℝ)) := by
          field_simp [hk0.ne', hk1.ne']
          ring
        rw [hstep, show f k = 1 / ((k : ℝ) - 1) from rfl, htel]
        exact one_div_le_one_div_of_le (mul_pos hk1 hk0) (by nlinarith only [hk0])
      _ = f a - f b := by
        simpa only [neg_sub_neg] using Finset.sum_Ico_sub (fun k ↦ -f k) hab
      _ ≤ _ := by
        have hb : (2 : ℝ) ≤ (b : ℝ) := by exact_mod_cast ha.trans hab
        exact sub_le_self _ (div_nonneg zero_le_one (by linarith))
  · rw [Finset.not_nonempty_iff_eq_empty.mp he, Finset.sum_empty]
    have ha' : (2 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
    exact div_nonneg zero_le_one (by linarith)

-- Divisibility makes `j ↦ j / n` injective on the queried multiples.
private theorem cofactor_sum_le {N n : ℕ} (hn : 0 < n) (hnN : n < N) (J : Finset ℕ)
    (hquot : ∀ j ∈ J, n ∣ j → N ≤ (j / n) * (N - n)) :
    (∑ j ∈ shiftedQueries n J, (1 : ℝ) / (j : ℝ)^2) ≤
      (1 / (n : ℝ)^2) * (((N : ℝ) - n) / (n : ℝ)) := by
  let K := shiftedQueries n J
  let Q := K.image fun j ↦ j / n
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hd : 0 < (N : ℝ) - (n : ℝ) := sub_pos.mpr (by exact_mod_cast hnN)
  have hdiv (j : ℕ) (hj : j ∈ K) : (j / n) * n = j :=
    Nat.div_mul_cancel (Finset.mem_filter.mp hj).2
  have hQ (k : ℕ) (hk : k ∈ Q) : N ≤ k * (N - n) := by
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hk
    exact hquot j (Finset.mem_filter.mp hj).1 (Finset.mem_filter.mp hj).2
  have hsum : (∑ k ∈ Q, (1 : ℝ) / (k : ℝ)^2) ≤ ((N : ℝ) - n) / (n : ℝ) := by
    by_cases he : Q.Nonempty
    · let a := Q.min' he
      have ha_mem : a ∈ Q := Q.min'_mem he
      have ha : 2 ≤ a := by
        by_contra! h
        have hle := Nat.mul_le_mul_right (N - n) (show a ≤ 1 by omega)
        rw [Nat.one_mul] at hle
        have := hQ a ha_mem
        omega
      have haR : (2 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
      have hqa : (N : ℝ) ≤ (a : ℝ) * ((N : ℝ) - n) := by
        rw [← Nat.cast_sub hnN.le]
        exact_mod_cast hQ a ha_mem
      refine (inverse_square_sum_le Q ha (fun k hk ↦ Q.min'_le k hk)).trans ?_
      apply (div_le_div_iff₀ (show (0 : ℝ) < (a : ℝ) - 1 by linarith) hnR).2
      nlinarith only [hqa]
    · rw [Finset.not_nonempty_iff_eq_empty.mp he, Finset.sum_empty]
      exact div_nonneg hd.le hnR.le
  have hinj : Set.InjOn (fun j : ℕ ↦ j / n) ↑K := by
    intro j hj k hk h
    rw [← hdiv j hj, ← hdiv k hk]
    exact congrArg (· * n) h
  calc
    (∑ j ∈ K, (1 : ℝ) / (j : ℝ)^2) =
        (1 / (n : ℝ)^2) * (∑ k ∈ Q, (1 : ℝ) / (k : ℝ)^2) := by
      dsimp only [Q]
      rw [Finset.sum_image hinj, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j hj ↦ ?_
      have hj' : ((j / n : ℕ) : ℝ) * (n : ℝ) = (j : ℝ) := by exact_mod_cast hdiv j hj
      rw [← hj', mul_pow, div_mul_div_comm, one_mul, mul_comm]
    _ ≤ _ := mul_le_mul_of_nonneg_left hsum (by positivity)

private theorem one_sub_product_le_sum (K : Finset ℕ) (f : ℕ → ℝ)
    (h₀ : ∀ j ∈ K, 0 ≤ f j) (h₁ : ∀ j ∈ K, f j ≤ 1) :
    1 - (∏ j ∈ K, f j) ≤ ∑ j ∈ K, (1 - f j) := by
  induction K using Finset.induction_on with
  | empty => simp
  | @insert j K hj ih =>
    have h₀' k (hk : k ∈ K) := h₀ k (Finset.mem_insert_of_mem hk)
    have h₁' k (hk : k ∈ K) := h₁ k (Finset.mem_insert_of_mem hk)
    rw [Finset.prod_insert hj, Finset.sum_insert hj]
    calc
      _ = (1 - f j) * (∏ k ∈ K, f k) + (1 - ∏ k ∈ K, f k) := by ring
      _ ≤ _ := add_le_add
        (mul_le_of_le_one_right (sub_nonneg.mpr (h₁ j (Finset.mem_insert_self _ _)))
          (Finset.prod_le_one₀ h₀' h₁')) (ih h₀' h₁')

private theorem shift_product_loss_le {N n : ℕ} (hn : 0 < n) (hnN : n < N) (J : Finset ℕ)
    (hJ : ∀ j ∈ J, 0 < j) (hquot : ∀ j ∈ J, n ∣ j → N ≤ (j / n) * (N - n)) :
    1 - (∏ j ∈ shiftedQueries n J, Real.cos (Real.pi / (4 * (j : ℝ)))) ≤
      (Real.pi^2 / (32 * (n : ℝ)^2)) * (((N : ℝ) - n) / (n : ℝ)) := by
  let u (j : ℕ) : ℝ := Real.pi / (4 * (j : ℝ))
  have hcos (j : ℕ) (hj : j ∈ shiftedQueries n J) : 0 ≤ Real.cos (u j) := by
    have hj1 : (1 : ℝ) ≤ (j : ℝ) := Nat.one_le_cast.mpr (hJ j (Finset.mem_filter.mp hj).1)
    refine Real.cos_nonneg_of_mem_Icc ⟨?_, ?_⟩
    · exact (neg_nonpos.mpr Real.pi_div_two_pos.le).trans (by dsimp [u]; positivity)
    · exact div_le_div_of_nonneg_left Real.pi_pos.le (by norm_num) (by linarith)
  calc
    _ ≤ ∑ j ∈ shiftedQueries n J, (1 - Real.cos (u j)) :=
      one_sub_product_le_sum _ _ hcos fun j _ ↦ Real.cos_le_one (u j)
    _ ≤ ∑ j ∈ shiftedQueries n J, (Real.pi^2 / 32) * (1 / (j : ℝ)^2) := by
      refine Finset.sum_le_sum fun j _ ↦ ?_
      have h := Real.one_sub_sq_div_two_le_cos (x := u j)
      have heq : u j ^ 2 / 2 = (Real.pi^2 / 32) * (1 / (j : ℝ)^2) := by
        dsimp [u]
        ring
      linarith only [h, heq]
    _ = (Real.pi^2 / 32) * (∑ j ∈ shiftedQueries n J, 1 / (j : ℝ)^2) := by
      rw [Finset.mul_sum]
    _ ≤ (Real.pi^2 / 32) * ((1 / (n : ℝ)^2) * (((N : ℝ) - n) / (n : ℝ))) :=
      mul_le_mul_of_nonneg_left (cofactor_sum_le hn hnN J hquot) (by positivity)
    _ = _ := by ring

-- Jordan's inequality makes the derivative of the error nonnegative.
private theorem sin_sub_mul_cos_ge {t : ℝ} (ht : 0 ≤ t) (ht' : t ≤ Real.pi / 2) :
    (2 / (3 * Real.pi)) * t^3 ≤ Real.sin t - t * Real.cos t := by
  let f (x : ℝ) := Real.sin x - x * Real.cos x - (2 / (3 * Real.pi)) * x^3
  have hd (x : ℝ) : HasDerivAt f (x * Real.sin x - 2 / Real.pi * x^2) x := by
    have h := ((Real.hasDerivAt_sin x).sub ((hasDerivAt_id x).mul (Real.hasDerivAt_cos x))).sub
      (HasDerivAt.const_mul (2 / (3 * Real.pi)) ((hasDerivAt_id x).fun_pow 3))
    apply h.congr_deriv
    simp only [id, Nat.cast_ofNat, Nat.reduceSub, one_mul, mul_one]
    ring
  have hm : MonotoneOn f (Set.Icc 0 (Real.pi / 2)) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
    · exact fun x _ ↦ (hd x).continuousAt.continuousWithinAt
    · exact fun x _ ↦ (hd x).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      rw [(hd x).deriv]
      have h := mul_le_mul_of_nonneg_left (Real.mul_le_sin hx.1.le hx.2.le) hx.1.le
      nlinarith only [h]
  have h := hm (show (0 : ℝ) ∈ Set.Icc 0 (Real.pi / 2) from ⟨le_rfl, Real.pi_div_two_pos.le⟩)
    (show t ∈ Set.Icc 0 (Real.pi / 2) from ⟨ht, ht'⟩) ht
  simpa [f, sub_nonneg] using h

-- This is the source's sinc comparison, by differentiating instead of integrating twice.
private theorem sinc_difference_ge {z w : ℝ} (hz : 0 < z) (hzw : z ≤ w) (hw : w ≤ Real.pi / 2) :
    (w^2 - z^2) / (3 * Real.pi) ≤ Real.sin z / z - Real.sin w / w := by
  let f (x : ℝ) := Real.sin x / x + x^2 / (3 * Real.pi)
  have hd (x : ℝ) (hx : 0 < x) :
      HasDerivAt f ((x * Real.cos x - Real.sin x) / x^2 + 2 / (3 * Real.pi) * x) x := by
    have h := ((Real.hasDerivAt_sin x).fun_div (hasDerivAt_id x) hx.ne').add
      (((hasDerivAt_id x).fun_pow 2).div_const (3 * Real.pi))
    apply h.congr_deriv
    simp only [id, Nat.cast_ofNat, Nat.reduceSub, pow_one, mul_one]
    ring
  have hm : AntitoneOn f (Set.Ioc 0 (Real.pi / 2)) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ioc _ _)
    · exact fun x hx ↦ (hd x hx.1).continuousAt.continuousWithinAt
    · intro x hx
      rw [interior_Ioc] at hx
      exact (hd x hx.1).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Ioc] at hx
      rw [(hd x hx.1).deriv]
      have h : (x * Real.cos x - Real.sin x) / x^2 ≤ -(2 / (3 * Real.pi) * x) := by
        apply (div_le_iff₀ (sq_pos_of_pos hx.1)).2
        nlinarith only [sin_sub_mul_cos_ge hx.1.le hx.2.le]
      linarith only [h]
  have h := hm (show z ∈ Set.Ioc 0 (Real.pi / 2) from ⟨hz, hzw.trans hw⟩)
    (show w ∈ Set.Ioc 0 (Real.pi / 2) from ⟨hz.trans_le hzw, hw⟩) hzw
  dsimp [f] at h
  linarith only [h, sub_div (w^2) (z^2) (3 * Real.pi)]

private theorem grid_angle_bounds {n : ℕ} (hn : 0 < n) :
    Real.pi / (2 * (n : ℝ)) ∈ Set.Ioc 0 (Real.pi / 2) := by
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := Nat.one_le_cast.mpr hn
  exact ⟨by positivity, div_le_div_of_nonneg_left Real.pi_pos.le (by norm_num) (by linarith)⟩

private theorem grid_sin_pos {n : ℕ} (hn : 0 < n) :
    0 < Real.sin (Real.pi / (2 * (n : ℝ))) :=
  Real.sin_pos_of_pos_of_lt_pi (grid_angle_bounds hn).1
    ((grid_angle_bounds hn).2.trans_lt (by linarith [Real.pi_pos]))

private theorem gridMean_pos {n : ℕ} (hn : 0 < n) : 0 < gridMean n :=
  one_div_pos.mpr (mul_pos (Nat.cast_pos.mpr hn) (grid_sin_pos hn))

private theorem grid_advantage_ge {N n : ℕ} (hn : 0 < n) (hnN : n ≤ N) :
    Real.pi / (12 * (n : ℝ)^2) * (1 - ((n : ℝ) / (N : ℝ))^2) ≤
      1 - gridMean N / gridMean n := by
  have hN := hn.trans_le hnN
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hNR : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  let z := Real.pi / (2 * (N : ℝ))
  let w := Real.pi / (2 * (n : ℝ))
  have hz : 0 < z := (grid_angle_bounds hN).1
  have hw : 0 < w := (grid_angle_bounds hn).1
  have hzw : z ≤ w := div_le_div_of_nonneg_left Real.pi_pos.le (by positivity)
    (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hnN) (by norm_num))
  have hbound := sinc_difference_ge hz hzw (grid_angle_bounds hn).2
  have hsz : 0 < Real.sin z := grid_sin_pos hN
  have hsw : 0 < Real.sin w := grid_sin_pos hn
  have hdiff : 0 ≤ Real.sin z / z - Real.sin w / w :=
    (div_nonneg (sub_nonneg.mpr (pow_le_pow_left₀ hz.le hzw 2)) (by positivity)).trans hbound
  have hsz' : Real.sin z / z ≤ 1 := (div_le_one hz).2 (Real.sin_le hz.le)
  have hratio : gridMean N / gridMean n = (Real.sin w / w) / (Real.sin z / z) := by
    change (1 / ((N : ℝ) * Real.sin z)) / (1 / ((n : ℝ) * Real.sin w)) = _
    field_simp [hNR.ne', hnR.ne', hz.ne', hw.ne', hsz.ne', hsw.ne']
    dsimp only [z, w]
    field_simp
  calc
    _ = (w^2 - z^2) / (3 * Real.pi) := by
      dsimp [w, z]
      field_simp [Real.pi_pos.ne']
      ring
    _ ≤ Real.sin z / z - Real.sin w / w := hbound
    _ ≤ (Real.sin z / z - Real.sin w / w) / (Real.sin z / z) := by
      apply (le_div_iff₀ (div_pos hsz hz)).mpr
      exact mul_le_of_le_one_right hdiff hsz'
    _ = _ := by rw [hratio, sub_div, div_self (div_pos hsz hz).ne']

private theorem shift_loss_bound_lt_grid_advantage_bound {N n : ℕ} (hn : 0 < n)
    (hnN : n < N) (hlarge : 3 * N < 4 * n) :
    (Real.pi^2 / (32 * (n : ℝ)^2)) * (((N : ℝ) - n) / (n : ℝ)) <
      Real.pi / (12 * (n : ℝ)^2) * (1 - ((n : ℝ) / (N : ℝ))^2) := by
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hNR : (0 : ℝ) < N := Nat.cast_pos.mpr (hn.trans hnN)
  let x := (n : ℝ) / (N : ℝ)
  have hx : 0 < x := div_pos hnR hNR
  have hx1 : x < 1 := (div_lt_one hNR).2 (by exact_mod_cast hnN)
  have hxlarge : 3 / 4 < x := by
    apply (lt_div_iff₀ hNR).2
    have h : 3 * (N : ℝ) < 4 * (n : ℝ) := by exact_mod_cast hlarge
    linarith only [h]
  have hratio : (3 * Real.pi / 8) / x < 1 + x := by
    apply (div_lt_iff₀ hx).2
    calc
      _ < (7 / 4 : ℝ) * (3 / 4) := by linarith [Real.pi_lt_d4]
      _ ≤ _ := mul_le_mul (by linarith) hxlarge.le (by norm_num) (by positivity)
  have hgap : ((N : ℝ) - n) / (n : ℝ) = (1 - x) / x := by
    dsimp [x]
    field_simp
  let c := Real.pi / (12 * (n : ℝ)^2)
  have hc : 0 < c * (1 - x) := mul_pos (by dsimp [c]; positivity) (sub_pos.mpr hx1)
  calc
    _ = (c * (1 - x)) * ((3 * Real.pi / 8) / x) := by rw [hgap]; dsimp [c]; ring
    _ < (c * (1 - x)) * (1 + x) := mul_lt_mul_of_pos_left hratio hc
    _ = _ := by change _ = c * (1 - x^2); ring

/-- For a large grid strictly below `N`, the uniform cofactor bound from the
missing-divisor routing gives a strict product advantage over `C_N`. -/
public theorem gridMean_lt_shift_product {N n : ℕ} (hn : 0 < n) (hnN : n < N)
    (hlarge : 3 * N < 4 * n) (J : Finset ℕ) (hJ : ∀ j ∈ J, 0 < j)
    (hquot : ∀ j ∈ J, n ∣ j → N ≤ (j / n) * (N - n)) :
    gridMean N < gridMean n * (∏ j ∈ shiftedQueries n J, Real.cos (Real.pi / (4 * (j : ℝ)))) := by
  have h := (shift_product_loss_le hn hnN J hJ hquot).trans_lt
    ((shift_loss_bound_lt_grid_advantage_bound hn hnN hlarge).trans_le (grid_advantage_ge hn hnN.le))
  rw [mul_comm, ← div_lt_iff₀ (gridMean_pos hn)]
  linarith only [h]

/-- The large branch of missing-divisor routing: the explicit shifted-grid law
annihilates every queried complex moment and its envelope mean is at least `C_N`.
The routing and top-grid premises are the corresponding outputs of
`Masullo.exists_sparse_missing_divisor`; at `n = N` the shifts are empty. -/
public theorem annihilates_and_mean_ge_of_large_missing_divisor {N n : ℕ}
    (hn : 1 ≤ n) (hnN : n ≤ N) (hlarge : 3 * N < 4 * n)
    (J : Finset ℕ) (hJ : ∀ j ∈ J, 0 < j)
    (hroute : ∀ j ∈ J, n ∣ j → N < j ∧
      (∃ m : ℕ, n < m ∧ m ≤ N ∧ m ∉ J ∧ m ∣ j) ∧
      (n < N → N ≤ (j / n) * (N - n)))
    (htop : n = N → ∀ j ∈ J, ¬ n ∣ j) :
    (∀ j ∈ J, average n (shiftedQueries n J)
      (fun s ↦ Complex.exp (↑((j : ℝ) * s) * Complex.I)) = 0) ∧
    gridMean N ≤ average n (shiftedQueries n J) (fun s ↦ |Real.sin (s / 2)|) := by
  obtain ⟨hmoments, hmean⟩ := annihilates_and_mean_ge hn J hJ
  refine ⟨hmoments, le_trans ?_ hmean⟩
  change gridMean N ≤ gridMean n * _
  rcases lt_or_eq_of_le hnN with hlt | heq
  · exact (gridMean_lt_shift_product hn hlt hlarge J hJ
      (fun j hj hdiv ↦ (hroute j hj hdiv).2.2 hlt)).le
  · have hK : shiftedQueries n J = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro j hj
      exact htop heq j (Finset.mem_filter.mp hj).1 (Finset.mem_filter.mp hj).2
    rw [hK, Finset.prod_empty, mul_one, heq]

end Masullo.SparseShiftedGrid
