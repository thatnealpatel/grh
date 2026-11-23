module

public import Lemmas.SeparationQuadraticCost
public import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.RingTheory.PowerSeries.Inverse

/-!
# Finite coefficient ratios for the detector's independence polynomial

Sources: `0e672a90:.godel/bob/separated-signed-tuples.md`, lines 15–39,
and `6fe747e1:.godel/bob/detection-radius.md`, lines 19–29.
Owning check session: `01a2095b-3cd7-7c85-a8af-4a73f8cbf3ba`.

We use the accepted polynomial on a finite set of natural starts, with real
activities and distance cutoff as in `SeparationQuadraticCost`. The logarithmic
derivative is formal: the polynomial has constant coefficient one, so its
power series inverse computes division by it. The quadratic bound uses the
unnormalized ordered close-pair cost (diagonal and cutoff equality included).
At a fixed shift this uses `primeStarts X d` and `primePairWeight X d` from
`SeparationQuadraticCost`, without dividing the activities by their total mass.
The finite ratio and exponential bounds only concern a positive activity sum,
with explicit hypotheses on the higher coefficients and on the two small
parameters. No analytic higher-coefficient bound, sign reduction, small-sum
estimate, or detector conclusion is proved here.
-/

open scoped BigOperators

namespace DetectorCoefficientRatios

open SeparationQuadraticCost (independencePolynomial independentSets closePairCost)

section Coefficients

variable (starts : Finset ℕ) (r : ℝ) (x : ℕ → ℝ)

local notation "P" => independencePolynomial starts r x

/-- The ordinary independence-polynomial coefficient multiplied by `m!`. -/
@[expose] public noncomputable def F (m : ℕ) : ℝ := (m.factorial : ℝ) * (P).coeff m

/-- The formal logarithmic derivative `P'/P`, using the series inverse of `P`. -/
@[expose] public noncomputable def logDerivative : PowerSeries ℝ :=
  PowerSeries.derivative (P : PowerSeries ℝ) * (P : PowerSeries ℝ)⁻¹

/-- For `j ≥ 1`, the coefficient of degree `j - 1` in `P'/P`. -/
@[expose] public noncomputable def b (j : ℕ) : ℝ :=
  PowerSeries.coeff (j - 1) (logDerivative starts r x)

private theorem coeff_zero : (P).coeff 0 = 1 := by
  classical
  rw [independencePolynomial, Polynomial.finsetSum_coeff,
    Finset.sum_eq_single_of_mem ∅ (by simp [independentSets])]
  · simp
  · intro I _ hI
    have hc : I.card ≠ 0 := by simpa using hI
    simp [Polynomial.coeff_monomial, hc]

private theorem coeff_one : (P).coeff 1 = ∑ p ∈ starts, x p := by
  classical
  rw [independencePolynomial, Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_monomial, Finsupp.single_apply, ← Finset.sum_filter]
  symm
  refine Finset.sum_nbij (fun p : ℕ ↦ ({p} : Finset ℕ)) ?_ ?_ ?_ ?_
  · intro p hp
    simp [independentSets, hp, Finset.singleton_subset_iff]
  · intro p _ q _ hpq
    simpa using hpq
  · intro I hI
    obtain ⟨hI, hcard⟩ := Finset.mem_filter.mp hI
    obtain ⟨p, rfl⟩ := Finset.card_eq_one.mp hcard
    have hsub := (Finset.mem_filter.mp hI).1
    exact ⟨p, Finset.mem_powerset.mp hsub (by simp), rfl⟩
  · intro p _
    simp

@[simp] public theorem F_zero : F starts r x 0 = 1 := by
  simp [F, coeff_zero]

private theorem logDerivative_mul :
    logDerivative starts r x * (P : PowerSeries ℝ) = PowerSeries.derivative (P : PowerSeries ℝ) := by
  rw [logDerivative, mul_assoc, mul_comm ((P : PowerSeries ℝ)⁻¹),
    PowerSeries.mul_inv_cancel, mul_one]
  rw [← PowerSeries.coeff_zero_eq_constantCoeff, Polynomial.coeff_coe, coeff_zero]
  exact one_ne_zero

private theorem coeff_succ (k : ℕ) :
    (P).coeff (k + 1) * ((k + 1 : ℕ) : ℝ) =
      ∑ i ∈ Finset.range (k + 1), b starts r x (i + 1) * (P).coeff (k - i) := by
  have h := congrArg (PowerSeries.coeff k) (logDerivative_mul starts r x)
  rw [PowerSeries.coeff_mul, PowerSeries.coeff_derivative,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j ↦
      PowerSeries.coeff i (logDerivative starts r x) * PowerSeries.coeff j (P : PowerSeries ℝ))] at h
  simpa only [b, Nat.add_sub_cancel, Polynomial.coeff_coe, Nat.cast_add, Nat.cast_one] using h.symm

/-- The constant coefficient of `P'/P` is the sum of the original activities. -/
public theorem b_one : b starts r x 1 = ∑ p ∈ starts, x p := by
  simpa [coeff_zero, coeff_one] using (coeff_succ starts r x 0).symm

/-- The degree-one coefficient of `P'/P` is the accepted signed quadratic expression. -/
public theorem b_two : b starts r x 2 = SeparationQuadraticCost.b2 starts r x := by
  have h := coeff_succ starts r x 1
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    Nat.sub_zero, Nat.sub_self, coeff_zero, mul_one] at h
  rw [b_one, coeff_one] at h
  unfold SeparationQuadraticCost.b2
  norm_num at h
  linear_combination -h

/-- Bound the actual logarithmic derivative coefficient by the ordered close-pair cost. -/
public theorem abs_b_two_le_closePairCost (hr : 0 ≤ r) (w : ℕ → ℝ)
    (hx : ∀ p ∈ starts, |x p| ≤ w p) : |b starts r x 2| ≤ closePairCost starts r w := by
  rw [b_two]
  exact SeparationQuadraticCost.abs_b2_le_closePairCost starts hr x w hx

private theorem F_succ_full (k : ℕ) :
    F starts r x (k + 1) = ∑ i ∈ Finset.range (k + 1),
      (k.descFactorial i : ℝ) * b starts r x (i + 1) * F starts r x (k - i) := by
  calc
    F starts r x (k + 1) = (k.factorial : ℝ) * ((P).coeff (k + 1) * ((k + 1 : ℕ) : ℝ)) := by
      simp only [F, Nat.factorial_succ, Nat.cast_mul]
      ring
    _ = _ := by
      rw [coeff_succ, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i hi ↦ ?_
      have hfac : ((k - i).factorial : ℝ) * (k.descFactorial i : ℝ) = (k.factorial : ℝ) :=
        by exact_mod_cast Nat.factorial_mul_descFactorial (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))
      rw [F, ← hfac]
      ring

/-- The separated-tuple recurrence with its first term split off. -/
public theorem F_recurrence {m : ℕ} (hm : 1 ≤ m) :
    F starts r x m = b starts r x 1 * F starts r x (m - 1) +
      ∑ j ∈ Finset.Icc 2 m, ((m - 1).descFactorial (j - 1) : ℝ) *
        b starts r x j * F starts r x (m - j) := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  rw [F_succ_full, Finset.sum_range_succ', add_comm, ← Finset.Ico_add_one_right_eq_Icc,
    Finset.sum_Ico_eq_sum_range]
  simp only [Nat.descFactorial_zero, Nat.cast_one, one_mul, Nat.zero_add, Nat.sub_zero,
    Nat.add_sub_cancel]
  have hlen : k + 1 + 1 - 2 = k := by omega
  rw [hlen]
  congr 1
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [show 2 + i = i + 1 + 1 by omega, Nat.add_sub_cancel,
    show k + 1 - (i + 1 + 1) = k - (i + 1) by omega]

end Coefficients

/-- The sum of the quadratic and higher-order relative error bounds at order `m`. -/
@[expose] public noncomputable def ratioError (s A B C2 : ℝ) (m : ℕ) : ℝ :=
  2 * m * C2 / s ^ 2 + 32 * A * (m : ℝ) ^ 2 * B ^ 2 / s ^ 3

private theorem ratioError_nonneg {s A B C2 : ℝ} (hs : 0 < s) (hA : 0 ≤ A) (hC : 0 ≤ C2)
    (m : ℕ) : 0 ≤ ratioError s A B C2 m := by
  unfold ratioError
  positivity

private theorem ratioError_mono {s A B C2 : ℝ} (hs : 0 < s) (hA : 0 ≤ A) (hC : 0 ≤ C2)
    {m n : ℕ} (hmn : m ≤ n) : ratioError s A B C2 m ≤ ratioError s A B C2 n := by
  unfold ratioError
  gcongr

-- Iterate only the lower bounds at indices already covered by the induction.
private theorem backward_le {f : ℕ → ℝ} {s : ℝ} (hs : 0 < s) {t : ℕ}
    (hstep : ∀ i < t, s / 2 * f i ≤ f (i + 1)) {k : ℕ} (hk : k ≤ t) :
    f (t - k) ≤ (2 / s) ^ k * f t := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h := hstep (t - (k + 1)) (by omega)
    rw [show t - (k + 1) + 1 = t - k by omega] at h
    calc
      _ ≤ (2 / s) * f (t - k) := by
        rw [div_mul_eq_mul_div, le_div_iff₀ hs]
        linarith only [h]
      _ ≤ (2 / s) * ((2 / s) ^ k * f t) :=
        mul_le_mul_of_nonneg_left (ih (by omega)) (by positivity)
      _ = _ := by rw [pow_succ', mul_assoc]

private theorem geom_le_two {q : ℝ} (hq : 0 ≤ q) (hq' : q ≤ 1 / 2) (l : ℕ) :
    ∑ i ∈ Finset.range l, q ^ i ≤ 2 := by
  induction l with
  | zero => simp
  | succ l ih =>
    rw [Finset.sum_range_succ']
    simp only [pow_succ', pow_zero, ← Finset.mul_sum]
    linarith only [mul_le_mul_of_nonneg_left ih hq, hq']

private theorem geom_tail_le {q : ℝ} (hq : 0 ≤ q) (hq' : q ≤ 1 / 2) (m : ℕ) :
    ∑ j ∈ Finset.Icc 3 m, q ^ (j - 1) ≤ 2 * q ^ 2 := by
  rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
  simp only [show ∀ i : ℕ, 3 + i - 1 = 2 + i from fun i ↦ by omega, pow_add,
    ← Finset.mul_sum]
  exact (mul_le_mul_of_nonneg_left (geom_le_two hq hq' _) (sq_nonneg q)).trans_eq (mul_comm _ _)

private theorem abs_step_term_le {s : ℝ} (hs : 0 < s) {f b : ℕ → ℝ} {m j : ℕ}
    (hj : j ∈ Finset.Icc 2 m) (hprev : ∀ i < m, 0 < f i)
    (hstep : ∀ i < m - 1, s / 2 * f i ≤ f (i + 1)) :
    |((m - 1).descFactorial (j - 1) : ℝ) * b j * f (m - j) / (s * f (m - 1))| ≤
      |b j| / s * (2 * m / s) ^ (j - 1) := by
  obtain ⟨hj2, hjm⟩ := Finset.mem_Icc.mp hj
  have hp := hprev (m - 1) (by omega)
  have hf := hprev (m - j) (by omega)
  have hback : f (m - j) / f (m - 1) ≤ (2 / s) ^ (j - 1) := by
    apply (div_le_iff₀ hp).2
    rw [show m - j = m - 1 - (j - 1) by omega]
    exact backward_le hs hstep (by omega)
  have hfac : ((m - 1).descFactorial (j - 1) : ℝ) ≤ (m : ℝ) ^ (j - 1) := by
    exact_mod_cast (Nat.descFactorial_le_pow (m - 1) (j - 1)).trans
      (Nat.pow_le_pow_left (Nat.sub_le m 1) (j - 1))
  rw [abs_div, abs_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg _), abs_of_pos hf,
    abs_of_pos (mul_pos hs hp)]
  calc
    _ = (|b j| / s) * (((m - 1).descFactorial (j - 1) : ℝ) * (f (m - j) / f (m - 1))) := by
      ring
    _ ≤ (|b j| / s) * ((m : ℝ) ^ (j - 1) * (2 / s) ^ (j - 1)) := by
      gcongr
    _ = _ := by rw [← mul_pow]; ring

private theorem split_quadratic (g : ℕ → ℝ) (m : ℕ) :
    ∑ j ∈ Finset.Icc 2 m, g j = (if 2 ≤ m then g 2 else 0) + ∑ j ∈ Finset.Icc 3 m, g j := by
  by_cases hm : 2 ≤ m
  · rw [ite_eq_left hm, ← Finset.Ico_add_one_right_eq_Icc, ← Finset.Ico_add_one_right_eq_Icc]
    exact Finset.sum_eq_sum_Ico_succ_bot (by omega) g
  · rw [ite_eq_right hm, ← Finset.Ico_add_one_right_eq_Icc, ← Finset.Ico_add_one_right_eq_Icc,
      Finset.Ico_eq_empty_of_le (show m + 1 ≤ 2 by omega),
      Finset.Ico_eq_empty_of_le (show m + 1 ≤ 3 by omega)]
    simp

-- Divide by the leading term using only the positivity of the previous coefficient.
private theorem one_step_error {s A B C2 : ℝ} (hs : 0 < s) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hC : 0 ≤ C2) {f b : ℕ → ℝ} {m : ℕ} (hm : 1 ≤ m)
    (hprev : ∀ i < m, 0 < f i) (hstep : ∀ i < m - 1, s / 2 * f i ≤ f (i + 1))
    (hq : 2 * m * B / s ≤ 1 / 2) (h₂ : |b 2| ≤ C2)
    (hhigher : ∀ j ∈ Finset.Icc 3 m, |b j| ≤ 4 * A * B ^ (j - 1))
    (hrec : f m = s * f (m - 1) + ∑ j ∈ Finset.Icc 2 m,
      ((m - 1).descFactorial (j - 1) : ℝ) * b j * f (m - j)) :
    |f m / (s * f (m - 1)) - 1| ≤ ratioError s A B C2 m := by
  let t (j : ℕ) : ℝ := ((m - 1).descFactorial (j - 1) : ℝ) * b j * f (m - j) / (s * f (m - 1))
  have hd := (mul_pos hs (hprev (m - 1) (by omega))).ne'
  have hid : f m / (s * f (m - 1)) - 1 = ∑ j ∈ Finset.Icc 2 m, t j := by
    rw [hrec, add_div, div_self hd, add_sub_cancel_left]
    simp only [t, div_eq_mul_inv, Finset.sum_mul]
  have hterm (j : ℕ) (hj : j ∈ Finset.Icc 2 m) :
      |t j| ≤ |b j| / s * (2 * m / s) ^ (j - 1) :=
    abs_step_term_le hs hj hprev hstep
  have hquad : (if 2 ≤ m then |t 2| else 0) ≤ 2 * m * C2 / s ^ 2 := by
    by_cases h : 2 ≤ m
    · rw [ite_eq_left h]
      calc
        _ ≤ |b 2| / s * (2 * m / s) := by
          simpa using hterm 2 (Finset.mem_Icc.mpr ⟨le_rfl, h⟩)
        _ ≤ C2 / s * (2 * m / s) := by gcongr
        _ = _ := by ring
    · rw [ite_eq_right h]
      positivity
  have htail : ∑ j ∈ Finset.Icc 3 m, |t j| ≤ 32 * A * (m : ℝ) ^ 2 * B ^ 2 / s ^ 3 := by
    let q : ℝ := 2 * m * B / s
    have hq₀ : 0 ≤ q := by dsimp [q]; positivity
    calc
      _ ≤ ∑ j ∈ Finset.Icc 3 m, (4 * A / s) * q ^ (j - 1) := by
        refine Finset.sum_le_sum fun j hj ↦ ?_
        obtain ⟨hj₁, hj₂⟩ := Finset.mem_Icc.mp hj
        calc
          _ ≤ |b j| / s * (2 * m / s) ^ (j - 1) :=
            hterm j (Finset.mem_Icc.mpr ⟨by omega, hj₂⟩)
          _ ≤ (4 * A * B ^ (j - 1)) / s * (2 * m / s) ^ (j - 1) := by
            gcongr
            exact hhigher j hj
          _ = _ := by
            rw [show q = B * (2 * m / s) by dsimp [q]; ring, mul_pow]
            ring
      _ ≤ (4 * A / s) * (2 * q ^ 2) := by
        rw [← Finset.mul_sum]
        exact mul_le_mul_of_nonneg_left (geom_tail_le hq₀ hq _) (by positivity)
      _ = _ := by dsimp [q]; ring
  rw [hid]
  exact (Finset.abs_sum_le_sum_abs _ _).trans (by
    rw [split_quadratic]
    exact add_le_add hquad htail)

private theorem one_sub_ge_exp_neg_two {e : ℝ} (he : 0 ≤ e) (he' : e ≤ 1 / 2) :
    Real.exp (-(2 * e)) ≤ 1 - e := by
  rw [Real.exp_neg, inv_eq_one_div, div_le_iff₀ (Real.exp_pos _)]
  calc
    1 ≤ (1 - e) * (2 * e + 1) := by
      nlinarith only [mul_nonneg he (show 0 ≤ 1 - 2 * e by linarith)]
    _ ≤ (1 - e) * Real.exp (2 * e) :=
      mul_le_mul_of_nonneg_left (Real.add_one_le_exp _) (by linarith)

private theorem exp_bounds {f : ℕ → ℝ} {e : ℕ → ℝ} {s : ℝ} (hs : 0 < s) (hzero : f 0 = 1)
    {n : ℕ} (hprev : ∀ i ≤ n, 0 < f i)
    (he : ∀ i ≤ n, 0 ≤ e i ∧ e i ≤ 1 / 2)
    (hrat : ∀ i ∈ Finset.Icc 1 n, |f i / (s * f (i - 1)) - 1| ≤ e i) :
    s ^ n * Real.exp (-2 * ∑ i ∈ Finset.Icc 1 n, e i) ≤ f n ∧
      f n ≤ s ^ n * Real.exp (∑ i ∈ Finset.Icc 1 n, e i) := by
  induction n with
  | zero => simp [hzero]
  | succ k ih =>
    obtain ⟨hlo, hhi⟩ := ih (fun i hi ↦ hprev i (by omega)) (fun i hi ↦ he i (by omega))
      (fun i hi ↦ hrat i (Finset.Icc_subset_Icc_right (Nat.le_succ k) hi))
    have hd : 0 < s * f k := mul_pos hs (hprev k (by omega))
    have hrat' := hrat (k + 1) (Finset.mem_Icc.mpr ⟨by omega, le_rfl⟩)
    rw [Nat.add_sub_cancel] at hrat'
    obtain ⟨hl, hu⟩ := abs_le.mp hrat'
    obtain ⟨he₀, he₁⟩ := he (k + 1) le_rfl
    have hl' : Real.exp (-(2 * e (k + 1))) ≤ f (k + 1) / (s * f k) :=
      (one_sub_ge_exp_neg_two he₀ he₁).trans (by linarith)
    have hu' : f (k + 1) / (s * f k) ≤ Real.exp (e (k + 1)) :=
      (show _ ≤ e (k + 1) + 1 by linarith).trans (Real.add_one_le_exp _)
    have hsum : ∑ i ∈ Finset.Icc 1 (k + 1), e i = e (k + 1) + ∑ i ∈ Finset.Icc 1 k, e i := by
      rw [show Finset.Icc 1 (k + 1) = insert (k + 1) (Finset.Icc 1 k) by
        ext i; simp only [Finset.mem_Icc, Finset.mem_insert]; omega,
        Finset.sum_insert (by simp)]
    constructor
    · rw [hsum, mul_add, Real.exp_add, pow_succ]
      calc
        _ = Real.exp (-(2 * e (k + 1))) * (s * (s ^ k * Real.exp (-2 * ∑ i ∈ Finset.Icc 1 k, e i))) := by
          rw [show -2 * e (k + 1) = -(2 * e (k + 1)) by ring]
          ring
        _ ≤ Real.exp (-(2 * e (k + 1))) * (s * f k) := by gcongr
        _ ≤ _ := (le_div_iff₀ hd).mp hl'
    · rw [hsum, Real.exp_add, pow_succ]
      calc
        _ ≤ Real.exp (e (k + 1)) * (s * f k) := (div_le_iff₀ hd).mp hu'
        _ ≤ Real.exp (e (k + 1)) * (s * (s ^ k * Real.exp (∑ i ∈ Finset.Icc 1 k, e i))) := by gcongr
        _ = _ := by ring

/-- The finite ratio induction and its product bounds, for the actual independence polynomial.
The higher-coefficient estimate is needed only through order `n`. -/
public theorem finite_ratio_bounds (starts : Finset ℕ) (r : ℝ) (x : ℕ → ℝ) (n : ℕ)
    {s A B C2 : ℝ} (hsb : b starts r x 1 = s) (hs : 0 < s)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C2) (h₂ : |b starts r x 2| ≤ C2)
    (hhigher : ∀ j ∈ Finset.Icc 3 n, |b starts r x j| ≤ 4 * A * B ^ (j - 1))
    (hgeom : 2 * n * B / s ≤ 1 / 2) (hsmall : ratioError s A B C2 n ≤ 1 / 2) :
    (∀ m ∈ Finset.Icc 1 n, 0 < F starts r x m ∧
      |F starts r x m / (s * F starts r x (m - 1)) - 1| ≤ ratioError s A B C2 m) ∧
    s ^ n * Real.exp (-2 * ∑ m ∈ Finset.Icc 1 n, ratioError s A B C2 m) ≤ F starts r x n ∧
    F starts r x n ≤ s ^ n * Real.exp (∑ m ∈ Finset.Icc 1 n, ratioError s A B C2 m) := by
  let f := F starts r x
  let e := ratioError s A B C2
  have he (m : ℕ) (hm : m ≤ n) : 0 ≤ e m ∧ e m ≤ 1 / 2 :=
    ⟨ratioError_nonneg hs hA hC m, (ratioError_mono hs hA hC hm).trans hsmall⟩
  have h (m : ℕ) (hm : m ≤ n) : 0 < f m ∧ (1 ≤ m → |f m / (s * f (m - 1)) - 1| ≤ e m) := by
    induction m using Nat.strong_induction_on with
    | ind m ih =>
      by_cases hm₀ : 1 ≤ m
      · have hprev (i : ℕ) (hi : i < m) : 0 < f i := (ih i hi (hi.le.trans hm)).1
        have hstep (i : ℕ) (hi : i < m - 1) : s / 2 * f i ≤ f (i + 1) := by
          have hi' : i + 1 < m := by omega
          have hr := (ih (i + 1) hi' (hi'.le.trans hm)).2 (by omega)
          rw [Nat.add_sub_cancel] at hr
          have hl : 1 / 2 ≤ f (i + 1) / (s * f i) := by
            linarith only [(abs_le.mp hr).1, (he (i + 1) (hi'.le.trans hm)).2]
          have hl' := (le_div_iff₀ (mul_pos hs (hprev i (by omega)))).mp hl
          linear_combination hl'
        have hgeom' : 2 * m * B / s ≤ 1 / 2 := by
          apply le_trans _ hgeom
          gcongr
        have hr : |f m / (s * f (m - 1)) - 1| ≤ e m :=
          one_step_error hs hA hB hC hm₀ hprev hstep hgeom' h₂
            (fun j hj ↦ hhigher j (Finset.Icc_subset_Icc_right hm hj))
            (by simpa only [hsb] using F_recurrence starts r x hm₀)
        -- Only now, after proving the estimate, may we infer positivity at `m`.
        have hrpos : 0 < f m / (s * f (m - 1)) := by
          linarith only [(abs_le.mp hr).1, (he m hm).2]
        have hd : 0 < s * f (m - 1) := mul_pos hs (hprev (m - 1) (by omega))
        exact ⟨(div_pos_iff_of_pos_right hd).mp hrpos, fun _ ↦ hr⟩
      · have hz : m = 0 := by omega
        subst m
        simp [f]
  refine ⟨fun m hm ↦ ?_, exp_bounds hs (F_zero starts r x) (fun i hi ↦ (h i hi).1) he ?_⟩
  · obtain ⟨hm₁, hm₂⟩ := Finset.mem_Icc.mp hm
    exact ⟨(h m hm₂).1, (h m hm₂).2 hm₁⟩
  · intro i hi
    exact (h i (Finset.mem_Icc.mp hi).2).2 (Finset.mem_Icc.mp hi).1

end DetectorCoefficientRatios
