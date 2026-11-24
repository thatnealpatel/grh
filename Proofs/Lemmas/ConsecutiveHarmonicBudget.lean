module

public import Lemmas.ConsecutiveHarmonicMajorant
import all Lemmas.ConsecutiveHarmonicGrid -- unfold the shifted node in the sample identities
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Convex.SpecificFunctions.Deriv
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Coefficient budget for the attaining consecutive-harmonic majorant

Source: `8fde6138dc2ec249c6560b66ca0976aa8ea34dab:.godel/bob/initial-harmonic-budget.md:13–29`,
including “The height cost of this same majorant.” The coefficient mass is used
in the height bound there (lines 25–27) and in
`b825bc58:.godel/bob/noisy-sparse-harmonics.md:9`. We recover the coefficients
of the global, shifted majorant itself from value and derivative contact on the
grid, then prove its coefficient mass. No arithmetic packet or sparse minimax
bound is claimed here.

Owning check session: `01a20b8b-65a1-7430-ae92-47e2bde881a8`.
-/

open scoped BigOperators

namespace Masullo.ConsecutiveHarmonicBudget

open ConsecutiveHarmonicGrid (node average_cos_sin_eq_zero)

private noncomputable def step (n : ℕ) : ℝ := Real.pi / (2 * (n : ℝ))

private theorem cast_n_pos {n : ℕ} (hn : 2 ≤ n) : 0 < (n : ℝ) :=
  Nat.cast_pos.mpr (by omega)

private theorem step_pos {n : ℕ} (hn : 2 ≤ n) : 0 < step n :=
  div_pos Real.pi_pos (mul_pos (by norm_num) (cast_n_pos hn))

private theorem step_mul {n : ℕ} (hn : 2 ≤ n) : 2 * (n : ℝ) * step n = Real.pi :=
  mul_div_cancel₀ _ (by have := cast_n_pos hn; positivity)

private theorem half_angle_mem {n q : ℕ} (hn : 2 ≤ n) (hq : q < n) :
    (2 * (q : ℝ) + 1) * step n ∈ Set.Ioo 0 Real.pi := by
  have hqn : (q : ℝ) + 1 ≤ (n : ℝ) := by
    exact_mod_cast (show q + 1 ≤ n by omega)
  have hz := step_pos hn
  exact ⟨by positivity, step_mul hn ▸ mul_lt_mul_of_pos_right (by linarith) hz⟩

private theorem sin_node_pos {n l : ℕ} (hn : 2 ≤ n) (hl : l < n) :
    0 < Real.sin (node n l / 2) := by
  have hangle : node n l / 2 = (2 * (l : ℝ) + 1) * step n := by
    unfold node step
    ring
  rw [hangle]
  obtain ⟨hlo, hhi⟩ := half_angle_mem hn hl
  exact Real.sin_pos_of_pos_of_lt_pi hlo hhi

-- Use p - sin(s/2) as the nonnegative gap; this is differentiable even off the grid.
private theorem derivative_contact {n : ℕ} (hn : 2 ≤ n) (c : ℝ) (d : ℕ → ℝ)
    (hmajor : ∀ s : ℝ, |Real.sin (s / 2)| ≤
      c + ∑ m ∈ Finset.Ico 1 n, d m * Real.cos ((m : ℝ) * s))
    (hcontact : ∀ l < n, c + ∑ m ∈ Finset.Ico 1 n, d m * Real.cos ((m : ℝ) * node n l) =
      |Real.sin (node n l / 2)|)
    {l : ℕ} (hl : l < n) :
    (∑ m ∈ Finset.Ico 1 n, ((m : ℝ) * d m) * Real.sin ((m : ℝ) * node n l)) =
      -(Real.cos (node n l / 2) / 2) := by
  let t := node n l
  let gap (s : ℝ) := c + (∑ m ∈ Finset.Ico 1 n, d m * Real.cos ((m : ℝ) * s)) - Real.sin (s / 2)
  have hgap : gap t = 0 := by
    dsimp [gap, t]
    rw [hcontact l hl, abs_of_pos (sin_node_pos hn hl), sub_self]
  have hmin : IsMinOn gap Set.univ t := isMinOn_univ_iff.mpr fun s ↦ by
    rw [hgap]
    exact sub_nonneg.mpr ((le_abs_self _).trans (hmajor s))
  have hp : HasDerivAt (fun s : ℝ ↦ c + ∑ m ∈ Finset.Ico 1 n, d m * Real.cos ((m : ℝ) * s))
      (∑ m ∈ Finset.Ico 1 n, -(((m : ℝ) * d m) * Real.sin ((m : ℝ) * t))) t := by
    apply HasDerivAt.const_add
    apply HasDerivAt.fun_sum
    intro m _
    have hm := (Real.hasDerivAt_cos ((m : ℝ) * t)).scomp t ((hasDerivAt_id t).const_mul (m : ℝ))
    simpa only [Function.comp_def, id_eq, smul_eq_mul, mul_one, mul_neg, neg_mul, ← mul_assoc,
      mul_comm (d m) (m : ℝ)] using hm.const_mul (d m)
  have hf : HasDerivAt (fun s : ℝ ↦ Real.sin (s / 2)) (Real.cos (t / 2) / 2) t := by
    simpa only [Function.comp_def, id_eq, smul_eq_mul, div_mul_eq_mul_div, one_mul] using
      (Real.hasDerivAt_sin (t / 2)).scomp t ((hasDerivAt_id t).div_const 2)
  have hd := (hmin.isLocalMin Filter.univ_mem).hasDerivAt_eq_zero (hp.sub hf)
  rw [Finset.sum_neg_distrib] at hd
  linarith only [hd]

private noncomputable def cosineSum (n : ℕ) (a : ℝ) : ℝ :=
  ∑ l ∈ Finset.range n, Real.cos (a * node n l)

private theorem cosineSum_small {n q : ℕ} (hn : 2 ≤ n) (hq : q < n) :
    cosineSum n q = if q = 0 then (n : ℝ) else 0 := by
  by_cases h : q = 0
  · simp [h, cosineSum]
  · rw [ite_eq_right h]
    exact (div_eq_zero_iff.mp (average_cos_sin_eq_zero hn (by omega) hq).1).resolve_right
      (cast_n_pos hn).ne'

private theorem cosineSum_neg (n : ℕ) (a : ℝ) : cosineSum n (-a) = cosineSum n a := by
  simp [cosineSum, neg_mul]

-- Adding n to a grid frequency multiplies that mode by -1, not +1.
private theorem cosineSum_shift {n : ℕ} (hn : 2 ≤ n) (q : ℝ) :
    cosineSum n (q + (n : ℝ)) = -cosineSum n q := by
  unfold cosineSum
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro l _
  have ht : (n : ℝ) * node n l = Real.pi + (l : ℝ) * (2 * Real.pi) := by
    unfold node
    field_simp [(cast_n_pos hn).ne']
    ring
  rw [add_mul, ht, ← add_assoc, Real.cos_add_nat_mul_two_pi, Real.cos_add_pi]

private theorem cosineSum_sub {n m k : ℕ} (hn : 2 ≤ n) (hm : m < n) (hk : k < n) :
    cosineSum n ((m : ℝ) - (k : ℝ)) = if m = k then (n : ℝ) else 0 := by
  rcases le_total k m with h | h
  · rw [← Nat.cast_sub h, cosineSum_small hn (by omega)]
    have he : m - k = 0 ↔ m = k := by omega
    simp only [he]
  · rw [← neg_sub (k : ℝ) (m : ℝ), cosineSum_neg, ← Nat.cast_sub h, cosineSum_small hn (by omega)]
    have he : k - m = 0 ↔ m = k := by omega
    simp only [he]

private theorem cosineSum_add {n m k : ℕ} (hn : 2 ≤ n) (hm : m < n) (hk₀ : 0 < k) (hk : k < n) :
    cosineSum n ((m : ℝ) + (k : ℝ)) = if m = n - k then -(n : ℝ) else 0 := by
  rw [← Nat.cast_add]
  rcases lt_trichotomy (m + k) n with h | h | h
  · rw [cosineSum_small hn h, ite_eq_right (by omega), ite_eq_right (by omega)]
  · rw [h, ite_eq_left (by omega : m = n - k)]
    calc
      _ = -cosineSum n ((0 : ℕ) : ℝ) := by simpa using cosineSum_shift hn 0
      _ = _ := by rw [cosineSum_small hn (by omega), ite_eq_left rfl]
  · have he : m + k = (m + k - n) + n := by omega
    rw [he, Nat.cast_add, cosineSum_shift hn, cosineSum_small hn (by omega),
      ite_eq_right (by omega), neg_zero, ite_eq_right (by omega)]

-- In the central alias m = k = n - k, the cosine kernel is zero and the
-- sine kernel is 2n. Keep both contributions even when the two indices coincide.
private theorem grid_kernels {n m k : ℕ} (hn : 2 ≤ n) (hm : m < n) (hk₀ : 0 < k) (hk : k < n) :
    let A : ℝ := if m = k then n else 0
    let B : ℝ := if m = n - k then n else 0
    (2 * (∑ l ∈ Finset.range n, Real.cos ((m : ℝ) * node n l) *
        Real.cos ((k : ℝ) * node n l)) = A - B) ∧
    (2 * (∑ l ∈ Finset.range n, Real.sin ((m : ℝ) * node n l) *
        Real.sin ((k : ℝ) * node n l)) = A + B) := by
  dsimp only
  constructor
  · simp only [Finset.mul_sum, ← mul_assoc, Real.two_mul_cos_mul_cos, ← sub_mul, ← add_mul,
      Finset.sum_add_distrib]
    change cosineSum n ((m : ℝ) - k) + cosineSum n ((m : ℝ) + k) = _
    rw [cosineSum_sub hn hm hk, cosineSum_add hn hm hk₀ hk]
    split_ifs <;> ring
  · simp only [Finset.mul_sum, ← mul_assoc, Real.two_mul_sin_mul_sin, ← sub_mul, ← add_mul,
      Finset.sum_sub_distrib]
    change cosineSum n ((m : ℝ) - k) - cosineSum n ((m : ℝ) + k) = _
    rw [cosineSum_sub hn hm hk, cosineSum_add hn hm hk₀ hk]
    split_ifs <;> ring

private theorem project {n k : ℕ} (hk : k ∈ Finset.Ico 1 n) (a : ℕ → ℝ) (v : ℝ → ℝ) (ε : ℝ)
    (hkernel : ∀ m ∈ Finset.Ico 1 n,
      2 * (∑ l ∈ Finset.range n, v ((m : ℝ) * node n l) * v ((k : ℝ) * node n l)) =
        (if m = k then (n : ℝ) else 0) + ε * (if m = n - k then (n : ℝ) else 0)) :
    2 * (∑ l ∈ Finset.range n,
        (∑ m ∈ Finset.Ico 1 n, a m * v ((m : ℝ) * node n l)) * v ((k : ℝ) * node n l)) =
      (n : ℝ) * (a k + ε * a (n - k)) := by
  have hj : n - k ∈ Finset.Ico 1 n := by
    have := Finset.mem_Ico.mp hk
    exact Finset.mem_Ico.mpr (by omega)
  calc
    _ = ∑ m ∈ Finset.Ico 1 n,
        a m * (2 * ∑ l ∈ Finset.range n, v ((m : ℝ) * node n l) * v ((k : ℝ) * node n l)) := by
      simp only [Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun m _ ↦ Finset.sum_congr rfl fun l _ ↦ by ring
    _ = ∑ m ∈ Finset.Ico 1 n,
        ((if m = k then a m * (n : ℝ) else 0) +
          (if m = n - k then a m * (ε * (n : ℝ)) else 0)) := by
      apply Finset.sum_congr rfl
      intro m hm
      rw [hkernel m hm]
      split_ifs <;> ring
    _ = _ := by
      rw [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq', ite_eq_left hk, ite_eq_left hj]
      ring

-- Half-integral sine modes have nonzero average. Telescope their sine samples
-- against cosine differences with endpoints 1 and -1.
private theorem sum_half_sin {n q : ℕ} (hn : 2 ≤ n) (hq : q < n) :
    (∑ l ∈ Finset.range n, Real.sin (((q : ℝ) + 1 / 2) * node n l)) =
      1 / Real.sin ((2 * (q : ℝ) + 1) * step n) := by
  let a := (2 * (q : ℝ) + 1) * step n
  let g (l : ℕ) := Real.cos (2 * (l : ℝ) * a)
  have hmem := half_angle_mem hn hq
  have hs : 0 < Real.sin a := Real.sin_pos_of_pos_of_lt_pi hmem.1 hmem.2
  have hlast : g n = -1 := by
    have hangle : 2 * (n : ℝ) * a = Real.pi + (q : ℝ) * (2 * Real.pi) := by
      calc
        _ = (2 * (q : ℝ) + 1) * (2 * (n : ℝ) * step n) := by dsimp [a]; ring
        _ = _ := by rw [step_mul hn]; ring
    simp [g, hangle, Real.cos_add_nat_mul_two_pi, Real.cos_pi]
  have hstep (l : ℕ) :
      2 * Real.sin a * Real.sin (((q : ℝ) + 1 / 2) * node n l) = g l - g (l + 1) := by
    dsimp only [g]
    rw [Real.cos_sub_cos, Nat.cast_add, Nat.cast_one]
    have hmid : (2 * (l : ℝ) * a + 2 * ((l : ℝ) + 1) * a) / 2 =
        ((q : ℝ) + 1 / 2) * node n l := by unfold a step node; ring
    have hdiff : (2 * (l : ℝ) * a - 2 * ((l : ℝ) + 1) * a) / 2 = -a := by ring
    rw [hmid, hdiff, Real.sin_neg]
    ring
  have htotal : 2 * Real.sin a * (∑ l ∈ Finset.range n, Real.sin (((q : ℝ) + 1 / 2) * node n l)) = 2 := calc
    _ = ∑ l ∈ Finset.range n, (g l - g (l + 1)) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun l _ ↦ hstep l
    _ = g 0 - g n := by
      simpa only [neg_sub_neg] using Finset.sum_range_sub (fun l ↦ -g l) n
    _ = _ := by norm_num [hlast, g]
  exact (eq_div_iff hs.ne').mpr (by linarith only [htotal])

private theorem envelope_samples {n k : ℕ} (hn : 2 ≤ n) (hk : k ∈ Finset.Ico 1 n) :
    let U := 1 / Real.sin ((2 * (k : ℝ) - 1) * step n)
    let V := 1 / Real.sin ((2 * (k : ℝ) + 1) * step n)
    (2 * (∑ l ∈ Finset.range n, Real.sin (node n l / 2) * Real.cos ((k : ℝ) * node n l)) = V - U) ∧
    (2 * (∑ l ∈ Finset.range n, (Real.cos (node n l / 2) / 2) *
      Real.sin ((k : ℝ) * node n l)) = (U + V) / 2) := by
  obtain ⟨hk₁, hkn⟩ := Finset.mem_Ico.mp hk
  have hminus : (∑ l ∈ Finset.range n, Real.sin (((k : ℝ) - 1 / 2) * node n l)) =
      1 / Real.sin ((2 * (k : ℝ) - 1) * step n) := by
    have h := sum_half_sin hn (q := k - 1) (by omega)
    rw [Nat.cast_sub hk₁, Nat.cast_one] at h
    convert h using 5 <;> ring
  have hplus := sum_half_sin hn hkn
  dsimp only
  constructor
  · rw [← hplus, ← hminus, ← Finset.sum_sub_distrib, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro l _
    have h₁ : (((k : ℝ) + 1 / 2) * node n l - ((k : ℝ) - 1 / 2) * node n l) / 2 =
        node n l / 2 := by ring
    have h₂ : (((k : ℝ) + 1 / 2) * node n l + ((k : ℝ) - 1 / 2) * node n l) / 2 =
        (k : ℝ) * node n l := by ring
    rw [Real.sin_sub_sin, h₁, h₂, mul_assoc]
  · rw [← hplus, ← hminus, ← Finset.sum_add_distrib, Finset.mul_sum, div_eq_mul_inv, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro l _
    rw [Real.sin_add_sin]
    have h₁ : (((k : ℝ) - 1 / 2) * node n l + ((k : ℝ) + 1 / 2) * node n l) / 2 =
        (k : ℝ) * node n l := by ring
    have h₂ : (((k : ℝ) - 1 / 2) * node n l - ((k : ℝ) + 1 / 2) * node n l) / 2 =
        -(node n l / 2) := by ring
    rw [h₁, h₂, Real.cos_neg]
    ring

-- The adjacent half-modes in j = n - k telescope in this form.
private noncomputable def cost (n j : ℕ) : ℝ :=
  ((j : ℝ) - 1 / 2) / Real.sin ((2 * (j : ℝ) - 1) * step n)

private theorem cost_succ (n j : ℕ) :
    cost n (j + 1) = ((j : ℝ) + 1 / 2) / Real.sin ((2 * (j : ℝ) + 1) * step n) := by
  unfold cost
  push_cast
  congr 1
  · ring
  · congr 1
    ring

private theorem coefficient_eq {n : ℕ} (hn : 2 ≤ n) (c : ℝ) (d : ℕ → ℝ)
    (hmajor : ∀ s : ℝ, |Real.sin (s / 2)| ≤
      c + ∑ m ∈ Finset.Ico 1 n, d m * Real.cos ((m : ℝ) * s))
    (hcontact : ∀ l < n, c + ∑ m ∈ Finset.Ico 1 n, d m * Real.cos ((m : ℝ) * node n l) =
      |Real.sin (node n l / 2)|)
    {k : ℕ} (hk : k ∈ Finset.Ico 1 n) :
    d k = (cost n (n - k) - cost n (n - k + 1)) / (n : ℝ) ^ 2 := by
  obtain ⟨hk₁, hkn⟩ := Finset.mem_Ico.mp hk
  have hk₀ : 0 < k := by omega
  let j := n - k
  have hkj : (k : ℝ) + (j : ℝ) = (n : ℝ) := by
    dsimp [j]
    rw [Nat.cast_sub hkn.le]
    ring
  let U := 1 / Real.sin ((2 * (k : ℝ) - 1) * step n)
  let V := 1 / Real.sin ((2 * (k : ℝ) + 1) * step n)
  obtain ⟨hval, hderiv⟩ := envelope_samples hn hk
  have hzero : (∑ l ∈ Finset.range n, Real.cos ((k : ℝ) * node n l)) = 0 :=
    (div_eq_zero_iff.mp (average_cos_sin_eq_zero hn hk₀ hkn).1).resolve_right (cast_n_pos hn).ne'
  have hC : (n : ℝ) * (d k - d j) = V - U := calc
    _ = 2 * (∑ l ∈ Finset.range n,
        (∑ m ∈ Finset.Ico 1 n, d m * Real.cos ((m : ℝ) * node n l)) *
          Real.cos ((k : ℝ) * node n l)) := by
      symm
      simpa only [j, sub_eq_add_neg, neg_one_mul] using project hk d Real.cos (-1) (by
        intro m hm
        simpa only [sub_eq_add_neg, neg_one_mul] using
          (grid_kernels hn (Finset.mem_Ico.mp hm).2 hk₀ hkn).1)
    _ = 2 * (∑ l ∈ Finset.range n,
        (c + ∑ m ∈ Finset.Ico 1 n, d m * Real.cos ((m : ℝ) * node n l)) *
          Real.cos ((k : ℝ) * node n l)) := by
      simp only [add_mul, Finset.sum_add_distrib, ← Finset.mul_sum, hzero, mul_zero, zero_add]
    _ = 2 * (∑ l ∈ Finset.range n, Real.sin (node n l / 2) * Real.cos ((k : ℝ) * node n l)) := by
      congr 1
      apply Finset.sum_congr rfl
      intro l hl
      rw [hcontact l (Finset.mem_range.mp hl), abs_of_pos (sin_node_pos hn (Finset.mem_range.mp hl))]
    _ = V - U := hval
  have hS : (n : ℝ) * ((k : ℝ) * d k + (j : ℝ) * d j) = -((U + V) / 2) := calc
    _ = 2 * (∑ l ∈ Finset.range n,
        (∑ m ∈ Finset.Ico 1 n, ((m : ℝ) * d m) * Real.sin ((m : ℝ) * node n l)) *
          Real.sin ((k : ℝ) * node n l)) := by
      symm
      simpa only [j, one_mul] using project hk (fun m ↦ (m : ℝ) * d m) Real.sin 1 (by
        intro m hm
        simpa only [one_mul] using (grid_kernels hn (Finset.mem_Ico.mp hm).2 hk₀ hkn).2)
    _ = -(2 * (∑ l ∈ Finset.range n, (Real.cos (node n l / 2) / 2) *
        Real.sin ((k : ℝ) * node n l))) := by
      rw [← mul_neg, ← Finset.sum_neg_distrib]
      congr 1
      apply Finset.sum_congr rfl
      intro l hl
      rw [derivative_contact hn c d hmajor hcontact (Finset.mem_range.mp hl), neg_mul]
    _ = _ := congrArg Neg.neg hderiv
  -- Eliminate the reflected coefficient, without requiring k ≠ n - k.
  have hd : d k * (n : ℝ) ^ 2 = ((j : ℝ) - 1 / 2) * V - ((j : ℝ) + 1 / 2) * U := by
    linear_combination (j : ℝ) * hC + hS - ((n : ℝ) * d k) * hkj
  have hreflect (a : ℝ) : Real.sin ((2 * (k : ℝ) - a) * step n) =
      Real.sin ((2 * (j : ℝ) + a) * step n) := by
    have ht : (2 * (k : ℝ) - a) * step n = Real.pi - (2 * (j : ℝ) + a) * step n := by
      linear_combination step_mul hn + 2 * step n * hkj
    rw [ht, Real.sin_pi_sub]
  have hV : Real.sin ((2 * (k : ℝ) + 1) * step n) =
      Real.sin ((2 * (j : ℝ) - 1) * step n) := by
    simpa only [sub_eq_add_neg, neg_neg] using hreflect (-1)
  apply (eq_div_iff_mul_eq (pow_ne_zero 2 (cast_n_pos hn).ne')).mpr
  change d k * (n : ℝ) ^ 2 = cost n j - cost n (j + 1)
  rw [cost_succ n j]
  simpa only [cost, U, V, hreflect 1, hV, div_eq_mul_inv, one_mul] using hd

private theorem angle_ratio_lt {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < Real.pi) :
    a / Real.sin a < b / Real.sin b := by
  have hb₀ := ha.trans hab
  have ht₀ : 0 < a / b := div_pos ha hb₀
  have ht₁ : 0 < 1 - a / b := sub_pos.mpr ((div_lt_one hb₀).mpr hab)
  have ht := strictConcaveOn_sin_Icc.2 (x := 0) (y := b)
    ⟨le_rfl, Real.pi_pos.le⟩ ⟨hb₀.le, hb.le⟩ hb₀.ne ht₁ ht₀ (sub_add_cancel 1 (a / b))
  have hs : a * Real.sin b / b < Real.sin a := by
    simpa only [smul_eq_mul, Real.sin_zero, mul_zero, zero_add, div_mul_cancel₀ a hb₀.ne',
      div_mul_eq_mul_div] using ht
  rw [div_lt_div_iff₀ (Real.sin_pos_of_pos_of_lt_pi ha (hab.trans hb))
    (Real.sin_pos_of_pos_of_lt_pi hb₀ hb)]
  exact mul_comm (Real.sin a) b ▸ (div_lt_iff₀ hb₀).mp hs

private theorem cost_lt_cost_succ {n j : ℕ} (hn : 2 ≤ n) (hj₁ : 1 ≤ j) (hj : j < n) :
    cost n j < cost n (j + 1) := by
  let a := (2 * (j : ℝ) - 1) * step n
  let b := (2 * (j : ℝ) + 1) * step n
  have ha : 0 < a := by
    have h := (half_angle_mem hn (q := j - 1) (by omega)).1
    rw [Nat.cast_sub hj₁, Nat.cast_one] at h
    convert h using 1
    dsimp [a]
    ring
  have hab : a < b := by
    exact mul_lt_mul_of_pos_right (by linarith) (step_pos hn)
  have hb : b < Real.pi := (half_angle_mem hn hj).2
  have ha' : ((j : ℝ) - 1 / 2) * (2 * step n) = a := by dsimp [a]; ring
  have hb' : ((j : ℝ) + 1 / 2) * (2 * step n) = b := by dsimp [b]; ring
  rw [cost_succ, cost]
  apply (mul_lt_mul_iff_left₀ (mul_pos (by norm_num : (0 : ℝ) < 2) (step_pos hn))).mp
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ha', hb']
  exact angle_ratio_lt ha hab hb

private theorem sin_step_pos {n : ℕ} (hn : 2 ≤ n) : 0 < Real.sin (step n) := by
  have h := half_angle_mem hn (q := 0) (by omega)
  exact Real.sin_pos_of_pos_of_lt_pi (step_pos hn) (by simpa using h.2)

private theorem sum_abs_eq {n : ℕ} (hn : 2 ≤ n) (d : ℕ → ℝ)
    (hcoef : ∀ k ∈ Finset.Ico 1 n, d k = (cost n (n - k) - cost n (n - k + 1)) / (n : ℝ) ^ 2)
    (hneg : ∀ k ∈ Finset.Ico 1 n, d k < 0) :
    (∑ k ∈ Finset.Ico 1 n, |d k|) = (1 - 1 / (n : ℝ)) * (1 / ((n : ℝ) * Real.sin (step n))) := by
  have hreflect := Finset.sum_Ico_reflect (fun k ↦ |d k|) 1 (m := n) (n := n) (by omega)
  rw [show n + 1 - n = 1 by omega, show n + 1 - 1 = n by omega] at hreflect
  rw [← hreflect]
  have htail : cost n n = ((n : ℝ) - 1 / 2) / Real.sin (step n) := by
    have ht : (2 * (n : ℝ) - 1) * step n = Real.pi - step n := by
      linear_combination step_mul hn
    rw [cost, ht, Real.sin_pi_sub]
  have hhead : cost n 1 = (1 / 2) / Real.sin (step n) := by norm_num [cost]
  calc
    _ = ∑ j ∈ Finset.Ico 1 n, (cost n (j + 1) - cost n j) / (n : ℝ) ^ 2 := by
      apply Finset.sum_congr rfl
      intro j hj
      have hj' := Finset.mem_Ico.mp hj
      have hk : n - j ∈ Finset.Ico 1 n := Finset.mem_Ico.mpr (by omega)
      rw [abs_of_neg (hneg _ hk), hcoef _ hk, show n - (n - j) = j by omega, ← neg_div, neg_sub]
    _ = (cost n n - cost n 1) / (n : ℝ) ^ 2 := by
      simp only [div_eq_mul_inv, ← Finset.sum_mul, Finset.sum_Ico_sub _ (by omega : 1 ≤ n)]
    _ = _ := by
      rw [htail, hhead]
      field_simp [(cast_n_pos hn).ne', (sin_step_pos hn).ne']
      ring

private theorem budget_lt {n : ℕ} (hn : 2 ≤ n) :
    (1 - 1 / (n : ℝ)) * (1 / ((n : ℝ) * Real.sin (step n))) < 2 / Real.pi := by
  have hn₀ := cast_n_pos hn
  have hn₂ : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hz := step_pos hn
  have hzn : step n * (n : ℝ) < 2 := by linarith only [step_mul hn, Real.pi_lt_four]
  have hz₁ : step n < 1 := by
    calc
      _ < 2 / (n : ℝ) := (lt_div_iff₀ hn₀).mpr hzn
      _ ≤ 1 := (div_le_one hn₀).mpr hn₂
  -- The cubic sine bound suffices since (π/(2n))² / 6 < 1/n.
  have hzsq : step n ^ 2 / 6 < 1 / (n : ℝ) := by
    apply (lt_div_iff₀ hn₀).mpr
    nlinarith only [mul_lt_mul_of_pos_left hz₁ (mul_pos hz hn₀), hzn]
  have hs : step n * (1 - 1 / (n : ℝ)) < Real.sin (step n) := by
    nlinarith only [mul_lt_mul_of_pos_left hzsq hz, Real.sin_gt_sub_cube hz]
  rw [mul_one_div, div_lt_div_iff₀ (mul_pos hn₀ (sin_step_pos hn)) Real.pi_pos]
  have h := mul_lt_mul_of_pos_left hs (mul_pos (by norm_num : (0 : ℝ) < 2) hn₀)
  calc
    _ = (2 * (n : ℝ)) * (step n * (1 - 1 / (n : ℝ))) := by rw [← mul_assoc, step_mul hn, mul_comm]
    _ < _ := by simpa only [mul_assoc] using h

/-- For every `n ≥ 2`, the global shifted majorant attaining `C_n` at the
shifted grid nodes has the explicit cosecant coefficients. They are strictly
negative and their total absolute mass is `(1 - 1/n) C_n < 2/π`. -/
public theorem exists_majorant_with_budget {n : ℕ} (hn : 2 ≤ n) :
    let z := Real.pi / (2 * (n : ℝ))
    let C := 1 / ((n : ℝ) * Real.sin z)
    ∃ d : ℕ → ℝ,
      (∀ s : ℝ, |Real.sin (s / 2)| ≤ C + ∑ k ∈ Finset.Ico 1 n, d k * Real.cos ((k : ℝ) * s)) ∧
      (∀ l < n, C + ∑ k ∈ Finset.Ico 1 n, d k * Real.cos ((k : ℝ) * node n l) =
        |Real.sin (node n l / 2)|) ∧
      (∀ k ∈ Finset.Ico 1 n, let j := n - k
        d k = (((j : ℝ) - 1 / 2) / Real.sin ((2 * (j : ℝ) - 1) * z) -
          ((j : ℝ) + 1 / 2) / Real.sin ((2 * (j : ℝ) + 1) * z)) / (n : ℝ) ^ 2) ∧
      (∀ k ∈ Finset.Ico 1 n, d k < 0) ∧
      (∑ k ∈ Finset.Ico 1 n, |d k|) = (1 - 1 / (n : ℝ)) * C ∧
      (1 - 1 / (n : ℝ)) * C < 2 / Real.pi := by
  obtain ⟨d, hmajor, hcontact⟩ := ConsecutiveHarmonicMajorant.exists_majorant hn
  have hcoef (k : ℕ) (hk : k ∈ Finset.Ico 1 n) := coefficient_eq hn _ d hmajor hcontact hk
  have hneg (k : ℕ) (hk : k ∈ Finset.Ico 1 n) : d k < 0 := by
    have hk' := Finset.mem_Ico.mp hk
    rw [hcoef k hk]
    exact div_neg_of_neg_of_pos (sub_neg.mpr (cost_lt_cost_succ hn (by omega) (by omega)))
      (pow_pos (cast_n_pos hn) 2)
  refine ⟨d, hmajor, hcontact, fun k hk ↦ ?_, hneg, sum_abs_eq hn d hcoef hneg, budget_lt hn⟩
  have h := hcoef k hk
  rw [cost_succ n (n - k)] at h
  simpa only [cost, step] using h

end Masullo.ConsecutiveHarmonicBudget
