module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Basic.Complex.BigOperators
import Mathlib.RingTheory.RootsOfUnity.Complex

/-!
# The shifted-grid lower bound for consecutive harmonic majorants

Source: `8fde6138dc2ec249c6560b66ca0976aa8ea34dab:.godel/bob/initial-harmonic-budget.md`,
“A sharp constant for degree less than n” (first paragraph), used for the final
“Conversely” degree obstruction. This module proves only the lower bound on the
constant term by averaging on the shifted grid. It does not construct a majorant
or make a claim about arbitrary sparse frequencies.

Owning check session: `01a20a16-7036-75bb-8ab9-3bc3a536b6e9`.
-/

open scoped BigOperators

namespace Masullo.ConsecutiveHarmonicGrid

/-- The angle of the `l`-th shifted node, with `0 ≤ l < n` on the grid. -/
public noncomputable def node (n l : ℕ) : ℝ :=
  (2 * (l : ℝ) + 1) * Real.pi / (n : ℝ)

private theorem node_mem_Ioo {n l : ℕ} (hn : 2 ≤ n) (hl : l < n) :
    node n l ∈ Set.Ioo (0 : ℝ) (2 * Real.pi) := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
  have hl' : (l : ℝ) + 1 ≤ (n : ℝ) := by
    exact_mod_cast (show l + 1 ≤ n by omega)
  refine ⟨div_pos (mul_pos (by positivity) Real.pi_pos) hn', (div_lt_iff₀ hn').2 ?_⟩
  calc
    (2 * (l : ℝ) + 1) * Real.pi < (2 * (n : ℝ)) * Real.pi :=
      mul_lt_mul_of_pos_right (by linarith) Real.pi_pos
    _ = 2 * Real.pi * (n : ℝ) := by ring

/-- The average of the angular envelope on the shifted grid is the source's `C_n`. -/
public theorem average_abs_sin {n : ℕ} (hn : 2 ≤ n) :
    (∑ l ∈ Finset.range n, |Real.sin (node n l / 2)|) / (n : ℝ) =
      1 / ((n : ℝ) * Real.sin (Real.pi / (2 * (n : ℝ)))) := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
  let a : ℝ := Real.pi / (2 * (n : ℝ))
  have hhalf (l : ℕ) : node n l / 2 = (2 * (l : ℝ) + 1) * a := by
    unfold node a
    field_simp [hn'.ne']
  have hpos (l : ℕ) (hl : l < n) : 0 < Real.sin (node n l / 2) := by
    have hnode := node_mem_Ioo hn hl
    exact Real.sin_pos_of_pos_of_lt_pi (by linarith [hnode.1]) (by linarith [hnode.2])
  have hs : 0 < Real.sin a := by
    simpa only [hhalf, Nat.cast_zero, mul_zero, zero_add, one_mul] using hpos 0 (by omega)
  let g (l : ℕ) : ℝ := Real.cos (2 * (l : ℝ) * a)
  have hstep (l : ℕ) (hl : l ∈ Finset.range n) :
      2 * Real.sin a * |Real.sin (node n l / 2)| = g l - g (l + 1) := by
    rw [abs_of_pos (hpos l (Finset.mem_range.mp hl)), hhalf]
    dsimp only [g]
    rw [Real.cos_sub_cos, Nat.cast_add, Nat.cast_one]
    have hmid : (2 * (l : ℝ) * a + 2 * ((l : ℝ) + 1) * a) / 2 =
        (2 * (l : ℝ) + 1) * a := by ring
    have hdiff : (2 * (l : ℝ) * a - 2 * ((l : ℝ) + 1) * a) / 2 = -a := by ring
    rw [hmid, hdiff, Real.sin_neg]
    ring
  -- The cosine differences telescope from angle 0 to angle π.
  have hangle : 2 * (n : ℝ) * a = Real.pi :=
    mul_div_cancel₀ _ (by positivity : 2 * (n : ℝ) ≠ 0)
  have htel : 2 * Real.sin a * (∑ l ∈ Finset.range n, |Real.sin (node n l / 2)|) = 2 := calc
    _ = ∑ l ∈ Finset.range n, (g l - g (l + 1)) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl hstep
    _ = g 0 - g n := by
      simpa only [neg_sub_neg] using Finset.sum_range_sub (fun l ↦ -g l) n
    _ = 2 := by norm_num [g, hangle, Real.cos_pi]
  have hsum : (∑ l ∈ Finset.range n, |Real.sin (node n l / 2)|) = 1 / Real.sin a :=
    (eq_div_iff hs.ne').2 (by linarith only [htel])
  rw [hsum, div_div, mul_comm (Real.sin a)]

private theorem sum_exp_eq_zero {n k : ℕ} (hn : 2 ≤ n) (hk : 0 < k) (hkn : k < n) :
    (∑ l ∈ Finset.range n, Complex.exp (↑((k : ℝ) * node n l) * Complex.I)) = 0 := by
  let ω : ℂ := 2 * ↑Real.pi * Complex.I / (n : ℂ)
  let ζ : ℂ := Complex.exp ω
  have hroot : IsPrimitiveRoot ζ n := Complex.isPrimitiveRoot_exp n (by omega)
  have hpow : (ζ ^ k) ^ n = 1 := by
    rw [← pow_mul, Nat.mul_comm k n, pow_mul, hroot.pow_eq_one, one_pow]
  have hgeom : (∑ l ∈ Finset.range n, (ζ ^ k) ^ l) = 0 := by
    have h := geom_sum_mul (ζ ^ k) n
    rw [hpow, sub_self] at h
    exact (mul_eq_zero.mp h).resolve_right (sub_ne_zero.mpr
      (hroot.pow_ne_one_of_pos_of_lt hk.ne' hkn))
  -- The half-step shift contributes only a common phase to the geometric sum.
  let phase : ℂ := Complex.exp (↑((k : ℝ) * (Real.pi / (n : ℝ))) * Complex.I)
  have hfactor (l : ℕ) :
      Complex.exp (↑((k : ℝ) * node n l) * Complex.I) = phase * (ζ ^ k) ^ l := by
    have harg : (↑((k : ℝ) * node n l) : ℂ) * Complex.I =
        ↑((k : ℝ) * (Real.pi / (n : ℝ))) * Complex.I + (l : ℂ) * ((k : ℂ) * ω) := by
      unfold node ω
      push_cast
      ring
    rw [harg, Complex.exp_add, Complex.exp_nat_mul, Complex.exp_nat_mul]
  simp only [hfactor, ← Finset.mul_sum, hgeom, mul_zero]

private theorem sum_cos_sin_eq_zero {n k : ℕ} (hn : 2 ≤ n) (hk : 0 < k) (hkn : k < n) :
    (∑ l ∈ Finset.range n, Real.cos ((k : ℝ) * node n l)) = 0 ∧
      (∑ l ∈ Finset.range n, Real.sin ((k : ℝ) * node n l)) = 0 := by
  have h := sum_exp_eq_zero hn hk hkn
  exact ⟨by simpa only [Complex.re_sum, Complex.exp_ofReal_mul_I_re, Complex.zero_re]
           using congrArg Complex.re h,
    by simpa only [Complex.im_sum, Complex.exp_ofReal_mul_I_im, Complex.zero_im]
         using congrArg Complex.im h⟩

/-- The shifted grid annihilates both real modes at every frequency `0 < k < n`. -/
public theorem average_cos_sin_eq_zero {n k : ℕ} (hn : 2 ≤ n) (hk : 0 < k) (hkn : k < n) :
    (∑ l ∈ Finset.range n, Real.cos ((k : ℝ) * node n l)) / (n : ℝ) = 0 ∧
      (∑ l ∈ Finset.range n, Real.sin ((k : ℝ) * node n l)) / (n : ℝ) = 0 := by
  obtain ⟨hc, hs⟩ := sum_cos_sin_eq_zero hn hk hkn
  simp only [hc, hs, zero_div, and_self]

/-- A real trigonometric polynomial of degree `m < n` majorizing `|sin (s/2)|`
on one period has constant coefficient at least `C_n`. Both coefficient families
are arbitrary, and `m = 0` is allowed. -/
public theorem constant_term_ge {n m : ℕ} (hn : 2 ≤ n) (hmn : m < n)
    (c : ℝ) (a b : ℕ → ℝ)
    (hmajor : ∀ s ∈ Set.Icc (0 : ℝ) (2 * Real.pi),
      |Real.sin (s / 2)| ≤ c + ∑ k ∈ Finset.Icc 1 m,
        (a k * Real.cos ((k : ℝ) * s) + b k * Real.sin ((k : ℝ) * s))) :
    1 / ((n : ℝ) * Real.sin (Real.pi / (2 * (n : ℝ)))) ≤ c := by
  let mode (k l : ℕ) : ℝ :=
    a k * Real.cos ((k : ℝ) * node n l) + b k * Real.sin ((k : ℝ) * node n l)
  have hmode (k : ℕ) (hk : k ∈ Finset.Icc 1 m) :
      (∑ l ∈ Finset.range n, mode k l) = 0 := by
    have hk' := Finset.mem_Icc.mp hk
    obtain ⟨hc, hs⟩ := sum_cos_sin_eq_zero hn (by omega : 0 < k) (hk'.2.trans_lt hmn)
    simp only [mode, Finset.sum_add_distrib, ← Finset.mul_sum, hc, hs, mul_zero, add_zero]
  have hsum :
      (∑ l ∈ Finset.range n, (c + ∑ k ∈ Finset.Icc 1 m, mode k l)) = (n : ℝ) * c := by
    rw [Finset.sum_add_distrib, Finset.sum_comm, Finset.sum_eq_zero hmode]
    simp [nsmul_eq_mul]
  rw [← average_abs_sin hn, div_le_iff₀ (Nat.cast_pos.mpr (by omega : 0 < n)),
    mul_comm c (n : ℝ), ← hsum]
  exact Finset.sum_le_sum fun l hl ↦
    hmajor (node n l) (Set.Ioo_subset_Icc_self (node_mem_Ioo hn (Finset.mem_range.mp hl)))

end Masullo.ConsecutiveHarmonicGrid
