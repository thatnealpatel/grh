module

public import Lemmas.SignedPoissonDefect
public import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
# Exterior Poisson width replacement with exceptional pairs

Source: `10c1c87:.godel/bob/first-depth-bands.md:27–39`, especially the
finite width-replacement estimate at line 33.

Scope: the unnormalized kernel `k_u(z) = u / (u² + z²)` and the difference of
two full finite local sums, each divided by `R`. A pair carries two nonnegative
weights, one for each offset `b` and `-b` at the same ordinate; a line zero can
be counted once by giving one member zero weight. Exceptional pairs remain in
both full sums and are charged separately by the sum of their two weights times
`exp (D * |b|)`. No deletion, zero-counting estimate, or trace limit is asserted.

Owning check session: `01a20d17-2b2a-7097-a6d0-937638b43d97`.
-/

namespace ExceptionalPoissonWidth

open SignedPoissonDefect (kernel)

/-- An explicit constant depending only on the exterior width and displacement. -/
@[expose] public noncomputable def widthConstant (a v : ℝ) : ℝ :=
  (2 + 2 * v ^ 2) / (a - 1 / 2) ^ 2 + 2

/-- Uniform inverse-square cost of replacing a signed width shift by zero. -/
public theorem abs_kernel_sub_le {a : ℝ} (ha : 1 / 2 < a) (v x : ℝ)
    {b : ℝ} (hb : |b| ≤ 1 / 2) :
    |kernel (a - b) (x - v) - kernel a (x - v)| ≤
      widthConstant a v * |b| / (1 + x ^ 2) := by
  let m := a - 1 / 2
  let u := a - b
  let z := x - v
  let p := u ^ 2 + z ^ 2
  let q := a ^ 2 + z ^ 2
  let r := m ^ 2 + z ^ 2
  have hm : 0 < m := sub_pos.mpr ha
  have hma : m ≤ a := by dsimp [m]; linarith
  have hmu : m ≤ u := sub_le_sub_left (abs_le.mp hb).2 a
  have hr : 0 < r := by dsimp only [r]; positivity
  have hrp : r ≤ p := add_le_add (pow_le_pow_left₀ hm.le hmu 2) le_rfl
  have hrq : r ≤ q := add_le_add (pow_le_pow_left₀ hm.le hma 2) le_rfl
  have hp : 0 < p := hr.trans_le hrp
  have hq : 0 < q := hr.trans_le hrq
  have hdiff : kernel u z - kernel a z = b * (a * u - z ^ 2) / (p * q) := by
    have hab : a - u = b := by dsimp [u]; ring
    rw [← hab]
    unfold kernel
    change u / p - a / q = (a - u) * (a * u - z ^ 2) / (p * q)
    field_simp [hp.ne', hq.ne']
    dsimp only [p, q]
    ring
  have hnum : |a * u - z ^ 2| ≤ (p + q) / 2 := by
    apply abs_le.mpr
    dsimp only [p, q]
    constructor
    · nlinarith only [sq_nonneg (a + u)]
    · nlinarith only [sq_nonneg (a - u), sq_nonneg z]
  have hrnum : r * |a * u - z ^ 2| ≤ p * q := by
    calc
      _ ≤ r * ((p + q) / 2) := mul_le_mul_of_nonneg_left hnum hr.le
      _ = (r * p + r * q) / 2 := by ring
      _ ≤ p * q := by
        have h₁ := mul_le_mul_of_nonneg_right hrq hp.le
        rw [mul_comm q p] at h₁
        have h₂ := mul_le_mul_of_nonneg_right hrp hq.le
        linarith only [h₁, h₂]
  have hcenter : 1 + x ^ 2 ≤ widthConstant a v * r := by
    calc
      _ ≤ (2 + 2 * v ^ 2) + 2 * z ^ 2 := by
        dsimp only [z]
        nlinarith only [sq_nonneg (x - 2 * v)]
      _ = ((2 + 2 * v ^ 2) / m ^ 2) * m ^ 2 + 2 * z ^ 2 := by
        rw [div_mul_cancel₀ _ (pow_ne_zero _ hm.ne')]
      _ ≤ _ := by
        change _ ≤ ((2 + 2 * v ^ 2) / m ^ 2 + 2) * (m ^ 2 + z ^ 2)
        have h : 0 ≤ (2 + 2 * v ^ 2) / m ^ 2 := by positivity
        nlinarith only [mul_nonneg h (sq_nonneg z), sq_nonneg m]
  change |kernel u z - kernel a z| ≤ _
  calc
    _ ≤ |b| / r := by
      rw [hdiff, abs_div, abs_mul, abs_of_pos (mul_pos hp hq)]
      apply (div_le_div_iff₀ (mul_pos hp hq) hr).mpr
      rw [mul_assoc, mul_comm |a * u - z ^ 2| r]
      exact mul_le_mul_of_nonneg_left hrnum (abs_nonneg b)
    _ ≤ _ := by
      apply (div_le_div_iff₀ hr (by positivity)).mpr
      calc
        _ ≤ |b| * (widthConstant a v * r) := mul_le_mul_of_nonneg_left hcenter (abs_nonneg b)
        _ = _ := by ring

/-- Replace both signed widths in the full finite pair sum. The first budget
uses all pairs, and the second budget uses only exceptional pairs in that sum.
The nonnegative weights may in particular be real casts of multiplicities. -/
public theorem abs_normalized_pair_sum_sub_le {ι : Type*} (s : Finset ι)
    (E : ι → Prop) [DecidablePred E] (x b wPlus wMinus : ι → ℝ)
    {a D R c : ℝ} (ha : 1 / 2 < a) (v : ℝ) (hD : 0 < D) (hR : 0 < R) (hc : 0 ≤ c)
    (hwPlus : ∀ i ∈ s, 0 ≤ wPlus i) (hwMinus : ∀ i ∈ s, 0 ≤ wMinus i)
    (hb : ∀ i ∈ s, |b i| ≤ 1 / 2)
    (hshallow : ∀ i ∈ s, ¬ E i → |b i| ≤ c / D) :
    |(∑ i ∈ s, (wPlus i * kernel (a - b i) (x i - v) +
        wMinus i * kernel (a + b i) (x i - v))) / R -
      (∑ i ∈ s, (wPlus i + wMinus i) * kernel a (x i - v)) / R| ≤
    (widthConstant a v / D) *
      (c * ((∑ i ∈ s, (wPlus i + wMinus i) / (1 + x i ^ 2)) / R) +
        (∑ i ∈ s.filter E, (wPlus i + wMinus i) * Real.exp (D * |b i|)) / R) := by
  let C := widthConstant a v
  let W i := wPlus i + wMinus i
  let f i := wPlus i * kernel (a - b i) (x i - v) + wMinus i * kernel (a + b i) (x i - v)
  let g i := W i * kernel a (x i - v)
  let A i := W i / (1 + x i ^ 2)
  let B i := W i * Real.exp (D * |b i|)
  have hC : 0 ≤ C := by dsimp only [C, widthConstant]; positivity
  have hpair i (hi : i ∈ s) : |f i - g i| ≤ C * W i * (|b i| / (1 + x i ^ 2)) := by
    have hPlus := abs_kernel_sub_le ha v (x i) (hb i hi)
    have hMinus : |kernel (a + b i) (x i - v) - kernel a (x i - v)| ≤
        C * |b i| / (1 + x i ^ 2) := by
      simpa only [sub_neg_eq_add, abs_neg] using
        abs_kernel_sub_le ha v (x i) (b := -b i) (by simpa only [abs_neg] using hb i hi)
    have hsplit : f i - g i =
        wPlus i * (kernel (a - b i) (x i - v) - kernel a (x i - v)) +
        wMinus i * (kernel (a + b i) (x i - v) - kernel a (x i - v)) := by
      dsimp only [f, g, W]
      ring
    rw [hsplit]
    calc
      _ ≤ _ := abs_add_le _ _
      _ ≤ wPlus i * (C * |b i| / (1 + x i ^ 2)) + wMinus i * (C * |b i| / (1 + x i ^ 2)) := by
        simp only [abs_mul, abs_of_nonneg (hwPlus i hi), abs_of_nonneg (hwMinus i hi)]
        exact add_le_add (mul_le_mul_of_nonneg_left hPlus (hwPlus i hi))
          (mul_le_mul_of_nonneg_left hMinus (hwMinus i hi))
      _ = _ := by dsimp only [W]; ring
  have hdepth i (hi : i ∈ s) : |b i| / (1 + x i ^ 2) ≤
      (c / (1 + x i ^ 2) + (if E i then Real.exp (D * |b i|) else 0)) / D := by
    have hx : 0 < 1 + x i ^ 2 := by positivity
    by_cases he : E i
    · rw [ite_eq_left he]
      have hexp : D * |b i| ≤ Real.exp (D * |b i|) :=
        (le_add_of_nonneg_right zero_le_one).trans (Real.add_one_le_exp _)
      apply (le_div_iff₀ hD).mpr
      calc
        _ = (D * |b i|) / (1 + x i ^ 2) := by ring
        _ ≤ (D * |b i|) / 1 :=
          div_le_div_of_nonneg_left (by positivity) zero_lt_one
            (le_add_of_nonneg_right (sq_nonneg (x i)))
        _ ≤ _ := by
          rw [div_one]
          exact hexp.trans (le_add_of_nonneg_left (div_nonneg hc hx.le))
    · rw [ite_eq_right he, add_zero]
      calc
        _ ≤ (c / D) / (1 + x i ^ 2) := div_le_div_of_nonneg_right (hshallow i hi he) hx.le
        _ = _ := by ring
  have hterm i (hi : i ∈ s) :
      |f i - g i| ≤ C / D * (c * A i + (if E i then B i else 0)) := by
    have hW : 0 ≤ W i := add_nonneg (hwPlus i hi) (hwMinus i hi)
    calc
      _ ≤ C * W i * (|b i| / (1 + x i ^ 2)) := hpair i hi
      _ ≤ C * W i * ((c / (1 + x i ^ 2) +
          (if E i then Real.exp (D * |b i|) else 0)) / D) :=
        mul_le_mul_of_nonneg_left (hdepth i hi) (mul_nonneg hC hW)
      _ = _ := by
        by_cases he : E i
        · simp only [ite_eq_left he, A, B]
          ring
        · simp only [ite_eq_right he, A]
          ring
  have hsum : |∑ i ∈ s, (f i - g i)| ≤
      C / D * (c * (∑ i ∈ s, A i) + ∑ i ∈ s.filter E, B i) := by
    calc
      _ ≤ ∑ i ∈ s, |f i - g i| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i ∈ s, C / D * (c * A i + (if E i then B i else 0)) := Finset.sum_le_sum hterm
      _ = _ := by rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_filter]
  change |(∑ i ∈ s, f i) / R - (∑ i ∈ s, g i) / R| ≤
    C / D * (c * ((∑ i ∈ s, A i) / R) + (∑ i ∈ s.filter E, B i) / R)
  rw [← sub_div, abs_div, abs_of_pos hR, ← Finset.sum_sub_distrib]
  calc
    _ ≤ (C / D * (c * (∑ i ∈ s, A i) + ∑ i ∈ s.filter E, B i)) / R :=
      div_le_div_of_nonneg_right hsum hR.le
    _ = _ := by ring

end ExceptionalPoissonWidth
