module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.RingTheory.Coprime.Basic
import Mathlib.Algebra.Order.Ring.Cast
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Collinearity in a spaced gap rectangle

Source: `a9dedc89:.godel/alice/spaced-product-cut.md`, “A spaced gap rectangle,”
lines 15–19. This is the geometry for a fixed affine congruence in the branch
`s ≤ L`: the index half-width is `U = L / s` and the vertical half-width is
`V = H`. It does not count the occupancy of a line or the number of moduli.

Owning check session: `01a208d1-f4a1-7e74-9d68-6b0dfb6d9df9`.
-/

namespace SpacedGapCollinearity

private theorem abs_sub_le_of_center {x y c W : ℝ}
    (hx : |x - c| ≤ W) (hy : |y - c| ≤ W) : |x - y| ≤ 2 * W := by
  calc
    |x - y| = |(x - c) - (y - c)| := by rw [sub_sub_sub_cancel_right]
    _ ≤ |x - c| + |y - c| := abs_sub _ _
    _ ≤ 2 * W := by simpa only [two_mul] using add_le_add hx hy

private theorem eq_zero_of_dvd_of_abs_cast_lt {f z : ℤ}
    (hdvd : f ∣ z) (hsmall : |(z : ℝ)| < (f : ℝ)) : z = 0 := by
  by_contra hz
  have hle : f ≤ |z| := Int.le_of_dvd (abs_pos.mpr hz) ((dvd_abs f z).mpr hdvd)
  have hleReal : (f : ℝ) ≤ |(z : ℝ)| := by
    rw [← Int.cast_abs]
    exact Int.cast_le.mpr hle
  exact (not_lt_of_ge hleReal) hsmall

/-- In a translated box of half-widths `L / s ≥ 1` and `V ≥ L`, every triple of
solutions of the affine congruence has zero determinant in the `(j,b)` coordinates.
Distinct solutions differ in both coordinates, and every physical horizontal
separation is at most `2 * L`. `IsCoprime f A` and `IsCoprime f B` express that
`A` and `B` are units modulo `f`; the stride `s` need not be a unit. -/
public theorem spacedGapRectangle_geometry
    {S : Set (ℤ × ℤ)} {a₀ s A B f : ℤ} {j₀ b₀ L V : ℝ}
    (hs : 0 < s) (hU : 1 ≤ L / (s : ℝ)) (hLV : L ≤ V)
    (hf : 8 * (L / (s : ℝ)) * V < (f : ℝ)) (hA : IsCoprime f A) (hB : IsCoprime f B)
    (hbox : ∀ p ∈ S, |(p.1 : ℝ) - j₀| ≤ L / (s : ℝ) ∧ |(p.2 : ℝ) - b₀| ≤ V)
    (hcong : ∀ p ∈ S, A * (a₀ + s * p.1) ≡ B * p.2 [ZMOD f]) :
    (∀ p ∈ S, ∀ q ∈ S, ∀ r ∈ S,
      (q.1 - p.1) * (r.2 - p.2) - (r.1 - p.1) * (q.2 - p.2) = 0) ∧
    (∀ p ∈ S, ∀ q ∈ S, p ≠ q → q.1 - p.1 ≠ 0 ∧ q.2 - p.2 ≠ 0) ∧
    (∀ p ∈ S, ∀ q ∈ S, (s : ℝ) * |((q.1 - p.1 : ℤ) : ℝ)| ≤ 2 * L) := by
  let U : ℝ := L / (s : ℝ)
  change 1 ≤ U at hU
  change 8 * U * V < (f : ℝ) at hf
  have hUpos : 0 < U := zero_lt_one.trans_le hU
  have hsReal : (0 : ℝ) < s := by exact_mod_cast hs
  have hsU : (s : ℝ) * U = L := by
    rw [mul_comm]
    exact div_mul_cancel₀ L hsReal.ne'
  have hLpos : 0 < L := hsU ▸ mul_pos hsReal hUpos
  have hVnonneg : 0 ≤ V := hLpos.le.trans hLV
  have hVf : 2 * V < (f : ℝ) :=
    (mul_le_mul_of_nonneg_right (show (2 : ℝ) ≤ 8 * U by linarith only [hU])
      hVnonneg).trans_lt hf
  have hjbox {p q : ℤ × ℤ} (hp : p ∈ S) (hq : q ∈ S) :
      |((q.1 - p.1 : ℤ) : ℝ)| ≤ 2 * U := by
    rw [Int.cast_sub]
    exact abs_sub_le_of_center (hbox q hq).1 (hbox p hp).1
  have hbbox {p q : ℤ × ℤ} (hp : p ∈ S) (hq : q ∈ S) :
      |((q.2 - p.2 : ℤ) : ℝ)| ≤ 2 * V := by
    rw [Int.cast_sub]
    exact abs_sub_le_of_center (hbox q hq).2 (hbox p hp).2
  have hphysical (p : ℤ × ℤ) (hp : p ∈ S) (q : ℤ × ℤ) (hq : q ∈ S) :
      (s : ℝ) * |((q.1 - p.1 : ℤ) : ℝ)| ≤ 2 * L := by
    calc
      _ ≤ (s : ℝ) * (2 * U) := mul_le_mul_of_nonneg_left (hjbox hp hq) hsReal.le
      _ = 2 * L := by rw [mul_left_comm, hsU]
  have hdiff {p q : ℤ × ℤ} (hp : p ∈ S) (hq : q ∈ S) :
      f ∣ A * (s * (q.1 - p.1)) - B * (q.2 - p.2) := by
    have h := Int.modEq_iff_dvd.mp (((hcong q hq).sub (hcong p hp)).symm)
    convert h using 1
    ring
  refine ⟨?_, ?_, hphysical⟩
  · intro p hp q hq r hr
    let D : ℤ := (q.1 - p.1) * (r.2 - p.2) - (r.1 - p.1) * (q.2 - p.2)
    -- Eliminate the common coefficient `A * s`, then cancel only `B`.
    have hBD : f ∣ B * D := by
      have h := dvd_sub ((hdiff hp hq).mul_left (r.1 - p.1))
        ((hdiff hp hr).mul_left (q.1 - p.1))
      convert h using 1
      dsimp only [D]
      ring
    have hprod {q r : ℤ × ℤ} (hq : q ∈ S) (hr : r ∈ S) :
        |((q.1 - p.1 : ℤ) : ℝ)| * |((r.2 - p.2 : ℤ) : ℝ)| ≤ 2 * U * (2 * V) :=
      mul_le_mul (hjbox hp hq) (hbbox hp hr) (abs_nonneg _)
        (mul_nonneg zero_le_two hUpos.le)
    have hbound : |(D : ℝ)| ≤ 8 * U * V := by
      simp only [D, Int.cast_sub, Int.cast_mul]
      calc
        _ ≤ |((q.1 : ℝ) - p.1) * ((r.2 : ℝ) - p.2)| +
            |((r.1 : ℝ) - p.1) * ((q.2 : ℝ) - p.2)| := abs_sub _ _
        _ ≤ 2 * U * (2 * V) + 2 * U * (2 * V) := by
          simpa only [abs_mul, Int.cast_sub] using add_le_add (hprod hq hr) (hprod hr hq)
        _ = 8 * U * V := by ring
    exact eq_zero_of_dvd_of_abs_cast_lt (hB.dvd_of_dvd_mul_left hBD) (hbound.trans_lt hf)
  · intro p hp q hq hpq
    have h := hdiff hp hq
    have eq_of_diffs_zero (hj : q.1 - p.1 = 0) (hb : q.2 - p.2 = 0) : p = q :=
      Prod.ext (sub_eq_zero.mp hj).symm (sub_eq_zero.mp hb).symm
    constructor
    · intro hj
      have hdvd : f ∣ B * (q.2 - p.2) := by
        simpa only [hj, mul_zero, zero_sub, dvd_neg] using h
      have hb := eq_zero_of_dvd_of_abs_cast_lt (hB.dvd_of_dvd_mul_left hdvd)
        ((hbbox hp hq).trans_lt hVf)
      exact hpq (eq_of_diffs_zero hj hb)
    · intro hb
      have hdvd : f ∣ A * (s * (q.1 - p.1)) := by
        simpa only [hb, mul_zero, sub_zero] using h
      have hlt : |((s * (q.1 - p.1) : ℤ) : ℝ)| < (f : ℝ) := by
        rw [Int.cast_mul, abs_mul, abs_of_pos hsReal]
        exact ((hphysical p hp q hq).trans
          (mul_le_mul_of_nonneg_left hLV zero_le_two)).trans_lt hVf
      have hz := eq_zero_of_dvd_of_abs_cast_lt (hA.dvd_of_dvd_mul_left hdvd) hlt
      exact hpq (eq_of_diffs_zero ((mul_eq_zero.mp hz).resolve_left hs.ne') hb)

end SpacedGapCollinearity
