module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Nat.Prime.Int
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.Algebra.Order.Group.Unbundled.Int
import Mathlib.Algebra.Order.Ring.Cast
import Mathlib.RingTheory.Int.Basic
import Mathlib.Tactic.LinearCombination

/-!
# Geometry of a translated output strip

Source: `472c8e5d:.godel/alice/adaptive-complement-interval.md`, lines 15–26.
Consequence 3 of `1d3802f7:.godel/alice/two-cofactor-strips.md` explicitly uses
this translated-strip argument and its `2W < min xᵢ` condition before pricing
nonsingleton lines. Here points `p` are original integer coordinates `(z₁,z₂)`;
`T p` is the signed integral quotient and the rectangle is in `(z₁,T)`.
We prove the determinant multiple, collinearity, and the two original-coordinate
separations. We do not count primitive directions or affine occupancy, and do not
claim a uniform `√(LW/x₁)` count.

By contrast, `SpacedGapCollinearity.spacedGapRectangle_geometry` starts with an
already supplied affine congruence `A * (a₀ + s * j) ≡ B * b [ZMOD f]`, both
`IsCoprime f A` and `IsCoprime f B`, and the bounds `0 < s`, `1 ≤ L/s`, `L ≤ V`,
`8 * (L/s) * V < f`. It tests differences in `(j,b)`, and also bounds horizontal
separation after rescaling by `s`. It does not derive the determinant modulus
`e*x₁` from the signed row equation. Here the only coprimality used is derived
from primality of `q` and `q ∤ x₁*x₂`; none is imposed on the divisor `e`.

Owning check session: `01a208fa-736c-75e9-a336-a5cd6d3b0490`.
-/

namespace TranslatedOutputStrip

private theorem coprime_of_prime_not_dvd {q : ℕ} {x : ℤ}
    (hq : q.Prime) (hx : ¬ (q : ℤ) ∣ x) : IsCoprime (q : ℤ) x := by
  apply Int.isCoprime_iff_nat_coprime.mpr
  simpa only [Int.natAbs_natCast, hq.coprime_iff_not_dvd, ← Int.natCast_dvd_natCast,
    Int.dvd_natAbs] using hx

private theorem row_sub {q x₁ x₂ : ℤ} {p u : ℤ × ℤ} {tₚ tᵤ : ℤ}
    (hp : x₁ * p.2 - x₂ * p.1 = q * tₚ) (hu : x₁ * u.2 - x₂ * u.1 = q * tᵤ) :
    x₁ * (u.2 - p.2) - x₂ * (u.1 - p.1) = q * (tᵤ - tₚ) := by
  linear_combination hu - hp

/-- The determinant of two strip-coordinate differences is a multiple of `e*x₁`.
The algebra applies to the source's positive `e` without needing its positivity. -/
public theorem dvd_stripDet {q : ℕ} {x₁ x₂ e : ℤ} {S : Set (ℤ × ℤ)} {T : ℤ × ℤ → ℤ}
    (hq : q.Prime) (hqx : ¬ (q : ℤ) ∣ x₁ * x₂)
    (hrow : ∀ p ∈ S, x₁ * p.2 - x₂ * p.1 = (q : ℤ) * T p)
    (hdiv : ∀ p ∈ S, e ∣ p.1) {p u v : ℤ × ℤ} (hp : p ∈ S) (hu : u ∈ S) (hv : v ∈ S) :
    e * x₁ ∣ (u.1 - p.1) * (T v - T p) - (v.1 - p.1) * (T u - T p) := by
  have hcop := coprime_of_prime_not_dvd hq (fun h => hqx (h.mul_right x₂))
  obtain ⟨a, ha⟩ := dvd_sub (hdiv u hu) (hdiv p hp)
  obtain ⟨b, hb⟩ := dvd_sub (hdiv v hv) (hdiv p hp)
  have hu' := row_sub (hrow p hp) (hrow u hu)
  have hv' := row_sub (hrow p hp) (hrow v hv)
  rw [ha] at hu'
  rw [hb] at hv'
  -- Cancel `q` only against `x₁`, after normalizing the first-coordinate differences.
  have hcross : (q : ℤ) * (a * (T v - T p) - b * (T u - T p)) =
      x₁ * (a * (v.2 - p.2) - b * (u.2 - p.2)) := by
    linear_combination b * hu' - a * hv'
  have hdvd : x₁ ∣ a * (T v - T p) - b * (T u - T p) :=
    hcop.symm.dvd_of_dvd_mul_left ⟨_, hcross⟩
  rw [ha, hb, mul_assoc, mul_assoc, ← mul_sub]
  exact mul_dvd_mul_left e hdvd

private theorem abs_cast_sub_le_of_center {a b : ℤ} {c H : ℝ}
    (ha : |(a : ℝ) - c| ≤ H) (hb : |(b : ℝ) - c| ≤ H) :
    |((a - b : ℤ) : ℝ)| ≤ 2 * H := by
  rw [Int.cast_sub, ← sub_sub_sub_cancel_right (a : ℝ) (b : ℝ) c]
  exact (abs_sub _ _).trans (by simpa only [two_mul] using add_le_add ha hb)

private theorem eq_zero_of_dvd_of_abs_cast_lt {m z : ℤ}
    (hdvd : m ∣ z) (hsmall : |(z : ℝ)| < (m : ℝ)) : z = 0 := by
  apply Int.eq_zero_of_abs_lt_dvd hdvd
  rwa [← Int.cast_abs, Int.cast_lt] at hsmall

/-- If `8LW < e*x₁`, every triple in the translated rectangle has determinant zero
in strip coordinates. The centres are arbitrary real numbers. -/
public theorem stripDet_eq_zero {q : ℕ} {x₁ x₂ e : ℤ} {S : Set (ℤ × ℤ)} {T : ℤ × ℤ → ℤ}
    {c d L W : ℝ} (hq : q.Prime) (hqx : ¬ (q : ℤ) ∣ x₁ * x₂)
    (hrow : ∀ p ∈ S, x₁ * p.2 - x₂ * p.1 = (q : ℤ) * T p)
    (hdiv : ∀ p ∈ S, e ∣ p.1)
    (hbox : ∀ p ∈ S, |(p.1 : ℝ) - c| ≤ L ∧ |(T p : ℝ) - d| ≤ W)
    (hsmall : 8 * L * W < ((e * x₁ : ℤ) : ℝ))
    {p u v : ℤ × ℤ} (hp : p ∈ S) (hu : u ∈ S) (hv : v ∈ S) :
    (u.1 - p.1) * (T v - T p) - (v.1 - p.1) * (T u - T p) = 0 := by
  apply eq_zero_of_dvd_of_abs_cast_lt (dvd_stripDet hq hqx hrow hdiv hp hu hv)
  have hL : 0 ≤ L := (abs_nonneg _).trans (hbox p hp).1
  have hprod {u v : ℤ × ℤ} (hu : u ∈ S) (hv : v ∈ S) :
      |((u.1 : ℝ) - p.1) * ((T v : ℝ) - T p)| ≤ 2 * L * (2 * W) := by
    rw [abs_mul]
    have h₁ := abs_cast_sub_le_of_center (hbox u hu).1 (hbox p hp).1
    have hT := abs_cast_sub_le_of_center (hbox v hv).2 (hbox p hp).2
    simp only [Int.cast_sub] at h₁ hT
    exact mul_le_mul h₁ hT (abs_nonneg _) (mul_nonneg zero_le_two hL)
  simp only [Int.cast_mul] at hsmall
  simp only [Int.cast_sub, Int.cast_mul]
  calc
    _ ≤ _ := abs_sub _ _
    _ ≤ 2 * L * (2 * W) + 2 * L * (2 * W) := add_le_add (hprod hu hv) (hprod hv hu)
    _ = 8 * L * W := by ring
    _ < _ := hsmall

/-- The entire selected set in strip coordinates lies on an affine line (with
empty and singleton sets allowed) when `8LW < e*x₁`. -/
public theorem translatedRectangle_collinear {q : ℕ} {x₁ x₂ e : ℤ} {S : Set (ℤ × ℤ)}
    {T : ℤ × ℤ → ℤ} {c d L W : ℝ} (hq : q.Prime) (hqx : ¬ (q : ℤ) ∣ x₁ * x₂)
    (hrow : ∀ p ∈ S, x₁ * p.2 - x₂ * p.1 = (q : ℤ) * T p)
    (hdiv : ∀ p ∈ S, e ∣ p.1)
    (hbox : ∀ p ∈ S, |(p.1 : ℝ) - c| ≤ L ∧ |(T p : ℝ) - d| ≤ W)
    (hsmall : 8 * L * W < ((e * x₁ : ℤ) : ℝ)) :
    Collinear ℝ ((fun p ↦ ((p.1 : ℝ), (T p : ℝ))) '' S) := by
  rcases S.eq_empty_or_nonempty with rfl | ⟨p, hp⟩
  · simpa only [Set.image_empty] using collinear_empty ℝ (ℝ × ℝ)
  apply (collinear_iff_exists_forall_eq_smul_vadd _).mpr
  refine ⟨((p.1 : ℝ), (T p : ℝ)), ?_⟩
  by_cases h : ∃ u ∈ S, u.1 ≠ p.1
  · obtain ⟨u, hu, hu₁⟩ := h
    let a : ℝ := (u.1 : ℝ) - p.1
    let b : ℝ := (T u : ℝ) - T p
    have ha : a ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hu₁)
    refine ⟨(a, b), ?_⟩
    rintro _ ⟨v, hv, rfl⟩
    have hdet := congrArg (Int.cast : ℤ → ℝ) (stripDet_eq_zero hq hqx hrow hdiv hbox hsmall hp hu hv)
    simp only [Int.cast_sub, Int.cast_mul, Int.cast_zero] at hdet
    have hab : a * ((T v : ℝ) - T p) = ((v.1 : ℝ) - p.1) * b := sub_eq_zero.mp hdet
    refine ⟨((v.1 : ℝ) - p.1) / a, Prod.ext ?_ ?_⟩
    · change (v.1 : ℝ) = _ / a * a + (p.1 : ℝ)
      rw [div_mul_cancel₀ _ ha, sub_add_cancel]
    · change (T v : ℝ) = _ / a * b + (T p : ℝ)
      rw [div_mul_eq_mul_div, ← hab, mul_comm a, mul_div_cancel_right₀ _ ha, sub_add_cancel]
  · refine ⟨(0, 1), ?_⟩
    rintro _ ⟨v, hv, rfl⟩
    have hv₁ : v.1 = p.1 := not_ne_iff.mp (fun hne => h ⟨v, hv, hne⟩)
    refine ⟨(T v : ℝ) - T p, Prod.ext ?_ ?_⟩
    · change (v.1 : ℝ) = ((T v : ℝ) - T p) * 0 + (p.1 : ℝ)
      simp [hv₁]
    · change (T v : ℝ) = ((T v : ℝ) - T p) * 1 + (T p : ℝ)
      simp

/-- Under `2W < min xᵢ`, distinct points differ in both original coordinates.
The quotient `T` may agree; no restriction on the horizontal interval or on `e`
is needed for this step. -/
public theorem originalCoords_ne {q : ℕ} {x₁ x₂ : ℤ} {S : Set (ℤ × ℤ)}
    {T : ℤ × ℤ → ℤ} {d W : ℝ} (hq : q.Prime) (hqx : ¬ (q : ℤ) ∣ x₁ * x₂)
    (hrow : ∀ p ∈ S, x₁ * p.2 - x₂ * p.1 = (q : ℤ) * T p)
    (hstrip : ∀ p ∈ S, |(T p : ℝ) - d| ≤ W) (hsmall : 2 * W < min (x₁ : ℝ) (x₂ : ℝ))
    {p u : ℤ × ℤ} (hp : p ∈ S) (hu : u ∈ S) (hpu : p ≠ u) : p.1 ≠ u.1 ∧ p.2 ≠ u.2 := by
  have hx₁ : ¬ (q : ℤ) ∣ x₁ := fun h => hqx (h.mul_right x₂)
  have hx₂ : ¬ (q : ℤ) ∣ x₂ := fun h => hqx (h.mul_left x₁)
  have hdiff := row_sub (hrow p hp) (hrow u hu)
  have hT := abs_cast_sub_le_of_center (hstrip u hu) (hstrip p hp)
  have hzero {x : ℤ} (hx : ¬ (q : ℤ) ∣ x) (hWx : 2 * W < (x : ℝ))
      (hdvd : x ∣ (q : ℤ) * (T u - T p)) : T u - T p = 0 :=
    eq_zero_of_dvd_of_abs_cast_lt ((coprime_of_prime_not_dvd hq hx).symm.dvd_of_dvd_mul_left hdvd)
      (hT.trans_lt hWx)
  constructor
  · intro hz₁
    have hdvd : x₁ ∣ (q : ℤ) * (T u - T p) := by
      rw [← hdiff, hz₁, sub_self, mul_zero, sub_zero]
      exact dvd_mul_right _ _
    have hΔT := hzero hx₁ (hsmall.trans_le (min_le_left _ _)) hdvd
    have hx₁ne : x₁ ≠ 0 := fun h => hx₁ (h ▸ dvd_zero _)
    have hz₂ : u.2 = p.2 := by
      simpa [hz₁, hΔT, hx₁ne, sub_eq_zero] using hdiff
    exact hpu (Prod.ext hz₁ hz₂.symm)
  · intro hz₂
    have hdvd : x₂ ∣ (q : ℤ) * (T u - T p) := by
      rw [← hdiff, hz₂, sub_self, mul_zero, zero_sub, dvd_neg]
      exact dvd_mul_right _ _
    have hΔT := hzero hx₂ (hsmall.trans_le (min_le_right _ _)) hdvd
    have hx₂ne : x₂ ≠ 0 := fun h => hx₂ (h ▸ dvd_zero _)
    have hz₁ : u.1 = p.1 := by
      simpa [hz₂, hΔT, hx₂ne, sub_eq_zero] using hdiff
    exact hpu (Prod.ext hz₁.symm hz₂)

end TranslatedOutputStrip
