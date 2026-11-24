module

public import Lemmas.MaskedGapDirections
public import Mathlib.Algebra.Module.LinearMap.Prod
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Masked gap collinearity in a common bracket bin

Source: `d673969:.godel/alice/masked-gap-bracket.md:19–33`, “Why the full credit is
available.” We count primitive signed vectors in one fixed mask group, with one modulus
and a common positive dyadic bin for the absolute value of the linear form. This is the
local direction count, not the enumeration of masks or the recovery of columns from vectors.
The reference vector need not satisfy the mask conditions.

Owning check session: `01a20d4e-3533-70d0-b28a-ab27fa9217cc`.
-/

namespace MaskedGapBracketBin

/-- The signed determinant with `x` and `y` as its columns. -/
@[expose] public def det (x y : ℤ × ℤ) : ℤ := x.1 * y.2 - y.1 * x.2

private theorem reference_det_identity (ℓ : (ℤ × ℤ) →ₗ[ℤ] ℤ) (x₀ x y : ℤ × ℤ) :
    ℓ x₀ * det x y = ℓ y * det x x₀ - ℓ x * det y x₀ := by
  have eval (z : ℤ × ℤ) : ℓ z = z.1 * ℓ (1, 0) + z.2 * ℓ (0, 1) := by
    have hz : z.1 • ((1, 0) : ℤ × ℤ) + z.2 • ((0, 1) : ℤ × ℤ) = z := by
      ext <;> simp
    calc
      ℓ z = ℓ (z.1 • (1, 0) + z.2 • (0, 1)) := congrArg ℓ hz.symm
      _ = _ := by simp only [map_add, map_smul, smul_eq_mul]
  rw [eval x₀, eval x, eval y]
  unfold det
  ring

/-- The two reference product tests in a common half-open bin give a strict
mutual determinant bound, without any sign restrictions on the linear form. -/
public theorem abs_det_lt_of_common_bin (ℓ : (ℤ × ℤ) →ₗ[ℤ] ℤ) {x₀ x y : ℤ × ℤ}
    {B₀ T C : ℝ} (hB₀ : 0 < B₀) (hT : 0 < T) (hC : 0 < C) (h₀ : ℓ x₀ ≠ 0)
    (hx : B₀ ≤ |(ℓ x : ℝ)| ∧ |(ℓ x : ℝ)| < 2 * B₀)
    (hy : B₀ ≤ |(ℓ y : ℝ)| ∧ |(ℓ y : ℝ)| < 2 * B₀)
    (hxprod : |(det x x₀ : ℝ)| * |(ℓ x : ℝ)| ≤ T * C * |(ℓ x₀ : ℝ)|)
    (hyprod : |(det y x₀ : ℝ)| * |(ℓ y : ℝ)| ≤ T * C * |(ℓ x₀ : ℝ)|) :
    |(det x y : ℝ)| < 4 * T * C := by
  let r : ℝ := |(ℓ x₀ : ℝ)|
  let K := T * C * r
  let D := K / B₀
  have hr : 0 < r := abs_pos.mpr (by exact_mod_cast h₀)
  have hD : 0 < D := div_pos (mul_pos (mul_pos hT hC) hr) hB₀
  have hdx : |(det x x₀ : ℝ)| ≤ D :=
    (le_div_iff₀ hB₀).mpr ((mul_le_mul_of_nonneg_left hx.1 (abs_nonneg _)).trans hxprod)
  have hdy : |(det y x₀ : ℝ)| ≤ D :=
    (le_div_iff₀ hB₀).mpr ((mul_le_mul_of_nonneg_left hy.1 (abs_nonneg _)).trans hyprod)
  have term_lt {u v : ℝ} (hu : |u| < 2 * B₀) (hv : |v| ≤ D) :
      |u| * |v| < (2 * B₀) * D :=
    (mul_le_mul_of_nonneg_left hv (abs_nonneg _)).trans_lt (mul_lt_mul_of_pos_right hu hD)
  have hid : (ℓ x₀ : ℝ) * (det x y : ℝ) =
      (ℓ y : ℝ) * (det x x₀ : ℝ) - (ℓ x : ℝ) * (det y x₀ : ℝ) := by
    exact_mod_cast reference_det_identity ℓ x₀ x y
  have hDB : D * B₀ = K := div_mul_cancel₀ K hB₀.ne'
  refine lt_of_mul_lt_mul_left ?_ hr.le
  calc
    r * |(det x y : ℝ)| = |(ℓ x₀ : ℝ) * (det x y : ℝ)| := (abs_mul _ _).symm
    _ ≤ |(ℓ y : ℝ)| * |(det x x₀ : ℝ)| + |(ℓ x : ℝ)| * |(det y x₀ : ℝ)| := by
      rw [hid]
      simpa only [abs_mul] using abs_sub ((ℓ y : ℝ) * (det x x₀ : ℝ))
        ((ℓ x : ℝ) * (det y x₀ : ℝ))
    _ < (2 * B₀) * D + (2 * B₀) * D := add_lt_add (term_lt hy.2 hdx) (term_lt hx.2 hdy)
    _ = 4 * (D * B₀) := by ring
    _ = r * (4 * T * C) := by rw [hDB]; dsimp only [K]; ring

private theorem dvd_det_of_congruences {a b N : ℤ} {x y : ℤ × ℤ} (hab : IsCoprime a b)
    (hx : a * x.1 - b * x.2 ≡ 0 [ZMOD N]) (hy : a * y.1 - b * y.2 ≡ 0 [ZMOD N]) :
    N ∣ det x y := by
  obtain ⟨p, hp⟩ := Int.modEq_zero_iff_dvd.mp hx
  obtain ⟨q, hq⟩ := Int.modEq_zero_iff_dvd.mp hy
  -- Eliminate one coordinate at a time, without cancelling either coefficient modulo `N`.
  have ha : a * det x y = N * (y.2 * p - x.2 * q) := by
    unfold det
    linear_combination y.2 * hp - x.2 * hq
  have hb : b * det x y = N * (y.1 * p - x.1 * q) := by
    unfold det
    linear_combination y.1 * hp - x.1 * hq
  obtain ⟨u, v, huv⟩ := hab
  refine ⟨u * (y.2 * p - x.2 * q) + v * (y.1 * p - x.1 * q), ?_⟩
  linear_combination u * ha + v * hb - det x y * huv

private theorem det_scaled (s t : ℤ) (z w : ℤ × ℤ) :
    det (s * z.1, t * z.2) (s * w.1, t * w.2) = s * t * det z w := by
  simp only [det]
  ring

/-- In one fixed mask group and one positive dyadic bin, the reference product
inequality forces the signed vectors to be collinear once `4T < f`. Primitivity
then gives at most two vectors. The single modulus `m_d * f * m_t` retains all
multiplicities even when its factors share primes. -/
public theorem det_eq_zero_and_card_le_two {S : Finset (ℤ × ℤ)}
    {a b L m₁ m₂ m_d m_t f : ℤ} {B₀ T : ℝ} (ℓ : (ℤ × ℤ) →ₗ[ℤ] ℤ) (x₀ : ℤ × ℤ)
    (hab : IsCoprime a b) (hL : 0 < L) (hm₁ : 0 < m₁) (hm₂ : 0 < m₂)
    (hm_d : 0 < m_d) (hm_t : 0 < m_t) (hB₀ : 0 < B₀) (hT : 1 ≤ T)
    (hf : 4 * T < (f : ℝ)) (h₀ : ℓ x₀ ≠ 0)
    (hprim : ∀ x ∈ S, IsCoprime x.1 x.2)
    (hcoords : ∀ x ∈ S, ∃ z : ℤ × ℤ, x = (m₁ * z.1, L * m₂ * z.2) ∧
      (a * z.1 - b * z.2 ≡ 0 [ZMOD m_d * f * m_t]))
    (hbin : ∀ x ∈ S, B₀ ≤ |(ℓ x : ℝ)| ∧ |(ℓ x : ℝ)| < 2 * B₀)
    (hprod : ∀ x ∈ S, |(det x x₀ : ℝ)| * |(ℓ x : ℝ)| ≤
      T * ((L * m₁ * m₂ * m_d * m_t : ℤ) : ℝ) * |(ℓ x₀ : ℝ)|) :
    (∀ x ∈ S, ∀ y ∈ S, det x y = 0) ∧ S.card ≤ 2 := by
  let C : ℤ := L * m₁ * m₂ * m_d * m_t
  have hC : 0 < C := mul_pos (mul_pos (mul_pos (mul_pos hL hm₁) hm₂) hm_d) hm_t
  have hCR : (0 : ℝ) < C := by exact_mod_cast hC
  have hTpos : 0 < T := zero_lt_one.trans_le hT
  have hcross : 4 * T * (C : ℝ) < ((C * f : ℤ) : ℝ) := by
    calc
      _ < (f : ℝ) * (C : ℝ) := mul_lt_mul_of_pos_right hf hCR
      _ = (C : ℝ) * (f : ℝ) := mul_comm _ _
      _ = _ := (Int.cast_mul C f).symm
  have hdet : ∀ x ∈ S, ∀ y ∈ S, det x y = 0 := by
    intro x hx y hy
    have hsmall : |(det x y : ℝ)| < ((C * f : ℤ) : ℝ) :=
      (abs_det_lt_of_common_bin ℓ hB₀ hTpos hCR h₀ (hbin x hx) (hbin y hy)
        (hprod x hx) (hprod y hy)).trans hcross
    obtain ⟨z, hxz, hz⟩ := hcoords x hx
    obtain ⟨w, hyw, hw⟩ := hcoords y hy
    obtain ⟨k, hk⟩ := dvd_det_of_congruences hab hz hw
    have hdvd : C * f ∣ det x y := by
      refine ⟨k, ?_⟩
      rw [hxz, hyw, det_scaled m₁ (L * m₂) z w, hk]
      dsimp only [C]
      ring
    have hCf := (abs_nonneg _).trans_lt hsmall
    apply Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hdvd
    exact_mod_cast (show ((det x y).natAbs : ℝ) < ((C * f).natAbs : ℝ) by
      simpa only [Nat.cast_natAbs, Int.cast_abs, abs_of_pos hCf] using hsmall)
  exact ⟨hdet, MaskedGapDirections.card_le_two_of_primitive_collinear hprim hdet⟩

end MaskedGapBracketBin
