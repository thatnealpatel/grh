module

public import Mathlib.Data.Nat.Prime.Int
public import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Order.Group.Unbundled.Int
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination

/-!
# Signed row recovery

Formalizes the standalone primitive-column uniqueness step of
`fd54047:.godel/alice/shared-row-labels.md` (lines 11–15), used in the recovery-product
count of `d15218c:.godel/alice/overlapping-lift-count.md` (lines 54–56). It does not
formalize the product-splitting or asymptotic fiber counts.

The cutoffs `H` and `Z` are real: the signed gaps are measured after casting to `ℝ`,
and the bounds on `d` and `d'` require no rounding. In the source at `g = 1`,
`Z = (1/2) √(N/H) B⁻²ᵏ` gives `4 H Z² = N B⁻⁴ᵏ`, so the lower row cutoff
`A₋ = N B⁻⁴ᵏ / Z` is precisely `4 H Z`.

Owning check session: `01a208be-3e66-7cc4-8f5d-223682424036`.
-/

namespace SignedRowRecovery

/-- For a fixed positive row, two positive primitive columns with bounded signed
integer gaps and denominators are equal if `q` is prime, `q ∤ x`, and `4 * H * Z ≤ x`.
The gaps may be of either sign or zero. -/
public theorem primitiveColumn_eq_of_signed_gaps
    {q x y c d c' d' : ℕ} {δ δ' : ℤ} {H Z : ℝ}
    (hq : q.Prime) (hqx : ¬ q ∣ x)
    (hx : 0 < x) (_hy : 0 < y)
    (_hc : 0 < c) (hd : 0 < d) (_hc' : 0 < c') (_hd' : 0 < d')
    (hcd : c.Coprime d) (hcd' : c'.Coprime d')
    (hdZ : (d : ℝ) ≤ Z) (hd'Z : (d' : ℝ) ≤ Z)
    (hgap : (c : ℤ) * x - (d : ℤ) * y = (q : ℤ) * δ)
    (hgap' : (c' : ℤ) * x - (d' : ℤ) * y = (q : ℤ) * δ')
    (hδ : |(δ : ℝ)| ≤ H) (hδ' : |(δ' : ℝ)| ≤ H)
    (hcutoff : 4 * H * Z ≤ (x : ℝ)) : c = c' ∧ d = d' := by
  let D : ℤ := (c : ℤ) * d' - (c' : ℤ) * d
  have hdet : (x : ℤ) * D = (q : ℤ) * (δ * d' - δ' * d) := by
    dsimp only [D]
    linear_combination (d' : ℤ) * hgap - (d : ℤ) * hgap'
  have hqD : (q : ℤ) ∣ D := by
    have hprod : (q : ℤ) ∣ (x : ℤ) * D := ⟨_, hdet⟩
    exact ((Nat.prime_iff_prime_int.mp hq).dvd_or_dvd hprod).resolve_left
      (fun h => hqx (Int.natCast_dvd_natCast.mp h))
  obtain ⟨k, hk⟩ := hqD
  have hmul : (x : ℤ) * k = δ * d' - δ' * d := by
    apply mul_left_cancel₀ (show (q : ℤ) ≠ 0 by exact_mod_cast hq.ne_zero)
    calc
      _ = (x : ℤ) * D := by rw [hk, mul_left_comm]
      _ = _ := hdet
  have hmulR : (x : ℝ) * (k : ℝ) = (δ : ℝ) * d' - (δ' : ℝ) * d := by
    exact_mod_cast hmul
  have hH : 0 ≤ H := (abs_nonneg _).trans hδ
  have hxR : (0 : ℝ) < x := by exact_mod_cast hx
  have hsmall : 2 * H * Z < (x : ℝ) := by linarith only [hcutoff, hxR]
  have hbound : |(x : ℝ) * (k : ℝ)| ≤ 2 * H * Z := by
    rw [hmulR]
    calc
      _ ≤ |(δ : ℝ) * (d' : ℝ)| + |(δ' : ℝ) * (d : ℝ)| := abs_sub _ _
      _ = |(δ : ℝ)| * (d' : ℝ) + |(δ' : ℝ)| * (d : ℝ) := by
        simp only [abs_mul, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) d'),
          abs_of_nonneg (Nat.cast_nonneg (α := ℝ) d)]
      _ ≤ H * Z + H * Z := add_le_add
        (mul_le_mul hδ hd'Z (Nat.cast_nonneg _) hH)
        (mul_le_mul hδ' hdZ (Nat.cast_nonneg _) hH)
      _ = _ := by rw [← two_mul, mul_assoc]
  have hk0 : k = 0 := by
    by_contra h
    have hkle : (1 : ℝ) ≤ |(k : ℝ)| := by exact_mod_cast Int.one_le_abs h
    have hxle : (x : ℝ) ≤ (x : ℝ) * |(k : ℝ)| := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hkle hxR.le
    rw [abs_mul, abs_of_nonneg hxR.le] at hbound
    exact (not_lt_of_ge (hxle.trans hbound)) hsmall
  have hcross : c * d' = c' * d := by
    have hD0 : D = 0 := by rw [hk, hk0, mul_zero]
    have hcrossInt : (c : ℤ) * d' = (c' : ℤ) * d := sub_eq_zero.mp hD0
    exact_mod_cast hcrossInt
  have hdvd : d ∣ d' := hcd.symm.dvd_of_dvd_mul_left (by
    rw [hcross]
    exact dvd_mul_left d c')
  have hdvd' : d' ∣ d := hcd'.symm.dvd_of_dvd_mul_left (by
    rw [← hcross]
    exact dvd_mul_left d' c)
  have hdd' : d = d' := Nat.dvd_antisymm hdvd hdvd'
  exact ⟨Nat.eq_of_mul_eq_mul_right hd (by simpa only [← hdd'] using hcross), hdd'⟩

end SignedRowRecovery
