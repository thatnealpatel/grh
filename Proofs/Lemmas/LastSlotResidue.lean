module

public import Mathlib.Algebra.BigOperators.ModEq
public import Mathlib.Algebra.Order.Round
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.GCD.BigOperators
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Last-slot residue decoding

Source: `ec81e8cb:.godel/bob/last-slot-residues.md:17–32`, with the center
and endpoint domain from lines 3–5. Omit one positive slot of a signed tuple
at a fixed positive integer shift `d`. Each remaining pair contributes `q + d`
and `q` in one order or the other, so the **unreduced** products `U` and `W`
are congruent modulo `d`. The endpoints are units in the source range for
large `X`: they are primes at least `exp (-8) * X > 5 * log X ≥ d`.
Cancellation after fraction reduction requires this unit property, not just
the aggregate congruence.

The decoder concerns an original positive-slot completion in `|t * ν| ≤ 8`.
It uses only the product congruence, units, a positive reduced fraction, and
the displayed exponential relation and size bounds. It does not formalize
the gate, a uniform residue substitution, or a probability identity.

Owning check session: `01a208d1-f4a1-7e74-9d68-6b0dfb6d9df9`.
-/

open scoped BigOperators

namespace LastSlotResidue

/-- Aggregate congruence and units for the remaining labeled pairs. Reversing
numerator and denominator at a negative label leaves its congruence intact. -/
public theorem remaining_products_modEq_and_coprime {ι : Type*} (s : Finset ι)
    (q : ι → ℕ) (positive : ι → Bool) (d : ℕ)
    (hunit : ∀ i ∈ s, (q i).Coprime d) :
    let U := ∏ i ∈ s, if positive i then q i + d else q i
    let W := ∏ i ∈ s, if positive i then q i else q i + d
    Nat.ModEq d U W ∧ U.Coprime d ∧ W.Coprime d := by
  have hshift (i : ι) : Nat.ModEq d (q i + d) (q i) := by simp [Nat.ModEq]
  have hshiftUnit (i : ι) (hi : i ∈ s) : (q i + d).Coprime d :=
    Nat.coprime_add_self_left.mpr (hunit i hi)
  refine ⟨Nat.ModEq.prod (fun i _ ↦ ?_), Nat.Coprime.prod_left (fun i hi ↦ ?_),
    Nat.Coprime.prod_left (fun i hi ↦ ?_)⟩
  · split <;> first | exact hshift i | exact (hshift i).symm
  · split <;> first | exact hunit i hi | exact hshiftUnit i hi
  · split <;> first | exact hunit i hi | exact hshiftUnit i hi

/-- Cancel the common factor of the two products from their congruence.
Only one aggregate unit hypothesis is needed for this cancellation. -/
public theorem reduced_modEq {U W M N g d : ℕ}
    (hUM : U = g * M) (hWN : W = g * N)
    (hmod : Nat.ModEq d U W) (hunit : U.Coprime d) : Nat.ModEq d M N := by
  have hg : g.Coprime d := Nat.Coprime.coprime_dvd_left ⟨M, hUM⟩ hunit
  exact Nat.ModEq.cancel_left_of_coprime hg.symm (hUM ▸ hWN ▸ hmod)

/-- A concrete sufficient cutoff for the uniform bound, at the source scale
`X = (3 * log (t / 2))²` (in particular at sufficiently large genuine centers). -/
public theorem height_bound_at_center_scale {t : ℝ}
    (ht : 2 * Real.exp 311040 ≤ t) : 64 * ((3 * Real.log (t / 2)) ^ 2) ^ 2 ≤ t := by
  let z := Real.log (t / 2)
  have ht' : Real.exp 311040 ≤ t / 2 := by linarith only [ht]
  have ht0 : 0 < t / 2 := (Real.exp_pos _).trans_le ht'
  have hz : 311040 ≤ z := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos (311040 : ℝ)) ht'
  have hz0 : 0 ≤ z := by linarith only [hz]
  have hlarge : 311040 * z ^ 4 ≤ z ^ 5 := by
    calc
      _ ≤ z * z ^ 4 := mul_le_mul_of_nonneg_right hz (pow_nonneg hz0 _)
      _ = _ := by ring
  have he : Real.exp z = t / 2 := Real.exp_log ht0
  have hexp : z ^ 5 / 120 ≤ t / 2 := by
    simpa [he, Nat.factorial] using Real.pow_div_factorial_le_exp z hz0 5
  change 64 * ((3 * z) ^ 2) ^ 2 ≤ t
  nlinarith only [hlarge, hexp]

/-- Exact reduced-fraction arithmetic and unique nearest-integer decoding of
an omitted positive start. The quotient in `k` is natural, the defect `ℓ` is
signed, and division in the decoding error and the identity for `V` is real. -/
public theorem decode {U W M N d p : ℕ} {t ν X : ℝ}
    (hfactor : ∃ g : ℕ, 0 < g ∧ U = g * M ∧ W = g * N)
    (hmod : Nat.ModEq d U W) (hunits : U.Coprime d ∧ W.Coprime d)
    (hreduced : M.Coprime N) (hpos : 0 < M ∧ 0 < N)
    (hd : 0 < d) (hp : 0 < p) (hpX : (p : ℝ) ≤ X) (hpdX : (p : ℝ) + d ≤ X)
    (ht : 64 * X ^ 2 ≤ t) (hν : |t * ν| ≤ 8)
    (hexp : Real.exp ν = (M : ℝ) * (p + d) / (N * p)) :
    let k : ℕ := (N - M) / d
    let ℓ : ℤ := (M : ℤ) - (k : ℤ) * p
    let V : ℝ := (N : ℝ) * p / (t * d)
    let δ : ℝ := Real.exp ν - 1
    M < N ∧ d ∣ (N - M) ∧ 0 < k ∧
      (M : ℝ) / k = (d : ℝ) * M / ((N : ℝ) - M) ∧
      (M : ℝ) / k - p = (p : ℝ) * (p + d) * δ / (d - p * δ) ∧
      |(M : ℝ) / k - p| < 1 / 2 ∧ round ((M : ℝ) / k) = (p : ℤ) ∧
      ℓ.gcd (k : ℤ) = 1 ∧ 0 < V ∧
      1 + (ℓ : ℝ) / (t * V) = (M : ℝ) * (p + d) / (N * p) := by
  intro k ℓ V δ
  obtain ⟨g, _, hUM, hWN⟩ := hfactor
  have hredMod := reduced_modEq hUM hWN hmod hunits.1
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hNR : (0 : ℝ) < N := by exact_mod_cast hpos.2
  have hpdR : 0 < (p : ℝ) + d := add_pos hpR hdR
  have hX : 1 ≤ X := (show (1 : ℝ) ≤ p by exact_mod_cast hp).trans hpX
  have hXR : 0 < X := by linarith only [hX]
  have hXsq : X ≤ X ^ 2 := by nlinarith only [mul_nonneg (sub_nonneg.mpr hX) hXR.le]
  have htR : 0 < t := (mul_pos (by norm_num) (pow_pos hXR _)).trans_le ht
  have hνt : t * |ν| ≤ 8 := by simpa only [abs_mul, abs_of_pos htR] using hν
  have hνX : 64 * X ^ 2 * |ν| ≤ 8 :=
    (mul_le_mul_of_nonneg_right ht (abs_nonneg ν)).trans hνt
  have hνsmall : |ν| ≤ 1 := by
    have h64 : (64 : ℝ) ≤ 64 * X ^ 2 := by
      simpa only [mul_one] using
        mul_le_mul_of_nonneg_left (hX.trans hXsq) (show (0 : ℝ) ≤ 64 by norm_num)
    linarith only [(mul_le_mul_of_nonneg_right h64 (abs_nonneg ν)).trans hνX]
  have hδX : X ^ 2 * |δ| ≤ 1 / 4 := by
    have h := mul_le_mul_of_nonneg_left (Real.abs_exp_sub_one_le hνsmall) (sq_nonneg X)
    change X ^ 2 * |δ| ≤ X ^ 2 * (2 * |ν|) at h
    nlinarith only [h, hνX]
  have hpδ : (p : ℝ) * δ ≤ 1 / 4 := calc
    _ ≤ (p : ℝ) * |δ| := mul_le_mul_of_nonneg_left (le_abs_self δ) hpR.le
    _ ≤ X ^ 2 * |δ| := mul_le_mul_of_nonneg_right (hpX.trans hXsq) (abs_nonneg δ)
    _ ≤ _ := hδX
  have hpp : (p : ℝ) * (p + d) ≤ X ^ 2 := by
    simpa only [pow_two] using mul_le_mul hpX hpdX hpdR.le hXR.le
  have hppδ : (p : ℝ) * (p + d) * |δ| ≤ 1 / 4 :=
    (mul_le_mul_of_nonneg_right hpp (abs_nonneg δ)).trans hδX
  have hden : 0 < (d : ℝ) - p * δ := by linarith only [hpδ, hd1]
  have hδeq : 1 + δ = Real.exp ν := by dsimp [δ]; ring
  have hcross : (N : ℝ) * p * (1 + δ) = (M : ℝ) * (p + d) := by
    rw [hδeq, mul_comm ((N : ℝ) * p)]
    exact (eq_div_iff (mul_pos hNR hpR).ne').mp hexp
  have hgap : ((N : ℝ) - M) * (p + d) = (N : ℝ) * (d - p * δ) := by
    linear_combination hcross
  have hMN : M < N := by
    have h : (0 : ℝ) < (N : ℝ) - M :=
      pos_of_mul_pos_left (hgap.symm ▸ mul_pos hNR hden) hpdR.le
    exact_mod_cast sub_pos.mp h
  have hdiv : d ∣ (N - M) := (Nat.modEq_iff_dvd' hMN.le).mp hredMod
  have hdk : d * k = N - M := Nat.mul_div_cancel' hdiv
  have hk : 0 < k := Nat.div_pos (Nat.le_of_dvd (Nat.sub_pos_of_lt hMN) hdiv) hd
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hNk : M + d * k = N := by rw [hdk, Nat.add_sub_of_le hMN.le]
  have hNkR : (M : ℝ) + d * k = N := by exact_mod_cast hNk
  have hdkR : (d : ℝ) * k = (N : ℝ) - M := by
    rw [← Nat.cast_sub hMN.le]
    exact_mod_cast hdk
  have hx : (M : ℝ) / k = (d : ℝ) * M / ((N : ℝ) - M) := by
    rw [← hdkR]
    field_simp [hdR.ne', hkR.ne']
  have herrorCross :
      ((M : ℝ) - k * p) * (d - p * δ) = k * ((p : ℝ) * (p + d) * δ) := by
    rw [← hNkR] at hcross
    linear_combination -hcross
  have herror : (M : ℝ) / k - p = (p : ℝ) * (p + d) * δ / (d - p * δ) := by
    field_simp [hkR.ne', hden.ne']
    linear_combination herrorCross
  have hnear : |(M : ℝ) / k - p| < 1 / 2 := by
    rw [herror, abs_div, abs_mul, abs_mul, abs_of_pos hpR, abs_of_pos hpdR, abs_of_pos hden]
    apply (div_lt_iff₀ hden).mpr
    linarith only [hppδ, hpδ, hd1]
  have hround : round ((M : ℝ) / k) = (p : ℤ) := by
    apply round_eq_iff.mpr
    rw [Int.cast_natCast, Set.mem_Ico]
    obtain ⟨hupper, hlower⟩ := abs_sub_lt_iff.mp hnear
    constructor <;> linarith only [hupper, hlower]
  -- A divisor common to `M` and `k` also divides `N = M + d*k`.
  have hMk : M.Coprime k := by
    have hM := Nat.gcd_dvd_left M k
    have hN : M.gcd k ∣ N := by
      rw [← hNk]
      exact Nat.dvd_add hM (dvd_mul_of_dvd_right (Nat.gcd_dvd_right M k) d)
    exact Nat.dvd_one.mp (hreduced ▸ Nat.dvd_gcd hM hN)
  have hℓ : ℓ.gcd (k : ℤ) = 1 := by
    rw [Int.gcd_comm, Int.gcd_sub_mul_left_right, Int.gcd_comm, Int.gcd_natCast_natCast]
    exact hMk
  have hV : 0 < V := div_pos (mul_pos hNR hpR) (mul_pos htR hdR)
  have htV : t * V = (N : ℝ) * p / d := by
    dsimp [V]
    field_simp [htR.ne', hdR.ne']
  have hℓR : (ℓ : ℝ) = (M : ℝ) - k * p := by simp [ℓ]
  have hratio : 1 + (ℓ : ℝ) / (t * V) = (M : ℝ) * (p + d) / (N * p) := by
    rw [htV, hℓR]
    field_simp [hNR.ne', hpR.ne', hdR.ne']
    linear_combination -(p : ℝ) * hNkR
  exact ⟨hMN, hdiv, hk, hx, herror, hnear, hround, hℓ, hV, hratio⟩

end LastSlotResidue
