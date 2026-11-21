module

public import Lemmas.RationalIntegralAdeles
import Theorems.RationalAdeleDenominators
import Mathlib.Tactic.FieldSimp

/-! # Residues of rational adeles with a fixed finite denominator -/

open NumberField

namespace Masullo

local notation "A" => AdeleRing (𝓞 ℚ) ℚ
local notation "W" => rationalIntegralAdeles
local notation "ι" => algebraMap ℚ A

private theorem nat_mul_mem (N : ℕ) {z : A} (hz : z ∈ W) : ι (N : ℚ) * z ∈ W := by
  simpa only [map_natCast, nsmul_eq_mul] using rationalIntegralAdeles.nsmul_mem hz N

public theorem rationalAdele_residue_exists {N : ℕ} (hN : 0 < N) (z : A) (hz : ι (N : ℚ) * z ∈ W) :
    ∃ j : Fin N, z - ι ((j.val : ℚ) / N) ∈ W := by
  obtain ⟨q, hq⟩ := exists_rational_sub_mem_integral z
  have hd : ι (N : ℚ) * (z - ι q) ∈ W := nat_mul_mem N hq
  have hqN := rationalIntegralAdeles.sub_mem hz hd
  rw [mul_sub, sub_sub_cancel, ← map_mul] at hqN
  obtain ⟨n, hn⟩ := (algebraMap_mem_rationalIntegralAdeles_iff _).mp hqN
  have hN' : (0 : ℤ) < N := by exact_mod_cast hN
  let r := n % (N : ℤ)
  have hr : 0 ≤ r := Int.emod_nonneg _ hN'.ne'
  have hval : (r.toNat : ℤ) = r := Int.toNat_of_nonneg hr
  let j : Fin N := ⟨r.toNat, by
    have hlt : r < (N : ℤ) := Int.emod_lt_of_pos _ hN'
    exact_mod_cast (hval.symm ▸ hlt)⟩
  refine ⟨j, ?_⟩
  have hcast : (j.val : ℚ) = (r : ℚ) := by exact_mod_cast hval
  have hdecomp : (r : ℚ) + (N : ℚ) * ((n / (N : ℤ) : ℤ) : ℚ) = (n : ℚ) := by
    exact_mod_cast Int.emod_add_mul_ediv n (N : ℤ)
  have hNq : (N : ℚ) ≠ 0 := by exact_mod_cast hN.ne'
  have hshift : q - (j.val : ℚ) / N = ((n / (N : ℤ) : ℤ) : ℚ) := by
    rw [hcast]
    calc
      q - (r : ℚ) / N = ((N : ℚ) * q - r) / N := by field_simp
      _ = ((n : ℚ) - r) / N := by rw [hn]
      _ = _ := (div_eq_iff hNq).2 (by linarith)
  have hsum := rationalIntegralAdeles.add_mem hq (intCast_mem_rationalIntegralAdeles (n / (N : ℤ)))
  rwa [← map_intCast ι, ← hshift, map_sub, sub_add_sub_cancel] at hsum

public theorem rationalAdele_residue_unique (N : ℕ) (z : A) {j k : Fin N}
    (hj : z - ι ((j.val : ℚ) / N) ∈ W) (hk : z - ι ((k.val : ℚ) / N) ∈ W) : j = k := by
  have h := rationalIntegralAdeles.sub_mem hk hj
  rw [sub_sub_sub_cancel_left, ← map_sub, ← sub_div] at h
  obtain ⟨n, hn⟩ := (algebraMap_mem_rationalIntegralAdeles_iff _).mp h
  have hN : (N : ℚ) ≠ 0 := by exact_mod_cast (Nat.zero_lt_of_lt j.isLt).ne'
  have hd : (j.val : ℤ) - (k.val : ℤ) = (N : ℤ) * n := by
    have hd' := (div_eq_iff hN).mp hn
    rw [mul_comm] at hd'
    exact_mod_cast hd'
  have hmod : ((j.val : ℤ) - (k.val : ℤ)) % (N : ℤ) = 0 := by rw [hd]; simp
  have hj' : (j.val : ℤ) < N := by exact_mod_cast j.isLt
  have hk' : (k.val : ℤ) < N := by exact_mod_cast k.isLt
  have he := Int.emod_eq_emod_iff_emod_sub_eq_zero.mpr hmod
  rw [Int.emod_eq_of_lt (by positivity) hj', Int.emod_eq_of_lt (by positivity) hk'] at he
  exact Fin.ext (by exact_mod_cast he)

/-- A point in a residue class modulo integral finite adeles has denominator
dividing `N` at all finite places. -/
public theorem rationalAdele_residue_mem {N : ℕ} (z : A) {j : Fin N}
    (hj : z - ι ((j.val : ℚ) / N) ∈ W) : ι (N : ℚ) * z ∈ W := by
  have hn : (N : ℚ) ≠ 0 := by exact_mod_cast (Nat.zero_lt_of_lt j.isLt).ne'
  have hc := nat_mul_mem N hj
  rw [mul_sub, ← map_mul, mul_comm (N : ℚ), div_mul_cancel₀ _ hn] at hc
  have hd : (j.val : A) ∈ W := by exact_mod_cast intCast_mem_rationalIntegralAdeles (j.val : ℤ)
  simpa only [map_natCast, sub_add_cancel] using rationalIntegralAdeles.add_mem hc hd

end Masullo
