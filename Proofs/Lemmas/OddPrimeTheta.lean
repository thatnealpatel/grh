module

public import Mathlib.NumberTheory.LSeries.WeakPNT

/-! # The Chebyshev sum over odd primes -/

open scoped BigOperators

namespace PrimeSquareRamp

/-- The logarithmic weight of an odd prime, and zero otherwise. -/
public noncomputable def oddWeight (n : ℕ) : ℝ := if n.Prime ∧ n ≠ 2 then Real.log n else 0

/-- The sum of the logarithms of the odd primes at most `t`. -/
public noncomputable def oddTheta (t : ℝ) : ℝ := ∑ n ∈ Finset.Icc 0 ⌊t⌋₊, oddWeight n

private theorem oddTheta_eq_theta_sub_log_two {t : ℝ} (ht : 2 ≤ t) :
    oddTheta t = Chebyshev.theta t - Real.log 2 := by
  have hfloor : 2 ≤ ⌊t⌋₊ := Nat.le_floor (by simpa only [Nat.cast_ofNat] using ht)
  let primes := (Finset.Icc 0 ⌊t⌋₊).filter Nat.Prime
  have htwo : 2 ∈ primes := Finset.mem_filter.mpr
    ⟨Finset.mem_Icc.mpr ⟨Nat.zero_le _, hfloor⟩, Nat.prime_two⟩
  have herase : primes.erase 2 = (Finset.Icc 0 ⌊t⌋₊).filter (fun n ↦ n.Prime ∧ n ≠ 2) := by
    ext n
    simp only [primes, Finset.mem_erase, Finset.mem_filter]
    exact and_rotate
  have hsum := Finset.sum_erase_add primes (fun n : ℕ ↦ Real.log n) htwo
  rw [herase, Finset.sum_filter, Nat.cast_ofNat] at hsum
  rw [Chebyshev.theta_eq_sum_Icc]
  exact eq_sub_of_add_eq hsum

/-- Removing the prime `2` does not change the prime number theorem in theta form. -/
public theorem tendsto_oddTheta_div :
    Filter.Tendsto (fun t : ℝ => oddTheta t / t) Filter.atTop (nhds 1) := by
  have hcorrection : Filter.Tendsto (fun t : ℝ ↦ Real.log 2 / t) Filter.atTop (nhds 0) :=
    Filter.tendsto_id.const_div_atTop (Real.log 2)
  have hlimit : Filter.Tendsto (fun t : ℝ ↦ Chebyshev.theta t / t - Real.log 2 / t)
      Filter.atTop (nhds 1) := by
    simpa only [sub_zero] using Chebyshev.tendsto_theta_div_atTop.sub hcorrection
  refine hlimit.congr' ?_
  filter_upwards [Filter.eventually_ge_atTop (2 : ℝ)] with t ht
  rw [oddTheta_eq_theta_sub_log_two ht, sub_div]

end PrimeSquareRamp
