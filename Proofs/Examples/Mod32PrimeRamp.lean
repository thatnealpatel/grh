module

public import Lemmas.LogRampAbel
public import Lemmas.IntegralRampAverage
public import Lemmas.OddPrimeTheta
import all Lemmas.OddPrimeTheta
import Mathlib.Tactic

/-!
# One column of the mod-32 square race

Square bucket 9 counts base primes in classes 3, 13, 19, and 29. This
example applies Mathlib’s progression PNT in exactly those four classes. It does not infer prime equidistribution from a residue table.
-/

open Filter MeasureTheory Finset Real
open scoped Topology

namespace PrimeSquareRamp

private noncomputable def classWeight (r n : ℕ) : ℝ :=
  if n % 32 = r then oddWeight n else 0

private noncomputable def bucket9 (n : ℕ) : ℝ :=
  if n ^ 2 % 32 = 9 then oddWeight n else 0

private theorem split9 (n : ℕ) : bucket9 n =
    classWeight 3 n + classWeight 13 n + classWeight 19 n + classWeight 29 n := by
  have hs : ∀ r : Fin 32, (r.val ^ 2 % 32 = 9 ↔
      r.val = 3 ∨ r.val = 13 ∨ r.val = 19 ∨ r.val = 29) := by decide
  have hr := hs ⟨n % 32, Nat.mod_lt _ (by decide)⟩
  rw [← Nat.pow_mod] at hr
  simp only [bucket9, classWeight, hr]
  split_ifs <;> simp_all

private def HasClassPNT (r : ℕ) : Prop := Tendsto
  (fun t : ℝ => (∑ n ∈ Icc 0 ⌊t⌋₊, classWeight r n) / t) atTop (𝓝 (1 / 16))

private theorem classPNT (r : ℕ) (hr : r < 32) (hc : r.Coprime 32) (h2 : r ≠ 2) :
    HasClassPNT r := by
  have h := Chebyshev.tendsto_sum_log_prime_modEq_div_atTop hc
  rw [show Nat.totient 32 = 16 by decide] at h
  unfold HasClassPNT
  apply (show Tendsto _ _ (𝓝 (1 / 16 : ℝ)) from by simpa using h).congr'
  filter_upwards with t
  congr 1
  rw [Finset.sum_filter, ← add_sum_Ioc_eq_sum_Icc] <;> try exact Nat.zero_le _
  simp only [classWeight, oddWeight, Nat.ModEq, Nat.mod_eq_of_lt hr]
  simp only [Nat.not_prime_zero, false_and, ite_false, ite_self, zero_add]
  apply sum_congr rfl
  intro n _
  by_cases hn : n = 2
  · subst n
    simp [Ne.symm h2]
  · split_ifs <;> simp_all

/-- In the `X = Y²` normalization used by the computation, the column
is `2 * logRamp bucket9 Y`. Each input class supplies `1/16` before
that factor of two. The same calculation works for the other fibers. -/
example :
    Tendsto (fun Y : ℝ => 2 * logRamp bucket9 Y / Y) atTop (𝓝 (1 / 2)) := by
  have h3 := classPNT 3 (by decide) (by decide) (by decide)
  have h13 := classPNT 13 (by decide) (by decide) (by decide)
  have h19 := classPNT 19 (by decide) (by decide) (by decide)
  have h29 := classPNT 29 (by decide) (by decide) (by decide)
  have hs : Tendsto (fun t : ℝ => (∑ n ∈ Icc 0 ⌊t⌋₊, bucket9 n) / t)
      atTop (𝓝 (1 / 4)) := by
    convert ((h3.add h13).add h19).add h29 using 1 <;>
      simp [split9, Finset.sum_add_distrib, add_div]
    norm_num
  have hav := tendsto_integral_average (fun _ hY => partialSum_div_intervalIntegrable bucket9 hY) hs
  have h := hav.const_mul (2 : ℝ)
  norm_num at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with Y hY
  rw [logRamp_eq_integral bucket9 (by simp [bucket9]) (by simp [bucket9]) hY, mul_div_assoc]

end PrimeSquareRamp
