module

public import Lemmas.TerminalTriangle
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import all Lemmas.TerminalTriangle
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! # Prime-only input for the twisted terminal prefix

The prime progression estimates are hypotheses. The contribution of higher
prime powers is bounded by the untwisted Chebyshev remainder. -/

open Filter Finset

namespace TerminalTriangle

/-- The Vinogradov–Korobov rate, with real exponents. -/
@[expose] public noncomputable def vkRate (u : ℝ) : ℝ :=
  (Real.log u) ^ (3 / 5 : ℝ) / (Real.log (Real.log u)) ^ (1 / 5 : ℝ)

/-- The sum of `log p` over primes `p ≤ u` congruent to `a` modulo `4`.
The inclusive cutoff uses the same natural floor as `D`. -/
@[expose] public noncomputable def primeThetaModFour (a : ℕ) (u : ℝ) : ℝ :=
  ∑ p ∈ Icc 1 ⌊u⌋₊ with p.Prime ∧ p % 4 = a, Real.log (p : ℝ)

private theorem chi4_real (n : ℕ) :
    ((ZMod.χ₄ (n : ZMod 4) : ℤ) : ℝ) =
      if n % 4 = 1 then 1 else if n % 4 = 3 then -1 else 0 := by
  rw [ZMod.χ₄_nat_eq_if_mod_four]
  split_ifs <;> first | omega | norm_num

private theorem primePart_eq (u : ℝ) :
    (∑ n ∈ Icc 1 ⌊u⌋₊ with n.Prime,
      ArithmeticFunction.vonMangoldt n * (ZMod.χ₄ (n : ZMod 4) : ℤ)) =
      primeThetaModFour 1 u - primeThetaModFour 3 u := by
  simp only [primeThetaModFour, sum_filter, ← sum_sub_distrib]
  apply sum_congr rfl
  intro n _
  by_cases hp : n.Prime
  · simp only [hp, ite_true, true_and, ArithmeticFunction.vonMangoldt_apply_prime hp, chi4_real]
    split_ifs <;> first | omega | ring
  · simp [hp]

/-- The absolute error in replacing `D` by the difference of the two prime
progression sums is bounded by the untwisted nonprime Chebyshev sum. -/
public theorem abs_D_sub_primeThetaModFour_le (u : ℝ) :
    |D u - (primeThetaModFour 1 u - primeThetaModFour 3 u)| ≤
      Chebyshev.psi u - Chebyshev.theta u := by
  have hI : Ioc 0 ⌊u⌋₊ = Icc 1 ⌊u⌋₊ := by
    ext n
    simp only [mem_Ioc, mem_Icc]
    omega
  rw [Chebyshev.psi_sub_theta_eq_sum_not_prime, hI, D,
    ← sum_filter_add_sum_filter_not _ Nat.Prime, primePart_eq, add_sub_cancel_left]
  refine (abs_sum_le_sum_abs ..).trans (sum_le_sum fun n _ ↦ ?_)
  rw [abs_mul, abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
  apply mul_le_of_le_one_right ArithmeticFunction.vonMangoldt_nonneg
  rw [chi4_real]
  split_ifs <;> norm_num

/-- Any fixed VK envelope eventually dominates the square-root remainder. -/
private theorem eventually_sqrt_le_vkEnvelope {c : ℝ} (hc : 0 < c) :
    ∀ᶠ u : ℝ in atTop, Real.sqrt u ≤ u * Real.exp (-c * vkRate u) := by
  have hpow := (tendsto_rpow_atTop (y := (2 / 5 : ℝ)) (by norm_num)).comp
    Real.tendsto_log_atTop
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1 : ℝ)),
    (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually
      (eventually_ge_atTop (1 : ℝ)),
    hpow.eventually (eventually_ge_atTop (2 * c))] with u hu hlog hloglog hlarge
  have hu_pos : 0 < u := zero_lt_one.trans_le hu
  have hlog_pos : 0 < Real.log u := zero_lt_one.trans_le hlog
  have hnum : 0 ≤ Real.log u ^ (3 / 5 : ℝ) := Real.rpow_nonneg hlog_pos.le _
  have hsplit : Real.log u ^ (3 / 5 : ℝ) * Real.log u ^ (2 / 5 : ℝ) = Real.log u := by
    rw [← Real.rpow_add hlog_pos]
    norm_num
  have hrate : vkRate u ≤ Real.log u ^ (3 / 5 : ℝ) := by
    exact div_le_self hnum (Real.one_le_rpow hloglog (by norm_num))
  change 2 * c ≤ Real.log u ^ (2 / 5 : ℝ) at hlarge
  have hhalf : c * vkRate u ≤ Real.log u / 2 := by
    nlinarith only [mul_le_mul_of_nonneg_left hrate hc.le,
      mul_le_mul_of_nonneg_left hlarge hnum, hsplit]
  calc
    Real.sqrt u = Real.exp (Real.log u * (1 / 2)) := by
      rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hu_pos]
    _ ≤ Real.exp (Real.log u + -c * vkRate u) := Real.exp_le_exp.mpr (by linarith)
    _ = u * Real.exp (-c * vkRate u) := by rw [Real.exp_add, Real.exp_log hu_pos]

/-- Prime-only weighted progression estimates imply the same eventual rate
for the twisted von Mangoldt prefix. The exponent constant can be kept unchanged. -/
public theorem eventually_abs_D_le_of_primeThetaModFour {C c : ℝ} (hC : 0 < C) (hc : 0 < c)
    (hprime : ∀ᶠ u : ℝ in atTop,
      |primeThetaModFour 1 u - u / 2| ≤ C * u * Real.exp (-c * vkRate u) ∧
      |primeThetaModFour 3 u - u / 2| ≤ C * u * Real.exp (-c * vkRate u)) :
    ∃ C' > 0, ∃ c' > 0, ∀ᶠ u : ℝ in atTop, |D u| ≤ C' * u * Real.exp (-c' * vkRate u) := by
  obtain ⟨K, hK⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
  refine ⟨2 * C + max K 0, by positivity, c, hc, ?_⟩
  filter_upwards [hprime, eventually_sqrt_le_vkEnvelope hc] with u h hsqrt
  let T := primeThetaModFour 1 u - primeThetaModFour 3 u
  have hT : |T| ≤ 2 * (C * u * Real.exp (-c * vkRate u)) := by
    have heq : T = (primeThetaModFour 1 u - u / 2) - (primeThetaModFour 3 u - u / 2) := by
      dsimp [T]
      ring
    rw [heq]
    linarith only [abs_sub (primeThetaModFour 1 u - u / 2) (primeThetaModFour 3 u - u / 2),
      h.1, h.2]
  calc
    |D u| ≤ |D u - T| + |T| := by
      simpa only [sub_add_cancel] using abs_add_le (D u - T) T
    _ ≤ K * Real.sqrt u + 2 * (C * u * Real.exp (-c * vkRate u)) :=
      add_le_add ((abs_D_sub_primeThetaModFour_le u).trans (hK u)) hT
    _ ≤ max K 0 * (u * Real.exp (-c * vkRate u)) + 2 * (C * u * Real.exp (-c * vkRate u)) :=
      add_le_add ((mul_le_mul_of_nonneg_right (le_max_left K 0) (Real.sqrt_nonneg u)).trans
        (mul_le_mul_of_nonneg_left hsqrt (le_max_right K 0))) le_rfl
    _ = (2 * C + max K 0) * u * Real.exp (-c * vkRate u) := by ring

end TerminalTriangle
