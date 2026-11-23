module

public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.NumberTheory.LegendreSymbol.ZModChar
public import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt

/-! # Reversing the signed terminal Vaughan triangle

The analytic input is kept separate: It suffices to control the prime prefix on
one dyadic interval. No cancellation in the inner coefficients is used. -/

namespace TerminalTriangle
open Finset

/-- The exact-quotient form, with outer factors given by adjacent differences. -/
public def triangle (q : ℕ) (F a : ℕ → ℝ) : ℝ :=
  ∑ t ∈ Ico (q + 1) (2*q), (F t - F (t+1)) * ∑ n ∈ Ico (q+1) (t+1), a n

public theorem reverse_sum (q : ℕ) (F a : ℕ → ℝ) : triangle q F a =
    ∑ n ∈ Ico (q+1) (2*q), a n * (F n - F (2*q)) := by
  unfold triangle
  simp_rw [mul_sum]
  rw [← sum_Ico_Ico_comm (q+1) (2*q) (fun n t => (F t - F (t+1)) * a n)]
  apply sum_congr rfl
  intro n hn
  rw [← sum_mul, mul_comm]
  congr 1
  have h := Finset.sum_Ico_sub (f := F) (Finset.mem_Ico.mp hn).2.le
  linarith [show (∑ t ∈ Ico n (2*q), (F t - F (t+1))) =
    -(∑ t ∈ Ico n (2*q), (F (t+1) - F t)) by simp [-Finset.sum_neg_distrib]]

/-- Pay once per endpoint, including the repeated common endpoint. -/
public theorem abs_triangle_le (q : ℕ) (F a : ℕ → ℝ) {K : ℝ} (hK : 0 ≤ K)
    (hF : ∀ n ∈ Icc (q+1) (2*q), |F n| ≤ K) (ha : ∀ n, |a n| ≤ 1) :
    |triangle q F a| ≤ q * (2*K) := by
  rw [reverse_sum]
  calc
    _ ≤ ∑ n ∈ Ico (q+1) (2*q), |a n * (F n - F (2*q))| := Finset.abs_sum_le_sum_abs ..
    _ ≤ ∑ _n ∈ Ico (q+1) (2*q), 2*K := by
      apply sum_le_sum
      intro n hn
      obtain ⟨hl, hr⟩ := mem_Ico.mp hn
      rw [abs_mul]
      calc
        _ ≤ 1 * |F n - F (2*q)| := mul_le_mul_of_nonneg_right (ha n) (abs_nonneg _)
        _ ≤ 2*K := by linarith [abs_sub (F n) (F (2*q)), hF n (mem_Icc.mpr ⟨hl,hr.le⟩),
                                  hF (2*q) (mem_Icc.mpr ⟨hl.trans hr.le, le_rfl⟩)]
    _ ≤ _ := by
      simp only [sum_const, Nat.card_Ico, nsmul_eq_mul]
      gcongr
      omega

/-- Twisted Chebyshev function, including all higher prime powers. -/
@[expose] public noncomputable def D (y : ℝ) : ℝ :=
  ∑ m ∈ Icc 1 ⌊y⌋₊, ArithmeticFunction.vonMangoldt m * (ZMod.χ₄ (m : ZMod 4) : ℤ)

/-- A difference of two prime prefixes really counts the half-open interval,
with the lower endpoint excluded even when it is integral. -/
public theorem D_sub {u v : ℝ} (h : v ≤ u) : D u - D v =
    ∑ m ∈ Ioc ⌊v⌋₊ ⌊u⌋₊, ArithmeticFunction.vonMangoldt m * (ZMod.χ₄ (m : ZMod 4) : ℤ) := by
  have he (k : ℕ) : Icc 1 k = Ioc 0 k := by ext m; simp; omega
  rw [D, D, he, he]
  exact sub_eq_iff_eq_add.mpr (by rw [add_comm, sum_Ioc_consecutive _ (Nat.zero_le _) (Nat.floor_mono h)])

public def coeff (n : ℕ) : ℝ :=
  ((ArithmeticFunction.moebius n * ZMod.χ₄ (n : ZMod 4) : ℤ) : ℝ)

public theorem coeff_bound (n : ℕ) : |coeff n| ≤ 1 := by
  unfold coeff
  exact_mod_cast (show |ArithmeticFunction.moebius n * ZMod.χ₄ (n : ZMod 4)| ≤ 1 by
    rw [abs_mul]
    have h : |ZMod.χ₄ (n : ZMod 4)| ≤ 1 := by
      rw [ZMod.χ₄_nat_eq_if_mod_four]; split_ifs <;> decide
    simpa using mul_le_mul ArithmeticFunction.abs_moebius_le_one h (abs_nonneg _) zero_le_one)

@[expose] public noncomputable def signedTriangle (x : ℝ) (q : ℕ) := triangle q (fun n => D (x/n)) coeff

end TerminalTriangle
