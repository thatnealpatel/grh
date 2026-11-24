module

public import Lemmas.TerminalTriangle

/-! # Divisor decomposition of the `χ₄`-weighted logarithmic sum -/

namespace Chi4Divisor

open Finset

/-- The character modulo `4`, evaluated on naturals and viewed in `ℝ`. -/
@[expose] public def chi (n : ℕ) : ℝ := ((ZMod.χ₄ (n : ZMod 4) : ℤ) : ℝ)

/-- The von Mangoldt function twisted by `chi`. -/
@[expose] public noncomputable def w (n : ℕ) : ℝ := ArithmeticFunction.vonMangoldt n * chi n

/-- The inclusive character prefix. -/
@[expose] public noncomputable def M (X : ℕ) : ℝ := ∑ m ∈ Icc 1 X, chi m

/-- The inclusive character prefix weighted by the logarithm. -/
@[expose] public noncomputable def A (X : ℕ) : ℝ := ∑ n ∈ Icc 1 X, chi n * Real.log n

/-- At a natural cutoff, `D` is the inclusive sum of `w`. -/
public theorem D_nat (X : ℕ) : TerminalTriangle.D (X : ℝ) = ∑ d ∈ Icc 1 X, w d := by
  simp only [TerminalTriangle.D, Nat.floor_natCast, w, chi]

private theorem chi_mul (d m : ℕ) : chi (d * m) = chi d * chi m := by
  simp only [chi, Nat.cast_mul, map_mul, Int.cast_mul]

/-- Expand the logarithm as a divisor sum and group the terms by divisor. -/
public theorem divisor_identity (X : ℕ) : A X = ∑ d ∈ Icc 1 X, w d * M (X / d) := by
  calc
    A X = ∑ n ∈ Icc 1 X, ∑ d ∈ n.divisors, w d * chi (n / d) := by
      unfold A
      apply sum_congr rfl
      intro n _
      rw [← ArithmeticFunction.vonMangoldt_sum, mul_sum]
      apply sum_congr rfl
      intro d hd
      have hdn := Nat.mul_div_cancel' (Nat.mem_divisors.mp hd).1
      have hchi : chi n = chi d * chi (n / d) :=
        (congrArg chi hdn.symm).trans (chi_mul d (n / d))
      rw [hchi, w]
      ring
    _ = ∑ d ∈ Icc 1 X, w d * M (X / d) := by
      simp only [M, mul_sum]
      rw [sum_sigma' (Icc 1 X) Nat.divisors (fun n d ↦ w d * chi (n / d)),
        sum_sigma' (Icc 1 X) (fun d ↦ Icc 1 (X / d)) (fun d m ↦ w d * chi m)]
      -- Send `(n, d)` to `(d, n / d)`, with inverse `(d, m) ↦ (d * m, d)`.
      refine sum_nbij' (fun p ↦ ⟨p.2, p.1 / p.2⟩) (fun q ↦ ⟨q.1 * q.2, q.1⟩)
        ?_ ?_ ?_ ?_ ?_
      · rintro ⟨n, d⟩ hp
        obtain ⟨hn, hd⟩ := mem_sigma.mp hp
        obtain ⟨hdvd, hn0⟩ := Nat.mem_divisors.mp hd
        have hd0 : 0 < d := Nat.pos_of_ne_zero (ne_zero_of_dvd_ne_zero hn0 hdvd)
        have hdn : d ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) hdvd
        have hm0 : 0 < n / d := Nat.div_pos hdn hd0
        have hnX := (mem_Icc.mp hn).2
        refine mem_sigma.mpr ⟨mem_Icc.mpr ⟨hd0, hdn.trans hnX⟩,
          mem_Icc.mpr ⟨hm0, (Nat.le_div_iff_mul_le hd0).mpr ?_⟩⟩
        rwa [Nat.div_mul_cancel hdvd]
      · rintro ⟨d, m⟩ hq
        obtain ⟨hd, hm⟩ := mem_sigma.mp hq
        obtain ⟨hd0, _⟩ := mem_Icc.mp hd
        obtain ⟨hm0, hmX⟩ := mem_Icc.mp hm
        have hprod : 0 < d * m := Nat.mul_pos hd0 hm0
        exact mem_sigma.mpr ⟨mem_Icc.mpr ⟨hprod, by
          rw [mul_comm]
          exact (Nat.le_div_iff_mul_le hd0).mp hmX⟩,
          Nat.mem_divisors.mpr ⟨dvd_mul_right d m, hprod.ne'⟩⟩
      · rintro ⟨n, d⟩ hp
        have hdn := Nat.mul_div_cancel' (Nat.mem_divisors.mp (mem_sigma.mp hp).2).1
        simp [hdn]
      · rintro ⟨d, m⟩ hq
        have hd0 : 0 < d := (mem_Icc.mp (mem_sigma.mp hq).1).1
        simp [Nat.mul_div_cancel_left m hd0]
      · intro p _
        rfl

end Chi4Divisor
