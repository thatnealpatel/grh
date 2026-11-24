module

public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Tactic.Linarith

/-!
# From the logarithmic prime ramp to a sharp cutoff

Source: `bbca37033019:.godel/bob/fixed-strip-endpoints.md:53–63`.
Owning check session: `01a20fbf-64d4-7ae0-ac41-09f991160e63`.

This is the finite-sum estimate for the sharp multiplier Gram argument, before
partial summation. The endpoints and logarithmic weights are real, and the
coefficients are complex and unnormalized. This does not establish a zero-free
strip or the Gram estimate itself.
-/

@[expose] public section

open scoped BigOperators

namespace PrimeRampSharpCutoff

/-- The primes at or below the real cutoff `U`, including equality. -/
noncomputable def primesUpTo (U : ℝ) : Finset ℕ :=
  (Finset.range (⌊U⌋₊ + 1)).filter Nat.Prime

/-- The boundary primes, strictly above `U` and at or below `V`. -/
noncomputable def boundaryPrimes (U V : ℝ) : Finset ℕ :=
  (Finset.Ioc ⌊U⌋₊ ⌊V⌋₊).filter Nat.Prime

theorem mem_primesUpTo {U : ℝ} (hU : 0 ≤ U) {p : ℕ} :
    p ∈ primesUpTo U ↔ p.Prime ∧ (p : ℝ) ≤ U := by
  simp only [primesUpTo, Finset.mem_filter, Finset.mem_range, Nat.lt_succ_iff,
    Nat.le_floor_iff hU, and_comm]

theorem mem_boundaryPrimes {U V : ℝ} (hU : 0 ≤ U) (hV : 0 ≤ V) {p : ℕ} :
    p ∈ boundaryPrimes U V ↔ p.Prime ∧ U < (p : ℝ) ∧ (p : ℝ) ≤ V := by
  simp only [boundaryPrimes, Finset.mem_filter, Finset.mem_Ioc,
    ← not_le (a := p) (b := ⌊U⌋₊), Nat.le_floor_iff hU, Nat.le_floor_iff hV, not_le,
    and_comm (b := p.Prime)]

/-- Equal integer floors leave no boundary terms, even for distinct real cutoffs. -/
theorem boundaryPrimes_eq_empty_of_floor_eq {U V : ℝ} (he : ⌊U⌋₊ = ⌊V⌋₊) :
    boundaryPrimes U V = ∅ := by
  simp [boundaryPrimes, he]

/-- The unnormalized logarithmic ramp `M(U)`. -/
noncomputable def ramp (a : ℕ → ℂ) (U : ℝ) : ℂ :=
  ∑ p ∈ primesUpTo U, a p * (Real.log (U / (p : ℝ)) : ℂ)

/-- The unnormalized sum through the inclusive sharp cutoff. -/
noncomputable def sharp (a : ℕ → ℂ) (U : ℝ) : ℂ :=
  ∑ p ∈ primesUpTo U, a p

private theorem le_exp_mul {U h : ℝ} (hU : 0 ≤ U) (hh : 0 ≤ h) :
    U ≤ Real.exp h * U :=
  le_mul_of_one_le_left hU (Real.one_le_exp_iff.mpr hh)

/-- Differencing the ramps restores the full coefficient on every prime through `U`;
only primes strictly above `U` retain a logarithmic weight. -/
theorem dividedDifference_sub_sharp (a : ℕ → ℂ) {U h : ℝ} (hU : 1 ≤ U) (hh : 0 < h) :
    (ramp a (Real.exp h * U) - ramp a U) / (h : ℂ) - sharp a U =
      ∑ p ∈ boundaryPrimes U (Real.exp h * U),
        a p * ((Real.log (Real.exp h * U / (p : ℝ)) / h : ℝ) : ℂ) := by
  have hU' : 0 < U := zero_lt_one.trans_le hU
  have hUV : U ≤ Real.exp h * U := le_exp_mul hU'.le hh.le
  have hV : 0 < Real.exp h * U := hU'.trans_le hUV
  have hunion : primesUpTo U ∪ boundaryPrimes U (Real.exp h * U) =
      primesUpTo (Real.exp h * U) := by
    ext p
    simp only [Finset.mem_union, mem_primesUpTo hU'.le, mem_primesUpTo hV.le,
      mem_boundaryPrimes hU'.le hV.le]
    constructor
    · rintro (⟨hp, hpU⟩ | ⟨hp, _, hpV⟩)
      · exact ⟨hp, hpU.trans hUV⟩
      · exact ⟨hp, hpV⟩
    · rintro ⟨hp, hpV⟩
      by_cases hpU : (p : ℝ) ≤ U
      · exact Or.inl ⟨hp, hpU⟩
      · exact Or.inr ⟨hp, lt_of_not_ge hpU, hpV⟩
  have hdis : Disjoint (primesUpTo U) (boundaryPrimes U (Real.exp h * U)) := by
    refine Finset.disjoint_left.mpr fun p hpU hpB ↦ ?_
    exact (not_lt_of_ge ((mem_primesUpTo hU'.le).mp hpU).2)
      ((mem_boundaryPrimes hU'.le hV.le).mp hpB).2.1
  have hdifference : ramp a (Real.exp h * U) - ramp a U =
      (∑ p ∈ primesUpTo U, a p * (h : ℂ)) +
        ∑ p ∈ boundaryPrimes U (Real.exp h * U),
          a p * (Real.log (Real.exp h * U / (p : ℝ)) : ℂ) := by
    unfold ramp
    rw [← hunion, Finset.sum_union hdis, add_sub_right_comm, ← Finset.sum_sub_distrib]
    congr 1
    refine Finset.sum_congr rfl fun p hp ↦ ?_
    have hp' : 0 < (p : ℝ) := Nat.cast_pos.mpr ((mem_primesUpTo hU'.le).mp hp).1.pos
    have hlog : Real.log (Real.exp h * U / (p : ℝ)) - Real.log (U / (p : ℝ)) = h := by
      rw [Real.log_div hV.ne' hp'.ne', Real.log_div hU'.ne' hp'.ne',
        Real.log_mul (Real.exp_pos h).ne' hU'.ne', Real.log_exp]
      linarith
    rw [← mul_sub, ← Complex.ofReal_sub, hlog]
  rw [hdifference, add_div, ← Finset.sum_mul, mul_div_cancel_right₀ _
    (Complex.ofReal_ne_zero.mpr hh.ne'), ← sharp, add_sub_cancel_left, Finset.sum_div]
  simp only [mul_div_assoc, ← Complex.ofReal_div]

/-- The complex cutoff error is bounded by the total norm of the boundary coefficients.
No coefficient size or sign assumption is needed. -/
theorem norm_dividedDifference_sub_sharp_le (a : ℕ → ℂ) {U h : ℝ}
    (hU : 1 ≤ U) (hh : 0 < h) :
    ‖(ramp a (Real.exp h * U) - ramp a U) / (h : ℂ) - sharp a U‖ ≤
      ∑ p ∈ boundaryPrimes U (Real.exp h * U), ‖a p‖ := by
  have hU' : 0 < U := zero_lt_one.trans_le hU
  have hV : 0 < Real.exp h * U := hU'.trans_le (le_exp_mul hU'.le hh.le)
  rw [dividedDifference_sub_sharp a hU hh]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun p hp ↦ ?_)
  obtain ⟨hpPrime, hpU, hpV⟩ := (mem_boundaryPrimes hU'.le hV.le).mp hp
  have hp' : 0 < (p : ℝ) := Nat.cast_pos.mpr hpPrime.pos
  have hlog_nonneg : 0 ≤ Real.log (Real.exp h * U / (p : ℝ)) :=
    Real.log_nonneg ((one_le_div hp').mpr hpV)
  have hlog_le : Real.log (Real.exp h * U / (p : ℝ)) ≤ h := by
    rw [Real.log_div hV.ne' hp'.ne', Real.log_mul (Real.exp_pos h).ne' hU'.ne', Real.log_exp]
    have hlogUp := Real.log_le_log hU' hpU.le
    linarith
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (div_nonneg hlog_nonneg hh.le)]
  exact mul_le_of_le_one_right (norm_nonneg _) ((div_le_one hh).mpr hlog_le)

/-- Counting the integers in `(U, V]` bounds the total norm of the boundary coefficients. -/
theorem boundary_sum_norm_le (a : ℕ → ℂ) {U V : ℝ} (hU : 1 ≤ U) (hUV : U ≤ V)
    (ha : ∀ p : ℕ, p.Prime → ‖a p‖ ≤ Real.log (p : ℝ)) :
    (∑ p ∈ boundaryPrimes U V, ‖a p‖) ≤ (V - U + 1) * Real.log V := by
  have hU' : 0 ≤ U := zero_le_one.trans hU
  have hV : 0 ≤ V := hU'.trans hUV
  have hlogV : 0 ≤ Real.log V := Real.log_nonneg (hU.trans hUV)
  have hcard : (boundaryPrimes U V).card ≤ ⌊V⌋₊ - ⌊U⌋₊ := by
    simpa only [boundaryPrimes, Nat.card_Ioc] using
      Finset.card_filter_le (Finset.Ioc ⌊U⌋₊ ⌊V⌋₊) Nat.Prime
  have hcard' : ((boundaryPrimes U V).card : ℝ) ≤ V - U + 1 := by
    calc
      _ ≤ ((⌊V⌋₊ - ⌊U⌋₊ : ℕ) : ℝ) := Nat.cast_le.mpr hcard
      _ = (⌊V⌋₊ : ℝ) - (⌊U⌋₊ : ℝ) := Nat.cast_sub (Nat.floor_mono hUV)
      _ ≤ V - U + 1 := by
        have hfloorV := Nat.floor_le hV
        have hfloorU := Nat.lt_floor_add_one U
        linarith
  calc
    (∑ p ∈ boundaryPrimes U V, ‖a p‖) ≤ ∑ _p ∈ boundaryPrimes U V, Real.log V := by
      refine Finset.sum_le_sum fun p hp ↦ ?_
      obtain ⟨hpPrime, _, hpV⟩ := (mem_boundaryPrimes hU' hV).mp hp
      exact (ha p hpPrime).trans (Real.log_le_log (Nat.cast_pos.mpr hpPrime.pos) hpV)
    _ = ((boundaryPrimes U V).card : ℝ) * Real.log V := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (V - U + 1) * Real.log V := mul_le_mul_of_nonneg_right hcard' hlogV

/-- A bound for the sharp prime sum using only the two ramp norms and the explicit
integer-counting boundary error. -/
theorem norm_sharp_le (a : ℕ → ℂ) {U h : ℝ} (hU : 1 ≤ U) (hh : 0 < h)
    (ha : ∀ p : ℕ, p.Prime → ‖a p‖ ≤ Real.log (p : ℝ)) :
    ‖sharp a U‖ ≤ (‖ramp a (Real.exp h * U)‖ + ‖ramp a U‖) / h +
      (Real.exp h * U - U + 1) * Real.log (Real.exp h * U) := by
  let d : ℂ := (ramp a (Real.exp h * U) - ramp a U) / (h : ℂ)
  have hd : ‖d‖ ≤ (‖ramp a (Real.exp h * U)‖ + ‖ramp a U‖) / h := by
    dsimp only [d]
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hh]
    exact div_le_div_of_nonneg_right (norm_sub_le _ _) hh.le
  have he : ‖d - sharp a U‖ ≤ (Real.exp h * U - U + 1) * Real.log (Real.exp h * U) :=
    (norm_dividedDifference_sub_sharp_le a hU hh).trans
      (boundary_sum_norm_le a hU (le_exp_mul (zero_le_one.trans hU) hh.le) ha)
  calc
    ‖sharp a U‖ = ‖d - (d - sharp a U)‖ := by rw [sub_sub_cancel]
    _ ≤ ‖d‖ + ‖d - sharp a U‖ := norm_sub_le _ _
    _ ≤ _ := add_le_add hd he

end PrimeRampSharpCutoff
