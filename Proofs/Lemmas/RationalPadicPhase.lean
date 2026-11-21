module

public import Theorems.PadicStandardCharacter

/-! # Rational inputs to the standard p-adic character -/

open scoped BigOperators Padic

namespace Masullo

local instance (p : Nat.Primes) : Fact (p : ℕ).Prime := ⟨p.property⟩

/-- The positive local character evaluated on a rational number. -/
public noncomputable def rationalPadicPhase (p : Nat.Primes) : AddChar ℚ ℂ :=
  (padicStdAddChar p).compAddMonoidHom (Rat.castHom ℚ_[(p : ℕ)]).toAddMonoidHom

/-- Precisely the primes dividing the reduced denominator can contribute to
    the finite diagonal phase. -/
public theorem rationalPadicPhase_eq_one_iff (p : Nat.Primes) (r : ℚ) :
    rationalPadicPhase p r = 1 ↔ ¬ (p : ℕ) ∣ r.den := by
  change padicStdAddChar p (r : ℚ_[(p : ℕ)]) = 1 ↔ _
  rw [padicStdAddChar_eq_one_iff]
  refine ⟨fun hr hd ↦ ?_, Padic.norm_rat_le_one⟩
  have hn : ¬ (p : ℕ) ∣ r.num.natAbs :=
    fun h ↦ p.property.dvd_iff_not_coprime.mp h (Nat.Coprime.coprime_dvd_left hd r.reduced.symm)
  have hnum : 1 ≤ ‖(r.num : ℚ_[(p : ℕ)])‖ := by
    rw [← not_lt, Padic.norm_intCast_lt_one_iff, Int.natCast_dvd]
    exact hn
  have hden := Padic.norm_natCast_lt_one_iff.mpr hd
  have hden0 : 0 < ‖(r.den : ℚ_[(p : ℕ)])‖ :=
    norm_pos_iff.mpr (Nat.cast_ne_zero.mpr r.den_ne_zero)
  rw [Rat.cast_def, norm_div, div_le_iff₀ hden0, one_mul] at hr
  exact (hden.trans_le hnum).not_ge hr

private theorem rationalPadicPhase_primePower_residue (p : Nat.Primes) (n b : ℕ) :
    rationalPadicPhase p ((b : ℚ) / (p : ℚ) ^ n) =
      ZMod.stdAddChar (b : ZMod ((p : ℕ) ^ n)) := by
  have hp : (p : ℚ_[(p : ℕ)]) ≠ 0 := Nat.cast_ne_zero.mpr p.property.ne_zero
  have hb : ((b : ℤ_[(p : ℕ)]) : ℚ_[(p : ℕ)]) =
      (p : ℚ_[(p : ℕ)]) ^ n * (((b : ℚ) / (p : ℚ) ^ n : ℚ) : ℚ_[(p : ℕ)]) := by
    push_cast
    field_simp
  change padicStdAddChar p (((b : ℚ) / (p : ℚ) ^ n : ℚ) : ℚ_[(p : ℕ)]) = _
  rw [padicStdAddChar_apply_of_scaled_integral p hb, map_natCast]

private theorem rationalPadicPhase_primePower (p : Nat.Primes) (n b : ℕ) :
    rationalPadicPhase p ((b : ℚ) / (p : ℚ) ^ n) =
      Complex.exp (2 * Real.pi * Complex.I * ((b : ℚ) / (p : ℚ) ^ n : ℚ)) := by
  rw [rationalPadicPhase_primePower_residue]
  rw [show (b : ZMod ((p : ℕ) ^ n)) = (↑(b : ℤ) : ZMod ((p : ℕ) ^ n)) by simp,
    ZMod.stdAddChar_coe]
  push_cast
  congr 1
  ring

private theorem exists_prime_power_phase (p : Nat.Primes) (r : ℚ) :
    ∃ n b : ℕ, rationalPadicPhase p r = rationalPadicPhase p ((b : ℚ) / (p : ℚ) ^ n) := by
  obtain ⟨n, a, ha⟩ := exists_padic_integral_numerator p (r : ℚ_[(p : ℕ)])
  refine ⟨n, a.appr n, ?_⟩
  rw [rationalPadicPhase_primePower_residue]
  change padicStdAddChar p (r : ℚ_[(p : ℕ)]) = _
  exact padicStdAddChar_apply_of_scaled_integral p ha

private theorem cross_phase_eq_one {p q : Nat.Primes} (h : p ≠ q) (n b : ℕ) :
    rationalPadicPhase p ((b : ℚ) / (q : ℚ) ^ n) = 1 := by
  have hc : (p : ℕ).Coprime (q : ℕ) :=
    (Nat.coprime_primes p.property q.property).mpr (Nat.Primes.coe_nat_inj p q |>.not.mpr h)
  change padicStdAddChar p (((b : ℚ) / (q : ℚ) ^ n : ℚ) : ℚ_[(p : ℕ)]) = 1
  rw [padicStdAddChar_eq_one_iff]
  push_cast
  rw [norm_div, norm_pow, Padic.norm_natCast_eq_one_iff.mpr hc, one_pow, div_one]
  simpa only [Int.cast_natCast] using Padic.norm_int_le_one (p := (p : ℕ)) (b : ℤ)

/-- A local phase on a rational is represented by rational turns that are
integral at every other prime. -/
public theorem exists_rationalPadicPhase_turns (p : Nat.Primes) (r : ℚ) :
    ∃ t : ℚ, rationalPadicPhase p t = rationalPadicPhase p r ∧
      rationalPadicPhase p t = Complex.exp (2 * Real.pi * Complex.I * (t : ℂ)) ∧
      ∀ q : Nat.Primes, q ≠ p → rationalPadicPhase q t = 1 := by
  obtain ⟨n, b, hb⟩ := exists_prime_power_phase p r
  exact ⟨_, hb.symm, rationalPadicPhase_primePower p n b,
    fun q hq ↦ cross_phase_eq_one hq n b⟩

/-- Applying a local phase to a finite sum multiplies its values. -/
public theorem rationalPadicPhase_sum (p : Nat.Primes) (S : Finset Nat.Primes) (f : Nat.Primes → ℚ) :
    rationalPadicPhase p (∑ q ∈ S, f q) = ∏ q ∈ S, rationalPadicPhase p (f q) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert q S h ih => simp [h, AddChar.map_add_eq_mul, ih]

/-- A rational number integral at every prime is an integer. -/
public theorem exists_int_of_all_rationalPadicPhases_eq_one (r : ℚ)
    (h : ∀ p : Nat.Primes, rationalPadicPhase p r = 1) : ∃ z : ℤ, r = z := by
  have hd : r.den = 1 := by
    by_contra hne
    obtain ⟨p, hp, hdvd⟩ := Nat.exists_prime_and_dvd hne
    exact (rationalPadicPhase_eq_one_iff ⟨p, hp⟩ r).mp (h ⟨p, hp⟩) hdvd
  exact ⟨r.num, by rw [← Rat.num_div_den r, hd]; simp⟩

/-- Rational inputs to the local character still have unit modulus. -/
public theorem norm_rationalPadicPhase (p : Nat.Primes) (r : ℚ) :
    ‖rationalPadicPhase p r‖ = 1 :=
  norm_padicStdAddChar p (r : ℚ_[(p : ℕ)])

end Masullo
