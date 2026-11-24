module

public import Mathlib.NumberTheory.DirichletCharacter.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-!
# Prime-power layers of a quadratic logarithmic ramp

The cutoff in `powerLayer χ k X` is on the prime power, not on its base.
The coefficient is `log p` at every power. Only the logarithmic ramp supplies
factor `k`; parity determines whether the character survives.
-/

open Finset Real

namespace QuadraticPowerRamp

variable {A : Type*} [CommRing A] [Algebra ℝ A] {q : ℕ}

/-- Base primes coprime to the modulus, up to a real cutoff. -/
@[expose] public noncomputable def primes (q : ℕ) (Y : ℝ) : Finset ℕ :=
  (Icc 0 ⌊Y⌋₊).filter fun p => p.Prime ∧ p.Coprime q

/-- A prime ramp; use the constant weight `1` for the unsigned ramp. -/
@[expose] public noncomputable def ramp (q : ℕ) (w : ℕ → A) (Y : ℝ) : A :=
  ∑ p ∈ primes q Y, algebraMap ℝ A (log (Y / p) * log p) * w p

/-- The `k`th layer at `X`, retaining precisely those base primes with `p^k ≤ X`. -/
@[expose] public noncomputable def powerLayer (χ : DirichletCharacter A q) (k : ℕ) (X : ℝ) : A :=
  ∑ p ∈ (primes q X).filter (fun p : ℕ => (p : ℝ)^k ≤ X),
    algebraMap ℝ A (log (X / (p : ℝ)^k) * log p) * χ ((p : ZMod q)^k)

private theorem cutoff {Y : ℝ} (hY : 0 ≤ Y) {k : ℕ} (hk : k ≠ 0) :
    (primes q (Y^k)).filter (fun p : ℕ => (p : ℝ)^k ≤ Y^k) = primes q Y := by
  ext p
  simp only [primes, mem_filter, mem_Icc, Nat.zero_le, true_and,
    Nat.le_floor_iff (pow_nonneg hY k), Nat.le_floor_iff hY,
    pow_le_pow_iff_left₀ (Nat.cast_nonneg p) hY hk]
  constructor
  · rintro ⟨⟨_, h⟩, hp⟩
    exact ⟨hp, h⟩
  · rintro ⟨hp, h⟩
    have hpp : (p : ℝ) ≤ (p : ℝ)^k := by exact_mod_cast Nat.le_self_pow hk p
    exact ⟨⟨hpp.trans (pow_le_pow_left₀ (by positivity) hp k), h⟩, hp⟩

/-- Exact even/odd decomposition, with no asymptotic or analytic hypotheses. -/
public theorem powerLayer_at_pow (χ : DirichletCharacter A q) (hχ : χ.IsQuadratic)
    {k : ℕ} (hk : 1 ≤ k) {Y : ℝ} (hY : 0 ≤ Y) :
    powerLayer χ k (Y^k) = (k : A) *
      (if Even k then ramp q (fun _ => 1) Y else ramp q (fun p => χ (p : ZMod q)) Y) := by
  have hk' : k ≠ 0 := by omega
  unfold powerLayer
  rw [cutoff hY hk']
  split_ifs with he <;> unfold ramp <;> rw [mul_sum] <;> apply sum_congr rfl <;> intro p hp
  · have hu := (ZMod.isUnit_iff_coprime p q).2 (mem_filter.mp hp).2.2
    rw [map_pow, ← MulChar.pow_apply' χ hk', hχ.pow_even he, MulChar.one_apply hu,
      ← div_pow, Real.log_pow, mul_assoc, map_mul, map_natCast]
    ring
  · rw [map_pow, ← MulChar.pow_apply' χ hk', hχ.pow_odd (Nat.not_even_iff_odd.mp he),
      ← div_pow, Real.log_pow, mul_assoc, map_mul, map_natCast]
    ring

end QuadraticPowerRamp
