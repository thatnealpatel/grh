module

public import Lemmas.PadicCharacterDenominators

/-!
# The standard additive character of `ℚ_[p]`

For Example A.3.1.6, p. 557, we realize the quotient character by clearing
`p`-power denominators and applying the standard finite cyclic character to
the numerator residue. Increasing the denominator multiplies the numerator by
the same factor, so the exponential is unchanged.
-/

open scoped Padic
open Filter Topology

namespace Masullo

variable (p : ℕ) [Fact p.Prime]

private noncomputable def padicCharValue (x : ℚ_[p]) : ℂ :=
  let h := exists_padic_integral_numerator p x
  ZMod.stdAddChar (PadicInt.toZModPow h.choose h.choose_spec.choose)

private theorem padicCharValue_spec {x : ℚ_[p]} {n : ℕ} {a : ℤ_[p]}
    (ha : (a : ℚ_[p]) = (p : ℚ_[p]) ^ n * x) :
    padicCharValue p x = ZMod.stdAddChar (PadicInt.toZModPow n a) := by
  let h := exists_padic_integral_numerator p x
  change ZMod.stdAddChar (PadicInt.toZModPow h.choose h.choose_spec.choose) = _
  rcases le_total h.choose n with hle | hle
  · exact padicResidueChar_eq_of_le p hle h.choose_spec.choose_spec ha
  · exact (padicResidueChar_eq_of_le p hle ha h.choose_spec.choose_spec).symm

/-- The standard additive character of `ℚ_[p]` with positive exponential sign. -/
public noncomputable def padicStdAddChar : AddChar ℚ_[p] ℂ where
  toFun := padicCharValue p
  map_zero_eq_one' := by
    rw [padicCharValue_spec p (n := 0) (a := 0) (by simp), map_zero, AddChar.map_zero_eq_one]
  map_add_eq_mul' x y := by
    obtain ⟨n, a, ha⟩ := exists_padic_integral_numerator p x
    obtain ⟨m, b, hb⟩ := exists_padic_integral_numerator p y
    let a' := (p : ℤ_[p]) ^ m * a
    let b' := (p : ℤ_[p]) ^ n * b
    have ha' : (a' : ℚ_[p]) = (p : ℚ_[p]) ^ (n + m) * x := by
      simp [a', ha, pow_add, mul_left_comm, mul_assoc]
    have hb' : (b' : ℚ_[p]) = (p : ℚ_[p]) ^ (n + m) * y := by
      simp [b', hb, pow_add, mul_assoc]
    have hab' : ((a' + b' : ℤ_[p]) : ℚ_[p]) = (p : ℚ_[p]) ^ (n + m) * (x + y) := by
      rw [PadicInt.coe_add, ha', hb', mul_add]
    rw [padicCharValue_spec p ha', padicCharValue_spec p hb', padicCharValue_spec p hab',
      map_add, AddChar.map_add_eq_mul]

/-- If `a = p^n x` is integral, the character is the exponential of the
residue of `a` modulo `p^n` divided by `p^n`, with angle measured in turns. -/
public theorem padicStdAddChar_apply_of_scaled_integral {x : ℚ_[p]} {n : ℕ} {a : ℤ_[p]}
    (ha : (a : ℚ_[p]) = (p : ℚ_[p]) ^ n * x) :
    padicStdAddChar p x = ZMod.stdAddChar (PadicInt.toZModPow n a) :=
  padicCharValue_spec p ha

/-- The kernel of the standard character is exactly the ring of `p`-adic integers. -/
public theorem padicStdAddChar_eq_one_iff (x : ℚ_[p]) :
    padicStdAddChar p x = 1 ↔ ‖x‖ ≤ 1 := by
  obtain ⟨n, a, ha⟩ := exists_padic_integral_numerator p x
  rw [padicStdAddChar_apply_of_scaled_integral p ha,
    ← (ZMod.stdAddChar (N := p ^ n)).map_zero_eq_one, ZMod.injective_stdAddChar.eq_iff,
    ← RingHom.mem_ker, PadicInt.ker_toZModPow, ← PadicInt.norm_le_pow_iff_mem_span_pow,
    ← PadicInt.norm_coe, ha, norm_mul, Padic.norm_p_pow, mul_le_iff_le_one_right]
  exact zpow_pos (Nat.cast_pos.mpr (Fact.out : p.Prime).pos) _

/-- The standard character takes values on the complex unit circle. -/
public theorem norm_padicStdAddChar (x : ℚ_[p]) : ‖padicStdAddChar p x‖ = 1 := by
  obtain ⟨n, a, ha⟩ := exists_padic_integral_numerator p x
  rw [padicStdAddChar_apply_of_scaled_integral p ha, ZMod.stdAddChar_apply, Circle.norm_coe]

/-- The standard character is continuous, since it is constant on translates of
its open kernel. -/
public theorem continuous_padicStdAddChar : Continuous (padicStdAddChar p : ℚ_[p] → ℂ) := by
  rw [continuous_iff_continuousAt]
  intro x
  have h : ∀ᶠ y in 𝓝 x, ‖y - x‖ ≤ 1 := by
    have hb := Metric.ball_mem_nhds x (zero_lt_one' ℝ)
    filter_upwards [hb] with y hy
    exact (show ‖y - x‖ < 1 from by simpa [Metric.mem_ball, dist_eq_norm] using hy).le
  have hconst : ContinuousAt (fun _ : ℚ_[p] ↦ padicStdAddChar p x) x := continuousAt_const
  apply hconst.congr_of_eventuallyEq
  filter_upwards [h] with y hy
  calc
    padicStdAddChar p y = padicStdAddChar p ((y - x) + x) := by rw [sub_add_cancel]
    _ = padicStdAddChar p x := by
      rw [AddChar.map_add_eq_mul, (padicStdAddChar_eq_one_iff p _).mpr hy, one_mul]

end Masullo
