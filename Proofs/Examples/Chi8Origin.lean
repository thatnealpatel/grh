module

public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.NumberTheory.LSeries.Nonvanishing
public import Mathlib.NumberTheory.LegendreSymbol.ZModChar

/-!
# The simple trivial zero of the quadratic character modulo 8

The primitive functional equation relates the completed value at `0` to the nonzero completed
value of the inverse character at `1`. Since the character is even, the residue `2` of `Gammaℝ`
at `0` then gives the derivative of its L-function there.
-/

open DirichletCharacter Filter
open scoped Topology

namespace Chi8Origin

/-- The complex Dirichlet character obtained from `ZMod.χ₈`. -/
@[expose] public def χ : DirichletCharacter ℂ 8 := ZMod.χ₈.ringHomComp (Int.castRingHom ℂ)

private theorem χ_at_five : χ ((5 : ℤ) : ZMod 8) = -1 := by
  rw [χ, MulChar.ringHomComp_apply, ZMod.χ₈_int_eq_if_mod_eight]
  norm_num

private theorem χ_even : χ.Even := by
  change χ ((-1 : ℤ) : ZMod 8) = 1
  rw [χ, MulChar.ringHomComp_apply, ZMod.χ₈_int_eq_if_mod_eight]
  norm_num

/-- The quadratic character `χ` is primitive modulo `8`. -/
public theorem conductor_eq : χ.conductor = 8 := by
  by_contra h
  have hd : χ.conductor ∣ 2 ^ 3 := χ.conductor_dvd_level
  obtain ⟨k, hk, he⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd
  have hk' : k ≤ 2 := by
    by_contra! hlt
    have h3 : k = 3 := by omega
    exact h (he.trans (by norm_num [h3]))
  have hd4 : χ.conductor ∣ 4 :=
    (Nat.dvd_prime_pow Nat.prime_two (m := 2)).mpr ⟨k, hk', he⟩
  obtain ⟨h48, ψ, hψ⟩ := χ.factorsThrough_conductor.mono χ hd4 (by decide : 4 ∣ 8)
  have h5 : IsCoprime (5 : ℤ) 8 := ⟨-3, 2, by decide⟩
  have hv := changeLevel_eq_cast_of_dvd' ψ h48 h5
  rw [← hψ, χ_at_five, show ((5 : ℤ) : ZMod 4) = 1 by decide, map_one] at hv
  exact (by norm_num : (-1 : ℂ) ≠ 1) hv

private theorem χ_ne_one : χ ≠ 1 := by
  intro h
  have hc := conductor_eq
  rw [h, conductor_one] at hc
  exact (by decide : (1 : ℕ) ≠ 8) hc

private theorem completedLFunction_zero_ne_zero : completedLFunction χ 0 ≠ 0 := by
  have hprim : χ.IsPrimitive := conductor_eq
  have hone : completedLFunction χ⁻¹ 1 ≠ 0 :=
    completedLFunction_ne_zero_of_one_le_re χ⁻¹ (Or.inl (inv_ne_one.mpr χ_ne_one)) (by simp)
  have h := hprim.completedLFunction_one_sub (1 : ℂ)
  rw [sub_self] at h
  rw [h]
  have h8 : (8 : ℂ) ≠ 0 := by norm_num
  exact mul_ne_zero (mul_ne_zero (Complex.cpow_ne_zero_iff.mpr (Or.inl h8))
    (rootNumber_ne_zero hprim)) hone

/-- The L-function of `χ` vanishes at `0`. -/
public theorem LFunction_zero : LFunction χ 0 = 0 := by
  have hg : Complex.Gammaℝ 0 = 0 := Complex.Gammaℝ_eq_zero_iff.mpr ⟨0, by simp⟩
  rw [LFunction_eq_completed_div_gammaFactor χ 0 (Or.inr (by decide)),
    χ_even.gammaFactor_def, hg, div_zero]

/-- The zero at `0` of the L-function of `χ` is simple. -/
public theorem deriv_LFunction_zero_ne_zero : deriv (LFunction χ) 0 ≠ 0 := by
  have hc : Tendsto (completedLFunction χ) (𝓝[≠] 0) (𝓝 (completedLFunction χ 0)) :=
    tendsto_nhdsWithin_of_tendsto_nhds
      ((differentiable_completedLFunction χ_ne_one).continuous.continuousAt.tendsto)
  have hlim : Tendsto (fun s ↦ completedLFunction χ s / (s * Complex.Gammaℝ s))
      (𝓝[≠] 0) (𝓝 (completedLFunction χ 0 / 2)) :=
    hc.div Complex.Gammaℝ_residue_zero two_ne_zero
  have hderiv : HasDerivAt (LFunction χ) (completedLFunction χ 0 / 2) 0 := by
    apply hasDerivAt_iff_tendsto_slope.mpr
    refine hlim.congr' (Eventually.of_forall fun s ↦ ?_)
    simp only [slope_def_field, LFunction_zero, sub_zero]
    rw [LFunction_eq_completed_div_gammaFactor χ s (Or.inr (by decide)),
      χ_even.gammaFactor_def, div_div, mul_comm s]
  rw [hderiv.deriv]
  exact div_ne_zero completedLFunction_zero_ne_zero two_ne_zero

end Chi8Origin
