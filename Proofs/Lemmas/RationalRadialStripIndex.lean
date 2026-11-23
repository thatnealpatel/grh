module

public import Lemmas.IdeleClassStripDivisor
public import Theorems.RationalRadialStripTrace
import Lemmas.CompletedZetaOrders
import Lemmas.RationalCompletedZetaZeros
import Lemmas.RationalTrivialHeckeOrder
import Mathlib.Tactic.NormNum

/-! # The rational norm-power part of the open-strip Hecke divisor

The unshifted norm exponent identifies the Hecke zeros trivial on norm-one
classes with the radial zeta zeros, preserving the full multiplicity. The two
poles have negative order, so this identification imposes no bound on the width.
-/

open NumberField

namespace Masullo

private theorem completedZetaOrder_eq_zetaZeroOrder (ρ : criticalStripZetaZeros) :
    meromorphicOrderAt completedRiemannZeta (ρ : ℂ) = ((zetaZeroOrder ρ : ℤ) : WithTop ℤ) := by
  obtain ⟨_, hpos, hlt⟩ := mem_criticalStripZetaZeros.mp ρ.property
  have h₀ : (ρ : ℂ) ≠ 0 := by intro h; simp [h] at hpos
  have h₁ : (ρ : ℂ) ≠ 1 := by intro h; simp [h] at hlt
  rw [order_completedZeta_away h₀ h₁,
    (entireZeta_analyticOnNhd _ (Set.mem_univ _)).meromorphicOrderAt_eq,
    analyticOrderAt_entireZeta_eq hpos hlt, ← zetaZeroOrder_cast_eq ρ, ENat.map_natCast]

private theorem mem_criticalStripZetaZeros_of_order_pos {s : ℂ}
    (h : 0 < meromorphicOrderAt completedRiemannZeta s) : s ∈ criticalStripZetaZeros := by
  have hp : ¬ (s = 0 ∨ s = 1) := by
    intro hs
    rw [order_completedZeta_atPole hs] at h
    have hneg : ((-1 : ℤ) : WithTop ℤ) ≤ 0 :=
      WithTop.coe_le_coe.mpr (show (-1 : ℤ) ≤ 0 by decide)
    exact (not_lt_of_ge hneg) h
  obtain ⟨h₀, h₁⟩ := not_or.mp hp
  apply (completedZeta_eq_zero_iff_mem_criticalStripZetaZeros h₀ h₁).mp
  by_contra hn
  have ha := analyticAt_completedZeta h₀ h₁
  simp [ha.meromorphicOrderAt_eq, ha.analyticOrderAt_eq_zero.mpr hn] at h

private theorem eq_normPower_of_trivialOnNormOne {a : ℝ} {z : OpenStripHeckeZero ℚ a}
    (hz : ∀ x : ideleClassNormOne (K := ℚ), z.character (x : _) = 1) :
    z.character = ideleClassNormPower (ideleClassNormExponent z.character) := by
  obtain ⟨s, hs, _⟩ := ideleClassNormPower_existsUnique z.character hz
  calc
    z.character = ideleClassNormPower s := hs
    _ = ideleClassNormPower (ideleClassNormExponent z.character) := by
      rw [hs, ideleClassNormExponent_normPower]

/-- Reindex the radial zeta divisor by Hecke zeros trivial on the norm-one subgroup. -/
public noncomputable def rationalRadialStripIndexEquiv (a : ℝ) :
    rationalRadialStripZeros a ≃
      {z : OpenStripHeckeZero ℚ a // ∀ x : ideleClassNormOne (K := ℚ), z.character (x : _) = 1} where
  toFun ρ :=
    ⟨⟨ideleClassNormPower (ρ.val : ℂ), by
        have hρ : |(shiftedZetaZero ρ.val).re| < a := ρ.property
        simpa [ideleClassNormExponent_normPower, shiftedZetaZero] using hρ,
      ⟨zetaZeroOrder ρ.val, zetaZeroOrder_pos ρ.val, by
        rw [ideleClassHeckeOrder_normPower_rat, completedZetaOrder_eq_zetaZeroOrder]⟩⟩,
      ideleClassNormPower_on_normOne _⟩
  invFun z := by
    let s := ideleClassNormExponent z.val.character
    have hc : z.val.character = ideleClassNormPower s := eq_normPower_of_trivialOnNormOne z.property
    have ho : 0 < meromorphicOrderAt completedRiemannZeta s := by
      rw [← ideleClassHeckeOrder_normPower_rat, ← hc, z.val.heckeOrder_eq]
      exact_mod_cast z.val.order_pos
    exact ⟨⟨s, mem_criticalStripZetaZeros_of_order_pos ho⟩, by
      simpa [shiftedZetaZero, s] using z.val.re_mem_strip⟩
  left_inv ρ := by
    apply Subtype.ext
    apply Subtype.ext
    exact ideleClassNormExponent_normPower (ρ.val : ℂ)
  right_inv z := by
    apply Subtype.ext
    apply OpenStripHeckeZero.character_injective
    exact (eq_normPower_of_trivialOnNormOne z.property).symm

@[simp] public theorem rationalRadialStripIndexEquiv_apply_character {a : ℝ}
    (ρ : rationalRadialStripZeros a) :
    ((rationalRadialStripIndexEquiv a) ρ).val.character = ideleClassNormPower (ρ.val : ℂ) := by
  rfl

@[simp] public theorem rationalRadialStripIndexEquiv_apply_order {a : ℝ}
    (ρ : rationalRadialStripZeros a) :
    ((rationalRadialStripIndexEquiv a) ρ).val.order = zetaZeroOrder ρ.val := by
  have h := ((rationalRadialStripIndexEquiv a) ρ).val.heckeOrder_eq
  rw [rationalRadialStripIndexEquiv_apply_character, ideleClassHeckeOrder_normPower_rat,
    completedZetaOrder_eq_zetaZeroOrder] at h
  exact_mod_cast h.symm

end Masullo
