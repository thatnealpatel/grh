module

public import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Algebra.Order.Group.Unbundled.Int
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Tactic.Ring

/-!
# Exact recovery from translated spatial masks

Sources: `48ad196a:.godel/bob/paired-10-2.md:21–41` and
`5ab1b80f:.godel/bob/sparse-10-2.md:43–59`, checked at base `0648ae05`.
The grid average reconstructs the first mask at every real phase, so the
finite separator retains its first price. Only the finite reconstruction
identity is proved here, not the properties of the specific sine kernel or
the subsequent price bound.

Owning check session: `01a20ce0-1582-79d6-b657-1b3239837bf7`.
-/

open scoped BigOperators

namespace Masullo.SpatialMaskRecovery

private theorem sum_exp_grid {N : ℕ} (hN : N ≠ 0) (m : ℤ) (hm : |m| < (N : ℤ)) :
    (∑ p ∈ Finset.range N,
      Complex.exp ((m : ℂ) * (↑(2 * Real.pi * (p : ℝ) / (N : ℝ)) : ℂ) * Complex.I)) =
      if m = 0 then (N : ℂ) else 0 := by
  by_cases hm0 : m = 0
  · subst m
    simp
  · rw [ite_eq_right hm0]
    let τ : ℂ := 2 * (Real.pi : ℂ) * Complex.I
    have hτ : τ ≠ 0 := by
      simp [τ, Real.pi_ne_zero, Complex.I_ne_zero]
    let a : ℂ := (m : ℂ) * τ / (N : ℂ)
    let z : ℂ := Complex.exp a
    have hN' : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN
    have hclear : (N : ℂ) * a = (m : ℂ) * τ := mul_div_cancel₀ _ hN'
    have hpow : z ^ N = 1 := by
      change Complex.exp a ^ N = 1
      rw [← Complex.exp_nat_mul, hclear]
      exact Complex.exp_eq_one_iff.mpr ⟨m, rfl⟩
    have hz : z ≠ 1 := by
      intro hz
      obtain ⟨q, hq⟩ := Complex.exp_eq_one_iff.mp hz
      change a = (q : ℂ) * τ at hq
      have hmq : (m : ℂ) = (N : ℂ) * (q : ℂ) := by
        apply mul_right_cancel₀ hτ
        rw [← hclear, hq, mul_assoc]
      have hmqInt : m = (N : ℤ) * q := by exact_mod_cast hmq
      exact hm0 (Int.eq_zero_of_abs_lt_dvd ⟨q, hmqInt⟩ hm)
    have hphase (p : ℕ) :
        Complex.exp ((m : ℂ) * (↑(2 * Real.pi * (p : ℝ) / (N : ℝ)) : ℂ) * Complex.I) =
          z ^ p := by
      change _ = Complex.exp a ^ p
      rw [← Complex.exp_nat_mul]
      congr 1
      dsimp only [a, τ]
      push_cast
      ring
    simp_rw [hphase]
    have hgeom := geom_sum_mul z N
    rw [hpow, sub_self] at hgeom
    exact (mul_eq_zero.mp hgeom).resolve_right (sub_ne_zero.mpr hz)

/-- Exact signed-frequency reconstruction by translated spatial masks. The
strict cross-support difference bound excludes every nonzero alias modulo `N`.
The phase `ξ` is arbitrary, not restricted to the sampling grid. -/
public theorem reconstruct {N : ℕ} (hN : 1 ≤ N) {J K : Finset ℤ} (hJK : J ⊆ K)
    (b d : ℤ → ℂ) (hd : ∀ j ∈ J, d j ≠ 0)
    (halias : ∀ j ∈ J, ∀ k ∈ K, |j - k| < (N : ℤ)) (ξ : ℝ) :
    let e : ℤ → ℝ → ℂ := fun j x ↦ Complex.exp ((j : ℂ) * (x : ℂ) * Complex.I)
    let θ : ℕ → ℝ := fun p ↦ 2 * Real.pi * (p : ℝ) / (N : ℝ)
    let V : ℕ → ℂ := fun p ↦ ∑ j ∈ J, (b j / d j) * e j (θ p)
    let D : ℕ → ℂ := fun p ↦ (N : ℂ)⁻¹ * ∑ k ∈ K, d k * e k (ξ - θ p)
    (∑ p ∈ Finset.range N, D p * V p) = ∑ j ∈ J, b j * e j ξ := by
  intro e θ V D
  have hN0 : N ≠ 0 := Nat.ne_of_gt hN
  have hN' : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN0
  let c (j k : ℤ) : ℂ := (N : ℂ)⁻¹ * (b j / d j) * d k * e k ξ
  let w (j k : ℤ) (p : ℕ) : ℂ := e (j - k) (θ p)
  have hterm (p : ℕ) (j k : ℤ) :
      (N : ℂ)⁻¹ * (d k * e k (ξ - θ p)) * ((b j / d j) * e j (θ p)) = c j k * w j k p := by
    have hphase : e k (ξ - θ p) * e j (θ p) = e k ξ * w j k p := by
      dsimp only [e, w]
      rw [← Complex.exp_add, ← Complex.exp_add]
      congr 1
      rw [Complex.ofReal_sub, Int.cast_sub]
      ring
    calc
      _ = (N : ℂ)⁻¹ * (b j / d j) * d k * (e k (ξ - θ p) * e j (θ p)) := by ring
      _ = _ := by rw [hphase, ← mul_assoc]
  calc
    (∑ p ∈ Finset.range N, D p * V p) =
        ∑ p ∈ Finset.range N, ∑ j ∈ J, ∑ k ∈ K, c j k * w j k p := by
      simp only [D, V, Finset.mul_sum, Finset.sum_mul, hterm]
    _ = ∑ j ∈ J, ∑ k ∈ K, c j k * ∑ p ∈ Finset.range N, w j k p := by
      rw [Finset.sum_comm (s := Finset.range N) (t := J)]
      simp_rw [Finset.sum_comm (s := Finset.range N) (t := K), Finset.mul_sum]
    _ = ∑ j ∈ J, b j * e j ξ := by
      refine Finset.sum_congr rfl fun j hj ↦ ?_
      have hw (k : ℤ) (hk : k ∈ K) :
          (∑ p ∈ Finset.range N, w j k p) = if j = k then (N : ℂ) else 0 := by
        simpa only [sub_eq_zero] using sum_exp_grid hN0 (j - k) (halias j hj k hk)
      rw [Finset.sum_eq_single_of_mem j (hJK hj)]
      · rw [hw j (hJK hj), ite_eq_left rfl]
        calc
          c j j * (N : ℂ) = ((N : ℂ)⁻¹ * (N : ℂ)) * ((b j / d j) * d j) * e j ξ := by
            dsimp only [c]
            ring
          _ = _ := by rw [inv_mul_cancel₀ hN', div_mul_cancel₀ _ (hd j hj), one_mul]
      · intro k hk hkj
        rw [hw k hk, ite_eq_right hkj.symm, mul_zero]

end Masullo.SpatialMaskRecovery
