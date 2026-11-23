module

public import Props.CopyDiagonalWeight
public import Theorems.RationalThetaBandTraceDensity
public import Mathlib.Topology.Algebra.InfiniteSum.Module

/-!
# Constant-copy split of the rational fixed-band trace

At fixed cutoffs, apply (12.2.2.1–7), p. 508, in the counting-copy
model of the rational principal window. The two-leg weight acts on the
already formed global theta-band kernel. In the rational prime-two
model the copy labels are powers of two: The identity relative copy
is the finite-unit base, and the other copies are the positive shell.
This uses a mask at primes *outside* two, not the right mask that
can erase the shell in (11.3.2.3), p. 495. The signed shell in
(11.3.1.4), p. 494, is the negative of the positive shell here.

This split uses one common trace before any limit. It does not
identify the shell with the orbital quotient of pp. 495–496 or the
base with the local comparison in (12.5.1.1–4), pp. 519–520.
-/

open MeasureTheory InnerProductSpace
open scoped InnerProductSpace

namespace Masullo.OperatorTrace

universe v

local notation "H" => Lp ℂ 2 (volume : Measure ℝ)

/-- The class-constant finite-copy lift splits the actual global band
operator's trace in the log chart. The common density also gives the
relative-copy traces, their counting sum, and the off-base counting sum.
Both pieces are dominated by the absolute whole trace, even for weights
chosen separately at each pair of cutoffs. -/
public theorem rationalThetaBand_copyTrace_split {G : Type*} [Group G] [DecidableEq G]
    (J : Finset G) (m : G → ℝ) (hm : ∀ j ∈ J, 0 ≤ m j) (hmass : ∑ j ∈ J, m j = 1)
    (a α s Y : ℝ) (hs : 0 ≤ s) (hα : 0 ≤ α)
    {ρ φ : ℝ → ℂ} (hρ : Continuous ρ) (hρK : HasCompactSupport ρ)
    (hφ : ContDiff ℝ 2 φ) (hφK : HasCompactSupport φ) :
    let w := symmetricStripWeightRoot α s
    let P := (rationalThetaWeightedEvenImage a hs hα {ξ | |ξ| ≤ Y}).toSubmodule.starProjection
    let c := copyDiagonalWeight J m
    ∃ (B : H →L[ℂ] H) (d : ℝ → ℂ),
      (∀ z : H, (B z : ℝ → ℂ) =ᵐ[volume] fun x =>
        (ρ x * (w x : ℂ)) * ∫ y, φ (x - y) * (P z) y * (w y : ℂ)⁻¹) ∧
      Integrable d volume ∧
      let T := ∫ x, d x
      let D (h : G) := ∫ x, (c h : ℂ) * d x
      (∀ {ι : Type v} (b : HilbertBasis ι ℂ H), HasSum (fun i => ⟪b i, B (b i)⟫_ℂ) T) ∧
      (∀ h, Integrable (fun x => (c h : ℂ) * d x) volume ∧
        D h = (c h : ℂ) * T ∧
        ∀ {ι : Type v} (b : HilbertBasis ι ℂ H),
          HasSum (fun i => ⟪b i, ((c h : ℂ) • B) (b i)⟫_ℂ) (D h)) ∧
      HasSum D T ∧
      HasSum (fun h => if h = 1 then 0 else D h) ((1 - (c 1 : ℂ)) * T) ∧
      D 1 - (-((1 - (c 1 : ℂ)) * T)) = T ∧
      ‖D 1‖ ≤ ‖T‖ ∧ ‖(1 - (c 1 : ℂ)) * T‖ ≤ ‖T‖ := by
  obtain ⟨B, d, hB, hd, htrace, _⟩ :=
    rationalThetaBand_traceDensity.{v, v} a α s Y hs hα hρ hρK hφ hφK
  let c := copyDiagonalWeight J m
  let T := ∫ x, d x
  let D (h : G) := ∫ x, (c h : ℂ) * d x
  have hD (h : G) : D h = (c h : ℂ) * T := integral_const_mul _ _
  obtain ⟨hc, _, hc₁, hall, hrest⟩ := copyDiagonalWeight_split J m hm hmass
  refine ⟨B, d, hB, hd, fun b => htrace b, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h
    refine ⟨hd.const_mul _, hD h, fun b => ?_⟩
    change HasSum (fun i => ⟪b i, ((c h : ℂ) • B) (b i)⟫_ℂ) (D h)
    rw [hD]
    simpa only [smul_apply, inner_smul_right] using (htrace b).mul_left (c h : ℂ)
  · have hcT : HasSum (fun h : G => (c h : ℂ) * T) T := by
      simpa only [Complex.real_smul, one_smul] using hall.smul_const T
    exact hcT.congr_fun hD
  · change HasSum (fun h => if h = 1 then 0 else D h) ((1 - (c 1 : ℂ)) * T)
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub, ← Complex.real_smul]
    refine (hrest.smul_const T).congr_fun ?_
    intro h
    by_cases hh : h = 1 <;> simp [hh, hD, Complex.real_smul, c]
  · change D 1 - (-((1 - (c 1 : ℂ)) * T)) = T
    rw [hD]
    ring
  · change ‖D 1‖ ≤ ‖T‖
    rw [hD, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hc 1)]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hc₁ (norm_nonneg T)
  · rw [norm_mul, ← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hc₁)]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right (sub_le_self 1 (hc 1)) (norm_nonneg T)

end Masullo.OperatorTrace
