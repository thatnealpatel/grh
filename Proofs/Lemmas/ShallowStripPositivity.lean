module

public import Mathlib.Analysis.Complex.AbsMax
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Algebra.Field.Periodic
import Mathlib.Order.Interval.Finset.Nat

/-!
# Pointwise positivity on the shallow strip

Source: `059232cff7d3894d8545eb11ffccf9cd2fec1646:.godel/bob/long-cutoff-moments.md`,
lines 45–56, and `.godel/bob/finite-cutoff-budget.md`, lines 7–25 at the same revision.
Use: `1171778a:.godel/bob/paired-radial-price.md`, lines 30–36 (unchanged at `e96c4611`),
applies this positivity at each zero's phase, including the rotated phase at the third height,
before weighting and summing.

Scope: a finite even cosine polynomial, with identical boundary data at depths `±c`.
The result is pointwise, before shallow averaging, and assumes only boundary positivity,
not Toeplitz positivity or an arithmetic realization of the moments.

Owning check session: `01a20c71-faab-7613-8747-63acf6b0d98e`.
-/

open Set
open scoped BigOperators

namespace Masullo.ShallowStripPositivity

/-- Minimize the periodic real part on a compact rectangle. A disk centered at the minimum and
reaching the nearer strip edge transfers the minimum to that edge by maximum modulus. -/
private theorem re_nonneg_of_periodic_strip (F : ℂ → ℂ) (hF : Differentiable ℂ F)
    {c p : ℝ} (hc : 0 ≤ c) (hp : 0 < p)
    (hperiod : ∀ y : ℝ, Function.Periodic (fun x : ℝ ↦ (F ⟨x, y⟩).re) p)
    (hboundary : ∀ x y : ℝ, |y| = c → 0 ≤ (F ⟨x, y⟩).re)
    {z : ℂ} (hz : |z.im| ≤ c) : 0 ≤ (F z).re := by
  let rect := Icc (0 : ℝ) p ×ˢ Icc (-c) c
  have hrect : IsCompact rect := isCompact_Icc.prod isCompact_Icc
  have hne : rect.Nonempty := ⟨(0, 0), ⟨le_rfl, hp.le⟩, ⟨neg_nonpos.mpr hc, hc⟩⟩
  have hmk : Continuous (fun q : ℝ × ℝ ↦ (⟨q.1, q.2⟩ : ℂ)) := by
    simp only [Complex.mk_eq_add_mul_I]
    fun_prop
  obtain ⟨m, hm, hmin⟩ := hrect.exists_isMinOn hne
    (Complex.continuous_re.comp (hF.continuous.comp hmk)).continuousOn
  let u : ℂ := ⟨m.1, m.2⟩
  have hminStrip (w : ℂ) (hw : |w.im| ≤ c) : (F u).re ≤ (F w).re := by
    obtain ⟨x, hx, heq⟩ := (hperiod w.im).exists_mem_Ico hp w.re 0
    have hx' : x ∈ Icc (0 : ℝ) p := Ico_subset_Icc_self (by simpa only [zero_add] using hx)
    exact ((isMinOn_iff.mp hmin) (x, w.im) ⟨hx', abs_le.mp hw⟩).trans_eq heq.symm
  let r := c - |m.2|
  let y := if 0 ≤ m.2 then c else -c
  have hy : |y| = c := by
    dsimp only [y]
    split_ifs <;> simp [abs_of_nonneg hc]
  let v : ℂ := ⟨m.1, y⟩
  have hv : v ∈ Metric.closedBall u r := by
    rw [Metric.mem_closedBall, Complex.dist_of_re_eq (show v.re = u.re from rfl)]
    change dist y m.2 ≤ c - |m.2|
    rw [Real.dist_eq]
    have hm' : m.2 ∈ Icc (-c) c := hm.2
    dsimp only [y]
    split_ifs with h
    · rw [abs_of_nonneg h, abs_of_nonneg (sub_nonneg.mpr hm'.2)]
    · rw [abs_of_neg (lt_of_not_ge h), abs_of_nonpos (sub_nonpos.mpr hm'.1)]
      linarith
  have hball (w : ℂ) (hw : w ∈ Metric.ball u r) : |w.im| ≤ c := by
    have h₁ : |w.im - m.2| ≤ ‖w - u‖ := Complex.abs_im_le_norm (w - u)
    have h₂ : ‖w - u‖ < c - |m.2| := by
      simpa only [Metric.mem_ball, Complex.dist_eq] using hw
    calc
      |w.im| = |w.im - m.2 + m.2| := by rw [sub_add_cancel]
      _ ≤ |w.im - m.2| + |m.2| := abs_add_le ..
      _ ≤ c := by linarith only [h₁, h₂]
  let G (w : ℂ) := Complex.exp (-(F w))
  have hG : Differentiable ℂ G := Complex.differentiable_exp.comp hF.neg
  have hnorm (w : ℂ) : ‖G w‖ = Real.exp (-(F w).re) := by
    change ‖Complex.exp (-(F w))‖ = _
    rw [Complex.norm_exp, Complex.neg_re]
  have hmax : IsMaxOn (norm ∘ G) (Metric.ball u r) u := by
    refine isMaxOn_iff.mpr fun w hw ↦ ?_
    change ‖G w‖ ≤ ‖G u‖
    rw [hnorm, hnorm, Real.exp_le_exp, neg_le_neg_iff]
    exact hminStrip w (hball w hw)
  have heq : ‖G v‖ = ‖G u‖ :=
    Complex.norm_eqOn_closedBall_of_isMaxOn hG.diffContOnCl hmax hv
  rw [hnorm, hnorm] at heq
  have hre : (F v).re = (F u).re := neg_injective (Real.exp_injective heq)
  exact ((hboundary m.1 y hy).trans_eq hre).trans (hminStrip z hz)

private theorem cos_re (z : ℂ) :
    (Complex.cos z).re = Real.cosh z.im * Real.cos z.re := by
  rw [Complex.cos_eq, Complex.sub_re, Complex.mul_I_re]
  simp [Complex.mul_re, Complex.mul_im, Complex.cos_ofReal_re, Complex.cos_ofReal_im,
    Complex.cosh_ofReal_re, Complex.cosh_ofReal_im, Complex.sin_ofReal_im,
    Complex.sinh_ofReal_im, mul_comm]

/-- The harmonic extension of a nonnegative finite even cosine polynomial is nonnegative
at every phase and every depth in the closed strip. The sum is empty when `n = 0`. -/
public theorem harmonic_extension_nonneg (n : ℕ) (b₀ : ℝ) (b : ℕ → ℝ)
    {c : ℝ} (hc : 0 < c)
    (h : ∀ θ : ℝ, 0 ≤ b₀ + ∑ j ∈ Finset.Icc 1 n, b j * Real.cos ((j : ℝ) * θ))
    (φ d : ℝ) (hd : |d| ≤ c) :
    0 ≤ b₀ + ∑ j ∈ Finset.Icc 1 n,
      b j * (Real.cosh ((j : ℝ) * d) / Real.cosh ((j : ℝ) * c)) * Real.cos ((j : ℝ) * φ) := by
  let F (z : ℂ) : ℂ := b₀ + ∑ j ∈ Finset.Icc 1 n,
    ((b j / Real.cosh ((j : ℝ) * c) : ℝ) : ℂ) * Complex.cos ((j : ℂ) * z)
  have hF : Differentiable ℂ F := by
    refine Differentiable.add (differentiable_const _) ?_
    apply Differentiable.fun_sum
    intro j _
    exact (Complex.differentiable_cos.comp (differentiable_id.const_mul (j : ℂ))).const_mul _
  have hRe (z : ℂ) : (F z).re = b₀ + ∑ j ∈ Finset.Icc 1 n,
      b j * (Real.cosh ((j : ℝ) * z.im) / Real.cosh ((j : ℝ) * c)) *
        Real.cos ((j : ℝ) * z.re) := by
    simp only [F, Complex.add_re, Complex.ofReal_re, Complex.re_sum]
    congr 1
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, cos_re]
    simp only [Complex.mul_re, Complex.mul_im, Complex.natCast_re, Complex.natCast_im,
      zero_mul, sub_zero, add_zero]
    ring
  have hperiod (y : ℝ) : Function.Periodic (fun x : ℝ ↦ (F ⟨x, y⟩).re) (2 * Real.pi) := by
    intro x
    change (F ⟨x + 2 * Real.pi, y⟩).re = (F ⟨x, y⟩).re
    rw [hRe, hRe]
    congr 1
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    change _ * Real.cos ((j : ℝ) * (x + 2 * Real.pi)) = _ * Real.cos ((j : ℝ) * x)
    rw [mul_add, ← nsmul_eq_mul j (2 * Real.pi), Real.cos_periodic.nsmul j]
  have hboundary (x y : ℝ) (hy : |y| = c) : 0 ≤ (F ⟨x, y⟩).re := by
    rw [hRe]
    have hcosh (j : ℕ) : Real.cosh ((j : ℝ) * y) = Real.cosh ((j : ℝ) * c) := by
      rcases le_total 0 y with hpos | hneg
      · rw [abs_of_nonneg hpos] at hy
        rw [hy]
      · rw [abs_of_nonpos hneg] at hy
        rw [← hy, mul_neg, Real.cosh_neg]
    simpa only [hcosh, div_self (Real.cosh_pos _).ne', mul_one] using h x
  simpa only [hRe] using
    re_nonneg_of_periodic_strip F hF hc.le (mul_pos two_pos Real.pi_pos) hperiod hboundary
      (z := ⟨φ, d⟩) hd

end Masullo.ShallowStripPositivity
