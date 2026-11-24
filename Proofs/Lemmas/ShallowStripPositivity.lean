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

/-!
## Mixed coefficients and the quadratic support bound

Source: `5ab1b80f:.godel/bob/sparse-10-2.md`, lines 29–41 (unchanged at `0648ae05`).
Use: apply the quadratic support bound at each fixed spatial point at `3t`, before integration.
The normalized harmonic factors are `cosh (j*d) / cosh (j*c)` for modes `1 ≤ j ≤ n`.
The argument allows any complex coefficients, including those from joint refits; it is a
pointwise transfer, not a certificate for the sparse choice or its integrated budget.

Owning check session: `01a20ce0-1582-79d6-b657-1b3239837bf7`.
-/

private theorem sin_re (z : ℂ) :
    (Complex.sin z).re = Real.cosh z.im * Real.sin z.re := by
  rw [Complex.sin_eq, ← Complex.ofReal_sin, ← Complex.ofReal_cosh,
    ← Complex.ofReal_cos, ← Complex.ofReal_sinh]
  simp only [← Complex.ofReal_mul, Complex.add_re, Complex.mul_I_re, Complex.ofReal_re,
    Complex.ofReal_im, neg_zero, add_zero]
  rw [mul_comm]

private theorem phase_re (a : ℂ) (θ : ℝ) :
    (a * Complex.exp (Complex.I * (θ : ℂ))).re = a.re * Real.cos θ - a.im * Real.sin θ := by
  rw [mul_comm Complex.I, Complex.exp_mul_I, Complex.mul_re]
  simp only [Complex.add_re, Complex.add_im, Complex.mul_I_re,
    Complex.mul_I_im, Complex.cos_ofReal_re, Complex.sin_ofReal_re, Complex.cos_ofReal_im,
    Complex.sin_ofReal_im, neg_zero, add_zero, zero_add]

private theorem exp_phase_periodic :
    Function.Periodic (fun θ : ℝ ↦ Complex.exp (Complex.I * (θ : ℂ))) (2 * Real.pi) := by
  intro θ
  change Complex.exp (Complex.I * (↑(θ + 2 * Real.pi) : ℂ)) = _
  rw [Complex.ofReal_add, mul_add]
  simpa only [Complex.ofReal_mul, Complex.ofReal_ofNat, mul_comm Complex.I] using
    Complex.exp_periodic ((θ : ℂ) * Complex.I)

private theorem exp_nat_phase_periodic (j : ℕ) :
    Function.Periodic (fun θ : ℝ ↦ Complex.exp (Complex.I * ↑((j : ℝ) * θ)))
      (2 * Real.pi) := by
  intro θ
  change Complex.exp (Complex.I * ↑((j : ℝ) * (θ + 2 * Real.pi))) = _
  rw [mul_add, ← nsmul_eq_mul j (2 * Real.pi)]
  exact (exp_phase_periodic.nsmul j) ((j : ℝ) * θ)

/-- The harmonic extension of a nonnegative trigonometric polynomial with arbitrary complex
coefficients is nonnegative on the closed strip. The same data are prescribed at both edges;
the sum is over modes `1` through `n` and is empty for `n = 0`. -/
public theorem harmonic_extension_complex_nonneg (n : ℕ) (a₀ : ℝ) (a : ℕ → ℂ)
    {c : ℝ} (hc : 0 < c)
    (h : ∀ θ : ℝ, 0 ≤ a₀ + (∑ j ∈ Finset.Icc 1 n,
      a j * Complex.exp (Complex.I * ↑((j : ℝ) * θ))).re)
    (φ d : ℝ) (hd : |d| ≤ c) :
    0 ≤ a₀ + (∑ j ∈ Finset.Icc 1 n,
      a j * ↑(Real.cosh ((j : ℝ) * d) / Real.cosh ((j : ℝ) * c)) *
        Complex.exp (Complex.I * ↑((j : ℝ) * φ))).re := by
  let F (z : ℂ) : ℂ := a₀ + ∑ j ∈ Finset.Icc 1 n,
    ↑((Real.cosh ((j : ℝ) * c))⁻¹) *
      (↑(a j).re * Complex.cos ((j : ℂ) * z) - ↑(a j).im * Complex.sin ((j : ℂ) * z))
  have hF : Differentiable ℂ F := by
    refine Differentiable.add (differentiable_const _) ?_
    apply Differentiable.fun_sum
    intro j _
    exact (((Complex.differentiable_cos.comp (differentiable_id.const_mul (j : ℂ))).const_mul _).sub
      ((Complex.differentiable_sin.comp (differentiable_id.const_mul (j : ℂ))).const_mul _)).const_mul _
  have hRe (z : ℂ) : (F z).re = a₀ + (∑ j ∈ Finset.Icc 1 n,
      a j * ↑(Real.cosh ((j : ℝ) * z.im) / Real.cosh ((j : ℝ) * c)) *
        Complex.exp (Complex.I * ↑((j : ℝ) * z.re))).re := by
    simp only [F, Complex.add_re, Complex.ofReal_re, Complex.re_sum]
    congr 1
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [mul_right_comm (a j), Complex.re_mul_ofReal, phase_re, Complex.re_ofReal_mul,
      Complex.sub_re, Complex.re_ofReal_mul, Complex.re_ofReal_mul, cos_re, sin_re]
    simp only [Complex.mul_re, Complex.mul_im, Complex.natCast_re, Complex.natCast_im,
      zero_mul, sub_zero, add_zero, div_eq_mul_inv]
    ring
  have hperiod (y : ℝ) : Function.Periodic (fun x : ℝ ↦ (F ⟨x, y⟩).re) (2 * Real.pi) := by
    intro x
    change (F ⟨x + 2 * Real.pi, y⟩).re = (F ⟨x, y⟩).re
    rw [hRe, hRe]
    congr 2
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    exact congrArg (fun e ↦ a j * ↑(Real.cosh ((j : ℝ) * y) / Real.cosh ((j : ℝ) * c)) * e)
      (exp_nat_phase_periodic j x)
  have hboundary (x y : ℝ) (hy : |y| = c) : 0 ≤ (F ⟨x, y⟩).re := by
    rw [hRe]
    have hcosh (j : ℕ) : Real.cosh ((j : ℝ) * y) = Real.cosh ((j : ℝ) * c) := by
      rcases le_total 0 y with hpos | hneg
      · rw [abs_of_nonneg hpos] at hy
        rw [hy]
      · rw [abs_of_nonpos hneg] at hy
        rw [← hy, mul_neg, Real.cosh_neg]
    simpa only [hcosh, div_self (Real.cosh_pos _).ne', Complex.ofReal_one, mul_one] using h x
  simpa only [hRe] using
    re_nonneg_of_periodic_strip F hF hc.le (mul_pos two_pos Real.pi_pos) hperiod hboundary
      (z := ⟨φ, d⟩) hd

/-- The support value `S(H,h)` of the first and second harmonics with coefficients `H,h`. -/
public noncomputable def quadraticSupport (H h : ℂ) : ℝ :=
  sSup (Set.range fun θ : ℝ ↦ (H * Complex.exp (Complex.I * (θ : ℂ)) +
    h * Complex.exp (Complex.I * ↑(2 * θ))).re)

/-- The support value is a maximum over all real phases. -/
public theorem isGreatest_quadraticSupport (H h : ℂ) :
    IsGreatest (Set.range fun θ : ℝ ↦ (H * Complex.exp (Complex.I * (θ : ℂ)) +
      h * Complex.exp (Complex.I * ↑(2 * θ))).re) (quadraticSupport H h) := by
  let f (θ : ℝ) : ℝ := (H * Complex.exp (Complex.I * (θ : ℂ)) +
    h * Complex.exp (Complex.I * ↑(2 * θ))).re
  change IsGreatest (Set.range f) (sSup (Set.range f))
  have hf : Continuous f := by
    dsimp only [f]
    fun_prop
  have hp : 0 < 2 * Real.pi := mul_pos two_pos Real.pi_pos
  have hperiod : Function.Periodic f (2 * Real.pi) := by
    intro θ
    exact congrArg₂ (fun e₁ e₂ ↦ (H * e₁ + h * e₂).re)
      (exp_phase_periodic θ) (exp_nat_phase_periodic 2 θ)
  obtain ⟨m, _, hmax⟩ := isCompact_Icc.exists_isMaxOn
    (show (Icc (0 : ℝ) (2 * Real.pi)).Nonempty from ⟨0, le_rfl, hp.le⟩) hf.continuousOn
  have hm : IsGreatest (Set.range f) (f m) := by
    refine ⟨⟨m, rfl⟩, ?_⟩
    rintro _ ⟨θ, rfl⟩
    obtain ⟨x, hx, heq⟩ := hperiod.exists_mem_Ico hp θ 0
    rw [heq]
    exact (isMaxOn_iff.mp hmax) x (Ico_subset_Icc_self (by simpa only [zero_add] using hx))
  rwa [hm.csSup_eq]

/-- The degree-two strip transfer used at `3t`: the support of `(H,h)` supplies the boundary
constant for `(H,-h)`, by a phase shift of `π`. -/
public theorem harmonic_extension_quadratic_support_nonneg (H h : ℂ)
    {c : ℝ} (hc : 0 < c) (φ d : ℝ) (hd : |d| ≤ c) :
    0 ≤ quadraticSupport H h +
      (H * ↑(Real.cosh d / Real.cosh c) * Complex.exp (Complex.I * (φ : ℂ)) -
        h * ↑(Real.cosh (2 * d) / Real.cosh (2 * c)) * Complex.exp (Complex.I * ↑(2 * φ))).re := by
  let a : ℕ → ℂ := fun
    | 1 => H
    | 2 => -h
    | _ => 0
  have ha₁ : a 1 = H := rfl
  have ha₂ : a 2 = -h := rfl
  have hIcc : Finset.Icc 1 2 = ({1, 2} : Finset ℕ) := by decide
  have hne : (1 : ℕ) ≠ 2 := by decide
  have hboundary (θ : ℝ) : 0 ≤ quadraticSupport H h + (∑ j ∈ Finset.Icc 1 2,
      a j * Complex.exp (Complex.I * ↑((j : ℝ) * θ))).re := by
    have hfirst : Complex.exp (Complex.I * ↑(θ + Real.pi)) =
        -Complex.exp (Complex.I * (θ : ℂ)) := by
      rw [Complex.ofReal_add, mul_add, Complex.exp_add, mul_comm Complex.I (Real.pi : ℂ),
        Complex.exp_pi_mul_I, mul_neg_one]
    have hsecond : Complex.exp (Complex.I * ↑(2 * (θ + Real.pi))) =
        Complex.exp (Complex.I * ↑(2 * θ)) := by
      rw [mul_add]
      exact exp_phase_periodic (2 * θ)
    have hbound : (H * Complex.exp (Complex.I * ↑(θ + Real.pi)) +
        h * Complex.exp (Complex.I * ↑(2 * (θ + Real.pi)))).re ≤ quadraticSupport H h :=
      (isGreatest_quadraticSupport H h).2 ⟨θ + Real.pi, rfl⟩
    rw [hfirst, hsecond, mul_neg, Complex.add_re, Complex.neg_re] at hbound
    simp only [hIcc, Finset.sum_pair hne, ha₁, ha₂, Nat.cast_one, Nat.cast_ofNat, one_mul,
      Complex.add_re, neg_mul, Complex.neg_re]
    linarith only [hbound]
  simpa only [hIcc, Finset.sum_pair hne, ha₁, ha₂, Nat.cast_one, Nat.cast_ofNat, one_mul,
    neg_mul, sub_eq_add_neg] using
    harmonic_extension_complex_nonneg 2 (quadraticSupport H h) a hc hboundary φ d hd

end Masullo.ShallowStripPositivity
