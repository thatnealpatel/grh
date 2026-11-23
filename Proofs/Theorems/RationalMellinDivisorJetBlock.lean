module

public import Theorems.RationalMellinDivisorKernel
public import Props.CompactLogMellin
public import Mathlib.Analysis.Convolution
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! # Finite jet blocks for rational radial convolution

The local calculation of §1.2.1 (p. 14) and (10.3.1.8)–(10.3.1.17), in
normalized Taylor coordinates at each actual shifted rational divisor point.
The coordinate matrix is lower triangular; the block acting on the dual
jet functionals has its transpose in the corresponding ordered basis.
This compact-log-profile calculation does not identify the completed
quotient dual, assert that its jets are total, or evaluate a Hilbert trace.
-/

open MeasureTheory
open scoped Convolution

namespace Masullo

local notation "L" => (ContinuousLinearMap.mul ℂ ℂ)

/-- Mellin convolution for compact continuous log profiles with the positive
exponent and normalized radial Haar `dx`. The inverse left translate is
`g (x - y)` in the convolution integrand. -/
public theorem compactLogMellin_convolution {φ g : ℝ → ℂ}
    (hφ : Continuous φ) (hcφ : HasCompactSupport φ)
    (hg : Continuous g) (hcg : HasCompactSupport g) :
    compactLogMellin (φ ⋆[L, volume] g) = compactLogMellin φ * compactLogMellin g := by
  funext z
  let e : ℝ → ℂ := fun x ↦ Complex.exp (z * (x : ℂ))
  have he : Continuous e := Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)
  have hφe : Integrable (φ * e) := (hφ.mul he).integrable_of_hasCompactSupport hcφ.mul_right
  have hge : Integrable (g * e) := (hg.mul he).integrable_of_hasCompactSupport hcg.mul_right
  have hpoint (x : ℝ) : (φ ⋆[L, volume] g) x * e x = ((φ * e) ⋆[L, volume] (g * e)) x := by
    unfold MeasureTheory.convolution
    rw [← integral_mul_const]
    apply integral_congr_ae
    filter_upwards with y
    change φ y * g (x - y) * e x = φ y * e y * (g (x - y) * e (x - y))
    have hexp : e x = e y * e (x - y) := by
      dsimp [e]
      rw [← Complex.exp_add, Complex.ofReal_sub]
      congr 1
      ring
    rw [hexp]
    ring
  change (∫ x, (φ ⋆[L, volume] g) x * e x) = (∫ x, φ x * e x) * (∫ x, g x * e x)
  simp_rw [hpoint]
  exact integral_convolution L hφe hge

private noncomputable def tcoef (f : ℂ → ℂ) (z : ℂ) (k : ℕ) : ℂ :=
  iteratedDeriv k f z / (k.factorial : ℂ)

private theorem tcoef_mul {f g : ℂ → ℂ} {z : ℂ} (hf : AnalyticAt ℂ f z)
    (hg : AnalyticAt ℂ g z) (k : ℕ) :
    tcoef (f * g) z k = ∑ j ∈ Finset.range (k + 1), tcoef f z (k - j) * tcoef g z j := by
  have h : f * g = g * f := mul_comm _ _
  rw [h, tcoef, iteratedDeriv_mul hg.contDiffAt hf.contDiffAt, Finset.sum_div]
  refine Finset.sum_congr rfl fun j hj ↦ ?_
  have hj' : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  have hchoose : (k.choose j : ℂ) * (j.factorial : ℂ) * ((k - j).factorial : ℂ) =
      (k.factorial : ℂ) := by exact_mod_cast Nat.choose_mul_factorial_mul_factorial hj'
  have h₁ : (j.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have h₂ : ((k - j).factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have h₃ : (k.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  rw [← hchoose] at h₃ ⊢
  have h₄ : (k.choose j : ℂ) ≠ 0 := fun h₄ ↦ h₃ (by simp [h₄])
  unfold tcoef
  field_simp

/-- Finite lower triangular block for convolution by the log kernel `φ`, in
normalized Taylor coordinates at `ρ - 1/2`. The row and column ranges are the
full multiplicity of the actual rational zero `ρ`. -/
@[expose] public noncomputable def rationalMellinDivisorJetBlock (φ : ℝ → ℂ)
    (ρ : criticalStripZetaZeros) : Matrix (Fin (zetaZeroOrder ρ)) (Fin (zetaZeroOrder ρ)) ℂ :=
  fun i j ↦ if (j : ℕ) ≤ (i : ℕ) then
    iteratedDeriv ((i : ℕ) - (j : ℕ)) (compactLogMellin φ) (shiftedZetaZero ρ) /
      ((((i : ℕ) - (j : ℕ)).factorial : ℕ) : ℂ) else 0

/-- The finite block acts on the existing normalized divisor jet of every
compact continuous input profile, before any Hilbert completion. -/
public theorem rationalMellinDivisorJet_convolution {φ g : ℝ → ℂ}
    (hφ : Continuous φ) (hcφ : HasCompactSupport φ)
    (hg : Continuous g) (hcg : HasCompactSupport g) (ρ : criticalStripZetaZeros) :
    rationalMellinDivisorJet (compactLogMellin (φ ⋆[L, volume] g)) ρ =
      (rationalMellinDivisorJetBlock φ ρ).mulVec (rationalMellinDivisorJet (compactLogMellin g) ρ) := by
  rw [compactLogMellin_convolution hφ hcφ hg hcg]
  funext i
  let z := shiftedZetaZero ρ
  let m := compactLogMellin φ
  let f := compactLogMellin g
  let u : ℕ → ℂ := fun j ↦ if j ≤ (i : ℕ) then tcoef m z ((i : ℕ) - j) * tcoef f z j else 0
  change tcoef (m * f) z i = ∑ j : Fin (zetaZeroOrder ρ),
    (if (j : ℕ) ≤ (i : ℕ) then tcoef m z ((i : ℕ) - (j : ℕ)) else 0) * tcoef f z j
  trans ∑ j : Fin (zetaZeroOrder ρ), u j
  · rw [tcoef_mul (analyticAt_compactLogMellin hφ hcφ _) (analyticAt_compactLogMellin hg hcg _),
      Fin.sum_univ_eq_sum_range]
    calc
      _ = ∑ j ∈ Finset.range ((i : ℕ) + 1), u j := by
        refine Finset.sum_congr rfl fun j hj ↦ ?_
        simp only [u, m, f, ite_eq_left (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))]
      _ = _ := Finset.sum_subset (Finset.range_mono i.isLt) fun j _ hj ↦ by
        simp only [u, ite_eq_right (fun h ↦ hj (Finset.mem_range.mpr (Nat.lt_succ_iff.mpr h)))]
  · exact Finset.sum_congr rfl fun j _ ↦ by dsimp only [u]; split <;> simp [*]

/-- The finite coordinate block (and hence its transpose) has trace equal to
multiplicity times the value of the Mellin multiplier at the shifted zero. -/
public theorem trace_rationalMellinDivisorJetBlock (φ : ℝ → ℂ) (ρ : criticalStripZetaZeros) :
    Matrix.trace (rationalMellinDivisorJetBlock φ ρ) =
      (zetaZeroOrder ρ : ℂ) * compactLogMellin φ (shiftedZetaZero ρ) := by
  simp [Matrix.trace, Matrix.diag, rationalMellinDivisorJetBlock, nsmul_eq_mul]

/-- Full size is not full rank: since the zero order is positive, the block
is singular exactly when the Mellin multiplier vanishes at the shifted zero. -/
public theorem det_rationalMellinDivisorJetBlock_eq_zero_iff (φ : ℝ → ℂ)
    (ρ : criticalStripZetaZeros) :
    (rationalMellinDivisorJetBlock φ ρ).det = 0 ↔
      compactLogMellin φ (shiftedZetaZero ρ) = 0 := by
  have htri : (rationalMellinDivisorJetBlock φ ρ).IsLowerTriangular := by
    intro i j hij
    have h : ¬ (j : ℕ) ≤ (i : ℕ) := Nat.not_le.mpr hij
    simp [rationalMellinDivisorJetBlock, h]
  rw [Matrix.det_of_isLowerTriangular _ htri]
  simpa [rationalMellinDivisorJetBlock] using
    (pow_eq_zero_iff (n := zetaZeroOrder ρ) (Nat.ne_of_gt (zetaZeroOrder_pos ρ)) :
      compactLogMellin φ (shiftedZetaZero ρ) ^ zetaZeroOrder ρ = 0 ↔ _)

end Masullo
