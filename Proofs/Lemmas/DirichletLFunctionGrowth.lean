module

public import Lemmas.BoundedMellinTail
public import Lemmas.DirichletPeriodicPrimitives
public import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Lemmas.BoundedPrimitiveIntegral
import Mathlib.Analysis.Complex.Convex
import Mathlib.NumberTheory.LSeries.SumCoeff

/-!
# Five centered primitives for a Dirichlet L-function

The partial-summation identity continues to `re s > -5`. After removing
its polynomial prefactor, the last integral has a uniform bound on the
closed half-plane `re s ≥ -4`.
-/

open Complex Filter Set
open scoped BigOperators

namespace Masullo

/-- Recursively integrate the previous function minus its period mean, starting
from the character's step partial sums. Every positive stage vanishes at `1`. -/
@[expose] public noncomputable def dirichletPrimitiveIter {q : ℕ}
    (χ : DirichletCharacter ℂ q) : ℕ → ℝ → ℂ
  | 0 => dirichletPartialSum χ
  | n + 1 => dirichletPrimitive q (dirichletPrimitiveIter χ n)

private theorem dirichletPrimitiveIter_data {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (n : ℕ) :
    PeriodicPrimitiveData q (dirichletPrimitiveIter χ n) := by
  induction n with
  | zero => exact dirichletPartialSum_data χ hχ
  | succ n ih => exact ih.primitive

/-- The monic rising product `(s)_n`, including `(s)_0 = 1`. -/
@[expose] public noncomputable def dirichletRising (s : ℂ) (n : ℕ) : ℂ :=
  ∏ j ∈ Finset.range n, (s + (j : ℂ))

private theorem dirichletRising_succ (s : ℂ) (n : ℕ) :
    dirichletRising s (n + 1) = dirichletRising s n * (s + (n : ℂ)) :=
  Finset.prod_range_succ _ _

private theorem LFunction_eq_firstTail {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) {s : ℂ} (hs : 1 < s.re) :
    χ.LFunction s = s * boundedMellinTail (dirichletPrimitiveIter χ 0) s := by
  obtain ⟨B, -, hB⟩ := (dirichletPartialSum_data χ hχ).bounded
  have hO : (fun n : ℕ ↦ ∑ k ∈ Finset.Icc 1 n, χ (k : ZMod q)) =O[atTop]
      fun n ↦ (n : ℝ) ^ (0 : ℝ) := by
    refine Asymptotics.IsBigO.of_bound B ?_
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
    simpa [dirichletPartialSum] using hB (n : ℝ) hn'
  rw [χ.LFunction_eq_LSeries hs]
  exact LSeries_eq_mul_integral _ le_rfl (zero_lt_one.trans hs)
    (χ.LSeriesSummable_of_one_lt_re hs) hO

private theorem LFunction_eq_iteratedTail {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) {s : ℂ} (hs : 1 < s.re) (n : ℕ) :
    χ.LFunction s =
      (∑ j ∈ Finset.range n, dirichletMean q (dirichletPrimitiveIter χ j) * dirichletRising s j) +
      dirichletRising s (n + 1) * boundedMellinTail (dirichletPrimitiveIter χ n) (s + (n : ℂ)) := by
  induction n with
  | zero => simpa [dirichletRising] using LFunction_eq_firstTail χ hχ hs
  | succ n ih =>
    let A := dirichletPrimitiveIter χ n
    let B := dirichletPrimitiveIter χ (n + 1)
    have hA := dirichletPrimitiveIter_data χ hχ n
    have hB := dirichletPrimitiveIter_data χ hχ (n + 1)
    have hw : 0 < (s + (n : ℂ)).re := by
      simp only [add_re, natCast_re]
      linarith [Nat.cast_nonneg (α := ℝ) n]
    have hstep := boundedPrimitive_integral_step (A := A) (B := B) (a := dirichletMean q A)
      hA.measurable hA.bounded hA.rightContinuous (fun _ ↦ rfl) hB.bounded hw
    have hshift : s + (↑(n + 1) : ℂ) = s + (n : ℂ) + 1 := by push_cast; ring
    have hstep' :
        (s + (n : ℂ)) * boundedMellinTail A (s + (n : ℂ)) =
          dirichletMean q A + (s + (n : ℂ)) * (s + (n : ℂ) + 1) *
            boundedMellinTail B (s + (n : ℂ) + 1) := by
      simpa only [boundedMellinTail, add_assoc, one_add_one_eq_two] using hstep
    rw [ih, Finset.sum_range_succ, dirichletRising_succ s (n + 1),
      dirichletRising_succ s n, hshift]
    change _ + dirichletRising s n * (s + (n : ℂ)) * boundedMellinTail A (s + (n : ℂ)) = _
    rw [mul_assoc (dirichletRising s n), hstep']
    ring

/-- Partial summation and five centered periodic primitives give this identity
for Mathlib's continued L-function, not just the convergent Dirichlet series. -/
public theorem dirichlet_LFunction_eq_five_primitives {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) {s : ℂ} (hs : -5 < s.re) :
    χ.LFunction s =
      (∑ j ∈ Finset.range 5, dirichletMean q (dirichletPrimitiveIter χ j) * dirichletRising s j) +
      dirichletRising s 6 * boundedMellinTail (dirichletPrimitiveIter χ 5) (s + 5) := by
  let U : Set ℂ := {z | -5 < z.re}
  let F : ℂ → ℂ := fun z ↦
    (∑ j ∈ Finset.range 5, dirichletMean q (dirichletPrimitiveIter χ j) * dirichletRising z j) +
    dirichletRising z 6 * boundedMellinTail (dirichletPrimitiveIter χ 5) (z + 5)
  have hU : IsOpen U := continuous_re.isOpen_preimage (Ioi (-5)) isOpen_Ioi
  obtain ⟨M, hM, hB⟩ := (dirichletPrimitiveIter_data χ hχ 5).bounded
  have hTail : DifferentiableOn ℂ
      (boundedMellinTail (dirichletPrimitiveIter χ 5)) {w | 0 < w.re} :=
    boundedMellinTail_differentiableOn (dirichletPrimitiveIter_data χ hχ 5).measurable hM hB
  have hShift : DifferentiableOn ℂ (fun z ↦ z + (5 : ℂ)) U :=
    (by fun_prop : Differentiable ℂ (fun z ↦ z + (5 : ℂ))).differentiableOn
  have hComp : DifferentiableOn ℂ
      (fun z ↦ boundedMellinTail (dirichletPrimitiveIter χ 5) (z + 5)) U := by
    apply hTail.comp hShift
    intro z hz
    change -5 < z.re at hz
    change 0 < (z + 5).re
    have h : (5 : ℂ).re = 5 := by norm_num
    rw [add_re, h]
    linarith
  have hProd (n : ℕ) : Differentiable ℂ (fun z ↦ dirichletRising z n) := by
    unfold dirichletRising
    fun_prop
  have hF : DifferentiableOn ℂ F U := by
    refine DifferentiableOn.add ?_ ((hProd 6).differentiableOn.mul hComp)
    apply DifferentiableOn.fun_sum
    intro j _
    exact (differentiableOn_const (dirichletMean q (dirichletPrimitiveIter χ j))).mul
      (hProd j).differentiableOn
  refine AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq
    (fun z _ ↦ (χ.differentiable_LFunction hχ).analyticAt z) (hF.analyticOnNhd hU)
    (convex_halfSpace_re_gt (-5)).isPreconnected (z₀ := 2) (by norm_num [U]) ?_ hs
  refine eventually_of_mem ((continuous_re.isOpen_preimage (Ioi 1) isOpen_Ioi).mem_nhds
    (show (2 : ℂ) ∈ re ⁻¹' Ioi 1 by simp)) ?_
  intro z hz
  simpa [F] using LFunction_eq_iteratedTail χ hχ hz 5

private theorem norm_dirichletRising_le (s : ℂ) (n : ℕ) (hn : n ≤ 6) :
    ‖dirichletRising s n‖ ≤ (‖s‖ + 6) ^ n := by
  rw [dirichletRising, norm_prod, ← show (∏ _j ∈ Finset.range n, (‖s‖ + 6)) = (‖s‖ + 6) ^ n by simp]
  refine Finset.prod_le_prod₀ (fun j _ ↦ norm_nonneg (s + (j : ℂ))) (fun j hj ↦ ?_)
  have hj' : (j : ℝ) ≤ 6 := by exact_mod_cast (Finset.mem_range.mp hj).le.trans hn
  calc
    ‖s + (j : ℂ)‖ ≤ ‖s‖ + ‖(j : ℂ)‖ := norm_add_le _ _
    _ ≤ ‖s‖ + 6 := by simpa only [Complex.norm_natCast] using add_le_add (le_refl ‖s‖) hj'

/-- The remainder integral without its degree-six prefactor has one bound
on `re s ≥ -4`, including the boundary. -/
public theorem exists_norm_dirichlet_five_primitive_tail_le {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ s : ℂ, -4 ≤ s.re →
      ‖boundedMellinTail (dirichletPrimitiveIter χ 5) (s + 5)‖ ≤ M := by
  have hA := dirichletPrimitiveIter_data χ hχ 5
  obtain ⟨M, hM, hB⟩ := hA.bounded
  refine ⟨M, hM, fun s hs ↦ norm_boundedMellinTail_le hA.measurable hM hB ?_⟩
  have h5 : (5 : ℂ).re = 5 := by norm_num
  rw [add_re, h5]
  linarith

/-- Uniform polynomial growth for a nontrivial Dirichlet L-function on the
closed half-plane. The exponent six comes from the last rising product. -/
public theorem exists_dirichlet_LFunction_growth_closed_halfPlane {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ s : ℂ, -4 ≤ s.re → ‖χ.LFunction s‖ ≤ C * (‖s‖ + 6) ^ 6 := by
  let a : ℕ → ℂ := fun j ↦ dirichletMean q (dirichletPrimitiveIter χ j)
  obtain ⟨M, hM, hB⟩ := exists_norm_dirichlet_five_primitive_tail_le χ hχ
  have ha : 0 ≤ ∑ j ∈ Finset.range 5, ‖a j‖ := Finset.sum_nonneg fun _ _ ↦ norm_nonneg _
  refine ⟨1 + (∑ j ∈ Finset.range 5, ‖a j‖) + M, by linarith, fun s hs ↦ ?_⟩
  have hs' : -5 < s.re := by linarith
  have hbase : 1 ≤ ‖s‖ + 6 := by linarith [norm_nonneg s]
  let R := (‖s‖ + 6) ^ 6
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hsum : ‖∑ j ∈ Finset.range 5, a j * dirichletRising s j‖ ≤
      (∑ j ∈ Finset.range 5, ‖a j‖) * R := by
    rw [Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j hj ↦ ?_)
    have hj' : j ≤ 6 := (Finset.mem_range.mp hj).le.trans (by decide)
    rw [norm_mul]
    refine mul_le_mul_of_nonneg_left ((norm_dirichletRising_le s j hj').trans ?_) (norm_nonneg _)
    exact pow_le_pow_right₀ hbase hj'
  have hrem : ‖dirichletRising s 6 * boundedMellinTail (dirichletPrimitiveIter χ 5) (s + 5)‖
      ≤ R * M := by
    rw [norm_mul]
    exact mul_le_mul (norm_dirichletRising_le s 6 le_rfl) (hB s hs) (norm_nonneg _) hR
  rw [dirichlet_LFunction_eq_five_primitives χ hχ hs']
  refine (norm_add_le _ _).trans ?_
  calc
    _ ≤ (∑ j ∈ Finset.range 5, ‖a j‖) * R + R * M := add_le_add hsum hrem
    _ ≤ (1 + (∑ j ∈ Finset.range 5, ‖a j‖) + M) * R := by nlinarith

end Masullo
