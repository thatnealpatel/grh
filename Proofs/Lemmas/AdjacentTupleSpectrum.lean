module

public import Lemmas.AdjacentTupleCellSquare
public import Lemmas.SignedBlockIntervalMoment
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! # Spectral identity for adjacent tuple cells

Source: `233d4a52:.godel/bob/adjacent-tuple-cells.md:5–23`, specifically the
spectral identity for the adjacent-cell square in Necessary cost (1).
This file proves the identity for finite indexed atoms and specializes it to
ordered tuples. It does not prove the lower bound (1) or its freezing step.
The weights are arbitrary nonnegative reals, and locations may repeat.
Owning check session: `01a209a4-4028-76c1-a295-487f5bedcbac`.
-/

open MeasureTheory
open scoped BigOperators ComplexConjugate NNReal

namespace Masullo.AdjacentTupleSpectrum

open AdjacentTupleCell (mass pairSum tent)
open SignedBlockIntervalMoment (phase sincKernel triangle)

/-- The source kernel at scale `U`, with the unnormalized sinc `sin v / v`. -/
@[expose] public noncomputable def kernel (U u : ℝ) : ℝ :=
  (Real.sinc (u / U) ^ 2 - Real.sinc (2 * u / U) ^ 2) / U

-- The two signed-block kernels have tent radii `2 / U` and `4 / U`, respectively.
private theorem scaled_kernel_eq {U : ℝ} (hU : 0 < U) (u : ℝ) :
    (2 / Real.pi) * kernel U u = 2 * sincKernel (40 * U) u - sincKernel (20 * U) u := by
  have h₁ : 80 * u / (2 * (40 * U)) = u / U := by field_simp [hU.ne']; ring
  have h₂ : 80 * u / (2 * (20 * U)) = 2 * u / U := by field_simp [hU.ne']; ring
  simp only [kernel, sincKernel, h₁, h₂]
  field_simp [hU.ne', Real.pi_ne_zero]
  ring

private theorem integrable_angular_mul {f : ℝ → ℝ} (hf : Integrable f) (ν : ℝ) :
    Integrable (fun u ↦ (f u : ℂ) * phase (u * ν)) := by
  have hcont : Continuous (fun u ↦ phase (u * ν)) := by
    unfold phase
    fun_prop
  refine hf.ofReal.mul_bdd (c := 1) hcont.aestronglyMeasurable ?_
  exact Filter.Eventually.of_forall fun u ↦ by simp [phase, Complex.norm_exp, Complex.mul_re]

private theorem integrable_scaled_kernel {U : ℝ} (hU : 0 < U) :
    Integrable (fun u ↦ (2 / Real.pi) * kernel U u) := by
  simp_rw [scaled_kernel_eq hU]
  exact ((SignedBlockIntervalMoment.integrable_sincKernel (mul_pos (by norm_num) hU)).const_mul 2).sub
    (SignedBlockIntervalMoment.integrable_sincKernel (mul_pos (by norm_num) hU))

private theorem scaled_kernel_transform {U : ℝ} (hU : 0 < U) (ν : ℝ) :
    (∫ u, (((2 / Real.pi) * kernel U u : ℝ) : ℂ) * phase (u * ν)) =
      ((2 * tent (2 / U) ν - tent (2 * (2 / U)) ν : ℝ) : ℂ) := by
  have h40 : 0 < 40 * U := mul_pos (by norm_num) hU
  have h20 : 0 < 20 * U := mul_pos (by norm_num) hU
  have h₁ := integrable_angular_mul (SignedBlockIntervalMoment.integrable_sincKernel h40) ν
  have h₂ := integrable_angular_mul (SignedBlockIntervalMoment.integrable_sincKernel h20) ν
  simp_rw [scaled_kernel_eq hU, Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_ofNat,
    sub_mul, mul_assoc]
  rw [integral_sub (h₁.const_mul 2) h₂, integral_const_mul,
    SignedBlockIntervalMoment.sincKernel_transform h40,
    SignedBlockIntervalMoment.sincKernel_transform h20]
  have hw₁ : 80 / (40 * U) = 2 / U := by field_simp [hU.ne']; ring
  have hw₂ : 80 / (20 * U) = 2 * (2 / U) := by field_simp [hU.ne']; ring
  simp only [triangle, tent, hw₁, hw₂, max_comm]

variable {ι : Type*} [Fintype ι]

/-- The weighted angular exponential sum, counting every atom index. -/
@[expose] public noncomputable def atomSum (y : ι → ℝ) (w : ι → ℝ≥0) (u : ℝ) : ℂ :=
  ∑ i, ((w i : ℝ) : ℂ) * phase (u * y i)

private theorem phase_add (a b : ℝ) : phase (a + b) = phase a * phase b := by
  simp only [phase, Complex.ofReal_add, add_mul, Complex.exp_add]

private theorem phase_neg (a : ℝ) : phase (-a) = conj (phase a) := by
  rw [phase, phase, ← Complex.exp_conj]
  simp

private theorem norm_atomSum_sq (y : ι → ℝ) (w : ι → ℝ≥0) (u : ℝ) :
    (↑(‖atomSum y w u‖ ^ 2) : ℂ) =
      ∑ i, ∑ j, (↑((w i : ℝ) * (w j : ℝ)) : ℂ) * phase (u * (y i - y j)) := by
  rw [← Complex.normSq_eq_norm_sq, ← Complex.mul_conj]
  simp only [atomSum, map_sum, map_mul, Complex.conj_ofReal, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
  rw [← phase_neg, mul_sub, sub_eq_add_neg, phase_add, Complex.ofReal_mul]
  ring

/-- The normalized spectral moment equals the adjacent-cell square for arbitrary
finite indexed atoms, with `δ = 2 / U`. -/
public theorem integral_kernel_norm_atomSum_sq (y : ι → ℝ) (w : ι → ℝ≥0)
    {U : ℝ} (hU : 0 < U) :
    let δ := 2 / U
    (2 / Real.pi) * (∫ u, kernel U u * ‖atomSum y w u‖ ^ 2) =
      (1 / (2 * δ)) * (∫ x, (mass y w δ x - mass y w δ (x + δ)) ^ 2) := by
  dsimp only
  rw [AdjacentTupleCell.normalized_integral_adjacent_mass_sub_sq y w (div_pos two_pos hU)]
  let c (i j : ι) : ℝ := (w i : ℝ) * (w j : ℝ)
  let A (i j : ι) (u : ℝ) : ℂ :=
    (c i j : ℂ) * ((((2 / Real.pi) * kernel U u : ℝ) : ℂ) * phase (u * (y i - y j)))
  have hA (i j : ι) : Integrable (A i j) :=
    (integrable_angular_mul (integrable_scaled_kernel hU) (y i - y j)).const_mul _
  apply Complex.ofReal_injective
  calc
    _ = ∫ u, (↑(((2 / Real.pi) * kernel U u) * ‖atomSum y w u‖ ^ 2 : ℝ) : ℂ) := by
      rw [← integral_const_mul]
      simp only [mul_assoc]
      exact (integral_ofReal (𝕜 := ℂ)).symm
    _ = ∫ u, ∑ i, ∑ j, A i j u := by
      apply integral_congr_ae
      filter_upwards with u
      rw [Complex.ofReal_mul, norm_atomSum_sq, Finset.mul_sum]
      simp only [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
      dsimp only [A, c]
      rw [mul_left_comm]
    _ = ∑ i, ∑ j, ∫ u, A i j u := by
      rw [integral_finsetSum _ (fun i _ ↦ integrable_finsetSum _ fun j _ ↦ hA i j)]
      exact Finset.sum_congr rfl fun i _ ↦ integral_finsetSum _ fun j _ ↦ hA i j
    _ = (↑(∑ i, ∑ j, c i j * (2 * tent (2 / U) (y i - y j) -
        tent (2 * (2 / U)) (y i - y j))) : ℂ) := by
      simp only [A, integral_const_mul, scaled_kernel_transform hU, Complex.ofReal_sum]
      simp only [Complex.ofReal_mul]
    _ = _ := by
      congr 1
      simp only [pairSum, Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
      dsimp only [c]
      ring

private theorem atomSum_tuple (y : ι → ℝ) (w : ι → ℝ≥0) (h : ℕ) (u : ℝ) :
    atomSum (fun a : Fin h → ι ↦ ∑ j, y (a j)) (fun a ↦ ∏ j, w (a j)) u =
      atomSum y w u ^ h := by
  classical
  rw [← Fin.prod_const h (atomSum y w u)]
  unfold atomSum
  rw [Fintype.prod_sum]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  simp only [phase, Finset.mul_sum, Complex.ofReal_sum, Finset.sum_mul, Complex.exp_sum,
    NNReal.coe_prod, Complex.ofReal_prod, Finset.prod_mul_distrib]

/-- For ordered `h`-tuples with product weights and summed labels, the spectral
integrand is the source `K(u) |Z(u)|^(2h)`, with `Z = atomSum y w`. -/
public theorem integral_kernel_norm_atomSum_pow (y : ι → ℝ) (w : ι → ℝ≥0) (h : ℕ)
    {U : ℝ} (hU : 0 < U) :
    let δ := 2 / U
    let m := mass (fun a : Fin h → ι ↦ ∑ j, y (a j)) (fun a ↦ ∏ j, w (a j)) δ
    (2 / Real.pi) * (∫ u, kernel U u * ‖atomSum y w u‖ ^ (2 * h)) =
      (1 / (2 * δ)) * (∫ x, (m x - m (x + δ)) ^ 2) := by
  simpa only [atomSum_tuple, norm_pow, ← pow_mul, Nat.mul_comm h 2] using
    integral_kernel_norm_atomSum_sq (fun a : Fin h → ι ↦ ∑ j, y (a j))
      (fun a ↦ ∏ j, w (a j)) hU

end Masullo.AdjacentTupleSpectrum
