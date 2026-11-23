module

public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Lemmas.EuclideanLatticePoisson
import Lemmas.LatticeSchwartzPeriodization
import Lemmas.SchwartzGaussian
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# Quartic Gaussian Poisson summation on the square lattice

The real inner product on `ℂ` gives the Fourier kernel with negative sign and the
basis `(1, I)` has covolume one. Differentiation in the combination `∂₁ + I ∂ᵢ`
annihilates the holomorphic polynomial factor, giving a simple Fourier recurrence.
-/

open Complex MeasureTheory Module
open scoped FourierTransform LineDeriv RealInnerProductSpace SchwartzMap

namespace Masullo

noncomputable section

private def gaussianDilation (b : ℝ) (hb : 0 < b) : ℂ ≃L[ℝ] ℂ :=
  (LinearEquiv.smulOfNeZero ℝ ℂ (Real.sqrt b) (Real.sqrt_pos.2 hb).ne').toContinuousLinearEquiv

private def monomialGaussian (b : ℝ) (hb : 0 < b) (n : ℕ) : 𝓢(ℂ, ℂ) :=
  SchwartzMap.bilinLeftCLM (ContinuousLinearMap.mul ℂ ℂ).flip
    ((ContinuousLinearMap.id ℝ ℂ).hasTemperateGrowth.pow n)
    (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (gaussianDilation b hb) (schwartzGaussian ℂ))

@[simp] private theorem monomialGaussian_apply {b : ℝ} (hb : 0 < b) (n : ℕ) (z : ℂ) :
    monomialGaussian b hb n z = z ^ n * (Real.exp (-b * ‖z‖ ^ 2) : ℂ) := by
  rw [monomialGaussian, SchwartzMap.bilinLeftCLM_apply,
    SchwartzMap.compCLMOfContinuousLinearEquiv_apply]
  change z ^ n * schwartzGaussian ℂ (gaussianDilation b hb z) = _
  rw [schwartzGaussian_apply]
  change z ^ n * (Real.exp (- ‖Real.sqrt b • z‖ ^ 2) : ℂ) = _
  rw [norm_smul, mul_pow, Real.norm_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt hb.le, neg_mul]

private theorem inner_one_left (z : ℂ) : ⟪(1 : ℂ), z⟫ = z.re := by simp

private theorem inner_I_left (z : ℂ) : ⟪I, z⟫ = z.im := by
  simp [Complex.mul_re]

private theorem inner_one_add_I_mul (z : ℂ) :
    (⟪z, (1 : ℂ)⟫ : ℂ) + I * (⟪z, I⟫ : ℂ) = z := by
  rw [← real_inner_comm z 1, ← real_inner_comm z I, inner_one_left, inner_I_left, mul_comm I]
  exact Complex.re_add_im z

private theorem lineDeriv_monomialGaussian {b : ℝ} (hb : 0 < b) (n : ℕ) (z v : ℂ) :
    ∂_{v} (monomialGaussian b hb n) z =
      ((n : ℂ) * z ^ (n - 1) * v + z ^ n * (-(2 * b : ℂ) * (⟪z, v⟫ : ℂ))) *
        (Real.exp (-b * ‖z‖ ^ 2) : ℂ) := by
  have hp := (hasFDerivAt_id (𝕜 := ℝ) z).pow n
  have hq := ((hasStrictFDerivAt_norm_sq z).hasFDerivAt.const_mul (-b)).exp
  have he := Complex.ofRealCLM.hasFDerivAt.comp z hq
  have h := hp.mul he
  change HasFDerivAt (fun x : ℂ ↦ x ^ n * (Real.exp (-b * ‖x‖ ^ 2) : ℂ)) _ z at h
  rw [SchwartzMap.lineDerivOp_apply,
    (monomialGaussian b hb n).differentiableAt.lineDeriv_eq_fderiv]
  have hf : (monomialGaussian b hb n : ℂ → ℂ) = _ := funext (monomialGaussian_apply hb n)
  rw [hf, h.fderiv]
  simp only [add_apply, smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply, id_eq, Function.comp_apply, innerSL_apply_apply,
    Complex.ofRealCLM_apply, nsmul_eq_mul, smul_eq_mul, Complex.ofReal_mul, Complex.ofReal_neg]
  push_cast
  ring

private theorem monomialGaussian_deriv_step {b : ℝ} (hb : 0 < b) (n : ℕ) :
    ∂_{(1 : ℂ)} (monomialGaussian b hb n) + I • ∂_{I} (monomialGaussian b hb n) =
      (-(2 * b) : ℂ) • monomialGaussian b hb (n + 1) := by
  ext1 z
  simp only [add_apply, smul_apply, smul_eq_mul,
    lineDeriv_monomialGaussian, monomialGaussian_apply]
  rw [pow_succ z n]
  linear_combination (norm := ring)
    (n : ℂ) * z ^ (n - 1) * (Real.exp (-b * ‖z‖ ^ 2) : ℂ) * Complex.I_sq +
    (-(2 * b) : ℂ) * z ^ n * (Real.exp (-b * ‖z‖ ^ 2) : ℂ) * inner_one_add_I_mul z

private theorem fourier_monomialGaussian_step {b : ℝ} (hb : 0 < b) (n : ℕ) (z : ℂ) :
    (𝓕 (monomialGaussian b hb (n + 1))) z =
      (-(Real.pi : ℂ) * I / b) * z * (𝓕 (monomialGaussian b hb n)) z := by
  have h := congrArg (fun f : 𝓢(ℂ, ℂ) ↦ (𝓕 f) z) (monomialGaussian_deriv_step hb n)
  simp only [FourierTransform.fourier_add, FourierTransform.fourier_smul,
    SchwartzMap.fourier_lineDerivOp_eq, add_apply, smul_apply] at h
  have ht (v : ℂ) : (inner ℝ · v).HasTemperateGrowth := ((innerSL ℝ).flip v).hasTemperateGrowth
  rw [SchwartzMap.smulLeftCLM_apply (ht 1), SchwartzMap.smulLeftCLM_apply (ht I)] at h
  simp only [smul_eq_mul, Complex.real_smul] at h
  have hb' : (b : ℂ) ≠ 0 := by exact_mod_cast hb.ne'
  field_simp [hb']
  linear_combination (norm := ring) (1 / 2 : ℂ) * h -
    (Real.pi : ℂ) * I * (𝓕 (monomialGaussian b hb n)) z * inner_one_add_I_mul z

private theorem fourier_monomialGaussian_zero {b : ℝ} (hb : 0 < b) (z : ℂ) :
    (𝓕 (monomialGaussian b hb 0)) z = ((Real.pi : ℂ) / b) *
      (Real.exp (-(Real.pi ^ 2 / b) * ‖z‖ ^ 2) : ℂ) := by
  rw [SchwartzMap.fourier_coe]
  have hf : (monomialGaussian b hb 0 : ℂ → ℂ) =
      fun v ↦ Complex.exp (-(b : ℂ) * (‖v‖ : ℂ) ^ 2) := by
    funext v
    simp only [monomialGaussian_apply, pow_zero, one_mul, Complex.ofReal_exp,
      Complex.ofReal_mul, Complex.ofReal_neg, Complex.ofReal_pow]
  rw [hf, fourier_gaussian_innerProductSpace (b := (b : ℂ)) (by simpa using hb),
    Complex.finrank_real_complex]
  norm_num only [Nat.cast_ofNat, show (2 : ℂ) / 2 = 1 by norm_num, Complex.cpow_one,
    Complex.ofReal_exp, Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_div, Complex.ofReal_neg]
  congr 2
  ring

private theorem fourier_monomialGaussian {b : ℝ} (hb : 0 < b) (n : ℕ) (z : ℂ) :
    (𝓕 (monomialGaussian b hb n)) z = (-(Real.pi : ℂ) * I / b) ^ n * z ^ n *
      (((Real.pi : ℂ) / b) * (Real.exp (-(Real.pi ^ 2 / b) * ‖z‖ ^ 2) : ℂ)) := by
  induction n with
  | zero => simpa only [pow_zero, one_mul] using fourier_monomialGaussian_zero hb z
  | succ n ih => rw [fourier_monomialGaussian_step hb, ih]; simp only [pow_succ]; ring

private theorem fourier_monomialGaussian_four {b : ℝ} (hb : 0 < b) (z : ℂ) :
    (𝓕 (monomialGaussian b hb 4)) z = ((Real.pi : ℂ) / b) ^ 5 *
      (z ^ 4 * (Real.exp (-(Real.pi ^ 2 / b) * ‖z‖ ^ 2) : ℂ)) := by
  rw [fourier_monomialGaussian hb, show -(Real.pi : ℂ) * I / b = ((Real.pi : ℂ) / b) * (-I) by ring,
    mul_pow, neg_pow, Complex.I_pow_four]
  ring

private def squareLattice : Submodule ℤ ℂ := Submodule.span ℤ (Set.range Complex.basisOneI)

private instance : DiscreteTopology squareLattice :=
  inferInstanceAs (DiscreteTopology (Submodule.span ℤ (Set.range Complex.basisOneI)))

private instance : IsZLattice ℝ squareLattice :=
  inferInstanceAs (IsZLattice ℝ (Submodule.span ℤ (Set.range Complex.basisOneI)))

private theorem squareLattice_covolume : ZLattice.covolume squareLattice volume = 1 := by
  rw [ZLattice.covolume_eq_measure_fundamentalDomain squareLattice volume
    (ZSpan.isAddFundamentalDomain Complex.basisOneI volume), measureReal_def,
    measure_congr (ZSpan.fundamentalDomain_ae_parallelepiped Complex.basisOneI volume),
    ← Complex.toBasis_orthonormalBasisOneI]
  change (volume (parallelepiped Complex.orthonormalBasisOneI)).toReal = 1
  rw [Complex.orthonormalBasisOneI.volume_parallelepiped, ENNReal.toReal_one]

private theorem squareLattice_selfDual : ZLattice.euclideanDual squareLattice = squareLattice := by
  ext z
  unfold squareLattice
  rw [ZLattice.mem_euclideanDual_iff_basis (Complex.basisOneI.restrictScalars ℤ),
    Complex.basisOneI.mem_span_iff_repr_mem ℤ]
  simp only [Basis.restrictScalars_apply, Complex.coe_basisOneI, Complex.coe_basisOneI_repr,
    Set.mem_range, algebraMap_int_eq]
  apply forall_congr'
  intro i
  fin_cases i
  · change (∃ m : ℤ, (m : ℝ) = ⟪(1 : ℂ), z⟫) ↔ ∃ m : ℤ, (m : ℝ) = z.re
    rw [inner_one_left]
  · change (∃ m : ℤ, (m : ℝ) = ⟪I, z⟫) ↔ ∃ m : ℤ, (m : ℝ) = z.im
    rw [inner_I_left]

private def rawSquarePoint (a : ℤ × ℤ) : ℂ := (a.1 : ℂ) + (a.2 : ℂ) * I

private def squareLatticeIndex : (ℤ × ℤ) ≃ squareLattice :=
  (finTwoArrowEquiv ℤ).symm.trans (Complex.basisOneI.restrictScalars ℤ).equivFun.symm.toEquiv

private theorem coe_squareLatticeIndex (a : ℤ × ℤ) :
    (squareLatticeIndex a : ℂ) = rawSquarePoint a := by
  change ((Complex.basisOneI.restrictScalars ℤ).equivFun.symm
    ((finTwoArrowEquiv ℤ).symm a) : ℂ) = _
  rw [Basis.equivFun_symm_apply, Submodule.coe_sum, Fin.sum_univ_two]
  simp [rawSquarePoint, Basis.restrictScalars_apply, zsmul_eq_mul]

private theorem squareLattice_tsum (g : ℂ → ℂ) :
    (∑' a : ℤ × ℤ, g (rawSquarePoint a)) = ∑' y : squareLattice, g (y : ℂ) := by
  calc
    (∑' a : ℤ × ℤ, g (rawSquarePoint a)) = ∑' a : ℤ × ℤ, g (squareLatticeIndex a : ℂ) :=
      tsum_congr fun a ↦ congrArg g (coe_squareLatticeIndex a).symm
    _ = ∑' y : squareLattice, g (y : ℂ) := squareLatticeIndex.tsum_eq (fun y ↦ g (y : ℂ))

private theorem squareLattice_poisson (f : 𝓢(ℂ, ℂ)) :
    (∑' a : ℤ × ℤ, f (rawSquarePoint a)) = ∑' a : ℤ × ℤ, (𝓕 f) (rawSquarePoint a) := by
  have hd (p : ℕ) : ∃ A ≥ (0 : ℝ), ∀ z, ‖z‖ ^ p * ‖f z‖ ≤ A := by
    obtain ⟨A, hA, h⟩ := f.decay p 0
    exact ⟨A, hA.le, by simpa only [norm_iteratedFDeriv_zero] using h⟩
  have hs : Summable (fun y : ZLattice.euclideanDual squareLattice ↦ 𝓕 (f : ℂ → ℂ) (y : ℂ)) := by
    rw [squareLattice_selfDual]
    simpa only [SchwartzMap.fourier_coe, zero_add] using
      (summable_norm_schwartz_lattice_add squareLattice (𝓕 f) 0).of_norm
  have h := ZLattice.tsum_eq_covolume_inv_smul_tsum_fourier squareLattice (f : ℂ → ℂ)
    f.continuous f.integrable hd hs
  rw [squareLattice_covolume, inv_one, one_smul, squareLattice_selfDual] at h
  have h' : (∑' x : squareLattice, f (x : ℂ)) = ∑' y : squareLattice, (𝓕 f) (y : ℂ) := by
    simpa only [SchwartzMap.fourier_coe] using h
  exact (squareLattice_tsum f).trans (h'.trans (squareLattice_tsum ⇑(𝓕 f : 𝓢(ℂ, ℂ))).symm)

private theorem quarticTheta_poisson_width {b : ℝ} (hb : 0 < b) :
    (∑' a : ℤ × ℤ, (rawSquarePoint a) ^ 4 * (Real.exp (-b * ‖rawSquarePoint a‖ ^ 2) : ℂ)) =
      ((Real.pi : ℂ) / b) ^ 5 * ∑' a : ℤ × ℤ,
        (rawSquarePoint a) ^ 4 * (Real.exp (-(Real.pi ^ 2 / b) * ‖rawSquarePoint a‖ ^ 2) : ℂ) := by
  simpa only [monomialGaussian_apply, fourier_monomialGaussian_four, tsum_mul_left] using
    squareLattice_poisson (monomialGaussian b hb 4)

/-- The square-lattice quartic Gaussian Poisson identity, in the negative-log scaling.
The index includes `(0, 0)`, whose quartic weight is zero. -/
public theorem quarticTheta_poisson (x : ℝ) (_hx : x < 0) :
    (∑' a : ℤ × ℤ, ((Real.exp (x / 2) : ℂ) * ((a.1 : ℂ) + (a.2 : ℂ) * I)) ^ 4 *
      (Real.exp (-(2 * Real.pi * ‖(Real.exp (x / 2) : ℂ) * ((a.1 : ℂ) + (a.2 : ℂ) * I)‖ ^ 2)) : ℂ)) =
      (1 / 32 : ℂ) * (Real.exp (-3 * x) : ℂ) * ∑' a : ℤ × ℤ,
        ((a.1 : ℂ) + (a.2 : ℂ) * I) ^ 4 *
          (Real.exp (-(Real.pi / 2 * Real.exp (-x) * ‖((a.1 : ℂ) + (a.2 : ℂ) * I)‖ ^ 2)) : ℂ) := by
  let b := 2 * Real.pi * Real.exp x
  have hb : 0 < b := by dsimp [b]; positivity
  have hwidth : Real.pi ^ 2 / b = Real.pi / 2 * Real.exp (-x) := by
    rw [Real.exp_neg]
    dsimp [b]
    field_simp [Real.pi_ne_zero, (Real.exp_pos x).ne']
  have hscale (z : ℂ) : 2 * Real.pi * ‖(Real.exp (x / 2) : ℂ) * z‖ ^ 2 = b * ‖z‖ ^ 2 := by
    rw [norm_mul, mul_pow, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le,
      ← Real.exp_nat_mul]
    norm_num only [Nat.cast_ofNat]
    rw [show (2 : ℝ) * (x / 2) = x by ring]
    dsimp [b]
    ring
  have hfactor : (Real.exp (x / 2) : ℂ) ^ 4 * ((Real.pi : ℂ) / b) ^ 5 =
      (1 / 32 : ℂ) * (Real.exp (-3 * x) : ℂ) := by
    have hratio : Real.pi / b = (2 * Real.exp x)⁻¹ := by
      dsimp [b]
      field_simp [Real.pi_ne_zero, (Real.exp_pos x).ne']
    have hreal : Real.exp (x / 2) ^ 4 * (Real.pi / b) ^ 5 = 1 / 32 * Real.exp (-3 * x) := by
      rw [hratio, inv_pow, mul_pow, mul_inv, ← Real.exp_nat_mul (x / 2),
        ← Real.exp_nat_mul x, ← Real.exp_neg]
      norm_num only [Nat.cast_ofNat, Nat.reducePow]
      rw [show (4 : ℝ) * (x / 2) = 2 * x by ring]
      calc
        _ = 1 / 32 * (Real.exp (2 * x) * Real.exp (-(5 * x))) := by ring
        _ = _ := by rw [← Real.exp_add, show 2 * x + -(5 * x) = -3 * x by ring]
    simpa only [Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_pow, Complex.ofReal_one,
      Complex.ofReal_ofNat] using congrArg (fun r : ℝ ↦ (r : ℂ)) hreal
  change (∑' a : ℤ × ℤ, ((Real.exp (x / 2) : ℂ) * rawSquarePoint a) ^ 4 *
    (Real.exp (-(2 * Real.pi * ‖(Real.exp (x / 2) : ℂ) * rawSquarePoint a‖ ^ 2)) : ℂ)) =
      (1 / 32 : ℂ) * (Real.exp (-3 * x) : ℂ) * ∑' a : ℤ × ℤ,
        (rawSquarePoint a) ^ 4 *
          (Real.exp (-(Real.pi / 2 * Real.exp (-x) * ‖rawSquarePoint a‖ ^ 2)) : ℂ)
  have hleft : (∑' a : ℤ × ℤ, ((Real.exp (x / 2) : ℂ) * rawSquarePoint a) ^ 4 *
      (Real.exp (-(2 * Real.pi * ‖(Real.exp (x / 2) : ℂ) * rawSquarePoint a‖ ^ 2)) : ℂ)) =
      (Real.exp (x / 2) : ℂ) ^ 4 * ∑' a : ℤ × ℤ,
        (rawSquarePoint a) ^ 4 * (Real.exp (-b * ‖rawSquarePoint a‖ ^ 2) : ℂ) := by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro a
    rw [mul_pow, hscale, neg_mul, mul_assoc]
  rw [hleft, quarticTheta_poisson_width hb, hwidth, ← mul_assoc, hfactor]
  simp only [neg_mul]

end

end Masullo
