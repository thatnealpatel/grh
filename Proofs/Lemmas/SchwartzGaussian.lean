module

public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-! # Isotropic Gaussian as a Schwartz function

Each Fréchet derivative of the Gaussian is the Gaussian times a temperate
multilinear coefficient. The coefficient estimates and the scalar exponential
bound do not require finite dimensionality or completeness.
-/

open scoped ContDiff SchwartzMap

namespace Masullo

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

private theorem temperateFderiv {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} (hf : f.HasTemperateGrowth) : (fderiv ℝ f).HasTemperateGrowth := by
  refine ⟨hf.1.fderiv_right (by simp), fun n ↦ ?_⟩
  simpa only [norm_iteratedFDeriv_fderiv] using hf.2 (n + 1)

private theorem temperateSmulRight {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {a : E → StrongDual ℝ E} {P : E → F} (ha : a.HasTemperateGrowth)
    (hP : P.HasTemperateGrowth) : (fun x ↦ (a x).smulRight (P x)).HasTemperateGrowth := by
  simpa only [ContinuousLinearMap.smulRightL_apply_apply] using
    ContinuousLinearMap.bilinear_hasTemperateGrowth (ContinuousLinearMap.smulRightL ℝ E F) ha hP

private theorem expDerivFactor {q : E → ℝ} (hq : q.HasTemperateGrowth) (n : ℕ) :
    ∃ P : E → (E [×n]→L[ℝ] ℝ), P.HasTemperateGrowth ∧
      ∀ x, iteratedFDeriv ℝ n (Real.exp ∘ q) x = Real.exp (q x) • P x := by
  induction n with
  | zero =>
    let U := (continuousMultilinearCurryFin0 ℝ E ℝ).symm
    refine ⟨fun _ ↦ U 1, .const _, fun x ↦ ?_⟩
    rw [iteratedFDeriv_zero_eq_comp]
    change U (Real.exp (q x)) = Real.exp (q x) • U 1
    rw [← U.map_smul, smul_eq_mul, mul_one]
  | succ n ih =>
    obtain ⟨P, hP, hEq⟩ := ih
    let U := (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) ↦ E) ℝ).symm
    -- After factoring out exp(q), the product rule leaves DP + Dq · P.
    let Q := fun x ↦ fderiv ℝ P x + (fderiv ℝ q x).smulRight (P x)
    have hQ : Q.HasTemperateGrowth :=
      (temperateFderiv hP).fun_add (temperateSmulRight (temperateFderiv hq) hP)
    refine ⟨U ∘ Q, U.toContinuousLinearEquiv.hasTemperateGrowth.comp hQ, fun x ↦ ?_⟩
    have hq' := (hq.1.differentiable (by simp) x).hasFDerivAt.exp
    have hP' := (hP.1.differentiable (by simp) x).hasFDerivAt
    have hFun : iteratedFDeriv ℝ n (Real.exp ∘ q) = (fun x ↦ Real.exp (q x)) • P :=
      funext hEq
    rw [iteratedFDeriv_succ_eq_comp_left, hFun, Function.comp_apply, (hq'.smul hP').fderiv]
    change U _ = Real.exp (q x) • U (Q x)
    rw [← U.map_smul]
    congr 1
    ext1 v
    simp only [Q, add_apply, smul_apply, ContinuousLinearMap.smulRight_apply, smul_add, smul_assoc]

/-- Absorb any polynomial weight into the Gaussian by the exponential series at `1 + r²`. -/
private theorem gaussianScalarBound (r : ℝ) (hr : 0 ≤ r) (m : ℕ) :
    (1 + r) ^ m * Real.exp (-r ^ 2) ≤ (2 : ℝ) ^ m * m.factorial * Real.exp 1 := by
  have hbase : 1 + r ≤ 2 * (1 + r ^ 2) := by nlinarith [sq_nonneg (r - 1)]
  have hfact : (0 : ℝ) < m.factorial := by exact_mod_cast Nat.factorial_pos m
  have hexp : (1 + r ^ 2) ^ m ≤ Real.exp (1 + r ^ 2) * m.factorial :=
    (div_le_iff₀ hfact).mp (Real.pow_div_factorial_le_exp (1 + r ^ 2) (by positivity) m)
  calc
    (1 + r) ^ m * Real.exp (-r ^ 2) ≤ (2 * (1 + r ^ 2)) ^ m * Real.exp (-r ^ 2) := by
      gcongr
    _ = (2 : ℝ) ^ m * (1 + r ^ 2) ^ m * Real.exp (-r ^ 2) := by rw [mul_pow]
    _ ≤ (2 : ℝ) ^ m * (Real.exp (1 + r ^ 2) * m.factorial) * Real.exp (-r ^ 2) := by
      gcongr
    _ = ((2 : ℝ) ^ m * m.factorial) * (Real.exp (1 + r ^ 2) * Real.exp (-r ^ 2)) := by ring
    _ = (2 : ℝ) ^ m * m.factorial * Real.exp 1 := by
      rw [← Real.exp_add, show (1 : ℝ) + r ^ 2 + (-r ^ 2) = 1 by ring]

private def realSchwartzGaussian (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] :
    𝓢(E, ℝ) where
  toFun := fun x ↦ Real.exp (- ‖x‖ ^ 2)
  smooth' := Real.contDiff_exp.comp (Function.hasTemperateGrowth_norm_sq E).1.neg
  decay' := by
    intro k n
    obtain ⟨P, hP, hEq⟩ := expDerivFactor (Function.hasTemperateGrowth_norm_sq E).fun_neg n
    obtain ⟨j, C, hC, hBound⟩ := hP.norm_iteratedFDeriv_le_uniform 0
    refine ⟨C * ((2 : ℝ) ^ (k + j) * (k + j).factorial * Real.exp 1), fun x ↦ ?_⟩
    have hPx : ‖P x‖ ≤ C * (1 + ‖x‖) ^ j := by simpa using hBound 0 le_rfl x
    change ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (Real.exp ∘ fun x : E ↦ - ‖x‖ ^ 2) x‖ ≤ _
    rw [hEq, norm_smul, Real.norm_of_nonneg (Real.exp_pos _).le]
    calc
      _ ≤ (1 + ‖x‖) ^ k * (Real.exp (- ‖x‖ ^ 2) * (C * (1 + ‖x‖) ^ j)) := by
        gcongr
        linarith
      _ = C * ((1 + ‖x‖) ^ (k + j) * Real.exp (- ‖x‖ ^ 2)) := by rw [pow_add]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (gaussianScalarBound _ (norm_nonneg x) _) hC

/-- The isotropic Gaussian `x ↦ exp (-‖x‖²)` on a real inner product space. -/
public noncomputable def schwartzGaussian (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] :
    𝓢(E, ℂ) := (realSchwartzGaussian E).postcompCLM Complex.ofRealCLM

@[simp] public theorem schwartzGaussian_apply
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] (x : E) :
    schwartzGaussian E x = (Real.exp (- ‖x‖ ^ 2) : ℂ) := by
  rw [schwartzGaussian, SchwartzMap.postcompCLM_apply]
  rfl

end

end Masullo
