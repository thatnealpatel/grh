module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # A real polynomial killing a finite family of Mellin samples -/

open Polynomial

namespace Masullo

private noncomputable def mellinRootQuadratic (z : ℂ) : Polynomial ℝ :=
  X ^ 2 - C (2 * z.re) * X + C (Complex.normSq z)

private theorem mellinRootQuadratic_eval₂ (z : ℂ) :
    (mellinRootQuadratic z).eval₂ Complex.ofRealHom z = 0 := by
  simp only [mellinRootQuadratic, eval₂_add, eval₂_sub, eval₂_mul, eval₂_pow, eval₂_X,
    eval₂_C, Complex.ofRealHom_eq_coe]
  rw [← Complex.add_conj, ← Complex.mul_conj]
  ring

private theorem mellinRootQuadratic_eval_pos (z : ℂ) {x : ℝ} (h : z.re < x) :
    0 < (mellinRootQuadratic z).eval x := by
  simp only [mellinRootQuadratic, eval_add, eval_sub, eval_mul, eval_pow, eval_X, eval_C,
    Complex.normSq_apply]
  nlinarith [sq_pos_of_ne_zero (ne_of_gt (sub_pos.mpr h)), sq_nonneg z.im]

/-- Kill the two polar samples and every finite-family root, without killing the
real sample strictly to the right of both the poles and the family's real parts. -/
public theorem exists_real_polynomial_polar_and_finite_roots {ι : Type*} (A : Finset ι)
    (w : ι → ℂ) {x : ℝ} (hx : (1 / 2 : ℝ) < x) (hw : ∀ i ∈ A, (w i).re < x) :
    ∃ P : Polynomial ℝ, P.eval (1 / 2) = 0 ∧ 0 < P.eval x ∧
      P.eval₂ Complex.ofRealHom (1 / 2) = 0 ∧ P.eval₂ Complex.ofRealHom (-1 / 2) = 0 ∧
      ∀ i ∈ A, P.eval₂ Complex.ofRealHom (w i) = 0 := by
  let P := (X - C (1 / 2)) * (X + C (1 / 2)) * ∏ i ∈ A, mellinRootQuadratic (w i)
  refine ⟨P, ?_, ?_, ?_, ?_, ?_⟩
  · simp [P, eval_mul, eval_sub]
  · simp only [P, eval_mul, eval_sub, eval_add, eval_X, eval_C, eval_prod]
    have hpolar₁ := sub_pos.mpr hx
    have hpolar₂ : 0 < x + 1 / 2 := by linarith
    exact mul_pos (mul_pos hpolar₁ hpolar₂) <|
      Finset.prod_pos fun i hi ↦ mellinRootQuadratic_eval_pos (w i) (hw i hi)
  · norm_num [P, eval₂_mul, eval₂_sub, eval₂_C, eval₂_X]
  · norm_num [P, eval₂_mul, eval₂_add, eval₂_C, eval₂_X]
  · intro i hi
    simp only [P, eval₂_mul, eval₂_finsetProd]
    rw [Finset.prod_eq_zero hi (mellinRootQuadratic_eval₂ (w i)), mul_zero]

end Masullo
