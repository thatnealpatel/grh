module

public import Lemmas.WindowSynthesis
public import Lemmas.RankOneSeries
public import Lemmas.TranslatedKernel
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.MeasureTheory.Function.L2Space

open MeasureTheory Filter InnerProductSpace
open scoped InnerProductSpace ComplexConjugate

namespace Masullo.OperatorTrace
noncomputable section
variable {L : ℝ} [Fact (0 < L)] {μ : Measure ℝ}
local notation "H" => Lp ℂ 2 μ

/-- Cut off the output character, including its Fourier coefficient. -/
@[expose] public def outputMode (p : H) (f : C(AddCircle L, ℂ)) (k : ℤ) : H :=
  fourierCoeff f k • W (L := L) p (fourier k)

private theorem mode_sum (p q : H) (f : C(AddCircle L, ℂ)) (hf : Summable (fourierCoeff f)) :
    Summable (fun k : ℤ => ‖outputMode p f k‖ * ‖W (L := L) q (fourier k)‖) := by
  apply ((hf.norm.mul_right ‖p‖).mul_right ‖q‖).of_nonneg_of_le (fun _ => by positivity)
  intro k
  simp only [outputMode, norm_smul]
  gcongr <;> apply norm_W_fourier_le

/-- Windowed convolution by a periodic kernel. The separate kernel theorem
identifies this operator-norm synthesis with its convolution integral. -/
public def windowKernel (p q : H) (f : C(AddCircle L, ℂ)) : H →L[ℂ] H :=
  ∑' k : ℤ, rankOne ℂ (outputMode p f k) (W q (fourier (T := L) k))

private theorem windowKernel_synthesis (p q : H) (f : C(AddCircle L, ℂ))
    (hf : Summable (fourierCoeff f)) (z : H) :
    HasSum (fun k : ℤ => ⟪W (L := L) q (fourier k), z⟫_ℂ • outputMode p f k)
      (windowKernel p q f z) := by
  have h : Summable (fun k : ℤ => rankOne ℂ (outputMode p f k) (W (L := L) q (fourier k))) := by
    apply Summable.of_norm
    simpa only [norm_rankOne] using mode_sum p q f hf
  exact h.hasSum.mapL (ContinuousLinearMap.apply ℂ H z)

private theorem window_inner (q z : H) (k : ℤ) :
    ⟪W (L := L) q (fourier k), z⟫_ℂ =
      ∫ y, conj (fourier k (y : AddCircle L)) * ⟪q y, z y⟫_ℂ ∂μ := by
  rw [MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [W_apply_ae q (fourier (T := L) k)] with y hy
  simp only [hy, RCLike.inner_apply, map_mul]
  ring

/-- The series computes an actual integral on the real line, including the
input window, with no pointwise assertion about representatives of `Lp`. -/
public theorem windowKernel_ae (p q : H) (f : C(AddCircle L, ℂ)) (hf : Summable (fourierCoeff f))
    (z : H) : (windowKernel p q f z : ℝ → ℂ) =ᵐ[μ]
      (fun x : ℝ => p x * ∫ y, f ((x : AddCircle L) - (y : AddCircle L)) * ⟪q y, z y⟫_ℂ ∂μ) := by
  let s (k : ℤ) : C(AddCircle L, ℂ) :=
    (fourierCoeff f k * ⟪W q (fourier (T := L) k), z⟫_ℂ) • fourier k
  have hs : Summable s := by
    apply Summable.of_norm_bounded ((hf.norm.mul_right ‖q‖).mul_right ‖z‖)
    intro k
    simp only [s, norm_smul, fourier_norm, mul_one, norm_mul, mul_assoc]
    gcongr
    exact (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right (norm_W_fourier_le q k) (norm_nonneg _))
  have hW : W p (∑' k, s k) = windowKernel p q f z := by
    apply (hs.hasSum.mapL (W p)).unique
    simpa only [s, map_smul, outputMode, smul_smul, mul_comm] using windowKernel_synthesis p q f hf z
  have hev (x : AddCircle L) : (∑' k, s k) x = ∫ y, f (x - (y : AddCircle L)) * ⟪q y, z y⟫_ℂ ∂μ := by
    apply (hs.hasSum.mapL (ContinuousMap.evalCLM ℂ x)).unique
    simpa only [s, ContinuousMap.evalCLM_apply, ContinuousMap.smul_apply, smul_eq_mul, window_inner] using
      hasSum_translated_integral f hf (MeasureTheory.L2.integrable_inner q z) x
  rw [← hW]
  simpa only [hev] using W_apply_ae p (∑' k, s k)

/-- Explicit Riesz vectors for the projected operator. The adjoint acts on
input modes only; when `Q` is an orthogonal projection this adjoint is `Q`. -/
public theorem windowKernel_rankOne {p q : H} {f : C(AddCircle L, ℂ)} (hf : Summable (fourierCoeff f))
    (Q : H →L[ℂ] H) :
    let term := fun k : ℤ => rankOne ℂ (outputMode p f k) (Q.adjoint (W (L := L) q (fourier k)))
    (Summable fun k => ‖term k‖) ∧ HasSum term ((windowKernel p q f).comp Q) := by
  let v k := W (L := L) q (fourier k)
  let a k := innerSL ℂ (v k)
  have h := hasSum_rankOne_comp (windowKernel p q f) Q (outputMode p f) a
    (by simpa only [a, v, innerSL_apply_norm] using mode_sum p q f hf)
    (windowKernel_synthesis p q f hf)
  have he (k : ℤ) : (toDual ℂ H).symm ((a k).comp Q) = Q.adjoint (v k) := by
    apply ext_inner_right ℂ
    intro x
    rw [toDual_symm_apply, Q.adjoint_inner_left]
    rfl
  simpa only [he, v] using h

/-- For any bounded operator on the right, the actual Hilbert diagonal and
its scalar trace series. No commutation with the convolution is used. -/
public theorem windowKernel_trace {ι : Type*} (b : HilbertBasis ι ℂ H) (p q : H)
    (f : C(AddCircle L, ℂ)) (hf : Summable (fourierCoeff f)) (Q : H →L[ℂ] H) :
    (Summable fun k : ℤ => ⟪W (L := L) q (fourier k), Q (outputMode p f k)⟫_ℂ) ∧
    HasSum (fun i => ⟪b i, windowKernel p q f (Q (b i))⟫_ℂ)
      (∑' k : ℤ, ⟪W (L := L) q (fourier k), Q (outputMode p f k)⟫_ℂ) := by
  apply hasSum_diagonal_comp b (windowKernel p q f) Q (outputMode p f)
    (fun k => innerSL ℂ (W (L := L) q (fourier k)))
  · simpa only [innerSL_apply_norm] using mode_sum p q f hf
  · exact windowKernel_synthesis p q f hf

end
end Masullo.OperatorTrace
