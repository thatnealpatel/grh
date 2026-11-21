module

public import Theorems.RationalAdeleBoxPoisson
import Lemmas.RationalAdeleBoxPeriodization
import Theorems.RationalAdelePoisson

/-! # Fourier transform and Poisson summation for finite sums of rational adelic boxes

This is the finite-linearity step from the translated generators in Example 2.1.3.1,
pp. 67–68, to the pointwise formula of Theorem D.1.2.7(3), p. 749.
-/

open NumberField MeasureTheory
open scoped ComplexConjugate FourierTransform SchwartzMap

namespace Masullo

local notation "A" => AdeleRing (𝓞 ℚ) ℚ
local notation "J" => IdeleGroup (𝓞 ℚ) ℚ
local notation "Cq" => A ⧸ rationalDiagonal
local notation "ι" => algebraMap ℚ A
local notation "χ" => rationalAdeleAddChar
local notation "μA" => rationalAdeleAddHaar

variable {I : Type*}

/-- A complex finite linear combination of translated, idele-dilated unramified tensors. -/
@[expose] public noncomputable def rationalAdeleBoxSum (s : Finset I) (c : I → ℂ)
    (b : I → 𝓢(ℝ, ℂ)) (a : I → A) (g : I → J) (x : A) : ℂ :=
  ∑ i ∈ s, c i * rationalAdeleBox (b i) (a i) (g i) x

variable (s : Finset I) (c : I → ℂ) (b : I → 𝓢(ℝ, ℂ)) (a : I → A) (g : I → J)

private theorem summable_norm_weighted_sum {D : Type*} {f : I → D → ℂ}
    (hf : ∀ i ∈ s, Summable (fun x ↦ ‖f i x‖)) :
    Summable (fun x ↦ ‖∑ i ∈ s, c i * f i x‖) := by
  have h : Summable (fun x ↦ ∑ i ∈ s, ‖c i‖ * ‖f i x‖) :=
    summable_sum fun i hi ↦ (hf i hi).mul_left ‖c i‖
  exact h.of_nonneg_of_le (fun _ ↦ norm_nonneg _) fun x ↦ by
    simp only [← norm_mul]
    exact norm_sum_le _ _

/-- The periodization converges absolutely at every lift of a quotient point and
is continuous on the quotient. -/
public theorem rationalAdeleBoxSum_periodization :
    (∀ x : A, Summable (fun d : rationalDiagonal ↦ ‖rationalAdeleBoxSum s c b a g (x + d)‖)) ∧
      Continuous (rationalAdeleComplexPeriodization (rationalAdeleBoxSum s c b a g)) := by
  refine ⟨fun x ↦ summable_norm_weighted_sum s c (fun i _ ↦
    summable_norm_rationalAdeleBox_add (b i) (a i) (g i) x), ?_⟩
  have h (q : Cq) : rationalAdeleComplexPeriodization (rationalAdeleBoxSum s c b a g) q =
      ∑ i ∈ s, c i * rationalAdeleComplexPeriodization (rationalAdeleBox (b i) (a i) (g i)) q := by
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective q
    simp only [rationalAdeleComplexPeriodization_mk, rationalAdeleBoxSum]
    rw [Summable.tsum_finsetSum]
    · simp only [tsum_mul_left]
    · exact fun i _ ↦ ((summable_norm_rationalAdeleBox_add (b i) (a i) (g i) x).of_norm).mul_left _
  rw [funext h]
  exact continuous_finsetSum s fun i _ ↦
    continuous_const.mul (continuous_rationalAdeleComplexPeriodization_box (b i) (a i) (g i))

set_option linter.concreteInstances false

variable [MeasurableSpace A] [BorelSpace A]

/-- At every adelic frequency the Fourier integral is the finite sum of the
box transforms, with the conjugated phase and the direct idelic Jacobian. -/
public theorem integral_rationalAdeleBoxSum_mul_conj_char (y : A) :
    (∫ x, rationalAdeleBoxSum s c b a g x * conj (χ (x * y)) ∂μA) =
      ∑ i ∈ s, c i * (ideleNorm (g i) •
        (conj (χ (a i * y)) * rationalAdeleUnramified (𝓕 (b i)) ((g i : A) * y))) := by
  simp only [rationalAdeleBoxSum, Finset.sum_mul, mul_assoc]
  rw [integral_finsetSum s (fun i _ ↦
    (integrable_rationalAdeleBox_mul_conj_char (b i) (a i) (g i) y).const_mul (c i))]
  simp only [integral_const_mul, integral_rationalAdeleBox_mul_conj_char]

/-- The Fourier samples on the diagonal, including frequency zero, are absolutely summable. -/
public theorem summable_norm_rationalAdeleBoxSum_fourier :
    Summable (fun r : ℚ ↦
      ‖∫ z, rationalAdeleBoxSum s c b a g z * conj (χ (z * ι r)) ∂μA‖) := by
  simp_rw [integral_rationalAdeleBoxSum_mul_conj_char]
  apply summable_norm_weighted_sum
  intro i _
  simpa only [integral_rationalAdeleBox_mul_conj_char] using
    summable_norm_rationalAdeleBox_fourier (b i) (a i) (g i)

variable [MeasurableSpace Cq] [BorelSpace Cq]

/-- At every adele the periodization of a finite linear combination of boxes equals
its absolutely convergent Fourier series, including both zero terms. -/
public theorem hasSum_rationalAdeleBoxSum_poisson (x : A) :
    HasSum (fun d : rationalDiagonal ↦ rationalAdeleBoxSum s c b a g (x + d))
      (∑' r : ℚ, (∫ z, rationalAdeleBoxSum s c b a g z * conj (χ (z * ι r)) ∂μA) *
        χ (x * ι r)) := by
  have hf : Continuous (rationalAdeleBoxSum s c b a g) :=
    continuous_finsetSum s fun i _ ↦
      continuous_const.mul (continuous_rationalAdeleBox (b i) (a i) (g i))
  have hfi : Integrable (rationalAdeleBoxSum s c b a g) μA :=
    integrable_finsetSum _ fun i _ ↦ (integrable_rationalAdeleBox (b i) (a i) (g i)).const_mul (c i)
  obtain ⟨hfib, hper⟩ := rationalAdeleBoxSum_periodization s c b a g
  exact hasSum_rationalAdele_poisson hf.measurable hfi hfib hper
    (summable_norm_rationalAdeleBoxSum_fourier s c b a g) x

end Masullo
