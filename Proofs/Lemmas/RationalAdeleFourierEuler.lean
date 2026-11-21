module

public import Theorems.RationalAdeleLFDilationDeriv
public import Theorems.RationalAdeleBoxThetaInversion

/-! # Fourier differentiation on the rational real-section boxes -/

open NumberField MeasureTheory LineDeriv
open scoped SchwartzMap FourierTransform ComplexConjugate

namespace Masullo

local notation "B" => 𝓢(ℝ, ℂ)
local notation "Mₓ" => SchwartzMap.smulLeftCLM ℂ Complex.ofReal
local notation "∂₁" => LineDeriv.lineDerivOp (1 : ℝ)

private theorem coordinate_mul_apply (b : B) (x : ℝ) :
    Mₓ b x = (x : ℂ) * b x := by
  rw [SchwartzMap.smulLeftCLM_apply_apply Complex.hasTemperateGrowth_ofReal, smul_eq_mul]

private theorem deriv_one_apply (b : B) (x : ℝ) : ∂₁ b x = deriv b x := by
  rfl

private theorem deriv_mul_coordinate (b : B) : ∂₁ (Mₓ b) = b + Mₓ (∂₁ b) := by
  ext x
  rw [deriv_one_apply, add_apply, coordinate_mul_apply, deriv_one_apply]
  have h : (⇑(Mₓ b) : ℝ → ℂ) = fun x : ℝ ↦ (x : ℂ) * b x := funext (coordinate_mul_apply b)
  rw [h]
  have hr : HasDerivAt (fun u : ℝ ↦ (u : ℂ)) 1 x := Complex.ofRealCLM.hasDerivAt
  simpa only [one_mul] using (hr.fun_mul (b.hasDerivAt x)).deriv

private theorem fourier_euler (b : B) (x : ℝ) :
    𝓕 (Mₓ (∂₁ b)) x = -(𝓕 b) x - (x : ℂ) * deriv (⇑(𝓕 b : B)) x := by
  have h₁ := SchwartzMap.fourier_lineDerivOp_eq (Mₓ b) (1 : ℝ)
  rw [deriv_mul_coordinate, FourierAdd.fourier_add] at h₁
  have h₂ := (SchwartzMap.lineDerivOp_fourier_eq b (1 : ℝ))
  have hm (p : B) : SchwartzMap.smulLeftCLM ℂ (inner ℝ · (1 : ℝ)) p = Mₓ p := by
    ext x
    have hi : (fun u : ℝ ↦ inner ℝ u (1 : ℝ)) = id := by
      funext u
      simp
    rw [hi, SchwartzMap.smulLeftCLM_apply_apply Function.HasTemperateGrowth.id,
      coordinate_mul_apply, id_eq, Complex.real_smul]
  rw [hm] at h₁ h₂
  have h₁x := congrArg (fun f : B ↦ f x) h₁
  have h₂x := congrArg (fun f : B ↦ f x) h₂
  simp only [add_apply, smul_apply, smul_eq_mul, coordinate_mul_apply] at h₁x
  simp only [FourierSMul.fourier_smul, smul_apply, smul_eq_mul, deriv_one_apply] at h₂x
  calc
    _ = (2 * (Real.pi : ℂ) * Complex.I) * ((x : ℂ) * 𝓕 (Mₓ b) x) - 𝓕 b x := by
      rw [← h₁x]; ring
    _ = _ := by rw [h₂x]; ring

private theorem hasDerivAt_fourier_euler (b : B) (x : ℝ) :
    HasDerivAt (fun s : ℝ ↦ Real.exp (-s) • 𝓕 b (Real.exp (-s) * x))
      (𝓕 (Mₓ (∂₁ b)) x) 0 := by
  have he : HasDerivAt (fun s : ℝ ↦ Real.exp (-s)) (-1) 0 := by
    simpa only [neg_zero, Real.exp_zero, one_mul, Function.comp_def] using
      (Real.hasDerivAt_exp (-(0 : ℝ))).comp 0 (hasDerivAt_neg (0 : ℝ))
  have hb := ((𝓕 b).hasDerivAt x).scomp_of_eq 0 (he.mul_const x) (by simp)
  have h' : HasDerivAt (fun s : ℝ ↦ Real.exp (-s) • 𝓕 b (Real.exp (-s) * x))
      (Real.exp (-(0 : ℝ)) • ((-1 * x : ℝ) • deriv (⇑(𝓕 b : B)) x) +
        (-1 : ℝ) • 𝓕 b (Real.exp (-(0 : ℝ)) * x)) 0 := he.fun_smul hb
  rw [fourier_euler]
  convert h' using 1
  simp [Complex.real_smul]
  ring

local notation "A" => AdeleRing (𝓞 ℚ) ℚ
local notation "J" => IdeleGroup (𝓞 ℚ) ℚ
local notation "χ" => rationalAdeleAddChar
local notation "τ" => rationalIdeleLogSection

private theorem real_mul (a b : A) :
    rationalAdeleReal (a * b) = rationalAdeleReal a * rationalAdeleReal b := by
  simp only [rationalAdeleReal_apply]
  exact map_mul (InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace) _ _

private theorem eq_of_real_finite {a b : A} (hr : rationalAdeleReal a = rationalAdeleReal b)
    (hf : a.2 = b.2) : a = b := by
  refine Prod.ext (funext fun v ↦ ?_) hf
  obtain rfl : v = Rat.infinitePlace := Subsingleton.elim _ _
  simp only [rationalAdeleReal_apply] at hr
  exact (InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace).injective hr

set_option linter.concreteInstances false

variable [MeasurableSpace A] [BorelSpace A]

/-- In a stage box sum the Fourier log-orbit derivative changes only the real
profiles. The norms, finite character, and finite frequency support are fixed. -/
public theorem hasDerivAt_rationalAdeleBoxSum_fourier_euler {I : Type*} (S : Finset I)
    (b : I → B) (a : I → A) (g : I → J) (ha : ∀ i, rationalAdeleReal (a i) = 0)
    (hg : ∀ i, rationalAdeleReal (g i : A) = 1) (y : A) :
    HasDerivAt (fun s : ℝ ↦ Real.exp (-s) •
      rationalAdeleFourier (rationalAdeleBoxSum S (fun _ ↦ 1) b a g)
        ((τ (Multiplicative.ofAdd (-s)) : A) * y))
      (rationalAdeleFourier (rationalAdeleBoxSum S (fun _ ↦ 1) (fun i ↦ Mₓ (∂₁ (b i))) a g) y)
      0 := by
  classical
  let w (s : ℝ) := (τ (Multiplicative.ofAdd (-s)) : A) * y
  have hwf (s : ℝ) : (w s).2 = y.2 := by
    dsimp only [w]
    rw [rationalIdeleLogSection_mul_adele, rationalAdeleAt_finite]
  have hwr (s : ℝ) : rationalAdeleReal (w s) = Real.exp (-s) * rationalAdeleReal y := by
    dsimp only [w]
    rw [rationalIdeleLogSection_mul_adele, rationalAdeleReal_at]
  have hw0 : w 0 = y := eq_of_real_finite (by simp [hwr]) (hwf 0)
  let c (i : I) : ℂ := if (g i : A) * y ∈ rationalIntegralAdeles then
    ideleNorm (g i) • conj (χ (a i * y)) else 0
  have h (p : I → B) (s : ℝ) :
      rationalAdeleFourier (rationalAdeleBoxSum S (fun _ ↦ 1) p a g) (w s) =
        ∑ i ∈ S, c i * 𝓕 (p i) (Real.exp (-s) * rationalAdeleReal y) := by
    rw [rationalAdeleFourier, integral_rationalAdeleBoxSum_mul_conj_char]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    have hphase : a i * w s = a i * y := by
      apply eq_of_real_finite
      · simp only [real_mul, ha, zero_mul]
      · change (a i).2 * (w s).2 = (a i).2 * y.2
        rw [hwf]
    have hmem : (g i : A) * w s ∈ rationalIntegralAdeles ↔
        (g i : A) * y ∈ rationalIntegralAdeles := by
      change (∀ v, ((g i : A).2 * (w s).2) v ∈ v.adicCompletionIntegers ℚ) ↔
        (∀ v, ((g i : A).2 * y.2) v ∈ v.adicCompletionIntegers ℚ)
      rw [hwf]
    rw [one_mul, hphase, rationalAdeleUnramified]
    by_cases hm : (g i : A) * y ∈ rationalIntegralAdeles
    · rw [Set.indicator_of_mem (hmem.mpr hm), real_mul, hg, one_mul, hwr]
      simp only [c, ite_eq_left hm, smul_mul_assoc]
    · rw [Set.indicator_of_notMem (mt hmem.mp hm), mul_zero, smul_zero]
      simp [c, hm]
  have hr : ∀ s : ℝ, Real.exp (-s) •
      rationalAdeleFourier (rationalAdeleBoxSum S (fun _ ↦ 1) b a g) (w s) =
      ∑ i ∈ S, c i * (Real.exp (-s) • 𝓕 (b i) (Real.exp (-s) * rationalAdeleReal y)) := by
    intro s
    simp only [h, Finset.smul_sum, mul_smul_comm]
  change HasDerivAt (fun s : ℝ ↦ Real.exp (-s) •
    rationalAdeleFourier (rationalAdeleBoxSum S (fun _ ↦ 1) b a g) (w s)) _ 0
  have h0 := h (fun i ↦ Mₓ (∂₁ (b i))) 0
  rw [hw0, neg_zero, Real.exp_zero, one_mul] at h0
  rw [funext hr, h0]
  exact HasDerivAt.fun_sum fun i _ ↦ (hasDerivAt_fourier_euler (b i) (rationalAdeleReal y)).const_mul _

end Masullo
