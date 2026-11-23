module

public import Lemmas.DisclosedReplacementList
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.Fourier.Convolution
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Signed block interval prices for disclosed replacement lists

Sources: `069b23dd:.godel/bob/replacement-frequency-lists.md:17–25` and
`069b23dd:.godel/bob/isolated-tuple-hits.md:29` (the angular kernel).
Owning check session: `01a2095b-3cd7-7c85-a8af-4a73f8cbf3ba`.

This is the fixed-mask Fourier price, before any interpolation, asymptotic
estimate, or union over masks. The finite product law is on labeled starts,
not distinct frequencies. Only source atoms are counted; no probability law
for a replacement witness is used.
-/

open MeasureTheory FourierTransform Set
open scoped BigOperators ComplexConjugate Convolution

namespace Masullo.SignedBlockIntervalMoment

open DisclosedReplacementList

variable {α : Type*} [Fintype α]

/-- The original, normalized label law independently on every slot. -/
@[expose] public noncomputable def iid (P : FiniteWeightLaw α) (m : ℕ) :
    FiniteWeightLaw (Fin m → α) where
  weight x := ∏ j, P.weight (x j)
  nonneg x := Finset.prod_nonneg fun j _ ↦ P.nonneg (x j)
  total := by
    classical
    rw [← Fintype.prod_sum (fun _ : Fin m ↦ P.weight)]
    simp only [P.total, Finset.prod_const_one]

/-- `true` denotes a positive sign and `false` a negative sign. -/
@[expose] public noncomputable def signedSum {m : ℕ} (labels : α → ℝ) (σ : Fin m → Bool)
    (x : Fin m → α) : ℝ :=
  ∑ j, if σ j then labels (x j) else -labels (x j)

/-- Angular exponential, with no `2π` in its argument. -/
@[expose] public noncomputable def phase (x : ℝ) : ℂ := Complex.exp ((x : ℂ) * Complex.I)

private theorem phase_add (x y : ℝ) : phase (x + y) = phase x * phase y := by
  simp only [phase, Complex.ofReal_add, add_mul, Complex.exp_add]

private theorem phase_neg (x : ℝ) : phase (-x) = conj (phase x) := by
  rw [phase, phase, ← Complex.exp_conj]
  simp

private theorem norm_phase (x : ℝ) : ‖phase x‖ = 1 := by
  simp [phase, Complex.norm_exp, Complex.mul_re]

private theorem continuous_phase : Continuous phase := by
  unfold phase
  fun_prop

/-- One-slot characteristic function, with the weights attached to labels. -/
@[expose] public noncomputable def char (P : FiniteWeightLaw α) (labels : α → ℝ) (u : ℝ) : ℂ :=
  ∑ p, (P.weight p : ℂ) * phase (u * labels p)

/-- The signed block characteristic function as an expectation under `iid`. -/
@[expose] public noncomputable def signedChar (P : FiniteWeightLaw α) (labels : α → ℝ)
    {m : ℕ} (σ : Fin m → Bool) (u : ℝ) : ℂ :=
  ∑ x, ((iid P m).weight x : ℂ) * phase (u * signedSum labels σ x)

/-- Each slot contributes `char` or its conjugate according to its fixed sign. -/
public theorem signedChar_eq_prod (P : FiniteWeightLaw α) (labels : α → ℝ)
    {m : ℕ} (σ : Fin m → Bool) (u : ℝ) :
    signedChar P labels σ u = ∏ j, if σ j then char P labels u else conj (char P labels u) := by
  classical
  let factor (j : Fin m) (p : α) : ℂ :=
    (P.weight p : ℂ) * phase (u * (if σ j then labels p else -labels p))
  have hphase (s : Finset (Fin m)) (a : Fin m → ℝ) :
      phase (∑ j ∈ s, a j) = ∏ j ∈ s, phase (a j) := by
    induction s using Finset.induction_on with
    | empty => simp [phase]
    | insert j s hj ih => simp [Finset.sum_insert, Finset.prod_insert, hj, phase_add, ih]
  calc
    _ = ∑ x : Fin m → α, ∏ j, factor j (x j) := by
      unfold signedChar signedSum
      refine Finset.sum_congr rfl fun x _ ↦ ?_
      simp only [iid, Complex.ofReal_prod, Finset.mul_sum, hphase, factor, Finset.prod_mul_distrib]
    _ = ∏ j, ∑ p, factor j p := (Fintype.prod_sum factor).symm
    _ = _ := by
      refine Finset.prod_congr rfl fun j _ ↦ ?_
      cases h : σ j <;> simp [factor, char, h, phase_neg, map_sum, map_mul]

/-- The modulus is independent of the sign pattern, including for an empty block. -/
public theorem norm_signedChar (P : FiniteWeightLaw α) (labels : α → ℝ)
    {m : ℕ} (σ : Fin m → Bool) (u : ℝ) :
    ‖signedChar P labels σ u‖ = ‖char P labels u‖ ^ m := by
  rw [signedChar_eq_prod, norm_prod]
  calc
    _ = ∏ _j : Fin m, ‖char P labels u‖ := by
      refine Finset.prod_congr rfl fun j _ ↦ ?_
      cases σ j <;> simp
    _ = _ := by simp

private theorem norm_char_le_one (P : FiniteWeightLaw α) (labels : α → ℝ) (u : ℝ) :
    ‖char P labels u‖ ≤ 1 := by
  calc
    _ ≤ ∑ p, ‖(P.weight p : ℂ) * phase (u * labels p)‖ := norm_sum_le _ _
    _ = 1 := by simp [norm_phase, Complex.norm_real, abs_of_nonneg (P.nonneg _), P.total]

/-- The triangle of outer radius `80/t` in the manuscript. -/
@[expose] public noncomputable def triangle (t x : ℝ) : ℝ := max (1 - |x| / (80 / t)) 0

private theorem integrable_sinc_sq : Integrable (fun x : ℝ ↦ Real.sinc x ^ 2) := by
  refine (integrable_inv_one_add_sq.const_mul 2).mono'
    (Real.continuous_sinc.pow 2).aestronglyMeasurable ?_
  filter_upwards with x
  have hs : Real.sinc x ^ 2 ≤ 1 := by
    simpa only [sq_abs, one_pow] using
      pow_le_pow_left₀ (abs_nonneg _) (Real.abs_sinc_le_one x) 2
  have hsin : Real.sin x ^ 2 ≤ 1 := by
    simpa only [sq_abs, one_pow] using
      pow_le_pow_left₀ (abs_nonneg _) (Real.abs_sin_le_one x) 2
  have hprod : Real.sinc x * x = Real.sin x := by
    by_cases hx : x = 0
    · simp [hx]
    · rw [Real.sinc_of_ne_zero hx, div_mul_cancel₀ _ hx]
  rw [Real.norm_of_nonneg (sq_nonneg _), ← div_eq_mul_inv,
    le_div_iff₀ (by positivity : 0 < 1 + x ^ 2), mul_add, mul_one, ← mul_pow, hprod]
  linarith

private noncomputable def box (a : ℝ) : ℝ → ℂ := (Icc (-(a / 2)) (a / 2)).indicator (fun _ ↦ 1)

private theorem integrable_box (a : ℝ) : Integrable (box a) :=
  (integrable_indicator_iff measurableSet_Icc).2 (integrableOn_const (by
    rw [Real.volume_Icc]
    exact ENNReal.ofReal_ne_top))

private theorem box_convolution (a : ℝ) (x : ℝ) :
    (box a ⋆[ContinuousLinearMap.mul ℂ ℂ] box a) x = (↑(max (a - |x|) 0) : ℂ) := by
  let l := max (-(a / 2)) (x - a / 2)
  let r := min (a / 2) (x + a / 2)
  have hI (y : ℝ) : y ∈ Icc l r ↔ y ∈ Icc (-(a / 2)) (a / 2) ∧
      x - y ∈ Icc (-(a / 2)) (a / 2) := by
    simp only [l, r, mem_Icc, max_le_iff, le_min_iff]
    constructor <;> intro h
    · exact ⟨⟨h.1.1, h.2.1⟩, ⟨by linarith [h.2.2], by linarith [h.1.2]⟩⟩
    · exact ⟨⟨h.1.1, by linarith [h.2.2]⟩, ⟨h.1.2, by linarith [h.2.1]⟩⟩
  have hlen : r - l = a - |x| := by
    dsimp only [l, r]
    by_cases hx : 0 ≤ x
    · rw [abs_of_nonneg hx, min_eq_left (by linarith), max_eq_right (by linarith)]
      ring
    · have hx' := le_of_not_ge hx
      rw [abs_of_nonpos hx', min_eq_right (by linarith), max_eq_left (by linarith)]
      ring
  rw [convolution_def]
  change (∫ y, box a y * box a (x - y)) = _
  calc
    _ = ∫ y, (Icc l r).indicator (fun _ ↦ (1 : ℂ)) y := by
      apply integral_congr_ae
      filter_upwards with y
      by_cases h₁ : y ∈ Icc (-(a / 2)) (a / 2) <;>
        by_cases h₂ : x - y ∈ Icc (-(a / 2)) (a / 2) <;>
        simp [box, hI, h₁, h₂]
    _ = _ := by
      rw [integral_indicator measurableSet_Icc, integral_const, Measure.real_def,
        Measure.restrict_apply_univ, Real.volume_Icc, ENNReal.toReal_ofReal', hlen]
      simp

private theorem fourier_box (a : ℝ) (ha : 0 < a) (w : ℝ) :
    𝓕 (box a) w = (↑(a * Real.sinc (Real.pi * a * w)) : ℂ) := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  have hf (y : ℝ) : Complex.exp (↑(-2 * Real.pi * y * w) * Complex.I) • box a y =
      (Icc (-(a / 2)) (a / 2)).indicator
        (fun y ↦ Complex.exp ((↑(-2 * Real.pi * w) * Complex.I) * (y : ℂ))) y := by
    by_cases hy : y ∈ Icc (-(a / 2)) (a / 2)
    · simp only [box, indicator_of_mem hy, smul_eq_mul, mul_one]
      push_cast
      congr 1
      ring
    · simp [box, indicator_of_notMem hy]
  simp_rw [hf]
  rw [integral_indicator measurableSet_Icc]
  by_cases hw : w = 0
  · subst w
    simp [integral_const, Measure.real_def, Real.volume_Icc,
      show a / 2 - -(a / 2) = a by ring, ha.le]
  · rw [integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by linarith : -(a / 2) ≤ a / 2)]
    have hc : (↑(-2 * Real.pi * w) * Complex.I : ℂ) ≠ 0 :=
      mul_ne_zero (Complex.ofReal_ne_zero.mpr
        (mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) hw)) Complex.I_ne_zero
    rw [integral_exp_mul_complex hc]
    let θ := Real.pi * a * w
    have hθ : θ ≠ 0 := mul_ne_zero (mul_ne_zero Real.pi_ne_zero ha.ne') hw
    change _ = (↑(a * Real.sinc θ) : ℂ)
    have hp : (↑(-2 * Real.pi * w) * Complex.I : ℂ) * ↑(a / 2) = -(θ : ℂ) * Complex.I := by
      dsimp [θ]
      push_cast
      ring
    have hm : (↑(-2 * Real.pi * w) * Complex.I : ℂ) * ↑(-(a / 2)) = (θ : ℂ) * Complex.I := by
      rw [Complex.ofReal_neg, mul_neg, hp, neg_mul, neg_neg]
    rw [hp, hm, Complex.exp_mul_I, Complex.exp_mul_I, Complex.cos_neg, Complex.sin_neg,
      Real.sinc_of_ne_zero hθ]
    push_cast [Complex.ofReal_sin]
    field_simp [hθ, Real.pi_ne_zero, ha.ne', hw, Complex.I_ne_zero, θ]
    dsimp [θ]
    push_cast
    ring

/-- The angular probability kernel with triangle radius `80/t`.
Here `Real.sinc` is unnormalized: `sin x / x` off zero, and `1` at zero. -/
@[expose] public noncomputable def sincKernel (t u : ℝ) : ℝ :=
  80 / (2 * Real.pi * t) * Real.sinc (80 * u / (2 * t)) ^ 2

public theorem sincKernel_nonneg {t : ℝ} (ht : 0 < t) (u : ℝ) : 0 ≤ sincKernel t u := by
  unfold sincKernel
  positivity

public theorem integrable_sincKernel {t : ℝ} (ht : 0 < t) : Integrable (sincKernel t) := by
  have h := (integrable_sinc_sq.comp_mul_left' (R := 80 / (2 * t)) (by positivity)).const_mul
    (80 / (2 * Real.pi * t))
  convert h using 1
  ext u
  unfold sincKernel
  congr 3
  ring

/-- Angular Fourier transform of the concrete sinc-square kernel. -/
public theorem sincKernel_transform {t : ℝ} (ht : 0 < t) (x : ℝ) :
    (∫ u, (sincKernel t u : ℂ) * phase (u * x)) = (triangle t x : ℂ) := by
  let a : ℝ := 80 / t
  have ha : 0 < a := by dsimp [a]; positivity
  let T (y : ℝ) : ℂ := (triangle t y : ℂ)
  -- A normalized self-convolution of a box is the desired triangle.
  have hT : T = ((a⁻¹ : ℝ) : ℂ) • (box a ⋆[ContinuousLinearMap.mul ℂ ℂ] box a) := by
    funext y
    change T y = ((a⁻¹ : ℝ) : ℂ) • (box a ⋆[ContinuousLinearMap.mul ℂ ℂ] box a) y
    rw [box_convolution, smul_eq_mul, ← Complex.ofReal_mul]
    dsimp [T, triangle]
    congr 1
    rw [mul_max_of_nonneg _ _ (inv_nonneg.mpr ha.le), mul_zero]
    congr 1
    change 1 - |y| / a = a⁻¹ * (a - |y|)
    field_simp
  have hc : Continuous T := by
    unfold T triangle
    fun_prop
  have hi : Integrable T := by
    rw [hT]
    exact ((integrable_box a).integrable_convolution (ContinuousLinearMap.mul ℂ ℂ)
      (integrable_box a)).smul ((a⁻¹ : ℝ) : ℂ)
  have hf (w : ℝ) : 𝓕 T w = (↑(a * Real.sinc (Real.pi * a * w) ^ 2) : ℂ) := by
    have hscale (k : ℂ) (f : ℝ → ℂ) : 𝓕 (k • f) w = k * 𝓕 f w := by
      simp only [Real.fourier_real_eq_integral_exp_smul, Pi.smul_apply, smul_eq_mul]
      rw [← integral_const_mul]
      congr 1
      funext y
      ring
    rw [hT, hscale, Real.fourier_mul_convolution_eq (integrable_box a) (integrable_box a),
      fourier_box a ha w, ← Complex.ofReal_mul, ← Complex.ofReal_mul]
    congr 1
    field_simp [ha.ne']
  have hfi : Integrable (𝓕 T) := by
    have heq : 𝓕 T = fun w ↦ (↑(a * Real.sinc (Real.pi * a * w) ^ 2) : ℂ) := funext hf
    rw [heq]
    exact ((integrable_sinc_sq.comp_mul_left' (R := Real.pi * a) (by positivity)).const_mul
      a).ofReal
  have hinv := congrFun (hc.fourierInv_fourier_eq hi hfi) x
  rw [Real.fourierInv_eq'] at hinv
  -- Convert the cycle-frequency inversion integral to the angular variable.
  let b := 2 * Real.pi
  have hb : 0 < b := by dsimp [b]; positivity
  let A (u : ℝ) : ℂ := (sincKernel t u : ℂ) * phase (u * x)
  have hrescale (w : ℝ) :
      Complex.exp (↑(2 * Real.pi * inner ℝ w x) * Complex.I) • 𝓕 T w = (b : ℂ) * A (b * w) := by
    have harg : 80 * (b * w) / (2 * t) = Real.pi * a * w := by
      dsimp [a, b]
      ring
    have hcoef : b * (80 / (2 * Real.pi * t)) = a := by
      dsimp [a, b]
      field_simp [Real.pi_ne_zero, ht.ne']
    have hkernel : b * sincKernel t (b * w) = a * Real.sinc (Real.pi * a * w) ^ 2 := by
      unfold sincKernel
      rw [harg, ← mul_assoc, hcoef]
    have hangle : 2 * Real.pi * (w * x) = (b * w) * x := by
      dsimp [b]
      ring
    rw [hf, Real.inner_apply, hangle, smul_eq_mul]
    change phase ((b * w) * x) * _ = (b : ℂ) *
      ((sincKernel t (b * w) : ℂ) * phase ((b * w) * x))
    rw [← hkernel, Complex.ofReal_mul]
    ring
  simp_rw [hrescale] at hinv
  rw [integral_const_mul, Measure.integral_comp_mul_left, abs_of_pos (inv_pos.mpr hb),
    Complex.real_smul, ← mul_assoc, ← Complex.ofReal_mul, mul_inv_cancel₀ hb.ne',
    Complex.ofReal_one, one_mul] at hinv
  exact hinv

/-- At frequency zero the triangle has value one, so the kernel has mass one. -/
public theorem integral_sincKernel {t : ℝ} (ht : 0 < t) : (∫ u, sincKernel t u) = 1 := by
  have h := sincKernel_transform ht 0
  simp only [mul_zero, phase, Complex.ofReal_zero, zero_mul, Complex.exp_zero, mul_one,
    triangle, abs_zero, zero_div, sub_zero, max_eq_left zero_le_one] at h
  exact_mod_cast h

/-- The order-`m` moment with the same kernel at each order. -/
@[expose] public noncomputable def moment (K : ℝ → ℝ) (P : FiniteWeightLaw α) (labels : α → ℝ)
    (m : ℕ) : ℝ := ∫ u, K u * ‖char P labels u‖ ^ m

private theorem integrable_moment_density {K : ℝ → ℝ} (hK : Integrable K)
    (P : FiniteWeightLaw α) (labels : α → ℝ) (m : ℕ) :
    Integrable (fun u ↦ K u * ‖char P labels u‖ ^ m) := by
  have hc : Continuous (char P labels) := by
    unfold char phase
    fun_prop
  exact hK.mul_bdd (hc.norm.pow m).aestronglyMeasurable
    (Filter.Eventually.of_forall fun u ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (norm_nonneg _) _)]
      exact pow_le_one₀ (norm_nonneg _) (norm_char_le_one P labels u))

/-- The expected translated triangle is the angular Fourier integral of the
signed block characteristic function with a unit-modulus translation phase. -/
public theorem expected_triangle_eq {t : ℝ} {K : ℝ → ℝ} (hK : Integrable K)
    (htransform : ∀ x : ℝ, (∫ u, (K u : ℂ) * phase (u * x)) = (triangle t x : ℂ))
    (P : FiniteWeightLaw α) (labels : α → ℝ) {m : ℕ} (σ : Fin m → Bool) (c : ℝ) :
    ((∑ x, (iid P m).weight x * triangle t (signedSum labels σ x - c) : ℝ) : ℂ) =
      ∫ u, (K u : ℂ) * phase (-(u * c)) * signedChar P labels σ u := by
  let A (x : Fin m → α) (u : ℝ) : ℂ :=
    ((iid P m).weight x : ℂ) * ((K u : ℂ) * phase (u * (signedSum labels σ x - c)))
  have hA (x : Fin m → α) : Integrable (A x) := by
    apply Integrable.const_mul
    exact (hK.ofReal (𝕜 := ℂ)).mul_bdd
      (continuous_phase.comp (continuous_id.mul_const _)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun u ↦ (norm_phase _).le)
  calc
    _ = ∑ x, ∫ u, A x u := by
      simp only [Complex.ofReal_sum, Complex.ofReal_mul, ← htransform, A, integral_const_mul]
    _ = ∫ u, ∑ x, A x u := (integral_finsetSum _ fun x _ ↦ hA x).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with u
      simp only [A, signedChar, Finset.mul_sum]
      refine Finset.sum_congr rfl fun x _ ↦ ?_
      rw [mul_sub, sub_eq_add_neg, phase_add]
      ring

/-- Universal interval price from the triangle transform, uniform in the center
and valid on the boundary of the inner interval. -/
public theorem intervalMass_le_two_moment_of_transform {t : ℝ} (ht : 0 < t)
    {K : ℝ → ℝ} (hK : Integrable K) (hK₀ : ∀ u, 0 ≤ K u)
    (htransform : ∀ x : ℝ, (∫ u, (K u : ℂ) * phase (u * x)) = (triangle t x : ℂ))
    (P : FiniteWeightLaw α) (labels : α → ℝ) {m : ℕ} (σ : Fin m → Bool)
    (c R : ℝ) (hR : R ≤ 40 / t) :
    (iid P m).mass (fun x ↦ |signedSum labels σ x - c| ≤ R) ≤ 2 * moment K P labels m := by
  classical
  let E : ℝ := ∑ x, (iid P m).weight x * triangle t (signedSum labels σ x - c)
  have hE : 0 ≤ E := Finset.sum_nonneg fun x _ ↦
    mul_nonneg ((iid P m).nonneg x) (le_max_right _ _)
  have hmaj : (iid P m).mass (fun x ↦ |signedSum labels σ x - c| ≤ R) ≤ 2 * E := by
    simp only [FiniteWeightLaw.mass, E, Finset.mul_sum]
    refine Finset.sum_le_sum fun x _ ↦ ?_
    split_ifs with hx
    · have hhalf : (1 / 2 : ℝ) ≤ triangle t (signedSum labels σ x - c) := by
        refine le_trans ?_ (le_max_left _ _)
        have hdiv : |signedSum labels σ x - c| / (80 / t) ≤ (1 / 2 : ℝ) := by
          apply (div_le_iff₀ (by positivity : 0 < 80 / t)).2
          calc
            _ ≤ 40 / t := hx.trans hR
            _ = (1 / 2 : ℝ) * (80 / t) := by ring
        linarith
      nlinarith [mul_nonneg ((iid P m).nonneg x) (sub_nonneg.mpr hhalf)]
    · exact mul_nonneg (by norm_num) (mul_nonneg ((iid P m).nonneg x) (le_max_right _ _))
  refine hmaj.trans (mul_le_mul_of_nonneg_left ?_ (by norm_num))
  have hFourier := expected_triangle_eq hK htransform P labels σ c
  change (E : ℂ) = _ at hFourier
  calc
    E = ‖(E : ℂ)‖ := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hE]
    _ ≤ moment K P labels m := by
      rw [hFourier]
      apply norm_integral_le_of_norm_le (integrable_moment_density hK P labels m)
      filter_upwards with u
      simp [norm_phase, norm_signedChar, Complex.norm_real, abs_of_nonneg (hK₀ u)]

/-- Fixed-mask two-hit source bound supplied by the two distinct hidden iid
blocks. The disclosed law and post-hoc admissibility predicate are unchanged. -/
public theorem twoHitMass_le_four_moments_of_transform {Z : Type*} [Fintype Z]
    {t : ℝ} (ht : 0 < t) {K : ℝ → ℝ} (hK : Integrable K) (hK₀ : ∀ u, 0 ≤ K u)
    (htransform : ∀ x : ℝ, (∫ u, (K u : ℂ) * phase (u * x)) = (triangle t x : ℂ))
    (Pz : FiniteWeightLaw Z) (P : FiniteWeightLaw α) (labels : α → ℝ) {r v : ℕ}
    (removedSign : Fin r → Bool) (retainedSourceSign retainedTargetSign : Fin v → Bool)
    (sourceDisclosed targetDisclosed : Z → ℝ) (D : Z → Finset ℝ)
    (admissible : Z → (Fin v → α) → (Fin r → α) → ℝ → Prop) {N : ℕ}
    (hcard : ∀ z, (D z).card ≤ N) :
    twoHitMass t Pz (iid P v) (iid P r) sourceDisclosed targetDisclosed
      (signedSum labels retainedSourceSign) (signedSum labels retainedTargetSign)
      (signedSum labels removedSign) D admissible ≤
        4 * (N : ℝ) * moment K P labels r * moment K P labels v := by
  have hr : 2 * Real.pi / t ≤ 40 / t :=
    (div_le_div_iff_of_pos_right ht).2 (by linarith [Real.pi_lt_four])
  have hv : (2 * Real.pi + 1) / t ≤ 40 / t :=
    (div_le_div_iff_of_pos_right ht).2 (by linarith [Real.pi_lt_four])
  exact twoHitMass_le_four ht Pz (iid P v) (iid P r) sourceDisclosed targetDisclosed
    (signedSum labels retainedSourceSign) (signedSum labels retainedTargetSign)
    (signedSum labels removedSign) D admissible hcard
    (fun c ↦ intervalMass_le_two_moment_of_transform ht hK hK₀ htransform
      P labels removedSign c _ hr)
    (fun c ↦ intervalMass_le_two_moment_of_transform ht hK hK₀ htransform
      P labels retainedTargetSign c _ hv)

/-- The concrete sinc-square bound for every translated closed interval of
radius at most `40/t`. -/
public theorem intervalMass_le_two_moment {t : ℝ} (ht : 0 < t)
    (P : FiniteWeightLaw α) (labels : α → ℝ) {m : ℕ} (σ : Fin m → Bool)
    (c R : ℝ) (hR : R ≤ 40 / t) :
    (iid P m).mass (fun x ↦ |signedSum labels σ x - c| ≤ R) ≤
      2 * moment (sincKernel t) P labels m :=
  intervalMass_le_two_moment_of_transform ht (integrable_sincKernel ht)
    (sincKernel_nonneg ht) (sincKernel_transform ht) P labels σ c R hR

/-- The fixed-mask disclosed replacement-list bound `4 N U_r U_v` with the
concrete kernel from the source. No separation or balance assumption is
added to the two-hit mass, and admissibility may read the whole source. -/
public theorem twoHitMass_le_four_moments {Z : Type*} [Fintype Z] {t : ℝ} (ht : 0 < t)
    (Pz : FiniteWeightLaw Z) (P : FiniteWeightLaw α) (labels : α → ℝ) {r v : ℕ}
    (removedSign : Fin r → Bool) (retainedSourceSign retainedTargetSign : Fin v → Bool)
    (sourceDisclosed targetDisclosed : Z → ℝ) (D : Z → Finset ℝ)
    (admissible : Z → (Fin v → α) → (Fin r → α) → ℝ → Prop) {N : ℕ}
    (hcard : ∀ z, (D z).card ≤ N) :
    twoHitMass t Pz (iid P v) (iid P r) sourceDisclosed targetDisclosed
      (signedSum labels retainedSourceSign) (signedSum labels retainedTargetSign)
      (signedSum labels removedSign) D admissible ≤
        4 * (N : ℝ) * moment (sincKernel t) P labels r * moment (sincKernel t) P labels v :=
  twoHitMass_le_four_moments_of_transform ht (integrable_sincKernel ht)
    (sincKernel_nonneg ht) (sincKernel_transform ht) Pz P labels
    removedSign retainedSourceSign retainedTargetSign sourceDisclosed targetDisclosed D
    admissible hcard

end Masullo.SignedBlockIntervalMoment
