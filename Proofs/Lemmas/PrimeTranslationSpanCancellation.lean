module

public import Lemmas.PrimeTranslationProfileApproximation
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! # Pole cancellation on the prime-translation endpoint span

Source and immediate consumer: `bdd74f2:.godel/adhoc/prime-translation-norm.md`,
§§2–3, especially lines 44–50.
Owning check session: `01a20d85-3fca-796b-bf11-8791e07c4ba8`.

Scope: the actual untwisted strict-cutoff translation sum minus the two-pole
operator, on the complex span of the zero-extended endpoint profiles on `[0,D]`.
The bound is uniform relative to the input's own window `L²` norm. It does not
estimate the residual on the full space or give a lower bound on its norm.
-/

open Filter MeasureTheory
open Real (exp log sqrt)
open scoped ArithmeticFunction.vonMangoldt Topology

namespace Masullo

local notation "fₚ" => primeTranslationProfile
local notation "gₚ" => primeTranslationReflectedProfile

/-- The complex version of the same two-sided strict-cutoff sum as
`primeTranslationApply`. Inputs are zero-extended and the output is read on the window. -/
@[expose] public noncomputable def primeTranslationComplexApply
    (D : ℝ) (u : ℝ → ℂ) (x : ℝ) : ℂ :=
  ∑ n ∈ Finset.Ico 1 ⌈exp D⌉₊, (↑(Λ n / sqrt n) : ℂ) * (u (x + log n) + u (x - log n))

/-- The pole operator `exp (D/2) * (f ⊗ g + g ⊗ f)`. The conjugates in the two
rank-one pairings are unnecessary because `f` and `g` are real. -/
@[expose] public noncomputable def primeTranslationPoleApply
    (D : ℝ) (u : ℝ → ℂ) (x : ℝ) : ℂ :=
  (exp (D / 2) : ℂ) *
    ((fₚ D x : ℂ) * (∫ z in Set.Icc 0 D, (gₚ D z : ℂ) * u z) +
      (gₚ D x : ℂ) * (∫ z in Set.Icc 0 D, (fₚ D z : ℂ) * u z))

/-- The ordinary `L²` norm on `[0,D]`, on square-integrable representatives. -/
@[expose] public noncomputable def primeTranslationWindowL2Norm (D : ℝ) (u : ℝ → ℂ) : ℝ :=
  sqrt (∫ x in Set.Icc 0 D, ‖u x‖ ^ 2)

private theorem reflect_mem {D x : ℝ} (hx : x ∈ Set.Icc 0 D) : D - x ∈ Set.Icc 0 D :=
  ⟨sub_nonneg.mpr hx.2, sub_le_self _ hx.1⟩

private theorem left_on {D x : ℝ} (hx : x ∈ Set.Icc 0 D) : fₚ D x = exp (-x / 2) :=
  Set.indicator_of_mem hx _

private theorem right_on {D x : ℝ} (hx : x ∈ Set.Icc 0 D) : gₚ D x = exp (-(D - x) / 2) :=
  left_on (reflect_mem hx)

private theorem left_continuousOn (D : ℝ) : ContinuousOn (fₚ D) (Set.Icc 0 D) :=
  (by fun_prop : Continuous (fun x : ℝ ↦ exp (-x / 2))).continuousOn.congr
    (fun _ hx ↦ left_on hx)

private theorem right_continuousOn (D : ℝ) : ContinuousOn (gₚ D) (Set.Icc 0 D) :=
  (by fun_prop : Continuous (fun x : ℝ ↦ exp (-(D - x) / 2))).continuousOn.congr
    (fun _ hx ↦ right_on hx)

private noncomputable def diagonal (D : ℝ) : ℝ := 1 - exp (-D)
private noncomputable def cross (D : ℝ) : ℝ := D * exp (-(D / 2))

private theorem left_sq_integral {D : ℝ} (hD : 0 ≤ D) :
    (∫ z in Set.Icc 0 D, fₚ D z ^ 2) = diagonal D := by
  calc
    _ = ∫ z in Set.Icc 0 D, exp (-z) := by
      apply setIntegral_congr_fun measurableSet_Icc
      intro z hz
      change fₚ D z ^ 2 = exp (-z)
      rw [left_on hz, pow_two, ← Real.exp_add]
      congr 1
      ring
    _ = diagonal D := by
      rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hD,
        intervalIntegral.integral_comp_neg exp, integral_exp]
      simp [diagonal]

private theorem right_sq_integral {D : ℝ} (hD : 0 ≤ D) :
    (∫ z in Set.Icc 0 D, gₚ D z ^ 2) = diagonal D := by
  have hreflect := intervalIntegral.integral_comp_sub_left (a := 0) (b := D)
    (fun y ↦ fₚ D y ^ 2) D
  rw [sub_self, sub_zero] at hreflect
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hD]
  exact hreflect.trans (by
    rw [intervalIntegral.integral_of_le hD, ← integral_Icc_eq_integral_Ioc]
    exact left_sq_integral hD)

private theorem cross_integral {D : ℝ} (hD : 0 ≤ D) :
    (∫ z in Set.Icc 0 D, fₚ D z * gₚ D z) = cross D := by
  calc
    _ = ∫ _ in Set.Icc 0 D, exp (-(D / 2)) := by
      apply setIntegral_congr_fun measurableSet_Icc
      intro z hz
      change fₚ D z * gₚ D z = exp (-(D / 2))
      rw [left_on hz, right_on hz, ← Real.exp_add]
      congr 1
      ring
    _ = _ := by simp [cross, hD, smul_eq_mul]

private theorem cross_tendsto : Tendsto cross atTop (𝓝 0) := by
  have hhalf : Tendsto (fun D : ℝ ↦ D / 2) atTop atTop := by
    refine tendsto_atTop_atTop.mpr fun y ↦ ⟨2 * y, fun D hD ↦ ?_⟩
    linarith
  have h := ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp hhalf).const_mul 2
  rw [mul_zero] at h
  refine h.congr fun D ↦ ?_
  simp only [Function.comp_apply, pow_one, cross]
  ring

private noncomputable def poleLeft (D x : ℝ) : ℝ :=
  exp (D / 2) * (fₚ D x * cross D + gₚ D x * diagonal D)

private noncomputable def residualLeft (D x : ℝ) : ℝ :=
  primeTranslationApply D (fₚ D) x - poleLeft D x

-- Subtract the actual pole row, not just its leading term `E * g`.
private theorem residual_left_on {η : ℝ} (hη : 0 < η) :
    ∀ᶠ D : ℝ in atTop, ∀ x ∈ Set.Ioo 0 D,
      |residualLeft D x| ≤ η * exp (D / 2) * (fₚ D x + gₚ D x) := by
  have hh : 0 < η / 2 := by positivity
  filter_upwards [primeTranslationProfileApproximationOn hh, eventually_ge_atTop (0 : ℝ),
    cross_tendsto.eventually_lt_const hh, Real.tendsto_exp_neg_atTop_nhds_zero.eventually_lt_const hh]
    with D hT hD hcross hexp
  intro x hx
  have hxc : x ∈ Set.Icc 0 D := ⟨hx.1.le, hx.2.le⟩
  have hf : 0 ≤ fₚ D x := by rw [left_on hxc]; positivity
  have hg : 0 ≤ gₚ D x := by rw [right_on hxc]; positivity
  have hpole : |poleLeft D x - exp (D / 2) * gₚ D x| ≤
      (η / 2) * exp (D / 2) * (fₚ D x + gₚ D x) := by
    have hform : poleLeft D x - exp (D / 2) * gₚ D x =
        exp (D / 2) * (fₚ D x * cross D - gₚ D x * exp (-D)) := by
      unfold poleLeft diagonal
      ring
    rw [hform, abs_mul, abs_of_pos (Real.exp_pos _)]
    have hc : 0 ≤ cross D := mul_nonneg hD (Real.exp_pos _).le
    calc
      _ ≤ exp (D / 2) * (|fₚ D x * cross D| + |gₚ D x * exp (-D)|) :=
        mul_le_mul_of_nonneg_left (abs_sub _ _) (Real.exp_pos _).le
      _ ≤ exp (D / 2) * (fₚ D x * (η / 2) + gₚ D x * (η / 2)) := by
        rw [abs_of_nonneg (mul_nonneg hf hc), abs_of_nonneg (mul_nonneg hg (Real.exp_pos _).le)]
        gcongr
      _ = _ := by ring
  unfold residualLeft
  calc
    _ ≤ |primeTranslationApply D (fₚ D) x - exp (D / 2) * gₚ D x| +
        |poleLeft D x - exp (D / 2) * gₚ D x| := by
      rw [show primeTranslationApply D (fₚ D) x - poleLeft D x =
        (primeTranslationApply D (fₚ D) x - exp (D / 2) * gₚ D x) -
          (poleLeft D x - exp (D / 2) * gₚ D x) by ring]
      exact abs_sub _ _
    _ ≤ _ := (add_le_add (hT x hx) hpole).trans_eq (by ring)

private noncomputable def combination (D : ℝ) (a b : ℂ) (x : ℝ) : ℂ :=
  a * (fₚ D x : ℂ) + b * (gₚ D x : ℂ)

private theorem right_reflect (D x : ℝ) : gₚ D (D - x) = fₚ D x := by
  change fₚ D (D - (D - x)) = fₚ D x
  rw [show D - (D - x) = x by ring]

private theorem apply_reflect (D x : ℝ) :
    primeTranslationApply D (gₚ D) x = primeTranslationApply D (fₚ D) (D - x) := by
  unfold primeTranslationApply
  refine Finset.sum_congr rfl fun n _ ↦ ?_
  change Λ n / sqrt n * (fₚ D (D - (x + log n)) + fₚ D (D - (x - log n))) = _
  rw [show D - (x + log n) = D - x - log n by ring,
    show D - (x - log n) = D - x + log n by ring, add_comm]

private theorem apply_combination (D : ℝ) (a b : ℂ) (x : ℝ) :
    primeTranslationComplexApply D (combination D a b) x =
      a * (primeTranslationApply D (fₚ D) x : ℂ) +
        b * (primeTranslationApply D (gₚ D) x : ℂ) := by
  unfold primeTranslationComplexApply primeTranslationApply
  push_cast
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun n _ ↦ ?_
  unfold combination
  ring

private theorem pair_combination (D : ℝ) (a b : ℂ) (h : ℝ → ℝ)
    (hh : ContinuousOn h (Set.Icc 0 D)) :
    (∫ z in Set.Icc 0 D, (h z : ℂ) * combination D a b z) =
      a * (↑(∫ z in Set.Icc 0 D, h z * fₚ D z) : ℂ) +
        b * (↑(∫ z in Set.Icc 0 D, h z * gₚ D z) : ℂ) := by
  have hi (c : ℂ) (v : ℝ → ℝ) (hv : ContinuousOn v (Set.Icc 0 D)) :
      IntegrableOn (fun z ↦ c * (↑(h z * v z) : ℂ)) (Set.Icc 0 D) volume :=
    (continuousOn_const.mul (Complex.continuous_ofReal.comp_continuousOn
      (hh.mul hv))).integrableOn_Icc
  have hof (v : ℝ → ℝ) : (∫ z in Set.Icc 0 D, (v z : ℂ)) =
      (↑(∫ z in Set.Icc 0 D, v z) : ℂ) := integral_ofReal
  calc
    _ = ∫ z in Set.Icc 0 D, a * (↑(h z * fₚ D z) : ℂ) + b * (↑(h z * gₚ D z) : ℂ) := by
      apply setIntegral_congr_fun measurableSet_Icc
      intro z _
      dsimp only [combination]
      push_cast
      ring
    _ = _ := by
      rw [integral_add (hi a _ (left_continuousOn D)) (hi b _ (right_continuousOn D)),
        integral_const_mul, integral_const_mul, hof (fun z ↦ h z * fₚ D z),
        hof (fun z ↦ h z * gₚ D z)]

private theorem pole_combination {D : ℝ} (hD : 0 ≤ D) (a b : ℂ) (x : ℝ) :
    primeTranslationPoleApply D (combination D a b) x =
      a * (poleLeft D x : ℂ) + b * (poleLeft D (D - x) : ℂ) := by
  rw [primeTranslationPoleApply, pair_combination D a b _ (left_continuousOn D),
    pair_combination D a b _ (right_continuousOn D)]
  have hgf : (∫ z in Set.Icc 0 D, gₚ D z * fₚ D z) = cross D := by
    simpa only [mul_comm (gₚ D _) (fₚ D _)] using cross_integral hD
  have hff := left_sq_integral hD
  have hgg := right_sq_integral hD
  simp only [pow_two] at hff hgg
  rw [hgf, cross_integral hD, hff, hgg]
  unfold poleLeft
  rw [right_reflect]
  change _ = a * (↑(exp (D / 2) * (fₚ D x * cross D + gₚ D x * diagonal D)) : ℂ) +
    b * (↑(exp (D / 2) * (gₚ D x * cross D + fₚ D x * diagonal D)) : ℂ)
  push_cast
  ring

private theorem residual_combination {D : ℝ} (hD : 0 ≤ D) (a b : ℂ) (x : ℝ) :
    primeTranslationComplexApply D (combination D a b) x -
        primeTranslationPoleApply D (combination D a b) x =
      a * (residualLeft D x : ℂ) + b * (residualLeft D (D - x) : ℂ) := by
  rw [apply_combination, pole_combination hD, apply_reflect]
  unfold residualLeft
  push_cast
  ring

private theorem residual_bound {D η : ℝ} (hD : 0 ≤ D)
    (hR : ∀ x ∈ Set.Ioo 0 D, |residualLeft D x| ≤ η * exp (D / 2) * (fₚ D x + gₚ D x))
    (a b : ℂ) {x : ℝ} (hx : x ∈ Set.Ioo 0 D) :
    ‖primeTranslationComplexApply D (combination D a b) x -
      primeTranslationPoleApply D (combination D a b) x‖ ≤
      (η * exp (D / 2) * (‖a‖ + ‖b‖)) * (fₚ D x + gₚ D x) := by
  have hr := hR (D - x) ⟨sub_pos.mpr hx.2, sub_lt_self _ hx.1⟩
  rw [show fₚ D (D - x) = gₚ D x from rfl, right_reflect,
    add_comm (gₚ D x) (fₚ D x)] at hr
  rw [residual_combination hD]
  calc
    _ ≤ ‖a * (residualLeft D x : ℂ)‖ + ‖b * (residualLeft D (D - x) : ℂ)‖ := norm_add_le _ _
    _ = ‖a‖ * |residualLeft D x| + ‖b‖ * |residualLeft D (D - x)| := by
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    _ ≤ ‖a‖ * (η * exp (D / 2) * (fₚ D x + gₚ D x)) +
        ‖b‖ * (η * exp (D / 2) * (fₚ D x + gₚ D x)) :=
      add_le_add (mul_le_mul_of_nonneg_left (hR x hx) (norm_nonneg _))
        (mul_le_mul_of_nonneg_left hr (norm_nonneg _))
    _ = _ := by ring

private noncomputable def coeffCross (a b : ℂ) : ℝ := a.re * b.re + a.im * b.im

private theorem combination_sq_integral {D : ℝ} (hD : 0 ≤ D) (a b : ℂ) :
    (∫ z in Set.Icc 0 D, ‖combination D a b z‖ ^ 2) =
      (‖a‖ ^ 2 + ‖b‖ ^ 2) * diagonal D + 2 * coeffCross a b * cross D := by
  have hfa : IntegrableOn (fun z ↦ ‖a‖ ^ 2 * fₚ D z ^ 2) (Set.Icc 0 D) volume :=
    (continuousOn_const.mul ((left_continuousOn D).pow 2)).integrableOn_Icc
  have hgb : IntegrableOn (fun z ↦ ‖b‖ ^ 2 * gₚ D z ^ 2) (Set.Icc 0 D) volume :=
    (continuousOn_const.mul ((right_continuousOn D).pow 2)).integrableOn_Icc
  have hab : IntegrableOn (fun z ↦ ‖a‖ ^ 2 * fₚ D z ^ 2 + ‖b‖ ^ 2 * gₚ D z ^ 2)
      (Set.Icc 0 D) volume := hfa.add hgb
  have hfg : IntegrableOn (fun z ↦ (2 * coeffCross a b) * (fₚ D z * gₚ D z))
      (Set.Icc 0 D) volume :=
    (continuousOn_const.mul ((left_continuousOn D).mul (right_continuousOn D))).integrableOn_Icc
  calc
    _ = ∫ z in Set.Icc 0 D, (‖a‖ ^ 2 * fₚ D z ^ 2 + ‖b‖ ^ 2 * gₚ D z ^ 2) +
        (2 * coeffCross a b) * (fₚ D z * gₚ D z) := by
      apply setIntegral_congr_fun measurableSet_Icc
      intro z _
      simp only [combination, coeffCross, Complex.sq_norm, Complex.normSq_apply, Complex.add_re,
        Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
      ring
    _ = _ := by
      rw [integral_add hab hfg, integral_add hfa hgb, integral_const_mul,
        integral_const_mul, integral_const_mul, left_sq_integral hD, right_sq_integral hD,
        cross_integral hD]
      ring

-- A uniform lower Gram bound controls coefficients by the norm of the actual input.
private theorem coefficients_le {D : ℝ} (hD : 0 ≤ D) (hd : 3 / 4 ≤ diagonal D)
    (hc : cross D ≤ 1 / 4) (a b : ℂ) :
    (‖a‖ + ‖b‖) ^ 2 ≤ 4 * ∫ z in Set.Icc 0 D, ‖combination D a b z‖ ^ 2 := by
  let S := ‖a‖ ^ 2 + ‖b‖ ^ 2
  have hS : 0 ≤ S := by dsimp [S]; positivity
  have hcross₀ : 0 ≤ cross D := mul_nonneg hD (Real.exp_pos _).le
  have hC : -S ≤ 2 * coeffCross a b := by
    simp only [S, coeffCross, Complex.sq_norm, Complex.normSq_apply]
    nlinarith only [sq_nonneg (a.re + b.re), sq_nonneg (a.im + b.im)]
  have hgram : S / 2 ≤ ∫ z in Set.Icc 0 D, ‖combination D a b z‖ ^ 2 := by
    rw [combination_sq_integral hD]
    calc
      S / 2 = S * (1 / 2) := by ring
      _ ≤ S * (diagonal D - cross D) := mul_le_mul_of_nonneg_left (by linarith) hS
      _ = S * diagonal D + (-S) * cross D := by ring
      _ ≤ _ := add_le_add le_rfl (mul_le_mul_of_nonneg_right hC hcross₀)
  calc
    _ ≤ 2 * S := by dsimp [S]; nlinarith only [sq_nonneg (‖a‖ - ‖b‖)]
    _ = 4 * (S / 2) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hgram (by norm_num)

private theorem weight_sq_integral_le {D : ℝ} (hD : 0 ≤ D) (hc : cross D ≤ 1 / 4) :
    (∫ z in Set.Icc 0 D, (fₚ D z + gₚ D z) ^ 2) ≤ 4 := by
  have h := combination_sq_integral hD 1 1
  simp only [combination, one_mul, ← Complex.ofReal_add, Complex.norm_real, Real.norm_eq_abs,
    sq_abs, norm_one, one_pow, coeffCross, Complex.one_re, Complex.one_im, mul_one, mul_zero,
    add_zero] at h
  rw [h]
  have hp := Real.exp_pos (-D)
  unfold diagonal
  linarith

private theorem left_measurable (D : ℝ) : Measurable (fₚ D) :=
  (by fun_prop : Measurable (fun x : ℝ ↦ exp (-x / 2))).indicator measurableSet_Icc

private theorem right_measurable (D : ℝ) : Measurable (gₚ D) :=
  (left_measurable D).comp (by fun_prop : Measurable (fun x : ℝ ↦ D - x))

private theorem residual_left_measurable (D : ℝ) : Measurable (residualLeft D) := by
  have hT : Measurable (primeTranslationApply D (fₚ D)) := by
    unfold primeTranslationApply
    apply Finset.measurable_sum
    intro n _
    exact measurable_const.mul
      (((left_measurable D).comp (by fun_prop : Measurable (fun x : ℝ ↦ x + log n))).add
        ((left_measurable D).comp (by fun_prop : Measurable (fun x : ℝ ↦ x - log n))))
  exact hT.sub (measurable_const.mul (((left_measurable D).mul measurable_const).add
    ((right_measurable D).mul measurable_const)))

/-- For every positive relative tolerance, on all sufficiently long windows
`T - R` sends every `a f + b g` to an output of window `L²` norm at most
that tolerance times `exp (D/2)` times the input's own window `L²` norm. -/
public theorem primeTranslationSpanCancellation {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ D : ℝ in atTop, ∀ a b : ℂ,
      let u : ℝ → ℂ := fun x ↦ a * (fₚ D x : ℂ) + b * (gₚ D x : ℂ)
      primeTranslationWindowL2Norm D
        (fun x ↦ primeTranslationComplexApply D u x - primeTranslationPoleApply D u x) ≤
        ε * exp (D / 2) * primeTranslationWindowL2Norm D u := by
  let η := ε / 4
  have hη : 0 < η := by dsimp [η]; positivity
  have hquarter : (0 : ℝ) < 1 / 4 := by norm_num
  filter_upwards [residual_left_on hη, eventually_ge_atTop (0 : ℝ),
    cross_tendsto.eventually_lt_const hquarter,
    Real.tendsto_exp_neg_atTop_nhds_zero.eventually_lt_const hquarter] with D hR hD hc he
  intro a b
  let u := combination D a b
  let v : ℝ → ℂ := fun x ↦ primeTranslationComplexApply D u x - primeTranslationPoleApply D u x
  let K := η * exp (D / 2) * (‖a‖ + ‖b‖)
  let w : ℝ → ℝ := fun x ↦ fₚ D x + gₚ D x
  let μ := volume.restrict (Set.Icc 0 D)
  have hd : (3 / 4 : ℝ) ≤ diagonal D := by unfold diagonal; linarith
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have ho : ∀ᵐ x ∂μ, x ∈ Set.Ioo 0 D := by
    dsimp only [μ]
    rw [← Measure.restrict_congr_set (Ioo_ae_eq_Icc (μ := volume) (a := 0) (b := D))]
    exact ae_restrict_mem measurableSet_Ioo
  have hpoint : ∀ᵐ x ∂μ, ‖v x‖ ^ 2 ≤ K ^ 2 * w x ^ 2 := by
    filter_upwards [ho] with x hx
    have hxc : x ∈ Set.Icc 0 D := ⟨hx.1.le, hx.2.le⟩
    have hw : 0 ≤ w x := by dsimp [w]; rw [left_on hxc, right_on hxc]; positivity
    rw [← mul_pow]
    exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hK hw)).2 (residual_bound hD hR a b hx)
  have hvi : Measurable v := by
    have hright := (residual_left_measurable D).comp (by fun_prop : Measurable (fun x : ℝ ↦ D - x))
    have hsum : Measurable (fun x ↦ a * (residualLeft D x : ℂ) + b * (residualLeft D (D - x) : ℂ)) :=
      (measurable_const.mul (Complex.measurable_ofReal.comp (residual_left_measurable D))).add
        (measurable_const.mul (Complex.measurable_ofReal.comp hright))
    simpa only [v, u, residual_combination hD] using hsum
  have hmajor : Integrable (fun x ↦ K ^ 2 * w x ^ 2) μ :=
    (continuousOn_const.mul (((left_continuousOn D).add (right_continuousOn D)).pow 2)).integrableOn_Icc
  have hvi₂ : Integrable (fun x ↦ ‖v x‖ ^ 2) μ :=
    hmajor.mono' (hvi.norm.pow_const (2 : ℕ)).aestronglyMeasurable
      (hpoint.mono fun x hx ↦ by rwa [Real.norm_of_nonneg (sq_nonneg ‖v x‖)])
  have hnormSq : (∫ x, ‖v x‖ ^ 2 ∂μ) ≤ (ε * exp (D / 2)) ^ 2 * ∫ x, ‖u x‖ ^ 2 ∂μ := by
    calc
      _ ≤ ∫ x, K ^ 2 * w x ^ 2 ∂μ := integral_mono_ae hvi₂ hmajor hpoint
      _ = K ^ 2 * ∫ x, w x ^ 2 ∂μ := integral_const_mul _ _
      _ ≤ K ^ 2 * 4 := mul_le_mul_of_nonneg_left (weight_sq_integral_le hD hc.le) (sq_nonneg _)
      _ = (ε * exp (D / 2)) ^ 2 / 4 * (‖a‖ + ‖b‖) ^ 2 := by dsimp [K, η]; ring
      _ ≤ (ε * exp (D / 2)) ^ 2 / 4 * (4 * ∫ x, ‖u x‖ ^ 2 ∂μ) :=
        mul_le_mul_of_nonneg_left (coefficients_le hD hd hc.le a b) (by positivity)
      _ = _ := by ring
  change sqrt (∫ x, ‖v x‖ ^ 2 ∂μ) ≤ ε * exp (D / 2) * sqrt (∫ x, ‖u x‖ ^ 2 ∂μ)
  apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp
  rw [mul_pow, Real.sq_sqrt (integral_nonneg fun _ ↦ sq_nonneg _),
    Real.sq_sqrt (integral_nonneg fun _ ↦ sq_nonneg _)]
  exact hnormSq

end Masullo
