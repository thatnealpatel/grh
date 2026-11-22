module

public import Mathlib.MeasureTheory.Integral.Prod
public import Props.ArchimedeanGammaLogDerivative
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Tactic.FieldSimp

/-! First-moment joint domination for the shifted, subtracted Gamma kernel. -/

open Complex MeasureTheory Set

namespace Masullo

/-- The Gauss difference after the substitution `t = exp (-d * x)`.
Keep the two terms together at the origin. -/
@[expose] public noncomputable def archimedeanGammaKernel (d : ℝ) (w : ℂ) (x : ℝ) : ℂ :=
  (exp (-(d : ℂ) * (x : ℂ)) - exp (-w * (x : ℂ))) /
    (1 - exp (-(d : ℂ) * (x : ℂ)))

private theorem one_sub_exp_neg_le (y : ℝ) : 1 - Real.exp (-y) ≤ y := by
  linarith [Real.add_one_le_exp (-y)]

private theorem abs_real_damping_sub_le (d u : ℝ) {x : ℝ} (hx : 0 < x) :
    |Real.exp (-d * x) - Real.exp (-u * x)| ≤ x * Real.exp (-min d u * x) * |d - u| := by
  wlog h : d ≤ u generalizing d u
  · simpa only [abs_sub_comm, min_comm] using this u d (le_of_not_ge h)
  have horder : Real.exp (-u * x) ≤ Real.exp (-d * x) := by
    apply Real.exp_le_exp.mpr
    gcongr
  rw [abs_of_nonneg (sub_nonneg.mpr horder), min_eq_left h, abs_of_nonpos (sub_nonpos.mpr h),
    show -u * x = -d * x + -((u - d) * x) by ring, Real.exp_add, ← mul_one_sub]
  calc
    _ ≤ Real.exp (-d * x) * ((u - d) * x) :=
      mul_le_mul_of_nonneg_left (one_sub_exp_neg_le _) (Real.exp_pos _).le
    _ = _ := by ring

/-- Pointwise domination of the subtracted Gamma kernel by an exponential
with a first-moment weight. -/
public theorem norm_archimedeanGammaKernel_le {d u v x : ℝ} (hd : 0 < d) (hx : 0 < x) :
    ‖archimedeanGammaKernel d ((u : ℂ) + (v : ℂ) * I) x‖ ≤
      (|d - u| + |v|) * ((1 / d + x) * Real.exp (-min d u * x)) := by
  let E (q : ℝ) := Real.exp (-q * x)
  let P := exp (I * ((-v * x : ℝ) : ℂ))
  have hdamp (q : ℝ) : exp (-(q : ℂ) * (x : ℂ)) = (E q : ℂ) := by
    dsimp only [E]
    rw [Complex.ofReal_exp, Complex.ofReal_mul, Complex.ofReal_neg]
  have hphase : exp (-((u : ℂ) + (v : ℂ) * I) * (x : ℂ)) = (E u : ℂ) * P := by
    rw [← hdamp, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hchord : ‖(1 : ℂ) - P‖ ≤ |v| * x := by
    rw [norm_sub_rev]
    simpa [P, Real.norm_eq_abs, abs_mul, abs_of_pos hx] using
      (Real.norm_exp_I_mul_ofReal_sub_one_le (x := -v * x))
  have hmono : E u ≤ E (min d u) := by
    dsimp [E]
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (neg_le_neg (min_le_right d u)) hx.le)
  have hnum : ‖(E d : ℂ) - (E u : ℂ) * P‖ ≤ x * E (min d u) * (|d - u| + |v|) := by
    rw [show (E d : ℂ) - (E u : ℂ) * P = ((E d : ℂ) - (E u : ℂ)) + (E u : ℂ) * (1 - P) by ring]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    calc
      _ ≤ x * E (min d u) * |d - u| + E (min d u) * (|v| * x) :=
        add_le_add (abs_real_damping_sub_le d u hx)
          (mul_le_mul hmono hchord (norm_nonneg _) (Real.exp_pos _).le)
      _ = _ := by ring
  -- `1 + dx ≤ exp (dx)` bounds the denominator from below near zero.
  have hd0 : 0 < 1 - E d :=
    sub_pos.mpr (Real.exp_lt_one_iff.mpr (mul_neg_of_neg_of_pos (neg_neg_of_pos hd) hx))
  have hrecip : (d * x + 1) * E d ≤ 1 := by
    dsimp [E]
    rw [show -d * x = -(d * x) by ring, Real.exp_neg, mul_inv_le_iff₀ (Real.exp_pos _), one_mul]
    exact Real.add_one_le_exp _
  have hxden : x ≤ (1 / d + x) * (1 - E d) := by
    apply (mul_le_mul_iff_right₀ hd).mp
    have h : d * x ≤ (d * x + 1) * (1 - E d) := by
      linarith only [hrecip, mul_sub (d * x + 1) 1 (E d)]
    calc
      d * x ≤ (d * x + 1) * (1 - E d) := h
      _ = d * ((1 / d + x) * (1 - E d)) := by field_simp; ring
  rw [archimedeanGammaKernel, hdamp, hphase, norm_div, ← Complex.ofReal_one,
    ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hd0]
  apply (div_le_iff₀ hd0).2
  refine hnum.trans ?_
  calc
    _ ≤ ((1 / d + x) * (1 - E d)) * E (min d u) * (|d - u| + |v|) := by gcongr
    _ = _ := by ring

private theorem integrableOn_gammaKernelEnvelope {d m : ℝ} (hm : 0 < m) :
    IntegrableOn (fun x : ℝ ↦ (1 / d + x) * Real.exp (-m * x)) (Ioi 0) := by
  have he : IntegrableOn (fun x : ℝ ↦ Real.exp (-m * x)) (Ioi 0) :=
    integrableOn_exp_mul_Ioi (neg_neg_of_pos hm) 0
  have hxe : IntegrableOn (fun x : ℝ ↦ x * Real.exp (-m * x)) (Ioi 0) := by
    simpa using (integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := 1) (by norm_num) one_pos hm)
  exact ((he.const_mul (1 / d)).add hxe).congr
    (Filter.Eventually.of_forall fun x ↦ (add_mul (1 / d) x _).symm)

/-- On a fixed positive line the subtracted digamma integral is bounded by
an ordinate-independent constant times `1 + |t|`. -/
public theorem archimedeanGammaFactor_rightLine_logDeriv_bound {a d b : ℝ}
    (ha : 0 < a) (hd : 0 < d) (hb : 0 ≤ b) (B τ : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ,
      ‖logDeriv (archimedeanGammaFactor B d b τ) ((a : ℂ) + (t : ℂ) * I)‖ ≤ C * (1 + |t|) := by
  let m := min d (a + b)
  let E (x : ℝ) := (1 / d + x) * Real.exp (-m * x)
  let A : ℂ := -((Real.log B : ℂ) + (Real.eulerMascheroniConstant : ℂ)) / (d : ℂ)
  let D := ∫ x in Ioi (0 : ℝ), E x
  have hD : 0 ≤ D := by
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with x hx
    have hx' : 0 < x := hx
    dsimp only [E]
    positivity
  have hEi : IntegrableOn E (Ioi 0) :=
    integrableOn_gammaKernelEnvelope (lt_min hd (add_pos_of_pos_of_nonneg ha hb))
  refine ⟨‖A‖ + (|d - (a + b)| + |τ| + 1) * D + 1, by positivity, fun t ↦ ?_⟩
  let s : ℂ := (a : ℂ) + (t : ℂ) * I
  let c := |d - (a + b)| + |t + τ|
  have hs : 0 < s.re := by simpa [s, mul_re] using ha
  have hw : s + (b : ℂ) + (τ : ℂ) * I = ((a + b : ℝ) : ℂ) + ((t + τ : ℝ) : ℂ) * I := by
    dsimp [s]
    push_cast
    ring
  have hEq : logDeriv (archimedeanGammaFactor B d b τ) s =
      A + ∫ x in Ioi (0 : ℝ), archimedeanGammaKernel d
        (((a + b : ℝ) : ℂ) + ((t + τ : ℝ) : ℂ) * I) x := by
    simpa only [A, archimedeanGammaKernel, hw] using
      (logDeriv_archimedeanGammaFactor_eq_integral (B := B) (τ := τ) hd hb hs).2.2
  change ‖logDeriv (archimedeanGammaFactor B d b τ) s‖ ≤ _
  rw [hEq]
  refine (norm_add_le _ _).trans ?_
  have hInt := norm_integral_le_of_norm_le (hEi.const_mul c)
    (f := archimedeanGammaKernel d (((a + b : ℝ) : ℂ) + ((t + τ : ℝ) : ℂ) * I)) (by
      filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with x hx
      exact norm_archimedeanGammaKernel_le hd hx)
  rw [integral_const_mul] at hInt
  refine (add_le_add_right hInt ‖A‖).trans ?_
  have hc : c ≤ (|d - (a + b)| + |τ| + 1) * (1 + |t|) := by
    dsimp only [c]
    nlinarith [abs_add_le t τ, abs_nonneg t, abs_nonneg τ, abs_nonneg (d - (a + b)),
      mul_nonneg (abs_nonneg t) (abs_nonneg (d - (a + b))),
      mul_nonneg (abs_nonneg t) (abs_nonneg τ)]
  calc
    ‖A‖ + c * D ≤ ‖A‖ + ((|d - (a + b)| + |τ| + 1) * (1 + |t|)) * D :=
      add_le_add_right (mul_le_mul_of_nonneg_right hc hD) _
    _ ≤ _ := by
      nlinarith [mul_nonneg (norm_nonneg A) (abs_nonneg t), abs_nonneg t]

/-- Any measurable weight with an integrable first absolute ordinate moment
permits exchange on the right line *with the subtraction intact*. -/
public theorem integrable_archimedeanGamma_rightLine_product {a d b τ : ℝ} (ha : 0 < a)
    (hd : 0 < d) (hb : 0 ≤ b) {W : ℝ → ℂ} (hW : Measurable W)
    (hWt : Integrable (fun t ↦ ‖W t‖ * (1 + |t|))) :
    Integrable (fun p : ℝ × ℝ ↦ W p.1 * archimedeanGammaKernel d
      (((a : ℂ) + (p.1 : ℂ) * I) + ((b : ℂ) + (τ : ℂ) * I)) p.2)
      ((volume : Measure ℝ).prod (volume.restrict (Ioi 0))) := by
  let m := min d (a + b)
  let C := |d - (a + b)| + |τ| + 1
  have hm : 0 < m := lt_min hd (add_pos_of_pos_of_nonneg ha hb)
  have hEnv := integrableOn_gammaKernelEnvelope (d := d) hm
  refine (hWt.mul_prod (hEnv.const_mul C)).mono'
    (Measurable.aestronglyMeasurable (by unfold archimedeanGammaKernel; fun_prop)) ?_
  have hx : ∀ᵐ p : ℝ × ℝ ∂((volume : Measure ℝ).prod (volume.restrict (Ioi 0))), p.2 ∈ Ioi 0 :=
    (Measure.ae_prod_mem_iff_ae_ae_mem (measurable_snd measurableSet_Ioi)).mpr <|
      Filter.Eventually.of_forall fun _ ↦ ae_restrict_mem measurableSet_Ioi
  filter_upwards [hx] with ⟨t, x⟩ hx
  have hx' : 0 < x := hx
  change ‖W t * archimedeanGammaKernel d _ x‖ ≤ ‖W t‖ * (1 + |t|) *
    (C * ((1 / d + x) * Real.exp (-m * x)))
  rw [norm_mul, show ((a : ℂ) + (t : ℂ) * I) + ((b : ℂ) + (τ : ℂ) * I) =
    ((a + b : ℝ) : ℂ) + ((t + τ : ℝ) : ℂ) * I by push_cast; ring]
  have hC : |d - (a + b)| + |t + τ| ≤ (1 + |t|) * C := by
    calc
      _ ≤ |d - (a + b)| + (|t| + |τ|) := add_le_add_right (abs_add_le t τ) _
      _ ≤ _ := by
        dsimp [C]
        nlinarith [mul_nonneg (abs_nonneg t) (abs_nonneg (d - (a + b))),
          mul_nonneg (abs_nonneg t) (abs_nonneg τ)]
  calc
    _ ≤ ‖W t‖ * ((|d - (a + b)| + |t + τ|) * ((1 / d + x) * Real.exp (-m * x))) :=
      mul_le_mul_of_nonneg_left (norm_archimedeanGammaKernel_le hd hx') (norm_nonneg _)
    _ ≤ ‖W t‖ * (((1 + |t|) * C) * ((1 / d + x) * Real.exp (-m * x))) := by gcongr
    _ = _ := by ring

end Masullo
