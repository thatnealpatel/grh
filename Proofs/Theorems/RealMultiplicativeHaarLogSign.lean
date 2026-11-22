module

public import Lemmas.ArchimedeanCompletionHaar
import Mathlib.MeasureTheory.Function.JacobianOneDim

/-! # Signed log coordinates for real multiplicative Haar

Definitions A.3.1.2(1), PDF p. 556, and A.3.2.2(1), p. 560, specify
`dy / |y|` off zero. The positive half-line appears in (A.2.3.20),
p. 550. To measure this restriction and retain both signs at the other
real places, we compute the pushforward to log-radius and sign. The
change of variables is a local calculation, not the quotient volume.
The locators use the pinned Markdown and PDF text (provisional;
rendered pages were not inspected).
-/

open MeasureTheory NumberField InfinitePlace.Completion Set
open scoped ENNReal

namespace Masullo

private theorem measurable_realLogSign :
    Measurable (fun y : ℝ ↦ (Real.log |y|, if 0 < y then true else false)) :=
  (Real.measurable_log.comp continuous_abs.measurable).prodMk
    (Measurable.ite measurableSet_Ioi measurable_const measurable_const)

private theorem lintegral_realLogSign_half (f : ℝ × Bool → ℝ≥0∞) (b : Bool) :
    (∫⁻ y in (if b then Ioi (0 : ℝ) else Iio 0),
        ENNReal.ofReal |y|⁻¹ * f (Real.log |y|, if 0 < y then true else false)) =
      ∫⁻ x, f (x, b) := by
  let e (x : ℝ) : ℝ := if b then Real.exp x else -Real.exp x
  have hd (x : ℝ) : HasDerivAt e (e x) x := by
    cases b <;> simp only [e, Bool.false_eq_true, ↓reduceIte]
    · exact (Real.hasDerivAt_exp x).neg
    · exact Real.hasDerivAt_exp x
  have hinj : Function.Injective e := by
    cases b <;> simp only [e, Bool.false_eq_true, ↓reduceIte]
    · exact neg_injective.comp Real.exp_injective
    · exact Real.exp_injective
  have himg : e '' univ = if b then Ioi 0 else Iio 0 := by
    rw [image_univ]
    cases b <;> simp only [e, Bool.false_eq_true, ↓reduceIte]
    · ext y
      exact ⟨fun ⟨x, hx⟩ ↦ hx ▸ neg_neg_of_pos (Real.exp_pos x),
        fun hy ↦ ⟨Real.log (-y), by
          change -Real.exp (Real.log (-y)) = y
          rw [Real.exp_log (neg_pos.mpr hy), neg_neg]⟩⟩
    · exact Real.range_exp
  rw [← himg, lintegral_image_eq_lintegral_abs_deriv_mul MeasurableSet.univ
    (fun x _ ↦ (hd x).hasDerivWithinAt) hinj.injOn, Measure.restrict_univ]
  apply lintegral_congr
  intro x
  have ha : |e x| = Real.exp x := by
    cases b <;> simp [e, abs_of_pos (Real.exp_pos x)]
  have hs : (if 0 < e x then true else false) = b := by
    cases b <;> simp [e, (Real.exp_pos x).not_gt, Real.exp_pos]
  rw [ha, hs, Real.log_exp, ← mul_assoc, ← ENNReal.ofReal_mul (Real.exp_pos x).le,
    mul_inv_cancel₀ (Real.exp_ne_zero x), ENNReal.ofReal_one, one_mul]

/-- Log absolute value and sign carry `dy / |y|` to Lebesgue times counting measure. -/
public theorem realMultiplicativeDensity_map_logSign :
    Measure.map (fun y : ℝ ↦ (Real.log |y|, if 0 < y then true else false))
        ((volume : Measure ℝ).withDensity (fun y ↦ ENNReal.ofReal |y|⁻¹)) =
      (volume : Measure ℝ).prod (Measure.count : Measure Bool) := by
  refine Measure.ext_of_lintegral _ fun f hf ↦ ?_
  have hf' : Measurable (fun y : ℝ ↦ f (Real.log |y|, if 0 < y then true else false)) :=
    hf.comp measurable_realLogSign
  rw [lintegral_map hf measurable_realLogSign,
    lintegral_withDensity_eq_lintegral_mul _ (by fun_prop) hf',
    lintegral_prod_symm' _ hf, lintegral_count, tsum_bool]
  -- Split at the null origin, and apply the signed exponential on each half-line.
  have hsplit : Iio (0 : ℝ) ∪ Ioi 0 = ({0} : Set ℝ)ᶜ := Iio_union_Ioi
  have hdisj : Disjoint (Iio (0 : ℝ)) (Ioi 0) :=
    disjoint_left.mpr (fun _ hlt hgt ↦ lt_asymm hlt hgt)
  calc
    _ = ∫⁻ y in Iio (0 : ℝ) ∪ Ioi 0,
        ENNReal.ofReal |y|⁻¹ * f (Real.log |y|, if 0 < y then true else false) := by
      rw [hsplit, restrict_compl_singleton]
      rfl
    _ = _ := by
      rw [lintegral_union measurableSet_Ioi hdisj]
      exact congrArg₂ (· + ·) (lintegral_realLogSign_half f false) (lintegral_realLogSign_half f true)

/-- Signed log-coordinate measure on the actual units of any real completion. -/
public theorem realCompletionHaar_map_logSign {K : Type*} [Field K] {v : InfinitePlace K}
    [MeasurableSpace v.Completionˣ] [BorelSpace v.Completionˣ] (hv : v.IsReal) :
    Measure.map
      (fun u : v.Completionˣ ↦
        (Real.log ‖u.val‖, if 0 < extensionEmbeddingOfIsReal hv u.val then true else false))
      (realCompletionHaar hv) =
      (volume : Measure ℝ).prod (Measure.count : Measure Bool) := by
  rw [← realMultiplicativeDensity_map_logSign, ← realCompletionHaar_map hv,
    Measure.map_map measurable_realLogSign (realCompletionEmbedding hv).measurable]
  congr 1
  funext u
  have hn := (isometry_extensionEmbeddingOfIsReal hv).dist_eq u.val 0
  simp only [map_zero, dist_zero_right, Real.norm_eq_abs] at hn
  simp only [Function.comp_apply, hn]

end Masullo
