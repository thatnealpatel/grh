module

public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral

/-! # Centering a reflected log Mellin integral

Masullo supplies the Poisson correction (2.2.3.7), PDF p. 83, the norm-one
pairing (2.2.5.2), p. 95, its large-norm decay (2.2.5.9), p. 97, and the
right-half-plane radial integral (3.2.2.4)–(5), p. 125. This lemma takes
the separately established shifted reflection of the averaged profile as
input and computes its centered Mellin split, an ingredient in replacing
the conductor calculation used in (B.4.2.3), p. 614. Source reading is
provisional (pinned Markdown and numbered PDF text).
-/

open Filter MeasureTheory Set

namespace Masullo

private theorem measurable_logExp (s : ℂ) : Measurable (fun y : ℝ ↦ Complex.exp (s * y)) :=
  (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)).measurable

private theorem norm_logExp (s : ℂ) (y : ℝ) :
    ‖Complex.exp (s * (y : ℂ))‖ = Real.exp (s.re * y) := by
  rw [Complex.norm_exp, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]

private theorem centeredLogMellin_integrableOn {Q : ℝ → ℂ} (hQ : Measurable Q) (d : ℝ)
    (hdecay : ∀ N : ℕ, ∃ B : ℝ, 0 ≤ B ∧ ∀ y : ℝ, d ≤ y →
      ‖Q y‖ ≤ B * Real.exp (-(N : ℝ) * (y - d)))
    (h2 : Integrable (fun y : ℝ ↦ Q y * Complex.exp ((2 : ℂ) * y))) (s : ℂ) :
    IntegrableOn (fun y : ℝ ↦ Q y * Complex.exp (s * y)) (Ici 0) := by
  let T := max 0 d
  have hT : 0 ≤ T := le_max_left ..
  have hF : Measurable (fun y : ℝ ↦ Q y * Complex.exp (s * y)) := hQ.mul (measurable_logExp s)
  -- Compare with the integrable weight at 2 on the bounded interval only.
  have hcompact : IntegrableOn (fun y : ℝ ↦ Q y * Complex.exp (s * y)) (Icc 0 T) := by
    refine (h2.integrableOn (s := Icc 0 T)).norm.const_mul (Real.exp (|s.re - 2| * T)) |>.mono'
      hF.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Icc] with y hy
    change 0 ≤ y ∧ y ≤ T at hy
    have hbound : (s.re - 2) * y ≤ |s.re - 2| * T :=
      (mul_le_mul_of_nonneg_right (le_abs_self _) hy.1).trans
        (mul_le_mul_of_nonneg_left hy.2 (abs_nonneg _))
    have hTwo : (2 : ℂ).re = 2 := by norm_num
    simp only [norm_mul, norm_logExp, hTwo]
    rw [show s.re * y = (s.re - 2) * y + 2 * y by ring, Real.exp_add]
    calc
      _ = Real.exp ((s.re - 2) * y) * (‖Q y‖ * Real.exp (2 * y)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hbound)
        (mul_nonneg (norm_nonneg _) (Real.exp_nonneg _))
  -- Apply the decay hypothesis only where the original argument is nonnegative.
  have htail : IntegrableOn (fun y : ℝ ↦ Q y * Complex.exp (s * y)) (Ioi T) := by
    obtain ⟨N, hN⟩ := exists_nat_ge (s.re + 1)
    obtain ⟨B, hB, hdec⟩ := hdecay N
    refine (integrableOn_exp_mul_Ioi (a := -1) (by norm_num) T).const_mul
      (B * Real.exp ((N : ℝ) * d)) |>.mono' hF.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    have hTy : T ≤ y := le_of_lt hy
    have hy0 := hT.trans hTy
    rw [norm_mul, norm_logExp]
    calc
      _ ≤ (B * Real.exp (-(N : ℝ) * (y - d))) * Real.exp (s.re * y) :=
        mul_le_mul_of_nonneg_right (hdec y ((le_max_right 0 d).trans hTy)) (Real.exp_nonneg _)
      _ = (B * Real.exp ((N : ℝ) * d)) * Real.exp ((s.re - N) * y) := by
        rw [mul_assoc B, ← Real.exp_add, mul_assoc B, ← Real.exp_add]
        congr 2
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (by linarith) hy0))
        (mul_nonneg hB (Real.exp_nonneg _))
  rw [← Icc_union_Ioi_eq_Ici hT]
  exact hcompact.union htail

private theorem differentiable_logMellin_Ici {Q : ℝ → ℂ} (hQ : Measurable Q)
    (hInt : ∀ s : ℂ, IntegrableOn (fun y : ℝ ↦ Q y * Complex.exp (s * y)) (Ici 0)) :
    Differentiable ℂ (fun s : ℂ ↦ ∫ y in Ici (0 : ℝ), Q y * Complex.exp (s * y)) := by
  intro z
  let F (w : ℂ) (y : ℝ) := Q y * Complex.exp (w * y)
  let D (w : ℂ) (y : ℝ) := (y : ℂ) * F w y
  have hF (w : ℂ) : Measurable (F w) := hQ.mul (measurable_logExp w)
  have hD : Measurable (D z) := Complex.continuous_ofReal.measurable.mul (hF z)
  -- On the unit ball about z, the weight with real exponent z.re + 2 absorbs both
  -- the change in the exponential and the factor y from differentiation.
  let b : ℂ := (z.re + 2 : ℝ)
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (F := F) (F' := D)
    (Metric.ball_mem_nhds z zero_lt_one) (Eventually.of_forall fun w ↦ (hF w).aestronglyMeasurable)
    (hInt z) hD.aestronglyMeasurable ?_ (hInt b).norm ?_).2.differentiableAt
  · filter_upwards [ae_restrict_mem measurableSet_Ici] with y hy w hw
    have hy0 : 0 ≤ y := hy
    have hwz : w.re ≤ z.re + 1 := by
      have hdist : ‖w - z‖ < 1 := by simpa [dist_eq_norm] using (Metric.mem_ball.mp hw)
      have h := (le_abs_self (w - z).re).trans ((Complex.abs_re_le_norm _).trans hdist.le)
      rw [Complex.sub_re] at h
      linarith
    have hyexp : y ≤ Real.exp y := by linarith [Real.add_one_le_exp y]
    simp only [D, F, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hy0, norm_logExp]
    calc
      _ ≤ Real.exp y * (‖Q y‖ * Real.exp ((z.re + 1) * y)) := by
        gcongr
      _ = _ := by
        rw [show b.re * y = y + (z.re + 1) * y by simp [b]; ring, Real.exp_add]
        ring
  · refine ae_of_all _ fun y w _ ↦ ?_
    have hlin : HasDerivAt (fun v : ℂ ↦ v * (y : ℂ)) (y : ℂ) w := by
      simpa only [id_eq, one_mul] using (hasDerivAt_id w).mul_const (y : ℂ)
    have hExp : HasDerivAt (fun v : ℂ ↦ Complex.exp (v * y))
        (Complex.exp (w * y) * y) w :=
      (Complex.hasDerivAt_exp (w * y)).comp w hlin
    simpa only [F, D, mul_comm (y : ℂ), mul_assoc] using hExp.const_mul (Q y)

private theorem integrableOn_neg_Iic {f : ℝ → ℂ} (hf : IntegrableOn f (Ici 0)) :
    IntegrableOn (fun y : ℝ ↦ f (-y)) (Iic 0) := by
  have he : MeasurableEmbedding (fun y : ℝ ↦ -y) :=
    (Homeomorph.neg ℝ).isClosedEmbedding.measurableEmbedding
  rw [← Measure.map_neg_eq_self (volume : Measure ℝ)] at hf
  have h := he.integrableOn_map_iff.mp hf
  simpa only [Function.comp_def, neg_preimage, neg_Ici, neg_zero] using h

/-- Split the Mellin integral of a reflected log profile at its symmetry center.
The positive centered half is entire; the reflected half contributes that same
function at `1 - s` and the two explicit zero modes. -/
public theorem centeredLogMellin_split {P : ℝ → ℂ} {δ : ℝ} {a : ℂ}
    (hP : Measurable P)
    (hdecay : ∀ N : ℕ, ∃ B : ℝ, 0 ≤ B ∧ ∀ x : ℝ, 0 ≤ x →
      ‖P x‖ ≤ B * Real.exp (-(N : ℝ) * x))
    (hreflect : ∀ x : ℝ, P x + a =
      (Real.exp (-δ / 2 - x) : ℂ) * (P (-δ - x) + a))
    (hlocal : ∀ s : ℂ, 1 < s.re → Integrable (fun x : ℝ => P x * Complex.exp (s * x))) :
    let J (s : ℂ) := ∫ y in Set.Ici (0 : ℝ), P (y - δ / 2) * Complex.exp (s * y)
    Differentiable ℂ J ∧ ∀ s : ℂ, 1 < s.re →
      (∫ x : ℝ, P x * Complex.exp (s * x)) =
        Complex.exp (-(δ : ℂ) / 2 * s) * (J s + J (1 - s) + a / (s - 1) - a / s) := by
  let d : ℝ := δ / 2
  let Q (y : ℝ) := P (y - d)
  let E (s : ℂ) (y : ℝ) := Complex.exp (s * y)
  let F (s : ℂ) (y : ℝ) := Q y * E s y
  let G (s : ℂ) (x : ℝ) := P x * E s x
  have hQ : Measurable Q := hP.comp (continuous_id.sub continuous_const).measurable
  have htrans (s : ℂ) (y : ℝ) : F s y = Complex.exp ((d : ℂ) * s) * G s (y - d) := by
    dsimp only [F, Q, E, G]
    rw [mul_left_comm, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  have hcenter (s : ℂ) (hs : 1 < s.re) : Integrable (F s) := by
    have h := (measurePreserving_add_right (volume : Measure ℝ) (-d)).integrable_comp_of_integrable
      (hlocal s hs)
    have heq : F s = fun y ↦ Complex.exp ((d : ℂ) * s) * G s (y + -d) :=
      funext fun y ↦ by rw [htrans, sub_eq_add_neg]
    rw [heq]
    exact h.const_mul _
  have hpos : ∀ s : ℂ, IntegrableOn (F s) (Ici 0) := by
    refine centeredLogMellin_integrableOn hQ d (fun N ↦ ?_) (hcenter 2 (by norm_num))
    obtain ⟨B, hB, h⟩ := hdecay N
    exact ⟨B, hB, fun y hy ↦ h _ (sub_nonneg.mpr hy)⟩
  refine ⟨differentiable_logMellin_Ici hQ hpos, fun s hs ↦ ?_⟩
  change (∫ x, G s x) = Complex.exp (-(δ : ℂ) / 2 * s) *
    ((∫ y in Ici 0, F s y) + (∫ y in Ici 0, F (1 - s) y) + a / (s - 1) - a / s)
  have hshift (y : ℝ) : G s (y + -d) = Complex.exp (-(δ : ℂ) / 2 * s) * F s y := by
    rw [htrans, ← mul_assoc, ← Complex.exp_add, show (d : ℂ) = (δ : ℂ) / 2 by simp [d]]
    rw [show -(δ : ℂ) / 2 * s + (δ : ℂ) / 2 * s = 0 by ring, Complex.exp_zero, one_mul]
    rfl
  have hsymm (y : ℝ) : F s y = F (1 - s) (-y) + a * E (s - 1) y - a * E s y := by
    have h := hreflect (y - d)
    rw [show -δ / 2 - (y - d) = -y by dsimp [d]; ring,
      show -δ - (y - d) = -y - d by dsimp [d]; ring] at h
    have h' : Q y = Complex.exp (-(y : ℂ)) * (Q (-y) + a) - a := by
      rw [← Complex.ofReal_neg, ← Complex.ofReal_exp, ← h, add_sub_cancel_right]
    have he₁ : Complex.exp (-(y : ℂ)) * E s y = E (1 - s) (-y) := by
      simp only [E, Complex.ofReal_neg, ← Complex.exp_add]
      congr 1
      ring
    have he₂ : Complex.exp (-(y : ℂ)) * E s y = E (s - 1) y := by
      simp only [E, ← Complex.exp_add]
      congr 1
      ring
    rw [show F s y = Q y * E s y from rfl, h', sub_mul, mul_add, add_mul,
      mul_comm (Complex.exp (-(y : ℂ))) (Q (-y)), mul_assoc (Q (-y)), he₁,
      mul_comm (Complex.exp (-(y : ℂ))) a, mul_assoc a, he₂]
  have ha : 0 < (s - 1).re := by simpa using sub_pos.mpr hs
  have hb : 0 < s.re := zero_lt_one.trans hs
  have hleft : (∫ y in Iic 0, F s y) = (∫ y in Ici 0, F (1 - s) y) + a / (s - 1) - a / s := by
    have h₁ := integrableOn_neg_Iic (hpos (1 - s))
    have h₂ : IntegrableOn (fun y ↦ a * E (s - 1) y) (Iic 0) :=
      (integrableOn_exp_mul_complex_Iic ha 0).const_mul a
    have h₃ : IntegrableOn (fun y ↦ a * E s y) (Iic 0) :=
      (integrableOn_exp_mul_complex_Iic hb 0).const_mul a
    have h₁₂ : IntegrableOn (fun y ↦ F (1 - s) (-y) + a * E (s - 1) y) (Iic 0) := h₁.add h₂
    calc
      _ = ∫ y in Iic 0, F (1 - s) (-y) + a * E (s - 1) y - a * E s y :=
        setIntegral_congr_fun measurableSet_Iic (fun y _ ↦ hsymm y)
      _ = _ := by
        rw [integral_sub h₁₂ h₃, integral_add h₁ h₂, integral_comp_neg_Iic, neg_zero,
          ← integral_Ici_eq_integral_Ioi, integral_const_mul, integral_const_mul]
        simp only [E, integral_exp_mul_complex_Iic ha, integral_exp_mul_complex_Iic hb,
          Complex.ofReal_zero, mul_zero, Complex.exp_zero, mul_one_div]
  calc
    _ = ∫ y : ℝ, G s (y + -d) := (integral_add_right_eq_self (G s) (-d)).symm
    _ = Complex.exp (-(δ : ℂ) / 2 * s) * (∫ y : ℝ, F s y) := by
      simp only [hshift, integral_const_mul]
    _ = _ := by
      rw [← integral_add_compl measurableSet_Ioi (hcenter s hs), compl_Ioi,
        ← integral_Ici_eq_integral_Ioi, hleft]
      ring

end Masullo
