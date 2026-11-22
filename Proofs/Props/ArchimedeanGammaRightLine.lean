module

public import Props.ArchimedeanGammaLogDerivative
public import Props.CompactLogMellin
import Lemmas.ArchimedeanGammaDomination
import Lemmas.CompactLogMellinInversion
import Mathlib.Tactic.Ring

/-!
# The tested Archimedean Gamma pair

In (B.4.2.13)–(16), p. 616, Masullo pairs the two Mellin weights and
uses Mellin inversion after moving to the central line. For compact
smooth log profiles we instead invert on the original right line.
The literal extracted (B.4.2.15) has a nonintegrable identity subtraction
at infinity on profiles with `g 0 ≠ 0`. The checked scalar identity
retains the contact constant and gives an exponentially decaying
subtraction. The joint first-moment bound justifies exchanging the
integrals without separating the singular terms at zero. This is a
repair in the parameterized local factors of (3.2.1.3)–(5), p. 123,
not a classification of local characters or the global contour formula.
These manuscript readings use extraction, not the rendered pages.
-/

open Complex MeasureTheory Set
open scoped ContDiff

namespace Masullo

/-- Evaluate the direct leg of (B.4.2.13) with absolute integrability
on the line and on the positive log half-line. The scalar factor is
written with `Real.log B`; a positive base identifies the local factors. -/
public theorem compactLogMellin_archimedeanGamma_direct {g : ℝ → ℂ}
    (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g)
    {a d b : ℝ} (ha : 0 < a) (hd : 0 < d) (hb : 0 ≤ b) (B τ : ℝ) :
    let s := fun t : ℝ ↦ (a : ℂ) + (t : ℂ) * I
    let W := fun t ↦ compactLogMellin g (s t) * logDeriv (archimedeanGammaFactor B d b τ) (s t)
    let K := fun x : ℝ ↦ (g 0 * exp (-(d : ℂ) * (x : ℂ)) -
      exp (-((b : ℂ) + (τ : ℂ) * I) * (x : ℂ)) * g x) /
        (1 - exp (-(d : ℂ) * (x : ℂ)))
    Integrable W ∧ IntegrableOn K (Ioi 0) ∧
      (∫ t, W t) / (2 * (Real.pi : ℂ)) =
        (-((Real.log B : ℂ) + (Real.eulerMascheroniConstant : ℂ)) / (d : ℂ)) * g 0 +
          ∫ x in Ioi (0 : ℝ), K x := by
  let s (t : ℝ) : ℂ := (a : ℂ) + (t : ℂ) * I
  let W (t : ℝ) := compactLogMellin g (s t)
  let β : ℂ := (b : ℂ) + (τ : ℂ) * I
  let A : ℂ := -((Real.log B : ℂ) + (Real.eulerMascheroniConstant : ℂ)) / (d : ℂ)
  let c : ℂ := 2 * (Real.pi : ℂ)
  let E (x : ℝ) := exp (-(d : ℂ) * (x : ℂ))
  let H (t x : ℝ) := archimedeanGammaKernel d (s t + β) x
  let F (x : ℝ) := (g 0 * E x - exp (-β * (x : ℂ)) * g x) / (1 - E x)
  have hΦ : Continuous (compactLogMellin g) := continuous_iff_continuousAt.mpr fun z ↦
    (analyticAt_compactLogMellin hg.continuous hc z).continuousAt
  have hW : Continuous W := hΦ.comp (by dsimp [s]; fun_prop)
  have hWi : Integrable W := integrable_compactLogMellin_vertical hg hc a
  have hJ : Integrable (fun p : ℝ × ℝ ↦ W p.1 * H p.1 p.2)
      ((volume : Measure ℝ).prod (volume.restrict (Ioi 0))) :=
    integrable_archimedeanGamma_rightLine_product ha hd hb hW.measurable
      (integrable_compactLogMellin_vertical_first_moment hg hc a)
  have hzero : (∫ t, W t) / c = g 0 := by
    simpa [W, s, c] using compactLogMellin_right_line_evaluation hg hc a 0
  -- Invert the ordinate integral at each fixed log position.
  have hslice (x : ℝ) : (∫ t, W t * H t x) / c = F x := by
    have hsample : (∫ t, W t * exp (-s t * (x : ℂ))) / c = g x :=
      compactLogMellin_right_line_evaluation hg hc a x
    have hExp (t : ℝ) : exp (-(s t + β) * (x : ℂ)) =
        exp (-β * (x : ℂ)) * exp (-s t * (x : ℂ)) := by
      rw [← Complex.exp_add]
      congr 1
      ring
    have hXi : Integrable (fun t ↦ W t * exp (-s t * (x : ℂ))) := by
      refine (hWi.norm.mul_const (Real.exp (-a * x))).mono'
        (Continuous.aestronglyMeasurable (by dsimp [s]; fun_prop))
        (Filter.Eventually.of_forall fun t ↦ ?_)
      simp [Complex.norm_exp, s, mul_re]
    have hpoint (t : ℝ) : W t * H t x = (W t * E x -
        exp (-β * (x : ℂ)) * (W t * exp (-s t * (x : ℂ)))) / (1 - E x) := by
      simp only [H, archimedeanGammaKernel, hExp, E, div_eq_mul_inv]
      ring
    simp_rw [hpoint]
    rw [integral_div, integral_sub (hWi.mul_const _) (hXi.const_mul _), integral_mul_const,
      integral_const_mul]
    rw [show (((∫ t, W t) * E x - exp (-β * (x : ℂ)) *
          (∫ t, W t * exp (-s t * (x : ℂ)))) / (1 - E x)) / c =
        (((∫ t, W t) / c) * E x - exp (-β * (x : ℂ)) *
          ((∫ t, W t * exp (-s t * (x : ℂ))) / c)) / (1 - E x) by
        simp only [div_eq_mul_inv]; ring, hzero, hsample]
  have hFi : IntegrableOn F (Ioi 0) :=
    (hJ.integral_prod_right.div_const c).congr (Filter.Eventually.of_forall hslice)
  have hΓ (t : ℝ) : logDeriv (archimedeanGammaFactor B d b τ) (s t) =
      A + ∫ x in Ioi (0 : ℝ), H t x := by
    have hs : 0 < (s t).re := by simpa [s, mul_re] using ha
    simpa only [A, H, β, archimedeanGammaKernel, add_assoc] using
      (logDeriv_archimedeanGammaFactor_eq_integral (B := B) (τ := τ) hd hb hs).2.2
  have hLine (t : ℝ) : W t * logDeriv (archimedeanGammaFactor B d b τ) (s t) =
      W t * A + ∫ x in Ioi (0 : ℝ), W t * H t x := by rw [hΓ, mul_add, integral_const_mul]
  change Integrable (fun t ↦ W t * logDeriv (archimedeanGammaFactor B d b τ) (s t)) ∧
    IntegrableOn F (Ioi 0) ∧ (∫ t, W t * logDeriv (archimedeanGammaFactor B d b τ) (s t)) / c =
      A * g 0 + ∫ x in Ioi (0 : ℝ), F x
  simp_rw [hLine]
  refine ⟨(hWi.mul_const A).add hJ.integral_prod_left, hFi, ?_⟩
  rw [integral_add (hWi.mul_const A) hJ.integral_prod_left, integral_mul_const,
    add_div, mul_div_right_comm, hzero, mul_comm (g 0), integral_integral_swap hJ, ← integral_div]
  simp_rw [hslice]

/-- Evaluate the reflected leg on the same upward line. Conjugation
keeps `b` and reverses `τ`; reflecting the test contributes `exp (-x)`
at the reflected sample, not a reversal of line orientation. -/
public theorem compactLogMellin_archimedeanGamma_reflected {g : ℝ → ℂ}
    (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g)
    {a d b : ℝ} (ha : 0 < a) (hd : 0 < d) (hb : 0 ≤ b) (B τ : ℝ) :
    let s := fun t : ℝ ↦ (a : ℂ) + (t : ℂ) * I
    let W := fun t ↦ compactLogMellin g (1 - s t) * logDeriv (archimedeanGammaFactor B d b (-τ)) (s t)
    let K := fun x : ℝ ↦ (g 0 * exp (-(d : ℂ) * (x : ℂ)) -
      exp (-((1 : ℂ) + (b : ℂ) - (τ : ℂ) * I) * (x : ℂ)) * g (-x)) /
        (1 - exp (-(d : ℂ) * (x : ℂ)))
    Integrable W ∧ IntegrableOn K (Ioi 0) ∧
      (∫ t, W t) / (2 * (Real.pi : ℂ)) =
        (-((Real.log B : ℂ) + (Real.eulerMascheroniConstant : ℂ)) / (d : ℂ)) * g 0 +
          ∫ x in Ioi (0 : ℝ), K x := by
  let gR (x : ℝ) := exp (-(x : ℂ)) * g (-x)
  have hExp : ContDiff ℝ ∞ (fun x : ℝ ↦ exp (-(x : ℂ))) :=
    Complex.contDiff_exp.comp Complex.ofRealCLM.contDiff.neg
  have hR : ContDiff ℝ ∞ gR := hExp.mul (hg.comp contDiff_neg)
  have hRc : HasCompactSupport gR := (hc.comp_homeomorph (Homeomorph.neg ℝ)).mul_left
  have hzero : gR 0 = g 0 := by simp [gR]
  have hsample (x : ℝ) : exp (-((b : ℂ) + ((-τ : ℝ) : ℂ) * I) * (x : ℂ)) * gR x =
      exp (-((1 : ℂ) + (b : ℂ) - (τ : ℂ) * I) * (x : ℂ)) * g (-x) := by
    dsimp only [gR]
    rw [← mul_assoc, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  have h := compactLogMellin_archimedeanGamma_direct hR hRc ha hd hb B (-τ)
  dsimp only at h ⊢
  simpa only [compactLogMellin_reflect (g := g), hzero, hsample] using h

/-- The corrected scalar pair (B.4.2.13)–(15), including the full
contact term and both subtracted samples. Both integrals are absolute. -/
public theorem compactLogMellin_archimedeanGamma_pair {g : ℝ → ℂ}
    (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g)
    {a d b : ℝ} (ha : 0 < a) (hd : 0 < d) (hb : 0 ≤ b) (B τ : ℝ) :
    let s := fun t : ℝ ↦ (a : ℂ) + (t : ℂ) * I
    let W := fun t : ℝ ↦ compactLogMellin g (s t) * logDeriv (archimedeanGammaFactor B d b τ) (s t) +
      compactLogMellin g (1 - s t) * logDeriv (archimedeanGammaFactor B d b (-τ)) (s t)
    let K := fun x : ℝ ↦ (2 * g 0 * exp (-(d : ℂ) * (x : ℂ)) -
      exp (-((b : ℂ) + (τ : ℂ) * I) * (x : ℂ)) * g x -
      exp (-((1 : ℂ) + (b : ℂ) - (τ : ℂ) * I) * (x : ℂ)) * g (-x)) /
        (1 - exp (-(d : ℂ) * (x : ℂ)))
    Integrable W ∧ IntegrableOn K (Ioi 0) ∧
      (∫ t, W t) / (2 * (Real.pi : ℂ)) =
        (-((Real.log B : ℂ) + (Real.eulerMascheroniConstant : ℂ)) / (d : ℂ)) * (2 * g 0) +
          ∫ x in Ioi (0 : ℝ), K x := by
  obtain ⟨hD, hKD, heD⟩ := compactLogMellin_archimedeanGamma_direct hg hc ha hd hb B τ
  obtain ⟨hR, hKR, heR⟩ := compactLogMellin_archimedeanGamma_reflected hg hc ha hd hb B τ
  dsimp only
  have hK (x : ℝ) :
      (2 * g 0 * exp (-(d : ℂ) * (x : ℂ)) - exp (-((b : ℂ) + (τ : ℂ) * I) * (x : ℂ)) * g x -
      exp (-((1 : ℂ) + (b : ℂ) - (τ : ℂ) * I) * (x : ℂ)) * g (-x)) /
        (1 - exp (-(d : ℂ) * (x : ℂ))) =
      (g 0 * exp (-(d : ℂ) * (x : ℂ)) - exp (-((b : ℂ) + (τ : ℂ) * I) * (x : ℂ)) * g x) /
        (1 - exp (-(d : ℂ) * (x : ℂ))) +
      (g 0 * exp (-(d : ℂ) * (x : ℂ)) - exp (-((1 : ℂ) + (b : ℂ) - (τ : ℂ) * I) * (x : ℂ)) * g (-x)) /
        (1 - exp (-(d : ℂ) * (x : ℂ))) := by
    rw [← add_div]
    congr 1
    ring
  simp_rw [hK]
  refine ⟨hD.add hR, hKD.add hKR, ?_⟩
  rw [integral_add hD hR, add_div, heD, heR, integral_add hKD hKR]
  ring

end Masullo
