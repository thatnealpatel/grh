module

public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-! # The two polar modes of the radial Mellin integral

Theorem 3.2.2.1(1a), p. 124, states the two residues. In the radial
coordinates of (3.2.2.4)–(5), p. 125, the powers on the small-norm side
are `t⁻¹` and `1`, with opposite signs as in (2.2.5.10), p. 97.
Integrating these two modes on the log half-line retains the frequency
of the character on the section. The identification of that frequency
and the assembly with the corrected Gaussian are separate steps.
Source reading: Provisional, from pinned Markdown and PDF layout.
-/

namespace Masullo

open MeasureTheory Set

/-- Evaluation of both removed zero modes on the left log half-line.
`a` and `b` include the character-weighted quotient mass, and `lam` is the
frequency of the unitary character on the norm section. -/
public theorem integral_logMellin_zeroModes
    (a b : ℂ) (lam : ℝ) (s : ℂ) (hs : 1 < s.re) :
    let modes (x : ℝ) := if x < 0 then Real.exp (-x) • a - b else 0
    let weight (x : ℝ) := Complex.exp (((lam * x : ℝ) : ℂ) * Complex.I) *
      Complex.exp (s * (x : ℂ))
    Integrable (fun x : ℝ ↦ modes x * weight x) ∧
      (∫ x : ℝ, modes x * weight x) =
        a / (s + (lam : ℂ) * Complex.I - 1) - b / (s + (lam : ℂ) * Complex.I) := by
  dsimp only
  let z := s + (lam : ℂ) * Complex.I
  change _ ∧ _ = a / (z - 1) - b / z
  have hz : 1 < z.re := by simpa [z, Complex.mul_re] using hs
  have hpos : 0 < (z - 1).re := by simpa using sub_pos.mpr hz
  have hz' : 0 < z.re := zero_lt_one.trans hz
  let E (w : ℂ) (x : ℝ) := Complex.exp (w * (x : ℂ))
  have hleft (w : ℂ) (hw : 0 < w.re) : IntegrableOn (E w) (Iio (0 : ℝ)) :=
    (integrableOn_Iic_iff_integrableOn_Iio).mp (integrableOn_exp_mul_complex_Iic hw 0)
  have hval (w : ℂ) (hw : 0 < w.re) : (∫ x in Iio (0 : ℝ), E w x) = 1 / w := by
    rw [← integral_Iic_eq_integral_Iio, show E w = (fun x : ℝ ↦ Complex.exp (w * (x : ℂ))) from rfl,
      integral_exp_mul_complex_Iic hw]
    simp
  have hpoint (x : ℝ) :
      ((Real.exp x)⁻¹ • a - b) * Complex.exp ((x : ℂ) * z) = a * E (z - 1) x - b * E z x := by
    rw [sub_mul, Complex.real_smul, ← Real.exp_neg, Complex.ofReal_exp, Complex.ofReal_neg]
    dsimp only [E]
    congr 1
    · rw [show (z - 1) * (x : ℂ) = -(x : ℂ) + (x : ℂ) * z by ring,
        Complex.exp_add, ← mul_assoc, mul_comm a (Complex.exp (-(x : ℂ)))]
    · rw [mul_comm z]
  have hphase (x : ℝ) : Complex.exp (((lam * x : ℝ) : ℂ) * Complex.I) *
      Complex.exp (s * (x : ℂ)) = Complex.exp ((x : ℂ) * z) := by
    rw [← Complex.exp_add]
    congr 1
    simp only [z, Complex.ofReal_mul]
    ring
  have hf : (fun x : ℝ ↦ (if x < 0 then Real.exp (-x) • a - b else 0) *
      (Complex.exp (((lam * x : ℝ) : ℂ) * Complex.I) * Complex.exp (s * (x : ℂ)))) =
      (Iio (0 : ℝ)).indicator (fun x ↦ a * E (z - 1) x - b * E z x) := by
    funext x
    rw [hphase x]
    by_cases hx : x < 0
    · simpa only [ite_eq_left hx, indicator_of_mem (show x ∈ Iio (0 : ℝ) from hx),
        Real.exp_neg] using hpoint x
    · simp [hx]
  rw [hf]
  have ha := (hleft (z - 1) hpos).const_mul a
  have hb := (hleft z hz').const_mul b
  refine ⟨(integrable_indicator_iff measurableSet_Iio).mpr (ha.sub hb), ?_⟩
  rw [integral_indicator measurableSet_Iio, integral_sub ha hb, integral_const_mul,
    integral_const_mul, hval _ hpos, hval _ hz']
  simp [div_eq_mul_inv]

end Masullo
