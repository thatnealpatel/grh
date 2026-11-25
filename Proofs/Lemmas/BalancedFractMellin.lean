module

public import Lemmas.FractionalPartZetaMellin
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Function.Floor

/-! # Mellin samples of balanced unit-interval fractional parts -/

open Complex MeasureTheory Set

namespace Masullo

private theorem unitInterval_fractMellin_substitution {a : ℝ} (ha : 0 < a) (s : ℂ) :
    (∫ x in Ioo (0 : ℝ) 1, ofReal (Int.fract (a / x)) * (x : ℂ) ^ (s - 1)) =
      (a : ℂ) ^ s * ∫ t in Ioi a, ofReal (Int.fract t) * (t : ℂ) ^ (-s - 1) := by
  let f := fun x : ℝ ↦ a / x
  have hf' (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) 1) :
      HasDerivWithinAt f (-(a / x ^ 2)) (Ioo 0 1) x := by
    have h := ((hasDerivAt_id x).inv hx.1.ne').const_mul a
    convert h.hasDerivWithinAt using 1 <;> simp [f, div_eq_mul_inv, mul_neg]
  have hfi : InjOn f (Ioo (0 : ℝ) 1) := by
    intro x _ y _ h
    apply inv_injective
    exact mul_left_cancel₀ ha.ne' (by simpa [f, div_eq_mul_inv] using h)
  have hfs : f '' Ioo (0 : ℝ) 1 = Ioi a := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (lt_div_iff₀ hx.1).2 (by nlinarith [ha, hx.2])
    · intro hy
      have hy' : a < y := hy
      have hy₀ := ha.trans hy'
      refine ⟨a / y, ⟨div_pos ha hy₀, (div_lt_iff₀ hy₀).2 (by simpa using hy')⟩, ?_⟩
      dsimp [f]
      field_simp
  let g := fun t : ℝ ↦ ofReal (Int.fract t) * (t : ℂ) ^ (-s - 1)
  rw [← hfs, integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo hf' hfi g,
    ← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioo
  intro x hx
  have hx₀ : 0 < x := hx.1
  have hxc : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hx₀.ne'
  have hac : (a : ℂ) ≠ 0 := ofReal_ne_zero.mpr ha.ne'
  have habs : |-(a / x ^ 2)| = a / x ^ 2 := by
    rw [abs_neg, abs_of_nonneg (div_nonneg ha.le (sq_nonneg x))]
  have hsplit : ((a / x : ℝ) : ℂ) ^ (-s - 1) =
      (a : ℂ) ^ (-s - 1) * (x : ℂ) ^ (s + 1) := by
    rw [div_eq_mul_inv, ofReal_mul, mul_cpow_ofReal_nonneg ha.le (inv_nonneg.mpr hx₀.le),
      ofReal_inv, inv_cpow _ _ (by rw [arg_ofReal_of_nonneg hx₀.le]; exact Real.pi_pos.ne),
      ← cpow_neg, show -(-s - 1) = s + 1 by ring]
  simp only [g, f, real_smul, habs, hsplit]
  rw [ofReal_div, ofReal_pow]
  rw [show (s + 1) = (s - 1) + (2 : ℕ) by push_cast; ring, cpow_add _ _ hxc, cpow_natCast]
  have ha' : (a : ℂ) ^ s * (a : ℂ) ^ (-s - 1) = (a : ℂ)⁻¹ := by
    rw [← cpow_add _ _ hac, show s + (-s - 1) = -1 by ring, cpow_neg_one]
  rw [show (a : ℂ) ^ s * ((a : ℂ) / (x : ℂ) ^ 2 *
      (ofReal (Int.fract (a / x)) * ((a : ℂ) ^ (-s - 1) *
        ((x : ℂ) ^ (s - 1) * (x : ℂ) ^ 2)))) =
      ((a : ℂ) ^ s * (a : ℂ) ^ (-s - 1)) *
        ((a : ℂ) / (x : ℂ) ^ 2 * (x : ℂ) ^ 2) *
        (ofReal (Int.fract (a / x)) * (x : ℂ) ^ (s - 1)) by ring, ha']
  field_simp

private theorem integral_fract_mul_cpow_below {a : ℝ} (ha : 0 < a) (ha₁ : a ≤ 1)
    {s : ℂ} (hs₀ : 0 < s.re) (hs₁ : s.re < 1) :
    (∫ t in Ioi a, ofReal (Int.fract t) * (t : ℂ) ^ (-s - 1)) =
      -riemannZeta s / s - (a : ℂ) ^ (1 - s) / (1 - s) := by
  let g := fun t : ℝ ↦ ofReal (Int.fract t) * (t : ℂ) ^ (-s - 1)
  have hInt := integrableOn_fract_mul_cpow hs₀ hs₁
  have hfull : (∫ t in Ioi (0 : ℝ), g t) = -riemannZeta s / s :=
    integral_fract_mul_cpow hs₀ hs₁
  have hhead : (∫ t in Ioc (0 : ℝ) a, g t) = (a : ℂ) ^ (1 - s) / (1 - s) := by
    rw [setIntegral_congr_set Ioo_ae_eq_Ioc.symm]
    have heq : EqOn g (fun t : ℝ ↦ (t : ℂ) ^ (-s)) (Ioo 0 a) := by
      intro t ht
      have ht₀ : 0 < t := ht.1
      dsimp [g]
      rw [Int.fract_eq_self.mpr ⟨ht₀.le, ht.2.trans_le ha₁⟩]
      nth_rw 1 [← cpow_one (t : ℂ)]
      rw [← cpow_add _ _ (ofReal_ne_zero.mpr ht₀.ne'), show 1 + (-s - 1) = -s by ring]
    have hn : 1 - s ≠ 0 := by
      intro h
      have he := congrArg Complex.re h
      simp only [sub_re, one_re, zero_re] at he
      linarith
    rw [setIntegral_congr_fun measurableSet_Ioo heq, setIntegral_congr_set Ioo_ae_eq_Ioc,
      ← intervalIntegral.integral_of_le ha.le, integral_cpow (Or.inl (by rw [neg_re]; linarith)),
      show -s + 1 = 1 - s by ring, ofReal_zero, zero_cpow hn, sub_zero]
  have hsplit : (∫ t in Ioi (0 : ℝ), g t) = (∫ t in Ioc (0 : ℝ) a, g t) +
      ∫ t in Ioi a, g t := by
    rw [← Ioc_union_Ioi_eq_Ioi ha.le, setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi
      (hInt.mono_set fun _ ht ↦ ht.1) (hInt.mono_set fun _ ht ↦ ha.trans ht)]
  change (∫ t in Ioi a, g t) = _
  rw [hfull, hhead] at hsplit
  linear_combination -hsplit

private theorem integral_unitInterval_fractMellin {a : ℝ} (ha : 0 < a) (ha₁ : a ≤ 1)
    {s : ℂ} (hs₀ : 0 < s.re) (hs₁ : s.re < 1) :
    (∫ x in Ioo (0 : ℝ) 1, ofReal (Int.fract (a / x)) * (x : ℂ) ^ (s - 1)) =
      -(a : ℂ) ^ s * (riemannZeta s / s) - a / (1 - s) := by
  rw [unitInterval_fractMellin_substitution ha, integral_fract_mul_cpow_below ha ha₁ hs₀ hs₁,
    mul_sub, ← mul_div_assoc, ← mul_div_assoc, ← cpow_add _ _ (ofReal_ne_zero.mpr ha.ne'),
    show s + (1 - s) = 1 by ring, cpow_one]
  ring

/-- The balanced column `frac(a/x) - a frac(1/x)` has `ζ(s)` as a common Mellin
factor throughout the open critical strip. -/
public theorem integral_balancedFract_mul_cpow {a : ℝ} (ha : 0 < a) (ha₁ : a ≤ 1)
    {s : ℂ} (hs₀ : 0 < s.re) (hs₁ : s.re < 1) :
    (∫ x in Ioo (0 : ℝ) 1, (ofReal (Int.fract (a / x)) - a * ofReal (Int.fract (1 / x))) *
      (x : ℂ) ^ (s - 1)) = ((a : ℂ) - (a : ℂ) ^ s) * (riemannZeta s / s) := by
  have hInt (b : ℝ) : IntegrableOn (fun x : ℝ ↦ ofReal (Int.fract (b / x)) *
      (x : ℂ) ^ (s - 1)) (Ioo (0 : ℝ) 1) := by
    have hpow := (intervalIntegral.integrableOn_Ioo_cpow_iff (s := s - 1) zero_lt_one).2
      (by simp [sub_re]; linarith)
    have hmf : Measurable (fun x : ℝ ↦ ofReal (Int.fract (b / x))) :=
      continuous_ofReal.measurable.comp (measurable_fract.comp (measurable_const.div measurable_id))
    refine hpow.norm.mono' (hmf.aestronglyMeasurable.mul hpow.aestronglyMeasurable) ?_
    exact Filter.Eventually.of_forall fun x ↦ by
      rw [norm_mul, norm_real, Real.norm_of_nonneg (Int.fract_nonneg _)]
      exact mul_le_of_le_one_left (norm_nonneg _) (Int.fract_lt_one _).le
  simp_rw [sub_mul, mul_assoc]
  rw [integral_sub (hInt a) ((hInt 1).const_mul _), integral_const_mul,
    integral_unitInterval_fractMellin ha ha₁ hs₀ hs₁,
    integral_unitInterval_fractMellin zero_lt_one le_rfl hs₀ hs₁, ofReal_one, one_cpow]
  ring

end Masullo
