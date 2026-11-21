module

public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Lemmas.ExpAbsDecay

/-! # Weighted log-line Mellin pairings and interior jet bounds -/

open MeasureTheory

namespace Masullo

/-- Square root of the real symmetric-strip weight (9.2.2.4), p. 412, in
log coordinates. Multiplication by this weight puts the norm in `L²(dx)` form. -/
public noncomputable def symmetricStripWeightRoot (α s x : ℝ) : ℝ :=
  Real.exp (α * |x|) * (1 + x ^ 2) ^ (s / 4)

public theorem symmetricStripWeightRoot_apply (α s x : ℝ) :
    symmetricStripWeightRoot α s x = Real.exp (α * |x|) * (1 + x ^ 2) ^ (s / 4) := by
  unfold symmetricStripWeightRoot
  rfl

public theorem symmetricStripWeightRoot_pos (α s x : ℝ) :
    0 < symmetricStripWeightRoot α s x := by
  unfold symmetricStripWeightRoot
  positivity

public theorem continuous_symmetricStripWeightRoot (α s : ℝ) :
    Continuous (symmetricStripWeightRoot α s) := by
  unfold symmetricStripWeightRoot
  exact (by fun_prop : Continuous (fun x : ℝ ↦ Real.exp (α * |x|))).mul
    ((show Continuous (fun x : ℝ ↦ 1 + x ^ 2) by fun_prop).rpow_const
      (fun x ↦ Or.inl (ne_of_gt (by positivity : 0 < 1 + x ^ 2))))

public theorem symmetricStripWeightRoot_sq (α s x : ℝ) :
    symmetricStripWeightRoot α s x ^ 2 =
      Real.exp (2 * (α * |x|)) * (1 + x ^ 2) ^ (s / 2) := by
  rw [symmetricStripWeightRoot, mul_pow, ← Real.exp_nat_mul,
    pow_two ((1 + x ^ 2) ^ (s / 4)), ← Real.rpow_add (by positivity),
    show s / 4 + s / 4 = s / 2 by ring]
  norm_num

/-- Reweighting the once-twisted profile gives exactly the two endpoint
powers of the shifted strip, not an additional Mellin twist. -/
public theorem symmetricStripWeightRoot_mul_exp_sq {α : ℝ} (hα : 0 ≤ α) (s a x : ℝ) :
    (symmetricStripWeightRoot α s x * Real.exp (a * x)) ^ 2 =
      max (Real.exp (2 * (a + -α) * x)) (Real.exp (2 * (a + α) * x)) * (1 + x ^ 2) ^ (s / 2) := by
  have hmax : max (Real.exp (2 * (a + -α) * x)) (Real.exp (2 * (a + α) * x)) =
      Real.exp (2 * (a * x + α * |x|)) := by
    rcases le_total 0 x with hx | hx
    · rw [abs_of_nonneg hx, max_eq_right (Real.exp_le_exp.mpr (by nlinarith [mul_nonneg hα hx]))]
      congr 1
      ring
    · rw [abs_of_nonpos hx, max_eq_left (Real.exp_le_exp.mpr
        (by nlinarith [mul_nonpos_of_nonneg_of_nonpos hα hx]))]
      congr 1
      ring
  rw [symmetricStripWeightRoot, hmax,
    show Real.exp (α * |x|) * (1 + x ^ 2) ^ (s / 4) * Real.exp (a * x) =
      Real.exp (a * x + α * |x|) * (1 + x ^ 2) ^ (s / 4) by rw [Real.exp_add]; ring,
    mul_pow, ← Real.exp_nat_mul, pow_two ((1 + x ^ 2) ^ (s / 4)), ← Real.rpow_add (by positivity),
    show s / 4 + s / 4 = s / 2 by ring]
  norm_num

/-- The divided kernel is conjugated only in the `L²` representing vector,
so the resulting functional pairs bilinearly with the Mellin kernel. -/
public noncomputable def weightedLogJet {α s : ℝ} {z : ℂ} {m : ℕ}
    (hk : MemLp (fun x : ℝ ↦ (x : ℂ) ^ m * Complex.exp (z * x) /
      (symmetricStripWeightRoot α s x : ℂ)) 2 volume) : Lp ℂ 2 (volume : Measure ℝ) →L[ℂ] ℂ :=
  innerSL ℂ ((Complex.isometry_conj.lipschitzWith.comp_memLp (by simp) hk).toLp _)

/-- Square integrability of the divided kernel gives an absolutely convergent
bilinear Mellin pairing for every profile in the weighted space. -/
public theorem weightedLogJet_toLp {α s : ℝ} {z : ℂ} {m : ℕ}
    (hk : MemLp (fun x : ℝ ↦ (x : ℂ) ^ m * Complex.exp (z * x) /
      (symmetricStripWeightRoot α s x : ℂ)) 2 volume) (u : ℝ → ℂ)
    (hu : MemLp (fun x ↦ (symmetricStripWeightRoot α s x : ℂ) * u x) 2 volume) :
    Integrable (fun x ↦ u x * ((x : ℂ) ^ m * Complex.exp (z * x))) ∧
    weightedLogJet hk (hu.toLp _) =
      ∫ x : ℝ, u x * ((x : ℂ) ^ m * Complex.exp (z * x)) := by
  let hk' := Complex.isometry_conj.lipschitzWith.comp_memLp (by simp) hk
  let k := hk'.toLp _
  let U := hu.toLp _
  have heq : (fun x : ℝ ↦ inner ℂ (k x) (U x)) =ᵐ[volume]
      (fun x ↦ u x * ((x : ℂ) ^ m * Complex.exp (z * x))) := by
    filter_upwards [hk'.coeFn_toLp, hu.coeFn_toLp] with x hkx hx
    change (k : ℝ → ℂ) x = _ at hkx
    change (U : ℝ → ℂ) x = _ at hx
    have hw : (symmetricStripWeightRoot α s x : ℂ) ≠ 0 := by
      exact_mod_cast (symmetricStripWeightRoot_pos α s x).ne'
    rw [hkx, hx, RCLike.inner_apply]
    change _ * star (star _) = _
    rw [star_star]
    field_simp [hw]
  refine ⟨(L2.integrable_inner (𝕜 := ℂ) k U).congr heq, ?_⟩
  rw [weightedLogJet, innerSL_apply_apply, L2.inner_def]
  exact integral_congr_ae heq

private theorem memLp_interiorLogJet {α s : ℝ} (hs : 0 ≤ s) {z : ℂ}
    (hz : |z.re| < α) (m : ℕ) :
    MemLp (fun x : ℝ ↦ (x : ℂ) ^ m * Complex.exp (z * x) /
      (symmetricStripWeightRoot α s x : ℂ)) 2 volume := by
  let k := fun x : ℝ ↦ (x : ℂ) ^ m * Complex.exp (z * x) /
    (symmetricStripWeightRoot α s x : ℂ)
  let r := (α - |z.re|) / 2
  have hr : 0 < r := by dsimp [r]; linarith
  let C : ℝ := m.factorial / r ^ m
  have hw (x : ℝ) : (symmetricStripWeightRoot α s x : ℂ) ≠ 0 := by
    exact_mod_cast (symmetricStripWeightRoot_pos α s x).ne'
  have hcont : Continuous k :=
    (by fun_prop : Continuous (fun x : ℝ ↦ (x : ℂ) ^ m * Complex.exp (z * x))).div
      (Complex.continuous_ofReal.comp (continuous_symmetricStripWeightRoot α s)) hw
  apply (memLp_two_iff_integrable_sq_norm hcont.aestronglyMeasurable).2
  refine ((integrable_exp_neg_mul_abs (r := 2 * r) (by positivity)).const_mul (C ^ 2)).mono'
    (hcont.norm.pow 2).aestronglyMeasurable (ae_of_all _ fun x ↦ ?_)
  have hpoly : |x| ^ m ≤ C * Real.exp (r * |x|) := by
    have h := (div_le_iff₀ (show 0 < (m.factorial : ℝ) by positivity)).mp
      (Real.pow_div_factorial_le_exp (r * |x|) (by positivity) m)
    rw [mul_pow] at h
    dsimp [C]
    rw [div_mul_eq_mul_div, le_div_iff₀ (pow_pos hr m), mul_comm (|x| ^ m),
      mul_comm (m.factorial : ℝ)]
    exact h
  have hweight : Real.exp (α * |x|) ≤ symmetricStripWeightRoot α s x := by
    unfold symmetricStripWeightRoot
    exact le_mul_of_one_le_right (Real.exp_pos _).le
      (Real.one_le_rpow (le_add_of_nonneg_right (sq_nonneg x)) (by positivity))
  have hdecay : ‖k x‖ ≤ C * Real.exp (-r * |x|) := by
    dsimp only [k]
    rw [norm_div, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      Complex.norm_exp, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero,
      Complex.norm_real, Real.norm_of_nonneg (symmetricStripWeightRoot_pos α s x).le]
    apply (div_le_iff₀ (symmetricStripWeightRoot_pos α s x)).2
    calc
      |x| ^ m * Real.exp (z.re * x) ≤ (C * Real.exp (r * |x|)) * Real.exp (|z.re| * |x|) := by
        have hRe : z.re * x ≤ |z.re| * |x| := by rw [← abs_mul]; exact le_abs_self _
        exact mul_le_mul hpoly (Real.exp_le_exp.mpr hRe) (by positivity) (by positivity)
      _ = (C * Real.exp (-r * |x|)) * Real.exp (α * |x|) := by
        rw [mul_assoc, mul_assoc, ← Real.exp_add, ← Real.exp_add]
        congr 2
        dsimp [r]
        ring
      _ ≤ (C * Real.exp (-r * |x|)) * symmetricStripWeightRoot α s x := by gcongr
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  calc
    _ ≤ (C * Real.exp (-r * |x|)) ^ 2 := by gcongr
    _ = C ^ 2 * Real.exp (-(2 * r) * |x|) := by
      rw [mul_pow, ← Real.exp_nat_mul]
      push_cast
      ring_nf

/-- The continuous complex-linear interior jet on the `L²(dx)` coordinate of
`W^s_{[-α,α]}`. An input profile `u` is represented by `W*u`, where `W` is
`symmetricStripWeightRoot α s`. -/
public noncomputable def interiorLogJet {α s : ℝ} (hs : 0 ≤ s) {z : ℂ}
    (hz : |z.re| < α) (m : ℕ) : Lp ℂ 2 (volume : Measure ℝ) →L[ℂ] ℂ :=
  weightedLogJet (memLp_interiorLogJet hs hz m)

/-- On every input in the weighted log-line space, the interior jet is the
absolutely convergent bilinear integral (9.2.1.27), with the log monomial
and the positive Mellin exponent as in (10.2.2.4). -/
public theorem interiorLogJet_toLp {α s : ℝ} (hs : 0 ≤ s) {z : ℂ}
    (hz : |z.re| < α) (m : ℕ) (u : ℝ → ℂ)
    (hu : MemLp (fun x ↦ (symmetricStripWeightRoot α s x : ℂ) * u x) 2 volume) :
    Integrable (fun x ↦ u x * ((x : ℂ) ^ m * Complex.exp (z * x))) ∧
    interiorLogJet hs hz m (hu.toLp _) =
      ∫ x : ℝ, u x * ((x : ℂ) ^ m * Complex.exp (z * x)) :=
  weightedLogJet_toLp (memLp_interiorLogJet hs hz m) u hu

end Masullo
