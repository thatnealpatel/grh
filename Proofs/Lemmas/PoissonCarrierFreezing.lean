module

public import Lemmas.SignedPoissonDefect
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Freezing a carrier in the Poisson integral

Source: `fb2dc2ff:.godel/bob/uncut-defect-price.md:37–41`, “The signed remainder”.
Consumer: `4c47eae3:.godel/bob/uncut-poisson-transfer.md:9–17`.

Scope: the whole-line, positive-width (`0 < v ≤ 1`) pointwise freezing estimate
for complex `C¹` envelopes with inverse-square value and derivative bounds.
The constant is independent of the frequency, width, and evaluation point.

Owning check session: `01a20e74-7a96-7653-9648-0eb1c4d5d43d`.
-/

open MeasureTheory Set

namespace PoissonCarrierFreezing

open SignedPoissonDefect (poisson kernel integral_poisson_exp)

private theorem poisson_nonneg {v : ℝ} (hv : 0 < v) (y : ℝ) : 0 ≤ poisson v y := by
  unfold poisson kernel
  positivity

private theorem continuous_poisson {v : ℝ} (hv : 0 < v) : Continuous (poisson v) := by
  unfold poisson kernel
  exact (continuous_const.div (by fun_prop) (fun y ↦
    (show 0 < v ^ 2 + y ^ 2 by positivity).ne')).div_const Real.pi

private theorem poisson_le {v : ℝ} (hv : 0 < v) (y : ℝ) (h : v ≤ 1) :
    poisson v y ≤ v⁻¹ * (1 + y ^ 2)⁻¹ := by
  have hπ : 1 ≤ Real.pi := by linarith [Real.pi_gt_three]
  unfold poisson kernel
  calc
    v / (v ^ 2 + y ^ 2) / Real.pi ≤ v / (v ^ 2 + y ^ 2) :=
      div_le_self (by positivity) hπ
    _ ≤ v⁻¹ * (1 + y ^ 2)⁻¹ := by
      rw [← mul_inv, ← one_div]
      apply (div_le_div_iff₀ (by positivity) (by positivity)).2
      have hy : v ^ 2 * y ^ 2 ≤ y ^ 2 := by
        simpa using mul_le_mul_of_nonneg_right (show v ^ 2 ≤ 1 by nlinarith) (sq_nonneg y)
      nlinarith only [hy]

private theorem integrable_poisson_of_le_one {v : ℝ} (hv : 0 < v) (hv₁ : v ≤ 1) :
    Integrable (poisson v) := by
  apply (integrable_inv_one_add_sq.const_mul v⁻¹).mono'
    (continuous_poisson hv).aestronglyMeasurable
  exact .of_forall fun y ↦ by
    rw [Real.norm_of_nonneg (poisson_nonneg hv y)]
    exact poisson_le hv y hv₁

-- The truncated first moment, not the divergent whole-line first moment.
private theorem local_moment_le {v : ℝ} (hv : 0 < v) (hv₁ : v ≤ 1) :
    (∫ y in Ioc (-1 : ℝ) 1, poisson v y * |y|) ≤ 2 * v * Real.log (2 / v) := by
  let m (y : ℝ) := poisson v y * |y|
  have hm : Continuous m := (continuous_poisson hv).mul continuous_abs
  have hEven (y : ℝ) : m (-y) = m y := by simp [m, poisson, kernel]
  change (∫ y in Ioc (-1 : ℝ) 1, m y) ≤ _
  rw [← intervalIntegral.integral_of_le (show (-1 : ℝ) ≤ 1 by norm_num),
    ← intervalIntegral.integral_add_adjacent_intervals
      (hm.intervalIntegrable (-1) 0) (hm.intervalIntegrable 0 1)]
  have hreflect : (∫ y in (-1 : ℝ)..0, m y) = ∫ y in (0 : ℝ)..1, m y := by
    simpa only [hEven, neg_zero] using
      (intervalIntegral.integral_comp_neg (a := (0 : ℝ)) (b := 1) m).symm
  rw [hreflect, ← two_mul]
  have hderiv (y : ℝ) : HasDerivAt (fun t : ℝ ↦ Real.log (v ^ 2 + t ^ 2))
      (2 * y / (v ^ 2 + y ^ 2)) y := by
    have hd : HasDerivAt (fun t : ℝ ↦ v ^ 2 + t ^ 2) (2 * y) y := by
      simpa using (((hasDerivAt_id y).pow 2).const_add (v ^ 2))
    exact hd.log (show 0 < v ^ 2 + y ^ 2 by positivity).ne'
  have hcont : Continuous (fun y : ℝ ↦ 2 * y / (v ^ 2 + y ^ 2)) :=
    (by fun_prop : Continuous fun y : ℝ ↦ 2 * y).div (by fun_prop) (fun y ↦ by positivity)
  have hm_eq : (∫ y in (0 : ℝ)..1, m y) =
      v / (2 * Real.pi) * (Real.log (v ^ 2 + 1) - 2 * Real.log v) := by
    calc
      (∫ y in (0 : ℝ)..1, m y) =
          ∫ y in (0 : ℝ)..1, v / (2 * Real.pi) * (2 * y / (v ^ 2 + y ^ 2)) := by
        apply intervalIntegral.integral_congr
        intro y hy
        rw [uIcc_of_le zero_le_one] at hy
        simp only [m, poisson, kernel, abs_of_nonneg hy.1]
        ring
      _ = _ := by
        rw [intervalIntegral.integral_const_mul,
          intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y _ ↦ hderiv y)
            (hcont.intervalIntegrable 0 1)]
        norm_num [Real.log_pow]
  have hlog : Real.log (v ^ 2 + 1) - 2 * Real.log v ≤ 2 * Real.log (2 / v) := by
    rw [Real.log_div (by norm_num) hv.ne']
    have h := Real.log_le_log (show 0 < v ^ 2 + 1 by positivity)
      (show v ^ 2 + 1 ≤ (2 : ℝ) ^ 2 by nlinarith)
    rw [Real.log_pow] at h
    norm_num at h
    linarith
  have hlog₀ : 0 ≤ Real.log (2 / v) :=
    Real.log_nonneg ((le_div_iff₀ hv).2 (by linarith))
  rw [hm_eq]
  calc
    2 * (v / (2 * Real.pi) * (Real.log (v ^ 2 + 1) - 2 * Real.log v))
        ≤ 2 * (v / (2 * Real.pi) * (2 * Real.log (2 / v))) := by gcongr
    _ = 2 * (v / Real.pi) * Real.log (2 / v) := by ring
    _ ≤ _ := by gcongr; exact div_le_self hv.le (by linarith [Real.pi_gt_three])

private theorem norm_sub_le_local {f : ℝ → ℂ} (hf : ContDiff ℝ 1 f) {M : ℝ}
    (hM : 0 ≤ M) (hderiv : ∀ t, ‖deriv f t‖ ≤ M / (1 + t ^ 2))
    (x y : ℝ) (hy : |y| ≤ 1) :
    ‖f (x - y) - f x‖ ≤ (3 * M / (1 + x ^ 2)) * |y| := by
  have hbound (t : ℝ) (ht : t ∈ Icc (x - 1) (x + 1)) :
      ‖deriv f t‖ ≤ 3 * M / (1 + x ^ 2) := by
    have hdist : (x - t) ^ 2 ≤ 1 := by
      have h : |x - t| ≤ 1 := abs_le.mpr ⟨by linarith [ht.2], by linarith [ht.1]⟩
      nlinarith [abs_nonneg (x - t), sq_abs (x - t)]
    have hweight : 1 + x ^ 2 ≤ 3 * (1 + t ^ 2) := by
      nlinarith [sq_nonneg (x - 2 * t), sq_nonneg t]
    apply (hderiv t).trans
    apply (div_le_div_iff₀ (by positivity) (by positivity)).2
    nlinarith only [mul_le_mul_of_nonneg_left hweight hM]
  have hx : x ∈ Icc (x - 1) (x + 1) := ⟨by linarith, by linarith⟩
  have hxy : x - y ∈ Icc (x - 1) (x + 1) := by
    obtain ⟨hl, hr⟩ := abs_le.mp hy
    exact ⟨by linarith, by linarith⟩
  simpa [Real.norm_eq_abs] using (convex_Icc (x - 1) (x + 1)).norm_image_sub_le_of_norm_deriv_le
    (fun t _ ↦ hf.differentiable one_ne_zero t) hbound hx hxy

private theorem poisson_le_tail {v : ℝ} (hv : 0 < v) (y : ℝ) (hy : 1 ≤ |y|) :
    poisson v y ≤ 2 * v * (1 + y ^ 2)⁻¹ := by
  have hy₂ : 1 ≤ y ^ 2 := by nlinarith only [hy, sq_abs y, sq_nonneg (|y| - 1)]
  unfold poisson kernel
  calc
    v / (v ^ 2 + y ^ 2) / Real.pi ≤ v / (v ^ 2 + y ^ 2) :=
      div_le_self (by positivity) (by linarith [Real.pi_gt_three])
    _ ≤ 2 * v * (1 + y ^ 2)⁻¹ := by
      rw [← div_eq_mul_inv]
      apply (div_le_div_iff₀ (by positivity) (by positivity)).2
      nlinarith only [mul_le_mul_of_nonneg_left hy₂ hv.le, mul_nonneg hv.le (sq_nonneg v)]

-- On the tail the output weight is paid for by the sum of two inverse squares.
private theorem weighted_tail_le {v M : ℝ} (hv : 0 < v) (hM : 0 ≤ M) {f : ℝ → ℂ}
    (hval : ∀ t, ‖f t‖ ≤ M / (1 + t ^ 2)) (x y : ℝ) (hy : 1 ≤ |y|) :
    poisson v y * ‖f (x - y) - f x‖ ≤
      (2 * M * v / (1 + x ^ 2)) * (3 * (1 + y ^ 2)⁻¹ + 2 * (1 + (x - y) ^ 2)⁻¹) := by
  let a := 1 + x ^ 2
  let b := 1 + y ^ 2
  let c := 1 + (x - y) ^ 2
  have ha : 0 < a := by dsimp [a]; positivity
  have hb : 0 < b := by dsimp [b]; positivity
  have hc : 0 < c := by dsimp [c]; positivity
  have hw : a ≤ 2 * c + 2 * b := by
    dsimp [a, b, c]
    nlinarith only [sq_nonneg (x - 2 * y)]
  have herr : ‖f (x - y) - f x‖ ≤ M / c + M / a :=
    (norm_sub_le ..).trans (add_le_add (hval (x - y)) (hval x))
  have hfrac : b⁻¹ * (M / c + M / a) ≤ (M / a) * (3 * b⁻¹ + 2 * c⁻¹) := by
    calc
      b⁻¹ * (M / c + M / a) = (M / a) * ((a + c) / (b * c)) := by
        field_simp
      _ ≤ (M / a) * ((3 * c + 2 * b) / (b * c)) := by
        exact mul_le_mul_of_nonneg_left
          (div_le_div_of_nonneg_right (by linarith only [hw]) (by positivity)) (by positivity)
      _ = _ := by field_simp
  calc
    poisson v y * ‖f (x - y) - f x‖ ≤ (2 * v * b⁻¹) * (M / c + M / a) :=
      mul_le_mul (poisson_le_tail hv y hy) herr (norm_nonneg _) (by positivity)
    _ = (2 * v) * (b⁻¹ * (M / c + M / a)) := by ring
    _ ≤ (2 * v) * ((M / a) * (3 * b⁻¹ + 2 * c⁻¹)) := by gcongr
    _ = _ := by change _ = (2 * M * v / a) * (3 * b⁻¹ + 2 * c⁻¹); ring

/-- Freezing the envelope in positive-width Poisson convolution costs at most
`C * M * v * log (2 / v) / (1 + x²)`, uniformly in the angular frequency. -/
public theorem norm_poisson_carrier_sub_le :
    ∃ C : ℝ, 0 < C ∧
      ∀ (f : ℝ → ℂ), ContDiff ℝ 1 f → ∀ (M : ℝ),
        (∀ t, ‖f t‖ ≤ M / (1 + t ^ 2)) →
        (∀ t, ‖deriv f t‖ ≤ M / (1 + t ^ 2)) →
        ∀ (v : ℝ), 0 < v → v ≤ 1 → ∀ (x ω : ℝ),
          ‖(∫ y : ℝ, (poisson v y : ℂ) * Complex.exp (↑(ω * (x - y)) * Complex.I) *
              f (x - y)) -
            (Real.exp (-v * |ω|) : ℂ) * Complex.exp (↑(ω * x) * Complex.I) * f x‖ ≤
            C * M * v * Real.log (2 / v) / (1 + x ^ 2) := by
  have hlog₂ : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨6 + 10 * Real.pi / Real.log 2, by positivity, ?_⟩
  intro f hf M hval hderiv v hv hv₁ x ω
  have hM : 0 ≤ M := by simpa using (norm_nonneg (f 0)).trans (hval 0)
  have hconst (t : ℝ) : ‖f t‖ ≤ M :=
    (hval t).trans (div_le_self hM (le_add_of_nonneg_right (sq_nonneg t)))
  let e (t : ℝ) := Complex.exp (↑(ω * t) * Complex.I)
  let k (y : ℝ) := (poisson v y : ℂ) * e (x - y)
  have hk_norm (y : ℝ) : ‖k y‖ = poisson v y := by
    dsimp only [k, e]
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
      Real.norm_of_nonneg (poisson_nonneg hv y)]
  have hk_cont : Continuous k := by
    have hc := continuous_poisson hv
    dsimp [k, e]
    fun_prop
  have hfi {g : ℝ → ℂ} (hg : Continuous g) (hb : ∀ y, ‖g y‖ ≤ M) :
      Integrable (fun y ↦ k y * g y) := by
    apply ((integrable_poisson_of_le_one hv hv₁).mul_const M).mono'
      (hk_cont.mul hg).aestronglyMeasurable
    exact .of_forall fun y ↦ by
      change ‖k y * g y‖ ≤ poisson v y * M
      rw [norm_mul, hk_norm]
      exact mul_le_mul_of_nonneg_left (hb y) (poisson_nonneg hv y)
  have hfi₁ : Integrable (fun y ↦ k y * f (x - y)) :=
    hfi (hf.continuous.comp (continuous_const.sub continuous_id)) (fun y ↦ hconst (x - y))
  have hfi₂ : Integrable (fun y ↦ k y * f x) := hfi continuous_const (fun _ ↦ hconst x)
  have hfreeze : (∫ y, k y * f x) = (Real.exp (-v * |ω|) : ℂ) * e x * f x := by
    have hphase (y : ℝ) : e (x - y) = Complex.exp (↑(-ω * y) * Complex.I) * e x := by
      dsimp only [e]
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    have heq (y : ℝ) : k y * f x =
        ((poisson v y : ℂ) * Complex.exp (↑(-ω * y) * Complex.I)) * (e x * f x) := by
      change (poisson v y : ℂ) * e (x - y) * f x = _
      simp only [hphase, mul_assoc]
    simp_rw [heq, integral_mul_const, integral_poisson_exp hv, mul_assoc]
  let r (y : ℝ) := k y * (f (x - y) - f x)
  have hr_eq : (fun y ↦ k y * f (x - y)) - (fun y ↦ k y * f x) = r := by
    funext y
    simp only [Pi.sub_apply, r, mul_sub]
  have hr : Integrable r := hr_eq ▸ hfi₁.sub hfi₂
  have hrn (y : ℝ) : ‖r y‖ = poisson v y * ‖f (x - y) - f x‖ := by
    simp only [r, norm_mul, hk_norm]
  let s := Ioc (-1 : ℝ) 1
  have hs : MeasurableSet s := measurableSet_Ioc
  have hlocal : (∫ y in s, ‖r y‖) ≤ (3 * M / (1 + x ^ 2)) * (2 * v * Real.log (2 / v)) := by
    let m (y : ℝ) := poisson v y * |y|
    have hm : Continuous m := (continuous_poisson hv).mul continuous_abs
    calc
      (∫ y in s, ‖r y‖) ≤ ∫ y in s, (3 * M / (1 + x ^ 2)) * m y := by
        refine setIntegral_mono_on hr.norm.integrableOn
          ((continuous_const.mul hm).integrableOn_Icc.mono_set Ioc_subset_Icc_self) hs ?_
        intro y hy
        have hy' : |y| ≤ 1 := abs_le.mpr ⟨hy.1.le, hy.2⟩
        rw [hrn]
        calc
          _ ≤ poisson v y * ((3 * M / (1 + x ^ 2)) * |y|) :=
            mul_le_mul_of_nonneg_left (norm_sub_le_local hf hM hderiv x y hy') (poisson_nonneg hv y)
          _ = _ := by dsimp [m]; ring
      _ = (3 * M / (1 + x ^ 2)) * ∫ y in s, m y := integral_const_mul ..
      _ ≤ _ := mul_le_mul_of_nonneg_left (local_moment_le hv hv₁) (by positivity)
  have htail : (∫ y in sᶜ, ‖r y‖) ≤ (2 * M * v / (1 + x ^ 2)) * (5 * Real.pi) := by
    let w (y : ℝ) := (1 + y ^ 2)⁻¹
    have hw : Integrable w := integrable_inv_one_add_sq
    have hshift : Integrable (fun y ↦ w (x - y)) := hw.comp_sub_left x
    let W (y : ℝ) := 3 * w y + 2 * w (x - y)
    have hW : Integrable W := (hw.const_mul 3).add (hshift.const_mul 2)
    have hWint : (∫ y, W y) = 5 * Real.pi := by
      change (∫ y, 3 * w y + 2 * w (x - y)) = _
      rw [integral_add (hw.const_mul 3) (hshift.const_mul 2), integral_const_mul,
        integral_const_mul, integral_sub_left_eq_self w volume x]
      dsimp [w]
      rw [integral_univ_inv_one_add_sq]
      ring
    calc
      (∫ y in sᶜ, ‖r y‖) ≤ ∫ y in sᶜ, (2 * M * v / (1 + x ^ 2)) * W y := by
        refine setIntegral_mono_on hr.norm.integrableOn
          (hW.const_mul _).integrableOn hs.compl ?_
        intro y hy
        have hy' : 1 ≤ |y| := by
          by_contra! h
          have hh := abs_lt.mp h
          exact hy ⟨hh.1, hh.2.le⟩
        rw [hrn]
        exact weighted_tail_le hv hM hval x y hy'
      _ ≤ ∫ y, (2 * M * v / (1 + x ^ 2)) * W y := by
        refine setIntegral_le_integral (hW.const_mul _) (.of_forall fun y ↦ ?_)
        dsimp [W, w]
        positivity
      _ = _ := by rw [integral_const_mul, hWint]
  have hlog : Real.log 2 ≤ Real.log (2 / v) :=
    Real.log_le_log (by norm_num) ((le_div_iff₀ hv).2 (by linarith))
  have habsorb : 10 * Real.pi ≤ (10 * Real.pi / Real.log 2) * Real.log (2 / v) := by
    calc
      10 * Real.pi = (10 * Real.pi / Real.log 2) * Real.log 2 := by field_simp
      _ ≤ _ := by gcongr
  change ‖(∫ y, k y * f (x - y)) - (Real.exp (-v * |ω|) : ℂ) * e x * f x‖ ≤ _
  rw [← hfreeze, ← integral_sub hfi₁ hfi₂]
  simp only [← mul_sub]
  calc
    ‖∫ y, r y‖ ≤ ∫ y, ‖r y‖ := norm_integral_le_integral_norm r
    _ = (∫ y in s, ‖r y‖) + (∫ y in sᶜ, ‖r y‖) := (integral_add_compl hs hr.norm).symm
    _ ≤ (3 * M / (1 + x ^ 2)) * (2 * v * Real.log (2 / v)) +
        (2 * M * v / (1 + x ^ 2)) * (5 * Real.pi) := add_le_add hlocal htail
    _ = (M * v / (1 + x ^ 2)) * (6 * Real.log (2 / v) + 10 * Real.pi) := by ring
    _ ≤ (M * v / (1 + x ^ 2)) *
        (6 * Real.log (2 / v) + (10 * Real.pi / Real.log 2) * Real.log (2 / v)) :=
      mul_le_mul_of_nonneg_left (add_le_add (le_refl _) habsorb) (by positivity)
    _ = _ := by ring

end PoissonCarrierFreezing
