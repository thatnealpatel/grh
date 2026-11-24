module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
import Mathlib.Probability.Distributions.Cauchy

/-!
# Quadratic Fourier identities for finite step profiles

Source: `4160d1ef:.godel/bob/single-shift-10-2.md:9–11,32–38` and
`4160d1ef:.godel/bob/separated-second-shifts.md:13–19,27–37`.

Scope: both quadratic angular Fourier integrals of the jump representer against the
normalized Cauchy density on the real line, for arbitrary finite real weights and
locations and every real shift. No numerical bounds or interpolation result are asserted.

Owning check session: `01a20ca9-0415-7de3-a7c2-ad7d2c76dee0`.
-/

open MeasureTheory Set Filter
open scoped FourierTransform Topology

namespace StepProfileQuadraticFourier

/-- The Cauchy rate on the half-line of real part `1/2`. -/
@[expose] public noncomputable def rate (x : ℝ) : ℂ := 1 / 2 + (x : ℂ) * Complex.I

/-- Positive angular phase, with no factor of `2π` in the frequency. -/
@[expose] public noncomputable def phase (y x : ℝ) : ℂ :=
  Complex.exp ((y : ℂ) * (x : ℂ) * Complex.I)

/-- The finite jump representer, with `b` already including the half-exponential weight. -/
@[expose] public noncomputable def jumpRepresenter {ι : Type*} (J : Finset ι)
    (b z : ι → ℝ) (x : ℝ) : ℂ :=
  (∑ j ∈ J, (b j : ℂ) * phase (z j) x) / rate x

/-- The normalized Cauchy density `1 / (2π |w|²)`. -/
@[expose] public noncomputable def density (x : ℝ) : ℝ := 1 / (2 * Real.pi * ‖rate x‖ ^ 2)

/-- The frequency-difference kernel for the squared norm. -/
@[expose] public noncomputable def differenceKernel (y : ℝ) : ℝ :=
  (2 + |y|) * Real.exp (-|y| / 2)

/-- The frequency-sum kernel for the complex square. -/
@[expose] public noncomputable def sumKernel (y : ℝ) : ℝ :=
  (1 + max y 0 + (max y 0) ^ 2 / 2) * Real.exp (-|y| / 2)

private theorem rate_re (x : ℝ) : (rate x).re = 1 / 2 := by
  norm_num [rate, Complex.div_re, Complex.mul_re]

private theorem rate_ne_zero (x : ℝ) : rate x ≠ 0 := by
  intro h
  have hr := rate_re x
  rw [h, Complex.zero_re] at hr
  norm_num at hr

private theorem rate_add (x : ℝ) : rate x + rate (-x) = 1 := by
  simp only [rate, Complex.ofReal_neg]
  ring

private theorem conj_rate (x : ℝ) : starRingEnd ℂ (rate x) = rate (-x) := by
  simp [rate, mul_neg, neg_mul, map_ofNat]

private theorem phase_norm (y x : ℝ) : ‖phase y x‖ = 1 := by
  simp [phase, Complex.norm_exp, Complex.mul_re, Complex.mul_im]

private theorem phase_add (a b x : ℝ) : phase (a + b) x = phase a x * phase b x := by
  rw [phase, phase, phase, ← Complex.exp_add, Complex.ofReal_add]
  congr 1
  ring

private theorem conj_phase (y x : ℝ) : starRingEnd ℂ (phase y x) = phase (-y) x := by
  unfold phase
  rw [← Complex.exp_conj]
  simp [mul_neg, neg_mul]

private noncomputable def moment (n : ℕ) (r : ℂ) (x : ℝ) : ℂ :=
  (x : ℂ) ^ n * Complex.exp (-r * x)

private theorem norm_moment (n : ℕ) (r : ℂ) {x : ℝ} (hx : 0 ≤ x) :
    ‖moment n r x‖ = x ^ n * Real.exp (-r.re * x) := by
  simp [moment, norm_pow, Complex.norm_exp, Complex.mul_re, abs_of_nonneg hx]

private theorem integrable_moment (n : ℕ) {r : ℂ} (hr : 0 < r.re) :
    IntegrableOn (moment n r) (Ioi 0) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := (n : ℝ))
    (neg_one_lt_zero.trans_le (Nat.cast_nonneg n)) zero_lt_one hr
  have hn : IntegrableOn (fun x : ℝ ↦ x ^ n * Real.exp (-r.re * x)) (Ioi 0) := by
    simpa only [Real.rpow_natCast, Real.rpow_one] using h
  apply hn.mono'
  · unfold moment
    exact (show Continuous (fun x : ℝ ↦ (x : ℂ) ^ n * Complex.exp (-r * x)) from
      by fun_prop).aestronglyMeasurable
  · exact (ae_restrict_iff' measurableSet_Ioi).2 (.of_forall fun x hx ↦
      (norm_moment n r hx.out.le).le)

private theorem tendsto_moment (n : ℕ) {r : ℂ} (hr : 0 < r.re) :
    Tendsto (moment n r) atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  refine (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (n : ℝ) r.re hr).congr' ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
  rw [Real.rpow_natCast, norm_moment n r hx]

-- Laplace moments on the positive ray; the recurrence uses the vanishing boundary term.
private theorem integral_moment (n : ℕ) {r : ℂ} (hr : 0 < r.re) :
    (∫ x in Ioi (0 : ℝ), moment n r x) = (n.factorial : ℂ) / r ^ (n + 1) := by
  have hr0 : r ≠ 0 := fun h ↦ by simp [h] at hr
  induction n with
  | zero =>
    have hn : (-r).re < 0 := by simpa using hr
    simpa [moment] using integral_exp_mul_complex_Ioi hn 0
  | succ n ih =>
    let u (x : ℝ) : ℂ := (x : ℂ) ^ (n + 1)
    let u' (x : ℝ) : ℂ := (n + 1 : ℕ) * (x : ℂ) ^ n
    let v (x : ℝ) : ℂ := Complex.exp (-r * x)
    let v' (x : ℝ) : ℂ := v x * (-r)
    have hd (x : ℝ) : HasDerivAt (fun t : ℝ ↦ (t : ℂ)) 1 x := by
      rw [← show (Complex.ofRealCLM : ℝ → ℂ) = (fun t : ℝ ↦ (t : ℂ)) from
        funext Complex.ofRealCLM_apply]
      simpa using Complex.ofRealCLM.hasDerivAt (x := x)
    have hu (x : ℝ) : HasDerivAt u (u' x) x := by
      change HasDerivAt ((fun t : ℝ ↦ (t : ℂ)) ^ (n + 1)) (u' x) x
      simpa [u'] using (hd x).pow (n + 1)
    have hv (x : ℝ) : HasDerivAt v (v' x) x := by
      simpa [v, v'] using ((hd x).const_mul (-r)).cexp
    have huv' : (u * v') = fun x ↦ moment (n + 1) r x * (-r) := by
      funext x
      simp [u, v, v', moment, mul_assoc]
    have hu'v : (u' * v) = fun x ↦ ((n + 1 : ℕ) : ℂ) * moment n r x := by
      funext x
      simp [u', v, moment, mul_assoc]
    have hc : Continuous (u * v) := by
      unfold u v
      fun_prop
    have hz : Tendsto (u * v) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      have h := hc.continuousWithinAt (s := Ioi 0) (x := 0)
      change Tendsto (u * v) _ (𝓝 ((u * v) 0)) at h
      simpa [u, v] using h
    have hibp := integral_Ioi_mul_deriv_eq_deriv_mul (fun x _ ↦ hu x) (fun x _ ↦ hv x)
      (huv' ▸ (integrable_moment (n + 1) hr).mul_const (-r))
      (hu'v ▸ (integrable_moment n hr).const_mul ((n + 1 : ℕ) : ℂ))
      hz (tendsto_moment (n + 1) hr)
    simp only [← Pi.mul_apply, huv', hu'v, integral_mul_const, integral_const_mul,
      sub_zero, zero_sub, ih] at hibp
    apply (mul_right_cancel₀ (neg_ne_zero.mpr hr0))
    rw [hibp, Nat.factorial_succ, Nat.cast_mul, pow_succ]
    field_simp
    ring

private noncomputable def polyExp (A B C r : ℂ) (x : ℝ) : ℂ :=
  (A + B * x + C * (x : ℂ) ^ 2) * Complex.exp (-r * x)

private theorem polyExp_eq (A B C r : ℂ) (x : ℝ) :
    polyExp A B C r x = A * moment 0 r x + B * moment 1 r x + C * moment 2 r x := by
  simp only [polyExp, moment, pow_zero, pow_one, one_mul, add_mul, mul_assoc]

private theorem integrable_polyExp (A B C : ℂ) {r : ℂ} (hr : 0 < r.re) :
    IntegrableOn (polyExp A B C r) (Ioi 0) := by
  simp_rw [funext (polyExp_eq A B C r)]
  exact (((integrable_moment 0 hr).const_mul A).add ((integrable_moment 1 hr).const_mul B)).add
    ((integrable_moment 2 hr).const_mul C)

private theorem integral_polyExp (A B C : ℂ) {r : ℂ} (hr : 0 < r.re) :
    (∫ x in Ioi (0 : ℝ), polyExp A B C r x) = A / r + B / r ^ 2 + 2 * C / r ^ 3 := by
  have hA := (integrable_moment 0 hr).const_mul A
  have hB := (integrable_moment 1 hr).const_mul B
  have hC := (integrable_moment 2 hr).const_mul C
  have hAB : Integrable (fun x ↦ A * moment 0 r x + B * moment 1 r x)
      (volume.restrict (Ioi 0)) := hA.add hB
  simp_rw [polyExp_eq]
  rw [integral_add hAB hC, integral_add hA hB]
  simp only [integral_const_mul, integral_moment _ hr]
  norm_num
  ring

private theorem phase_mul_polyExp (A B C : ℂ) (ω t : ℝ) :
    phase (-ω) t * polyExp A B C (1 / 2) t = polyExp A B C (rate ω) t := by
  rw [polyExp, polyExp, mul_left_comm, phase, ← Complex.exp_add]
  congr 2
  simp only [rate, Complex.ofReal_neg]
  ring

private theorem integrableOn_reflected {f : ℝ → ℂ} (hf : IntegrableOn f (Ioi 0)) :
    IntegrableOn (fun t ↦ f (-t)) (Iic 0) := by
  rw [← Measure.map_neg_eq_self (volume : Measure ℝ)]
  let h : MeasurableEmbedding (fun t : ℝ ↦ -t) :=
    (Homeomorph.neg ℝ).isClosedEmbedding.measurableEmbedding
  rw [h.integrableOn_map_iff]
  simpa only [Function.comp_def, neg_neg, neg_preimage, neg_Iic, neg_zero] using
    ((integrableOn_Ici_iff_integrableOn_Ioi (f := f)).mpr hf)

private theorem integrable_of_halves {f : ℝ → ℂ} {A B C D E F : ℂ}
    (hp : EqOn f (polyExp A B C (1 / 2)) (Ioi 0))
    (hn : EqOn f (fun t ↦ polyExp D E F (1 / 2) (-t)) (Iic 0)) : Integrable f := by
  have h : 0 < ((1 / 2 : ℂ)).re := by norm_num [Complex.div_re]
  have h₁ : IntegrableOn f (Ioi 0) := (integrable_polyExp A B C h).congr
    ((ae_restrict_iff' measurableSet_Ioi).2 (.of_forall fun t ht ↦ (hp ht).symm))
  have h₂ : IntegrableOn f (Iic 0) := (integrableOn_reflected (integrable_polyExp D E F h)).congr
    ((ae_restrict_iff' measurableSet_Iic).2 (.of_forall fun t ht ↦ (hn ht).symm))
  simpa only [← compl_Ioi, union_compl_self, integrableOn_univ] using h₁.union h₂

-- Transform each half in the forward (negative-phase) convention. Reflection on the
-- negative half changes the frequency from `ω` to `-ω`.
private theorem fourier_of_halves {f : ℝ → ℂ} {A B C D E F : ℂ}
    (hf : Continuous f) (hp : EqOn f (polyExp A B C (1 / 2)) (Ioi 0))
    (hn : EqOn f (fun t ↦ polyExp D E F (1 / 2) (-t)) (Iic 0)) (ξ : ℝ) :
    𝓕 f ξ = let ω := 2 * Real.pi * ξ
      A / rate ω + B / (rate ω) ^ 2 + 2 * C / (rate ω) ^ 3 +
      (D / rate (-ω) + E / (rate (-ω)) ^ 2 + 2 * F / (rate (-ω)) ^ 3) := by
  let ω := 2 * Real.pi * ξ
  let g (t : ℝ) := phase (-ω) t * f t
  have hg : Integrable g := by
    apply (integrable_of_halves hp hn).norm.mono'
    · unfold g phase
      exact (show Continuous (fun t : ℝ ↦ Complex.exp ((↑(-ω) : ℂ) * (t : ℂ) * Complex.I) *
        f t) from by fun_prop).aestronglyMeasurable
    · exact .of_forall fun t ↦ by
        change ‖phase (-ω) t * f t‖ ≤ ‖f t‖
        rw [norm_mul, phase_norm, one_mul]
  have hphase (t : ℝ) : Complex.exp (↑(-2 * Real.pi * t * ξ) * Complex.I) = phase (-ω) t := by
    unfold phase ω
    congr 1
    push_cast
    ring
  have hpos : EqOn g (polyExp A B C (rate ω)) (Ioi 0) := fun t ht ↦ by
    change phase (-ω) t * f t = _
    rw [hp ht, phase_mul_polyExp]
  have hneg : EqOn g (fun t ↦ polyExp D E F (rate (-ω)) (-t)) (Iic 0) := fun t ht ↦ by
    have hflip : phase (-ω) t = phase (-(-ω)) (-t) := by
      simp [phase, mul_neg, neg_mul]
    change phase (-ω) t * f t = _
    rw [hn ht, hflip, phase_mul_polyExp]
  rw [Real.fourier_real_eq_integral_exp_smul]
  simp only [hphase, smul_eq_mul]
  change (∫ t, g t) = _
  rw [← integral_add_compl measurableSet_Ioi hg, compl_Ioi,
    setIntegral_congr_fun measurableSet_Ioi hpos, setIntegral_congr_fun measurableSet_Iic hneg,
    integral_comp_neg_Iic, neg_zero, integral_polyExp _ _ _ (by rw [rate_re]; norm_num),
    integral_polyExp _ _ _ (by rw [rate_re]; norm_num)]

private theorem difference_pos : EqOn (fun t ↦ (differenceKernel t : ℂ))
    (polyExp 2 1 0 (1 / 2)) (Ioi 0) := fun t ht ↦ by
  simp only [differenceKernel, polyExp, abs_of_pos ht.out, Complex.ofReal_mul, Complex.ofReal_add,
    Complex.ofReal_ofNat, Complex.ofReal_exp, Complex.ofReal_div, Complex.ofReal_neg, one_mul,
    zero_mul, add_zero]
  congr 2
  ring

private theorem difference_neg : EqOn (fun t ↦ (differenceKernel t : ℂ))
    (fun t ↦ polyExp 2 1 0 (1 / 2) (-t)) (Iic 0) := fun t ht ↦ by
  simp only [differenceKernel, polyExp, abs_of_nonpos ht.out, Complex.ofReal_mul, Complex.ofReal_add,
    Complex.ofReal_ofNat, Complex.ofReal_exp, Complex.ofReal_div, Complex.ofReal_neg, one_mul,
    zero_mul, add_zero]
  congr 2
  ring

private theorem sum_pos : EqOn (fun t ↦ (sumKernel t : ℂ))
    (polyExp 1 1 (1 / 2) (1 / 2)) (Ioi 0) := fun t ht ↦ by
  simp only [sumKernel, polyExp, max_eq_left ht.out.le, abs_of_pos ht.out, Complex.ofReal_mul,
    Complex.ofReal_add, Complex.ofReal_one, Complex.ofReal_ofNat, Complex.ofReal_exp,
    Complex.ofReal_div, Complex.ofReal_neg, Complex.ofReal_pow, one_mul]
  congr 2 <;> ring

private theorem sum_neg : EqOn (fun t ↦ (sumKernel t : ℂ))
    (fun t ↦ polyExp 1 0 0 (1 / 2) (-t)) (Iic 0) := fun t ht ↦ by
  norm_num [sumKernel, polyExp, max_eq_right ht.out, abs_of_nonpos ht.out, Complex.ofReal_exp]
  congr 1
  ring

private noncomputable def rational (n m : ℕ) (x : ℝ) : ℂ :=
  1 / (rate x ^ n * rate (-x) ^ m)

private theorem fourier_difference (ξ : ℝ) :
    𝓕 (fun t ↦ (differenceKernel t : ℂ)) ξ = rational 2 2 (2 * Real.pi * ξ) := by
  rw [fourier_of_halves (by unfold differenceKernel; fun_prop) difference_pos difference_neg]
  let ω := 2 * Real.pi * ξ
  let w := rate ω
  let v := rate (-ω)
  change 2 / w + 1 / w ^ 2 + 2 * 0 / w ^ 3 + (2 / v + 1 / v ^ 2 + 2 * 0 / v ^ 3) =
    1 / (w ^ 2 * v ^ 2)
  simp only [mul_zero, zero_div, add_zero]
  calc
    _ = (w + v) ^ 2 / (w ^ 2 * v ^ 2) := by
      field_simp [show w ≠ 0 from rate_ne_zero _, show v ≠ 0 from rate_ne_zero _]
      have h : w + v = 1 := rate_add ω
      linear_combination (2 * w * v) * h
    _ = _ := by rw [show w + v = 1 from rate_add _, one_pow]

private theorem fourier_sum (ξ : ℝ) :
    𝓕 (fun t ↦ (sumKernel t : ℂ)) ξ = rational 3 1 (2 * Real.pi * ξ) := by
  rw [fourier_of_halves (by unfold sumKernel; fun_prop) sum_pos sum_neg]
  let ω := 2 * Real.pi * ξ
  let w := rate ω
  let v := rate (-ω)
  change 1 / w + 1 / w ^ 2 + 2 * (1 / 2) / w ^ 3 + (1 / v + 0 / v ^ 2 + 2 * 0 / v ^ 3) =
    1 / (w ^ 3 * v ^ 1)
  have h : w + v = 1 := rate_add _
  norm_num only [mul_div_cancel₀ _ (show (2 : ℂ) ≠ 0 by norm_num), mul_zero, zero_div,
    add_zero, pow_one]
  calc
    _ = (w ^ 2 * (w + v) + w * v + v) / (w ^ 3 * v) := by
      field_simp [show w ≠ 0 from rate_ne_zero _, show v ≠ 0 from rate_ne_zero _]
      ring
    _ = (w * (w + v) + v) / (w ^ 3 * v) := by
      rw [h, mul_one]
      congr 1
      linear_combination w * h
    _ = _ := by rw [h, mul_one, h]

private theorem norm_sq_rate (x : ℝ) : ‖rate x‖ ^ 2 = (1 / 2 : ℝ) ^ 2 + x ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply, rate_re]
  have hi : (rate x).im = x := by norm_num [rate, Complex.div_im, Complex.mul_im]
  rw [hi]
  ring

private theorem integrable_inv_norm_sq : Integrable (fun x : ℝ ↦ (‖rate x‖ ^ 2)⁻¹) := by
  let a : NNReal := ⟨1 / 2, by norm_num⟩
  apply ((ProbabilityTheory.integrable_cauchyPDFReal 0 (γ := a)).const_mul
    (2 * Real.pi)).congr
  exact .of_forall fun x ↦ by
    change 2 * Real.pi * ProbabilityTheory.cauchyPDFReal 0 a x = (‖rate x‖ ^ 2)⁻¹
    rw [ProbabilityTheory.cauchyPDFReal_def, norm_sq_rate, sub_zero, add_comm ((1 / 2 : ℝ) ^ 2)]
    change (2 * Real.pi) * (Real.pi⁻¹ * (1 / 2) * (x ^ 2 + (1 / 2) ^ 2)⁻¹) = _
    have h : (2 * Real.pi) * (Real.pi⁻¹ * (1 / 2)) = 1 := by
      field_simp [Real.pi_ne_zero]
    rw [← mul_assoc, h, one_mul]

private theorem integrable_rational {n m : ℕ} (hnm : n + m = 4) :
    Integrable (rational n m) := by
  apply (integrable_inv_norm_sq.const_mul 4).mono'
  · have hcont : Continuous (rational n m) := by
      unfold rational
      apply continuous_const.div (by unfold rate; fun_prop)
      exact fun x ↦ mul_ne_zero (pow_ne_zero _ (rate_ne_zero x)) (pow_ne_zero _ (rate_ne_zero (-x)))
    exact hcont.aestronglyMeasurable
  · refine .of_forall fun x ↦ ?_
    have hnorm : ‖rational n m x‖ = ((‖rate x‖ ^ 2)⁻¹) ^ 2 := by
      rw [rational, norm_div, norm_one, norm_mul, norm_pow, norm_pow, ← conj_rate,
        Complex.norm_conj, ← pow_add, hnm, one_div, inv_pow, ← pow_mul]
    rw [hnorm, pow_two]
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    rw [norm_sq_rate, inv_eq_one_div, div_le_iff₀ (by positivity : 0 < (1 / 2 : ℝ) ^ 2 + x ^ 2)]
    nlinarith [sq_nonneg x]

private noncomputable def term (n m : ℕ) (y x : ℝ) : ℂ :=
  phase y x * rational n m x / (2 * Real.pi : ℂ)

private theorem integrable_term {n m : ℕ} (hnm : n + m = 4) (y : ℝ) :
    Integrable (term n m y) := by
  apply Integrable.div_const _ _
  apply (integrable_rational hnm).norm.mono'
  · have hq := (integrable_rational hnm).aestronglyMeasurable
    exact (show Continuous (phase y) from by unfold phase; fun_prop).aestronglyMeasurable.mul hq
  · exact .of_forall fun x ↦ by rw [norm_mul, phase_norm, one_mul]

-- Inverting the standard Fourier transform introduces the factor `1 / (2π)`
-- when its frequency variable is converted to angular frequency.
private theorem integral_term_of_fourier {f : ℝ → ℂ} {n m : ℕ} (hnm : n + m = 4)
    (hf : Continuous f) (hi : Integrable f) (h : ∀ ξ : ℝ, 𝓕 f ξ = rational n m (2 * Real.pi * ξ))
    (y : ℝ) : (∫ x : ℝ, term n m y x) = f y := by
  have hp : (0 : ℝ) < 2 * Real.pi := by positivity
  have hq : Integrable (𝓕 f) := by
    rw [funext h]
    exact (integrable_rational hnm).comp_mul_left' hp.ne'
  have hh := congrFun (hf.fourierInv_fourier_eq hi hq) y
  rw [Real.fourierInv_eq_fourier_neg, Real.fourier_real_eq_integral_exp_smul] at hh
  simp only [h, smul_eq_mul] at hh
  have hphase (x : ℝ) : Complex.exp (↑(-2 * Real.pi * x * -y) * Complex.I) =
      phase y ((2 * Real.pi) * x) := by
    unfold phase
    congr 1
    push_cast
    ring
  simp_rw [hphase] at hh
  rw [Measure.integral_comp_mul_left (fun x ↦ phase y x * rational n m x),
    abs_of_pos (inv_pos.mpr hp), Complex.real_smul, Complex.ofReal_inv] at hh
  unfold term
  rw [integral_div]
  simpa only [Complex.ofReal_mul, Complex.ofReal_ofNat, div_eq_mul_inv, mul_comm] using hh

private theorem integral_difference_term (y : ℝ) :
    (∫ x : ℝ, term 2 2 y x) = (differenceKernel y : ℂ) :=
  integral_term_of_fourier rfl (by unfold differenceKernel; fun_prop)
    (integrable_of_halves difference_pos difference_neg) fourier_difference y

private theorem integral_sum_term (y : ℝ) :
    (∫ x : ℝ, term 3 1 y x) = (sumKernel y : ℂ) :=
  integral_term_of_fourier rfl (by unfold sumKernel; fun_prop)
    (integrable_of_halves sum_pos sum_neg) fourier_sum y

private theorem density_eq (x : ℝ) :
    (density x : ℂ) = (1 / (rate x * rate (-x))) / (2 * Real.pi : ℂ) := by
  rw [density, Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_mul, Complex.ofReal_mul,
    Complex.ofReal_ofNat, Complex.sq_norm, ← Complex.mul_conj, conj_rate, div_div,
    mul_comm (2 * (Real.pi : ℂ))]

private theorem expand_pairs {ι : Type*} (J : Finset ι) (b z z' : ι → ℝ)
    (n m : ℕ) (s x : ℝ) :
    phase s x * ((∑ j ∈ J, (b j : ℂ) * phase (z j) x) *
      (∑ k ∈ J, (b k : ℂ) * phase (z' k) x)) * (rational n m x / (2 * Real.pi : ℂ)) =
      ∑ j ∈ J, ∑ k ∈ J, (b j : ℂ) * (b k : ℂ) * term n m (s + z j + z' k) x := by
  simp only [Finset.sum_mul]
  simp only [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ ↦ Finset.sum_congr rfl fun k _ ↦ ?_
  unfold term
  simp only [phase_add]
  ring

private theorem expand_norm_sq {ι : Type*} (J : Finset ι) (b z : ι → ℝ) (s x : ℝ) :
    phase s x * (‖jumpRepresenter J b z x‖ ^ 2 : ℝ) * (density x : ℂ) =
      ∑ j ∈ J, ∑ k ∈ J, (b j : ℂ) * (b k : ℂ) * term 2 2 (s + z j - z k) x := by
  have hfactor (A B : ℂ) :
      phase s x * ((A / rate x) * (B / rate (-x))) * (density x : ℂ) =
        phase s x * (A * B) * (rational 2 2 x / (2 * Real.pi : ℂ)) := by
    rw [rational, density_eq]
    field_simp [rate_ne_zero, Complex.ofReal_ne_zero.mpr Real.pi_ne_zero]
  rw [Complex.sq_norm, ← Complex.mul_conj]
  simp only [jumpRepresenter, map_div₀, map_sum, map_mul, Complex.conj_ofReal, conj_rate, conj_phase]
  rw [hfactor]
  simpa only [sub_eq_add_neg] using expand_pairs J b z (fun k ↦ -z k) 2 2 s x

private theorem expand_sq {ι : Type*} (J : Finset ι) (b z : ι → ℝ) (s x : ℝ) :
    phase s x * jumpRepresenter J b z x ^ 2 * (density x : ℂ) =
      ∑ j ∈ J, ∑ k ∈ J, (b j : ℂ) * (b k : ℂ) * term 3 1 (s + z j + z k) x := by
  have hfactor (A B : ℂ) :
      phase s x * ((A / rate x) * (B / rate x)) * (density x : ℂ) =
        phase s x * (A * B) * (rational 3 1 x / (2 * Real.pi : ℂ)) := by
    rw [rational, density_eq, pow_one]
    field_simp [rate_ne_zero, Complex.ofReal_ne_zero.mpr Real.pi_ne_zero]
  rw [pow_two, jumpRepresenter, hfactor]
  exact expand_pairs J b z z 3 1 s x

private theorem integral_pairs {ι : Type*} (J : Finset ι) (b : ι → ℝ)
    (freq : ι → ι → ℝ) {n m : ℕ} (hnm : n + m = 4) {K : ℝ → ℝ}
    (hK : ∀ y : ℝ, (∫ x : ℝ, term n m y x) = (K y : ℂ)) :
    (∫ x : ℝ, ∑ j ∈ J, ∑ k ∈ J, (b j : ℂ) * (b k : ℂ) * term n m (freq j k) x) =
      ∑ j ∈ J, ∑ k ∈ J, (b j : ℂ) * (b k : ℂ) * (K (freq j k) : ℂ) := by
  have hterm (j k : ι) :
      Integrable (fun x ↦ (b j : ℂ) * (b k : ℂ) * term n m (freq j k) x) :=
    (integrable_term hnm (freq j k)).const_mul _
  rw [integral_finsetSum J (fun j _ ↦ integrable_finsetSum J (fun k _ ↦ hterm j k))]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [integral_finsetSum J (fun k _ ↦ hterm j k)]
  exact Finset.sum_congr rfl fun k _ ↦ by rw [integral_const_mul, hK]

/-- The positive angular Fourier transform of `‖G‖²` against the normalized Cauchy
measure, as a complex equality. The shift may be zero and the family may be empty. -/
public theorem integral_norm_sq {ι : Type*} (J : Finset ι) (b z : ι → ℝ) (s : ℝ) :
    (∫ x : ℝ, phase s x * (‖jumpRepresenter J b z x‖ ^ 2 : ℝ) * (density x : ℂ)) =
      ∑ j ∈ J, ∑ k ∈ J, (b j : ℂ) * (b k : ℂ) * (differenceKernel (s + z j - z k) : ℂ) := by
  simp_rw [expand_norm_sq]
  exact integral_pairs J b (fun j k ↦ s + z j - z k) rfl integral_difference_term

/-- The positive angular Fourier transform of `G²` against the normalized Cauchy
measure, as a complex equality. The one-sided polynomial uses the positive part
of the *sum* frequency `s + z j + z k`. -/
public theorem integral_sq {ι : Type*} (J : Finset ι) (b z : ι → ℝ) (s : ℝ) :
    (∫ x : ℝ, phase s x * jumpRepresenter J b z x ^ 2 * (density x : ℂ)) =
      ∑ j ∈ J, ∑ k ∈ J, (b j : ℂ) * (b k : ℂ) * (sumKernel (s + z j + z k) : ℂ) := by
  simp_rw [expand_sq]
  exact integral_pairs J b (fun j k ↦ s + z j + z k) rfl integral_sum_term

end StepProfileQuadraticFourier
