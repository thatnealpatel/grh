module

public import Lemmas.SignedPoissonDefect
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Fourier.Convolution

/-!
# Poisson transport of strip-holomorphic tests

Source: `4c47eae3387e:.godel/bob/uncut-poisson-transfer.md:17–23`.
Scope: the normalized whole-real-line Poisson smoothing of a holomorphic test with
inverse-square decay on each closed inner strip. We check absolute convergence,
holomorphy, the factor-three bound for widths at most one, and the angular Fourier
multiplier, including mass and logarithmic frequencies. This is not a Weil screen.

Owning check session: `01a20fa3-d781-7816-bdbd-149ebe36b7b4`.
-/

open MeasureTheory Set Filter Metric
open scoped Convolution FourierTransform Topology

namespace PoissonStripTest

open SignedPoissonDefect (kernel poisson)

/-- The open horizontal strip of half-width `a` centered on the real axis. -/
@[expose] public def horizontalStrip (a : ℝ) : Set ℂ := {z | |z.im| < a}

/-- Inverse-square bounds with a separate constant `M b` for each closed inner strip. -/
@[expose] public def StripBounds (a : ℝ) (F : ℂ → ℂ) (M : ℝ → ℝ) : Prop :=
  ∀ ⦃b : ℝ⦄, 0 ≤ b → b < a → ∀ z : ℂ, |z.im| ≤ b →
    ‖F z‖ ≤ M b / (1 / 4 + z.re ^ 2)

/-- Normalized Poisson smoothing by horizontal translations, at each complex input. -/
@[expose] public noncomputable def poissonSmooth (h : ℝ) (F : ℂ → ℂ) (z : ℂ) : ℂ :=
  ∫ y : ℝ, (poisson h y : ℂ) * F (z - (y : ℂ))

/-- The unnormalized real-axis Fourier integral at angular frequency, with negative phase. -/
@[expose] public noncomputable def angularFourier (f : ℝ → ℂ) (ω : ℝ) : ℂ :=
  ∫ x : ℝ, f x * Complex.exp (↑(-ω * x) * Complex.I)

private theorem isOpen_strip (a : ℝ) : IsOpen (horizontalStrip a) :=
  isOpen_lt Complex.continuous_im.abs continuous_const

private theorem translate_mem_strip {a : ℝ} {z : ℂ} (hz : z ∈ horizontalStrip a) (y : ℝ) :
    z - (y : ℂ) ∈ horizontalStrip a := by
  simpa [horizontalStrip] using hz

private theorem continuous_horizontalTranslate {a : ℝ} {G : ℂ → ℂ}
    (hG : ContinuousOn G (horizontalStrip a)) {z : ℂ} (hz : z ∈ horizontalStrip a) :
    Continuous (fun y : ℝ ↦ G (z - (y : ℂ))) :=
  hG.comp_continuous (continuous_const.sub Complex.continuous_ofReal) (translate_mem_strip hz)

private theorem continuous_kernel {h : ℝ} (hh : 0 < h) : Continuous (kernel h) :=
  continuous_const.div (by fun_prop) (fun x ↦ (by positivity : 0 < h ^ 2 + x ^ 2).ne')

private theorem continuous_poisson {h : ℝ} (hh : 0 < h) :
    Continuous (fun y : ℝ ↦ (poisson h y : ℂ)) :=
  Complex.continuous_ofReal.comp ((continuous_kernel hh).div_const Real.pi)

private theorem poisson_nonneg {h : ℝ} (hh : 0 < h) (y : ℝ) : 0 ≤ poisson h y := by
  unfold poisson kernel
  positivity

private theorem integrable_poissonC {h : ℝ} (hh : 0 < h) :
    Integrable (fun y : ℝ ↦ (poisson h y : ℂ)) := by
  -- The landed multiplier gives a nonzero integral at zero; a nonintegrable
  -- function would have Bochner integral zero.
  by_contra hnot
  have hm : (∫ y : ℝ, (poisson h y : ℂ)) = 1 := by
    simpa using SignedPoissonDefect.integral_poisson_exp hh 0
  rw [integral_undef hnot] at hm
  exact zero_ne_one hm

private theorem integrable_poisson {h : ℝ} (hh : 0 < h) : Integrable (poisson h) :=
  Integrable.iff_ofReal.mpr (integrable_poissonC hh)

private theorem const_nonneg {a : ℝ} {F : ℂ → ℂ} {M : ℝ → ℝ}
    (hM : StripBounds a F M) {b : ℝ} (hb : 0 ≤ b) (hba : b < a) : 0 ≤ M b := by
  have hz := hM hb hba 0 (by simpa using hb)
  have hden : 0 < (1 / 4 : ℝ) + (0 : ℂ).re ^ 2 := by positivity
  have hn : 0 ≤ M b / (1 / 4 + (0 : ℂ).re ^ 2) := (norm_nonneg _).trans hz
  simpa only [zero_mul] using (le_div_iff₀ hden).mp hn

private theorem uniform_inner_bound {a : ℝ} {F : ℂ → ℂ} {M : ℝ → ℝ}
    (hM : StripBounds a F M) {b : ℝ} (hb : 0 ≤ b) (hba : b < a)
    {z : ℂ} (hz : |z.im| ≤ b) : ‖F z‖ ≤ 4 * M b := by
  calc
    ‖F z‖ ≤ M b / (1 / 4 + z.re ^ 2) := hM hb hba z hz
    _ ≤ M b / (1 / 4) := div_le_div_of_nonneg_left (const_nonneg hM hb hba)
      (by norm_num) (le_add_of_nonneg_right (sq_nonneg _))
    _ = 4 * M b := by ring

/-- For every point of the open strip, the smoothing integrand is absolutely integrable. -/
public theorem integrable_poissonSmooth_integrand {a h : ℝ} {F : ℂ → ℂ} {M : ℝ → ℝ}
    (hh : 0 < h) (hF : DifferentiableOn ℂ F (horizontalStrip a)) (hM : StripBounds a F M)
    {z : ℂ} (hz : z ∈ horizontalStrip a) :
    Integrable (fun y : ℝ ↦ (poisson h y : ℂ) * F (z - (y : ℂ))) := by
  refine (integrable_poissonC hh).mul_bdd (c := 4 * M |z.im|)
    (continuous_horizontalTranslate hF.continuousOn hz).aestronglyMeasurable ?_
  exact .of_forall fun y ↦ uniform_inner_bound hM (abs_nonneg z.im) hz
    (by simp : |(z - (y : ℂ)).im| ≤ |z.im|)

private theorem abs_im_le_add_dist (z w : ℂ) : |z.im| ≤ |w.im| + dist z w := by
  calc
    |z.im| = |w.im + (z - w).im| := by rw [Complex.sub_im]; congr 1; ring
    _ ≤ |w.im| + |(z - w).im| := abs_add_le _ _
    _ ≤ |w.im| + dist z w := by
      rw [dist_eq_norm]
      exact add_le_add_right (Complex.abs_im_le_norm (z - w)) _

/-- Poisson smoothing is holomorphic on the original open strip. -/
public theorem differentiableOn_poissonSmooth {a h : ℝ} {F : ℂ → ℂ} {M : ℝ → ℝ}
    (hh : 0 < h) (hF : DifferentiableOn ℂ F (horizontalStrip a)) (hM : StripBounds a F M) :
    DifferentiableOn ℂ (poissonSmooth h F) (horizontalStrip a) := by
  intro z hz
  have hz' : |z.im| < a := hz
  obtain ⟨b, hzb, hba⟩ := exists_between hz'
  have hb : 0 ≤ b := (abs_nonneg _).trans hzb.le
  let r := (b - |z.im|) / 2
  have hr : 0 < r := half_pos (sub_pos.mpr hzb)
  have hball {w : ℂ} (hw : w ∈ ball z r) : w ∈ horizontalStrip a := by
    have hd := Metric.mem_ball.mp hw
    have hi := abs_im_le_add_dist w z
    change |w.im| < a
    dsimp [r] at hd
    linarith
  have hclosed {w : ℂ} (hw : w ∈ ball z r) (y : ℝ) {v : ℂ}
      (hv : v ∈ closedBall (w - (y : ℂ)) r) : |v.im| ≤ b := by
    have hdw := Metric.mem_ball.mp hw
    have hdv := Metric.mem_closedBall.mp hv
    have hiw := abs_im_le_add_dist w z
    have hiv := abs_im_le_add_dist v (w - (y : ℂ))
    simp only [Complex.sub_im, Complex.ofReal_im, sub_zero] at hiv
    dsimp [r] at hdw hdv
    linarith
  -- A fixed radius works for all real translates. Cauchy's estimate gives
  -- a derivative bound independent of the translate before multiplication by P_h.
  have hderiv {w : ℂ} (hw : w ∈ ball z r) (y : ℝ) :
      ‖deriv F (w - (y : ℂ))‖ ≤ 4 * M b / r := by
    have hs : closedBall (w - (y : ℂ)) r ⊆ horizontalStrip a :=
      fun _ hv ↦ (hclosed hw y hv).trans_lt hba
    rw [← Complex.cderiv_eq_deriv (isOpen_strip a) hF hr hs]
    exact Complex.norm_cderiv_le hr fun v hv ↦
      uniform_inner_bound hM hb hba (hclosed hw y (sphere_subset_closedBall hv))
  have hball_nhds : ∀ᶠ w in 𝓝 z, w ∈ ball z r := ball_mem_nhds z hr
  have hmeas : ∀ᶠ w in 𝓝 z,
      AEStronglyMeasurable (fun y : ℝ ↦ (poisson h y : ℂ) * F (w - (y : ℂ))) volume :=
    hball_nhds.mono fun _ hw ↦ ((continuous_poisson hh).mul
      (continuous_horizontalTranslate hF.continuousOn (hball hw))).aestronglyMeasurable
  have hdmeas : AEStronglyMeasurable
      (fun y : ℝ ↦ (poisson h y : ℂ) * deriv F (z - (y : ℂ))) volume :=
    ((continuous_poisson hh).mul (continuous_horizontalTranslate
      (hF.deriv (isOpen_strip a)).continuousOn hz)).aestronglyMeasurable
  have hd := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun w (y : ℝ) ↦ (poisson h y : ℂ) * F (w - (y : ℂ)))
    (F' := fun w (y : ℝ) ↦ (poisson h y : ℂ) * deriv F (w - (y : ℂ)))
    (bound := fun y ↦ poisson h y * (4 * M b / r))
    (ball_mem_nhds z hr) hmeas (integrable_poissonSmooth_integrand hh hF hM hz) hdmeas
    (.of_forall fun y w hw ↦ by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (poisson_nonneg hh y)]
      exact mul_le_mul_of_nonneg_left (hderiv hw y) (poisson_nonneg hh y))
    ((integrable_poisson hh).mul_const _)
    (.of_forall fun y w hw ↦ by
      have hdF := (hF.differentiableAt ((isOpen_strip a).mem_nhds
        (translate_mem_strip (hball hw) y))).hasDerivAt
      simpa only [Function.comp_def, id_eq, mul_one] using
        (hdF.comp w ((hasDerivAt_id w).sub_const (y : ℂ))).const_mul (poisson h y : ℂ))
  exact hd.2.differentiableAt.differentiableWithinAt

private theorem two_mul_half_kernel (x : ℝ) :
    2 * kernel (1 / 2) x = (1 / 4 + x ^ 2)⁻¹ := by
  rw [kernel, ← mul_div_assoc]
  norm_num [one_div]

private theorem integrable_poisson_mul_half_kernel {h : ℝ} (hh : 0 < h) (x : ℝ) :
    Integrable (fun y : ℝ ↦ poisson h y * kernel (1 / 2) (x - y)) := by
  refine (integrable_poisson hh).mul_bdd (c := 2)
    (((continuous_kernel (by norm_num : 0 < (1 / 2 : ℝ))).comp
      (continuous_const.sub continuous_id)).aestronglyMeasurable) ?_
  exact .of_forall fun y ↦ by
    rw [Real.norm_of_nonneg (by unfold kernel; positivity), kernel]
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith [sq_nonneg (x - y)]

/-- On each closed inner strip the original inverse-square bound holds with constant `3 * M b`. -/
public theorem stripBounds_poissonSmooth {a h : ℝ} {F : ℂ → ℂ} {M : ℝ → ℝ}
    (hh : 0 < h) (hh₁ : h ≤ 1) (hF : DifferentiableOn ℂ F (horizontalStrip a))
    (hM : StripBounds a F M) : StripBounds a (poissonSmooth h F) (fun b ↦ 3 * M b) := by
  intro b hb hba z hz
  have hMb := const_nonneg hM hb hba
  have hint := integrable_poissonSmooth_integrand hh hF hM (hz.trans_lt hba)
  have hhalf : (0 : ℝ) < 1 / 2 := by norm_num
  have hconv := SignedPoissonDefect.poisson_convolution_kernel hh hhalf.ne' z.re
  rw [Real.sign_of_pos hhalf, abs_of_pos hhalf, one_mul] at hconv
  calc
    ‖poissonSmooth h F z‖ ≤ ∫ y : ℝ, ‖(poisson h y : ℂ) * F (z - (y : ℂ))‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ y : ℝ, (2 * M b) * (poisson h y * kernel (1 / 2) (z.re - y)) := by
      refine integral_mono hint.norm ((integrable_poisson_mul_half_kernel hh z.re).const_mul _)
        fun y ↦ ?_
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (poisson_nonneg hh y)]
      have hy := hM hb hba (z - (y : ℂ)) (by simpa using hz)
      simp only [Complex.sub_re, Complex.ofReal_re] at hy
      calc
        _ ≤ poisson h y * (M b / (1 / 4 + (z.re - y) ^ 2)) :=
          mul_le_mul_of_nonneg_left hy (poisson_nonneg hh y)
        _ = poisson h y * (M b * (2 * kernel (1 / 2) (z.re - y))) := by
          rw [two_mul_half_kernel, div_eq_mul_inv]
        _ = _ := by ring
    _ = (2 * M b) * kernel (h + 1 / 2) z.re := by rw [integral_const_mul, hconv]
    _ ≤ (3 * M b) / (1 / 4 + z.re ^ 2) := by
      rw [kernel, ← mul_div_assoc]
      refine div_le_div₀ (by positivity) ?_ (by positivity) ?_
      · calc
          2 * M b * (h + 1 / 2) = M b * (2 * (h + 1 / 2)) := by ring
          _ ≤ M b * 3 := mul_le_mul_of_nonneg_left (by linarith) hMb
          _ = 3 * M b := mul_comm ..
      · nlinarith [sq_nonneg h]

private theorem integrable_realAxis {a : ℝ} {F : ℂ → ℂ} {M : ℝ → ℝ}
    (ha : 0 < a) (hF : DifferentiableOn ℂ F (horizontalStrip a)) (hM : StripBounds a F M) :
    Integrable (fun x : ℝ ↦ F x) := by
  have hc : Continuous (fun x : ℝ ↦ F x) := hF.continuousOn.comp_continuous
    Complex.continuous_ofReal (fun x ↦ by simpa [horizontalStrip] using ha)
  apply ((integrable_poisson (by norm_num : 0 < (1 / 2 : ℝ))).const_mul
    (2 * Real.pi * M 0)).mono' hc.aestronglyMeasurable
  exact .of_forall fun x ↦ calc
    ‖F x‖ ≤ M 0 / (1 / 4 + x ^ 2) := by simpa using hM le_rfl ha (x : ℂ) (by simp)
    _ = M 0 * (2 * kernel (1 / 2) x) := by rw [two_mul_half_kernel, div_eq_mul_inv]
    _ = (2 * Real.pi * M 0) * poisson (1 / 2) x := by
      unfold poisson
      field_simp [Real.pi_ne_zero]

private theorem integrable_angular_integrand {f : ℝ → ℂ} (hf : Integrable f) (ω : ℝ) :
    Integrable (fun x : ℝ ↦ f x * Complex.exp (↑(-ω * x) * Complex.I)) := by
  refine hf.mul_bdd (c := 1) (Continuous.aestronglyMeasurable (by fun_prop))
    (.of_forall fun x ↦ by simp [Complex.norm_exp, Complex.mul_re])

private theorem fourier_eq_angular (f : ℝ → ℂ) (ω : ℝ) :
    𝓕 f (ω / (2 * Real.pi)) = angularFourier f ω := by
  rw [Real.fourier_real_eq_integral_exp_smul, angularFourier]
  refine integral_congr_ae (.of_forall fun x ↦ ?_)
  change Complex.exp (↑(-2 * Real.pi * x * (ω / (2 * Real.pi))) * Complex.I) • f x =
    f x * Complex.exp (↑(-ω * x) * Complex.I)
  have hphase : -2 * Real.pi * x * (ω / (2 * Real.pi)) = -ω * x := by field_simp
  rw [hphase, smul_eq_mul, mul_comm]

/-- Both angular Fourier integrands are absolutely integrable, and the smoothed transform
is obtained by multiplication by `exp (-h * |ω|)`. -/
public theorem angularFourier_poissonSmooth {a h : ℝ} {F : ℂ → ℂ} {M : ℝ → ℝ}
    (ha : 0 < a) (hh : 0 < h) (hF : DifferentiableOn ℂ F (horizontalStrip a))
    (hM : StripBounds a F M) (ω : ℝ) :
    Integrable (fun x : ℝ ↦ F x * Complex.exp (↑(-ω * x) * Complex.I)) ∧
    Integrable (fun x : ℝ ↦ poissonSmooth h F x * Complex.exp (↑(-ω * x) * Complex.I)) ∧
    angularFourier (fun x : ℝ ↦ poissonSmooth h F x) ω =
      (Real.exp (-h * |ω|) : ℂ) * angularFourier (fun x : ℝ ↦ F x) ω := by
  let p (x : ℝ) := (poisson h x : ℂ)
  let f (x : ℝ) := F x
  have hp : Integrable p := integrable_poissonC hh
  have hf : Integrable f := integrable_realAxis ha hF hM
  have hc : (fun x : ℝ ↦ poissonSmooth h F x) =
      p ⋆[ContinuousLinearMap.mul ℂ ℂ] f := by
    funext x
    rw [convolution_mul, poissonSmooth]
    simp only [p, f, Complex.ofReal_sub]
  refine ⟨integrable_angular_integrand hf ω,
    integrable_angular_integrand (hc ▸ hp.integrable_convolution _ hf) ω, ?_⟩
  -- The L¹ convolution theorem includes absolute integrability on the product,
  -- Fubini, translation of the inner variable, and factorization of the phase.
  rw [hc, ← fourier_eq_angular, Real.fourier_mul_convolution_eq hp hf,
    fourier_eq_angular p, fourier_eq_angular f]
  rw [show angularFourier p ω = (Real.exp (-h * |ω|) : ℂ) from
    SignedPoissonDefect.integral_poisson_exp hh ω]

/-- The real-axis mass, hence also the mass divided by `2π`, is unchanged. -/
public theorem integral_poissonSmooth_realAxis {a h : ℝ} {F : ℂ → ℂ} {M : ℝ → ℝ}
    (ha : 0 < a) (hh : 0 < h) (hF : DifferentiableOn ℂ F (horizontalStrip a))
    (hM : StripBounds a F M) :
    (∫ x : ℝ, poissonSmooth h F x) = ∫ x : ℝ, F x := by
  simpa [angularFourier] using (angularFourier_poissonSmooth ha hh hF hM 0).2.2

/-- The multiplier at each of the two frequencies `±log n` is `n ^ (-h)`. -/
public theorem angularFourier_poissonSmooth_log {a h : ℝ} {F : ℂ → ℂ} {M : ℝ → ℝ}
    (ha : 0 < a) (hh : 0 < h) (hF : DifferentiableOn ℂ F (horizontalStrip a))
    (hM : StripBounds a F M) {n : ℕ} (hn : 0 < n) :
    angularFourier (fun x : ℝ ↦ poissonSmooth h F x) (Real.log n) =
      ↑((n : ℝ) ^ (-h)) * angularFourier (fun x : ℝ ↦ F x) (Real.log n) ∧
    angularFourier (fun x : ℝ ↦ poissonSmooth h F x) (-Real.log n) =
      ↑((n : ℝ) ^ (-h)) * angularFourier (fun x : ℝ ↦ F x) (-Real.log n) := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hn₁ : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hpow : Real.exp (-h * |Real.log n|) = (n : ℝ) ^ (-h) := by
    rw [abs_of_nonneg (Real.log_nonneg hn₁), Real.rpow_def_of_pos hnR, mul_comm (-h)]
  exact ⟨by simpa only [hpow] using (angularFourier_poissonSmooth ha hh hF hM (Real.log n)).2.2,
    by simpa only [abs_neg, hpow] using
      (angularFourier_poissonSmooth ha hh hF hM (-Real.log n)).2.2⟩

end PoissonStripTest
