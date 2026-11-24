module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Basic.Real.Sign
public import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
import Mathlib.Analysis.Fourier.Convolution
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Probability.Distributions.Cauchy

/-!
# Signed Poisson convolution and finite atom defect

Source: `d675c849:.godel/bob/deep-retained-excess.md:31–38`, equation (3) and
its single-kernel identity. See `b4a66edd:.godel/bob/interior-trace-depth-transfer.md:18`
and `11525496:.godel/bob/uncut-trace-normal.md:41` for uses of the identity.

Scope: whole-real-line convolution at every translate, followed by the depth
defect for a finite indexed family of atoms, with multiplicities. No infinite
divisor sum, convergence for zeta zeros, or logarithmic-derivative identity is asserted.

Owning check session: `01a20b8b-65a1-7430-ae92-47e2bde881a8`.
-/

open MeasureTheory Set
open scoped BigOperators Convolution FourierTransform

namespace SignedPoissonDefect

/-- The Cauchy kernel with signed width `d`. -/
@[expose] public noncomputable def kernel (d x : ℝ) : ℝ := d / (d ^ 2 + x ^ 2)

/-- The Poisson kernel, normalized to have mass one for positive width. -/
@[expose] public noncomputable def poisson (h x : ℝ) : ℝ := kernel h x / Real.pi

private theorem kernel_neg_width (d x : ℝ) : kernel (-d) x = -kernel d x := by
  simp [kernel, neg_div]

private theorem continuous_kernel {d : ℝ} (hd : d ≠ 0) : Continuous (kernel d) :=
  continuous_const.div (by fun_prop) (fun x ↦ (by positivity : 0 < d ^ 2 + x ^ 2).ne')

private theorem norm_kernel_le {d : ℝ} (hd : 0 < d) (x : ℝ) : ‖kernel d x‖ ≤ d⁻¹ := by
  rw [Real.norm_of_nonneg (by unfold kernel; positivity), kernel]
  apply (div_le_iff₀ (by positivity)).2
  calc
    d = d⁻¹ * d ^ 2 := by field_simp
    _ ≤ d⁻¹ * (d ^ 2 + x ^ 2) := by gcongr; exact le_add_of_nonneg_right (sq_nonneg x)

private theorem integrable_poisson {a : ℝ} (ha : 0 < a) : Integrable (poisson a) := by
  let A : NNReal := ⟨a, ha.le⟩
  have hpdf (x : ℝ) : poisson a x = ProbabilityTheory.cauchyPDFReal 0 A x := by
    rw [ProbabilityTheory.cauchyPDFReal_def]
    change a / (a ^ 2 + x ^ 2) / Real.pi = Real.pi⁻¹ * a * ((x - 0) ^ 2 + a ^ 2)⁻¹
    simp only [sub_zero, div_eq_mul_inv]
    ring
  exact (ProbabilityTheory.integrable_cauchyPDFReal 0 (γ := A)).congr
    (.of_forall fun x ↦ (hpdf x).symm)

private noncomputable def poissonC (a x : ℝ) : ℂ := (poisson a x : ℂ)

private noncomputable def profile (a t : ℝ) : ℂ :=
  (Real.exp (-(2 * Real.pi * a) * |t|) : ℂ)

private theorem continuous_profile (a : ℝ) : Continuous (profile a) := by
  unfold profile
  fun_prop

private theorem integrable_profile {a : ℝ} (ha : 0 < a) : Integrable (profile a) := by
  have h : 0 < 2 * Real.pi * a := by positivity
  have hp : IntegrableOn (profile a) (Ioi 0) := by
    apply (integrableOn_exp_mul_Ioi (neg_neg_of_pos h) 0).ofReal.congr
    exact (ae_restrict_iff' measurableSet_Ioi).2 (.of_forall fun t ht ↦ by
      simp [profile, abs_of_pos ht.out])
  have hn : IntegrableOn (profile a) (Iic 0) := by
    apply (integrableOn_exp_mul_Iic h 0).ofReal.congr
    exact (ae_restrict_iff' measurableSet_Iic).2 (.of_forall fun t ht ↦ by
      simp [profile, abs_of_nonpos ht.out, mul_neg, neg_mul])
  simpa [← compl_Ioi] using hp.union hn

-- Compute the transform of the integrable two-sided exponential on its two half-lines.
private theorem fourier_profile {a : ℝ} (ha : 0 < a) : 𝓕 (profile a) = poissonC a := by
  funext x
  let b : ℝ := 2 * Real.pi * a
  let c : ℝ := 2 * Real.pi * x
  let p : ℂ := -(b : ℂ) - (c : ℂ) * Complex.I
  let q : ℂ := (b : ℂ) - (c : ℂ) * Complex.I
  have hb : 0 < b := by dsimp [b]; positivity
  have hp : p.re < 0 := by simpa [p, Complex.mul_re] using hb
  have hq : 0 < q.re := by simpa [q, Complex.mul_re] using hb
  let w (t : ℝ) := Complex.exp (↑(-2 * Real.pi * t * x) * Complex.I) • profile a t
  have hw : Integrable w := by
    apply (integrable_profile ha).norm.mono'
    · unfold w profile; fun_prop
    · exact .of_forall fun t ↦ by simp [w, Complex.norm_exp, Complex.mul_re]
  rw [Real.fourier_real_eq_integral_exp_smul]
  change ∫ t, w t = _
  rw [← integral_add_compl (s := Ioi (0 : ℝ)) measurableSet_Ioi hw, compl_Ioi]
  have hphase (t r : ℝ) (ht : -(2 * Real.pi * a) * |t| = r * t) :
      w t = Complex.exp (((r : ℂ) - (c : ℂ) * Complex.I) * t) := by
    simp only [w, profile, ht, smul_eq_mul, Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    dsimp [c]
    push_cast
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi (f := w) (g := fun t ↦ Complex.exp (p * t))
      (fun t ht ↦ by
        simpa only [p, Complex.ofReal_neg] using
          hphase t (-b) (by rw [abs_of_pos ht.out])),
    setIntegral_congr_fun measurableSet_Iic (f := w) (g := fun t ↦ Complex.exp (q * t))
      (fun t ht ↦ hphase t b (by rw [abs_of_nonpos ht.out]; dsimp [b]; ring)),
    integral_exp_mul_complex_Ioi hp 0, integral_exp_mul_complex_Iic hq 0]
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, poissonC, poisson, kernel,
    Complex.ofReal_div, Complex.ofReal_add, Complex.ofReal_pow]
  have hp' : p ≠ 0 := fun h ↦ by simp [h] at hp
  have hq' : q ≠ 0 := fun h ↦ by simp [h] at hq
  have hax : ((a : ℂ) ^ 2 + (x : ℂ) ^ 2) ≠ 0 := by
    exact_mod_cast (by positivity : 0 < a ^ 2 + x ^ 2).ne'
  field_simp [hp', hq', hax, Complex.ofReal_ne_zero.mpr Real.pi_ne_zero]
  dsimp [p, q, b, c]
  push_cast
  linear_combination (norm := ring_nf)
    (-(a : ℂ) * (x : ℂ) ^ 2 * (Real.pi : ℂ) ^ 2 * 4) * Complex.I_sq

private theorem integrable_poissonC {a : ℝ} (ha : 0 < a) : Integrable (poissonC a) :=
  (integrable_poisson ha).ofReal

private theorem fourier_poissonC {a : ℝ} (ha : 0 < a) : 𝓕 (poissonC a) = profile a := by
  have hinv := (continuous_profile a).fourierInv_fourier_eq (integrable_profile ha)
    (fourier_profile ha ▸ integrable_poissonC ha)
  rw [fourier_profile ha] at hinv
  funext t
  simpa only [Real.fourierInv_eq_fourier_neg, neg_neg, profile, abs_neg] using congrFun hinv (-t)

private theorem poissonC_convolution {h d : ℝ} (hh : 0 < h) (hd : 0 < d) :
    (poissonC h ⋆[ContinuousLinearMap.mul ℂ ℂ] poissonC d) = poissonC (h + d) := by
  let B := ContinuousLinearMap.mul ℂ ℂ
  have htransform : 𝓕 (poissonC h ⋆[B] poissonC d) = 𝓕 (poissonC (h + d)) := by
    funext t
    rw [Real.fourier_mul_convolution_eq (integrable_poissonC hh) (integrable_poissonC hd),
      fourier_poissonC hh, fourier_poissonC hd, fourier_poissonC (add_pos hh hd)]
    simp only [profile, ← Complex.ofReal_mul, ← Real.exp_add]
    congr 2
    ring
  have hdcont : Continuous (poissonC d) :=
    Complex.continuous_ofReal.comp ((continuous_kernel hd.ne').div_const Real.pi)
  have hdbdd : BddAbove (range fun x ↦ ‖poissonC d x‖) := by
    refine ⟨d⁻¹ / Real.pi, ?_⟩
    rintro _ ⟨x, rfl⟩
    change ‖(poisson d x : ℂ)‖ ≤ _
    rw [Complex.norm_real, poisson, norm_div, Real.norm_of_nonneg Real.pi_pos.le]
    exact div_le_div_of_nonneg_right (norm_kernel_le hd x) Real.pi_pos.le
  have hcont := hdbdd.continuous_convolution_right_of_integrable B (integrable_poissonC hh) hdcont
  have hconv := (integrable_poissonC hh).integrable_convolution B (integrable_poissonC hd)
  have hs : Integrable (𝓕 (poissonC (h + d))) := by
    rw [fourier_poissonC (add_pos hh hd)]
    exact integrable_profile (add_pos hh hd)
  have hc := hcont.fourierInv_fourier_eq hconv (htransform.symm ▸ hs)
  have hp := (Complex.continuous_ofReal.comp
    ((continuous_kernel (add_pos hh hd).ne').div_const Real.pi)).fourierInv_fourier_eq
      (integrable_poissonC (add_pos hh hd)) hs
  exact hc.symm.trans ((congrArg (𝓕⁻ ·) htransform).trans hp)

private theorem poisson_convolution_kernel_pos {h d : ℝ} (hh : 0 < h) (hd : 0 < d) (x : ℝ) :
    (∫ y : ℝ, poisson h y * kernel d (x - y)) = kernel (h + d) x := by
  have hc := congrFun (poissonC_convolution hh hd) x
  rw [convolution_mul] at hc
  simp only [poissonC, ← Complex.ofReal_mul, integral_complex_ofReal] at hc
  have hr := Complex.ofReal_injective hc
  simp only [poisson] at hr
  simp_rw [← mul_div_assoc] at hr
  rw [integral_div, div_left_inj₀ Real.pi_ne_zero] at hr
  exact hr

/-- Actual Lebesgue convolution of the normalized positive Poisson kernel with a
nonzero signed-width kernel, at every real translate. -/
public theorem poisson_convolution_kernel {h d : ℝ} (hh : 0 < h) (hd : d ≠ 0) (x : ℝ) :
    (∫ y : ℝ, poisson h y * kernel d (x - y)) = Real.sign d * kernel (h + |d|) x := by
  rcases hd.lt_or_gt with hneg | hpos
  · have hodd (z : ℝ) : kernel d z = -kernel (-d) z := by
      simpa only [neg_neg] using kernel_neg_width (-d) z
    simp_rw [hodd (x - _), mul_neg, integral_neg, Real.sign_of_neg hneg, abs_of_neg hneg,
      poisson_convolution_kernel_pos hh (neg_pos.mpr hneg), neg_one_mul]
  · simpa only [Real.sign_of_pos hpos, abs_of_pos hpos, one_mul] using
      poisson_convolution_kernel_pos hh hpos x

private theorem norm_signed_kernel_le {d : ℝ} (hd : d ≠ 0) (x : ℝ) :
    ‖kernel d x‖ ≤ |d|⁻¹ := by
  rcases hd.lt_or_gt with hneg | hpos
  · have hodd : kernel d x = -kernel (-d) x := by
      simpa only [neg_neg] using kernel_neg_width (-d) x
    rw [hodd, norm_neg, abs_of_neg hneg]
    exact norm_kernel_le (neg_pos.mpr hneg) x
  · rw [abs_of_pos hpos]
    exact norm_kernel_le hpos x

private theorem integrable_poisson_mul_kernel {h d : ℝ} (hh : 0 < h) (hd : d ≠ 0) (x : ℝ) :
    Integrable (fun y ↦ poisson h y * kernel d (x - y)) := by
  apply ((integrable_poisson hh).norm.mul_const |d|⁻¹).mono'
  · exact (((continuous_kernel hh.ne').div_const Real.pi).mul
      ((continuous_kernel hd).comp (continuous_const.sub continuous_id))).aestronglyMeasurable
  · exact .of_forall fun y ↦ by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (norm_signed_kernel_le hd (x - y)) (norm_nonneg _)

/-- The signed trace of a finite indexed family. Distinct indices may have
identical depth and ordinate. -/
@[expose] public noncomputable def atomTrace {ι : Type*} (atoms : Finset ι)
    (β γ : ι → ℝ) (s v : ℝ) : ℝ := ∑ i ∈ atoms, kernel (s - β i) (v - γ i)

/-- Subtracting the Poisson-smoothed interior trace leaves the two kernels for
each atom to the right of the interior line. The exterior-width hypothesis
matches the source setting; the cancellation itself depends on the interior sign. -/
public theorem finite_atom_defect {ι : Type*} (atoms : Finset ι) (β γ : ι → ℝ)
    {s₀ s₁ : ℝ} (hs : s₀ < s₁) (_hβ₁ : ∀ i ∈ atoms, β i < s₁)
    (hβ₀ : ∀ i ∈ atoms, β i ≠ s₀) (v : ℝ) :
    atomTrace atoms β γ s₁ v -
        (∫ y : ℝ, poisson (s₁ - s₀) y * atomTrace atoms β γ s₀ (v - y)) =
      ∑ i ∈ atoms.filter (fun i ↦ s₀ < β i),
        (kernel (s₁ - β i) (v - γ i) + kernel (s₁ + β i - 2 * s₀) (v - γ i)) := by
  have hh : 0 < s₁ - s₀ := sub_pos.mpr hs
  have hd (i : ι) (hi : i ∈ atoms) : s₀ - β i ≠ 0 := sub_ne_zero.mpr (hβ₀ i hi).symm
  have hshift (i : ι) (y : ℝ) : v - y - γ i = v - γ i - y := sub_right_comm ..
  simp only [atomTrace, Finset.mul_sum, hshift]
  rw [integral_finsetSum atoms (fun i hi ↦ integrable_poisson_mul_kernel hh (hd i hi) (v - γ i)),
    ← Finset.sum_sub_distrib, Finset.sum_filter]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  rw [poisson_convolution_kernel hh (hd i hi)]
  rcases lt_or_gt_of_ne (hβ₀ i hi) with hleft | hright
  · have hw : 0 < s₀ - β i := sub_pos.mpr hleft
    have hadd : s₁ - s₀ + (s₀ - β i) = s₁ - β i := by ring
    simp [Real.sign_of_pos hw, abs_of_pos hw, hadd, not_lt_of_ge hleft.le]
  · have hw : s₀ - β i < 0 := sub_neg.mpr hright
    have hadd : s₁ - s₀ + -(s₀ - β i) = s₁ + β i - 2 * s₀ := by ring
    simp only [Real.sign_of_neg hw, abs_of_neg hw, hadd, neg_one_mul, sub_neg_eq_add,
      ite_eq_left hright]

end SignedPoissonDefect
