module

public import Theorems.RationalThetaInversion
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Absolute unfolding on the nonzero integer lattice

The analytic steps for the rational unramified model of Masullo's
(3.2.2.4) and (3.2.2.11), pp. 125–127.
-/

open MeasureTheory Set
open scoped ENNReal NNReal SchwartzMap

namespace Masullo

/-- The logarithmic Mellin integrand of the two real rays. -/
@[expose] public noncomputable def rationalMellinIntegrand (b : 𝓢(ℝ, ℂ)) (z : ℂ) (x : ℝ) : ℂ :=
  (b (Real.exp x) + b (-Real.exp x)) * Complex.exp (z * x)

private theorem continuous_rationalMellinIntegrand (b : 𝓢(ℝ, ℂ)) (z : ℂ) :
    Continuous (rationalMellinIntegrand b z) :=
  ((b.continuous.comp Real.continuous_exp).add
    (b.continuous.comp Real.continuous_exp.neg)).mul
    (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal))

private theorem norm_rationalMellinIntegrand_le (b : 𝓢(ℝ, ℂ)) (z : ℂ) (n : ℕ) (x : ℝ) :
    ‖rationalMellinIntegrand b z x‖ ≤
      (2 * SchwartzMap.seminorm ℂ n 0 b) * Real.exp ((z.re - (n : ℝ)) * x) := by
  let p := SchwartzMap.seminorm ℂ n 0 b
  have sample (y : ℝ) (hy : ‖y‖ = Real.exp x) :
      ‖b y‖ ≤ p / Real.exp ((n : ℝ) * x) := by
    rw [le_div_iff₀ (Real.exp_pos _), mul_comm, Real.exp_nat_mul, ← hy]
    simpa only [p, norm_iteratedFDeriv_zero] using b.le_seminorm ℂ n 0 y
  have hs₁ := sample (Real.exp x) (Real.norm_of_nonneg (Real.exp_pos x).le)
  have hs₂ := sample (-Real.exp x) (by rw [norm_neg, Real.norm_of_nonneg (Real.exp_pos x).le])
  rw [rationalMellinIntegrand, norm_mul, Complex.norm_exp]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  calc
    _ ≤ (2 * p / Real.exp ((n : ℝ) * x)) * Real.exp (z.re * x) := by
      apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
      refine (norm_add_le _ _).trans ?_
      rw [two_mul, add_div]
      exact add_le_add hs₁ hs₂
    _ = _ := by rw [sub_mul, Real.exp_sub]; ring

/-- The two real rays give an absolutely convergent log-coordinate Mellin integral for
`0 < z.re`, without moment conditions on the Schwartz input. -/
public theorem integrable_rationalMellinIntegrand (b : 𝓢(ℝ, ℂ)) {z : ℂ} (hz : 0 < z.re) :
    Integrable (rationalMellinIntegrand b z) := by
  obtain ⟨n : ℕ, hn⟩ := exists_nat_gt z.re
  have hcont := continuous_rationalMellinIntegrand b z
  have hlo : IntegrableOn (rationalMellinIntegrand b z) (Iic 0) := by
    refine ((integrableOn_exp_mul_Iic hz 0).const_mul
      (2 * SchwartzMap.seminorm ℂ 0 0 b)).mono' hcont.aestronglyMeasurable ?_
    exact Filter.Eventually.of_forall (fun x ↦ by simpa using norm_rationalMellinIntegrand_le b z 0 x)
  have hhi : IntegrableOn (rationalMellinIntegrand b z) (Ioi 0) := by
    refine ((integrableOn_exp_mul_Ioi (sub_neg.mpr hn) 0).const_mul
      (2 * SchwartzMap.seminorm ℂ n 0 b)).mono' hcont.aestronglyMeasurable ?_
    exact Filter.Eventually.of_forall (norm_rationalMellinIntegrand_le b z n)
  simpa using hhi.union hlo

-- The positive copy starts at one, and `Int.negSucc` already starts at minus one.
private def signedNatEquiv : ℕ ⊕ ℕ ≃ {n : ℤ // n ≠ 0} where
  toFun := Sum.elim (fun n ↦ ⟨Int.ofNat (n + 1), by intro h; cases h⟩)
    (fun n ↦ ⟨Int.negSucc n, by simp⟩)
  invFun := fun ⟨n, _⟩ ↦ match n with
    | .ofNat k => .inl k.pred
    | .negSucc k => .inr k
  left_inv := by rintro (n | n) <;> rfl
  right_inv := by
    rintro ⟨n, hn⟩
    cases n with
    | ofNat k => cases k with
      | zero => exact (hn rfl).elim
      | succ k => rfl
    | negSucc k => rfl

private theorem rationalTheta_eq_tsum_pairs (b : 𝓢(ℝ, ℂ)) {t : ℝ} (ht : t ≠ 0) :
    rationalTheta b t = ∑' n : ℕ, (b (t * ((n : ℝ) + 1)) + b (-(t * ((n : ℝ) + 1)))) := by
  let f (s : ℕ ⊕ ℕ) := b (t * (signedNatEquiv s : ℤ))
  have hs := ((summable_norm_schwartz_int_mul b ht).of_norm.subtype
    (fun n : ℤ ↦ n ≠ 0)).comp_injective signedNatEquiv.injective
  have hp : Summable (f ∘ Sum.inl) := hs.comp_injective Sum.inl_injective
  have hm : Summable (f ∘ Sum.inr) := hs.comp_injective Sum.inr_injective
  calc
    _ = ∑' s, f s := (signedNatEquiv.tsum_eq (fun n ↦ b (t * (n : ℤ)))).symm
    _ = _ := by
      have hsum := hp.tsum_add hm
      simp only [Function.comp_apply] at hsum
      rw [hp.tsum_sum hm, ← hsum]
      apply tsum_congr
      intro n
      change b (t * (((n + 1 : ℕ) : ℤ) : ℝ)) + b (t * (Int.negSucc n : ℝ)) = _
      rw [Int.cast_natCast, Int.cast_negSucc, Nat.cast_add, Nat.cast_one, mul_neg]

private noncomputable def dirichletWeight (z : ℂ) (n : ℕ) : ℂ := 1 / (n + 1 : ℂ) ^ z

private theorem dirichletWeight_as_exp (z : ℂ) (n : ℕ) :
    dirichletWeight z n = Complex.exp (-(z * (Real.log ((n : ℝ) + 1) : ℝ))) := by
  have hk : 0 < (n : ℝ) + 1 := by positivity
  have hk' : (n + 1 : ℂ) ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero n)
  have hkC : (((n : ℝ) + 1 : ℝ) : ℂ) = (n + 1 : ℂ) := by simp
  rw [dirichletWeight, one_div, Complex.cpow_def_of_ne_zero hk', ← Complex.exp_neg,
    ← hkC, ← Complex.ofReal_log hk.le, mul_comm]

private theorem summable_norm_dirichletWeight {z : ℂ} (hz : 1 < z.re) :
    Summable (fun n ↦ ‖dirichletWeight z n‖) := by
  have hp : Summable (fun n : ℕ ↦ (n : ℝ) ^ (-z.re)) := Real.summable_nat_rpow.mpr (by linarith)
  have hs := hp.comp_injective (Nat.succ_injective)
  convert hs using 1
  ext n
  have hk : 0 < (n : ℝ) + 1 := by positivity
  have hkC : (((n : ℝ) + 1 : ℝ) : ℂ) = (n + 1 : ℂ) := by simp
  simp only [Function.comp_apply, Nat.cast_succ]
  rw [dirichletWeight, one_div, norm_inv, ← hkC,
    Complex.norm_cpow_eq_rpow_re_of_pos hk, Real.rpow_neg hk.le]

private noncomputable def mellinSample (b : 𝓢(ℝ, ℂ)) (z : ℂ) (n : ℕ) (x : ℝ) : ℂ :=
  dirichletWeight z n * rationalMellinIntegrand b z (x + Real.log ((n : ℝ) + 1))

private theorem mellinSample_eq (b : 𝓢(ℝ, ℂ)) (z : ℂ) (n : ℕ) (x : ℝ) :
    mellinSample b z n x =
      (b (Real.exp x * ((n : ℝ) + 1)) + b (-(Real.exp x * ((n : ℝ) + 1)))) *
        Complex.exp (z * x) := by
  have hk : 0 < (n : ℝ) + 1 := by positivity
  rw [mellinSample, rationalMellinIntegrand, Real.exp_add, Real.exp_log hk,
    dirichletWeight_as_exp, Complex.ofReal_add, mul_add z]
  set u : ℂ := z * x
  set v : ℂ := z * (Real.log ((n : ℝ) + 1) : ℝ)
  rw [mul_left_comm, ← Complex.exp_add, add_left_comm (-v), neg_add_cancel, add_zero]

/-- Translation of the Mellin integrand and the Dirichlet-series bound justify
absolute integrability and termwise integration on the half-plane `1 < z.re`. -/
public theorem rationalTheta_mellin_hasSum (b : 𝓢(ℝ, ℂ)) {z : ℂ} (hz : 1 < z.re) :
    Integrable (fun x : ℝ ↦ rationalTheta b (Real.exp x) * Complex.exp (z * x)) ∧
    HasSum (fun n : ℕ ↦ (1 / (n + 1 : ℂ) ^ z) * ∫ x, rationalMellinIntegrand b z x)
      (∫ x : ℝ, rationalTheta b (Real.exp x) * Complex.exp (z * x)) := by
  have hloc := integrable_rationalMellinIntegrand b (zero_lt_one.trans hz)
  have hsample (n : ℕ) : Integrable (mellinSample b z n) :=
    ((measurePreserving_add_right volume _).integrable_comp_of_integrable hloc).const_mul _
  have hnorm (n : ℕ) : ∫ x, ‖mellinSample b z n x‖ =
      ‖dirichletWeight z n‖ * ∫ x, ‖rationalMellinIntegrand b z x‖ := by
    simp only [mellinSample, norm_mul, integral_const_mul]
    rw [integral_add_right_eq_self (fun x ↦ ‖rationalMellinIntegrand b z x‖)]
  have hseries : Summable (fun n ↦ ∫ x, ‖mellinSample b z n x‖) := by
    simpa only [hnorm] using (summable_norm_dirichletWeight hz).mul_right
      (∫ x, ‖rationalMellinIntegrand b z x‖)
  have htheta (x : ℝ) : rationalTheta b (Real.exp x) * Complex.exp (z * x) =
      ∑' n, mellinSample b z n x := by
    rw [rationalTheta_eq_tsum_pairs b (Real.exp_pos x).ne', ← tsum_mul_right]
    simp_rw [mellinSample_eq]
  have hfinite : (∑' n, ∫⁻ x, ‖mellinSample b z n x‖ₑ) ≠ ⊤ := by
    have hlin (n : ℕ) : ∫⁻ x, ‖mellinSample b z n x‖ₑ =
        ((‖∫ x, ‖mellinSample b z n x‖‖₊ : ℝ≥0) : ℝ≥0∞) := by
      change ∫⁻ x, (‖mellinSample b z n x‖₊ : ℝ≥0∞) = _
      rw [lintegral_coe_eq_integral _ (hsample n).norm,
        ENNReal.coe_nnreal_eq, coe_nnNorm, Real.norm_of_nonneg (integral_nonneg fun _ ↦ norm_nonneg _)]
      rfl
    simp_rw [hlin]
    exact ENNReal.tsum_coe_ne_top_iff_summable.mpr (NNReal.summable_coe.mp hseries.norm)
  constructor
  · have hcont := (rationalTheta_continuousOn b).comp_continuous Real.continuous_exp Real.exp_pos
    refine ⟨(hcont.mul (Complex.continuous_exp.comp (continuous_const.mul
      Complex.continuous_ofReal))).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_def]
    rw [← lintegral_tsum (fun n ↦ (hsample n).aestronglyMeasurable.eNorm)] at hfinite
    apply lt_of_le_of_lt (lintegral_mono (fun x ↦ ?_)) (Ne.lt_top hfinite)
    rw [htheta]
    exact eNorm_tsum_le_tsum_eNorm
  · simpa only [htheta, mellinSample, integral_const_mul, integral_add_right_eq_self,
      dirichletWeight] using hasSum_integral_of_summable_integral_norm hsample hseries

end Masullo
