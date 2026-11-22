module

public import Theorems.RadialHardySobolevCompletion
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Lemmas.LogMellinDerivative
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import Mathlib.MeasureTheory.Function.LpSpace.Complete

/-! # The radial two-edge Mellin seminorms

Use `x = log t`, `dt/t = dx` and the printed vertical coordinate `z = α + iu`.
At Mathlib Fourier frequency `ξ = -u/(2π)`, the edge jet is the Fourier transform
of `x^k exp(αx) f(x)`. The Plancherel measure in the ordinate is `du/(2π)`.
The two-edge comparison concerns the weighted completion, not a completion
for separate interior-line seminorms. No pointwise boundary assertion is made.
-/

open MeasureTheory Set
open scoped FourierTransform SchwartzMap Topology

namespace Masullo

/-- The positive-sign radial Mellin integral, in logarithmic coordinates. -/
@[expose] public noncomputable def logMellin (f : logWeightedProfiles univ) (z : ℂ) : ℂ :=
  ∫ x : ℝ, f.1 x * Complex.exp (z * x)

private noncomputable def logMoment (a : ℝ) (k : ℕ) :
    logWeightedProfiles univ →ₗ[ℂ] 𝓢(ℝ, ℂ) :=
  (SchwartzMap.smulLeftCLM ℂ fun x : ℝ ↦ (x : ℂ) ^ k).toLinearMap.comp
    ((LinearMap.proj ⟨a, mem_univ a⟩).comp (logWeightedProfileMap univ))

private theorem logMoment_apply (f : logWeightedProfiles univ) (a : ℝ) (k : ℕ) (x : ℝ) :
    logMoment a k f x = (x : ℂ) ^ k * (logStageWeight a x * f.1 x) := by
  change SchwartzMap.smulLeftCLM ℂ _ (logWeightedProfileMap univ f ⟨a, mem_univ a⟩) x = _
  rw [SchwartzMap.smulLeftCLM_apply_apply (by fun_prop), logWeightedProfileMap_apply, smul_eq_mul]

private theorem norm_mellinMoment (f : logWeightedProfiles univ) (z : ℂ) (k : ℕ) (x : ℝ) :
    ‖((x : ℂ) ^ k * f.1 x) * Complex.exp (z * x)‖ =
      ‖(x : ℂ) ^ k * f.1 x‖ * Real.exp (z.re * x) := by
  simp [Complex.norm_exp, Complex.mul_re]

private theorem hasDerivAt_mellinMoment (f : logWeightedProfiles univ) (z : ℂ) (k : ℕ) :
    Integrable (fun x : ℝ ↦ (x : ℂ) ^ k * f.1 x * Complex.exp (z * x)) ∧
    HasDerivAt (fun w : ℂ ↦ ∫ x : ℝ, (x : ℂ) ^ k * f.1 x * Complex.exp (w * x))
      (∫ x : ℝ, (x : ℂ) ^ (k + 1) * f.1 x * Complex.exp (z * x)) z := by
  let p := logMoment (z.re + 3) k f
  let q := logMoment (z.re - 3) k f
  let C := max (SchwartzMap.seminorm ℝ 0 0 p) (SchwartzMap.seminorm ℝ 0 0 q)
  have hf := f.property.1.continuous
  have hc : Continuous (fun x : ℝ ↦ (x : ℂ) ^ k * f.1 x) := by fun_prop
  have hnorm (a x : ℝ) : ‖logMoment a k f x‖ =
      ‖(x : ℂ) ^ k * f.1 x‖ * Real.exp (a * x) := by
    rw [logMoment_apply, logStageWeight, mul_left_comm, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), mul_comm]
  have hd (x : ℝ) : ‖((x : ℂ) ^ k * f.1 x) * Complex.exp (z * x)‖ ≤
      C * Real.exp (-(3 * 1) * |x|) := by
    rw [norm_mellinMoment]
    rcases le_total 0 x with hx | hx
    · have h : ‖p x‖ ≤ C := (SchwartzMap.norm_le_seminorm ℝ p x).trans (le_max_left _ _)
      change ‖logMoment (z.re + 3) k f x‖ ≤ C at h
      rw [hnorm] at h
      calc
        _ = (‖(x : ℂ) ^ k * f.1 x‖ * Real.exp ((z.re + 3) * x)) *
            Real.exp (-(3 * 1) * |x|) := by
          rw [mul_assoc, ← Real.exp_add, abs_of_nonneg hx]
          congr 2
          ring
        _ ≤ _ := mul_le_mul_of_nonneg_right h (Real.exp_pos _).le
    · have h : ‖q x‖ ≤ C := (SchwartzMap.norm_le_seminorm ℝ q x).trans (le_max_right _ _)
      change ‖logMoment (z.re - 3) k f x‖ ≤ C at h
      rw [hnorm] at h
      calc
        _ = (‖(x : ℂ) ^ k * f.1 x‖ * Real.exp ((z.re - 3) * x)) *
            Real.exp (-(3 * 1) * |x|) := by
          rw [mul_assoc, ← Real.exp_add, abs_of_nonpos hx]
          congr 2
          ring
        _ ≤ _ := mul_le_mul_of_nonneg_right h (Real.exp_pos _).le
  obtain ⟨hi, _, h⟩ := hasDerivAt_logMellin_of_decay hc z one_pos
    (le_trans (apply_nonneg (SchwartzMap.seminorm ℝ 0 0) p) (le_max_left _ _)) hd
  refine ⟨hi, ?_⟩
  convert h using 1
  apply integral_congr_ae
  exact ae_of_all _ fun x ↦ by dsimp only; rw [pow_succ]; ring

/-- The actual complex derivatives of the radial Mellin integral are absolutely
convergent log moments, at every point, for the all-weight tests. -/
public theorem iteratedDeriv_logMellin (f : logWeightedProfiles univ) (k : ℕ) (z : ℂ) :
    Integrable (fun x : ℝ ↦ (x : ℂ) ^ k * f.1 x * Complex.exp (z * x)) ∧
    iteratedDeriv k (logMellin f) z = ∫ x : ℝ, (x : ℂ) ^ k * f.1 x * Complex.exp (z * x) := by
  refine ⟨(hasDerivAt_mellinMoment f z k).1, ?_⟩
  induction k generalizing z with
  | zero => simp [logMellin]
  | succ k ih =>
    rw [iteratedDeriv_succ, funext ih]
    exact (hasDerivAt_mellinMoment f z k).2.deriv

private theorem fourier_logMoment (f : logWeightedProfiles univ) (a : ℝ) (k : ℕ) (u : ℝ) :
    (𝓕 (logMoment a k f)) (-u / (2 * Real.pi)) =
      iteratedDeriv k (logMellin f) ((a : ℂ) + (u : ℂ) * Complex.I) := by
  rw [(iteratedDeriv_logMellin f k _).2, SchwartzMap.fourier_coe,
    Real.fourier_real_eq_integral_exp_smul]
  apply integral_congr_ae
  refine ae_of_all _ fun x ↦ ?_
  have hphase : (-2 * Real.pi * x * (-u / (2 * Real.pi))) = u * x := by
    field_simp [Real.pi_ne_zero]
  simp only [hphase, smul_eq_mul, logMoment_apply, logStageWeight, Complex.ofReal_mul,
    Complex.ofReal_exp]
  rw [show ((a : ℂ) + (u : ℂ) * Complex.I) * (x : ℂ) =
    (a : ℂ) * (x : ℂ) + (u : ℂ) * (x : ℂ) * Complex.I by ring, Complex.exp_add]
  ring

private theorem norm_logMoment_sq (f : logWeightedProfiles univ) (a : ℝ) (k : ℕ) (x : ℝ) :
    ‖logMoment a k f x‖ ^ 2 = Real.exp (2 * a * x) * (x ^ 2) ^ k * ‖f.1 x‖ ^ 2 := by
  rw [logMoment_apply, norm_mul, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    logStageWeight, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), mul_pow,
    mul_pow, ← pow_mul, Nat.mul_comm k 2, pow_mul, sq_abs, ← Real.exp_nat_mul]
  push_cast
  rw [show (2 : ℝ) * (a * x) = 2 * a * x by ring]
  ring

/-- Parseval for the actual `k`-th derivative on a vertical line. The ordinate
integral shown uses ordinary Lebesgue measure and has the factor `2π`. -/
public theorem logMellin_edge_parseval (f : logWeightedProfiles univ) (a : ℝ) (k : ℕ) :
    Integrable (fun u : ℝ ↦ ‖iteratedDeriv k (logMellin f) ((a : ℂ) + (u : ℂ) * Complex.I)‖ ^ 2) ∧
    (∫ u : ℝ, ‖iteratedDeriv k (logMellin f) ((a : ℂ) + (u : ℂ) * Complex.I)‖ ^ 2) =
      (2 * Real.pi) * ∫ x : ℝ, Real.exp (2 * a * x) * (x ^ 2) ^ k * ‖f.1 x‖ ^ 2 := by
  simp_rw [← fourier_logMoment f a k]
  have hfreq (u : ℝ) : -u / (2 * Real.pi) = (-(2 * Real.pi))⁻¹ * u := by ring
  simp_rw [hfreq]
  let g := 𝓕 (logMoment a k f)
  let φ (ξ : ℝ) := ‖g ξ‖ ^ 2
  change Integrable (fun u : ℝ ↦ φ ((-(2 * Real.pi))⁻¹ * u)) ∧
    (∫ u : ℝ, φ ((-(2 * Real.pi))⁻¹ * u)) = _
  have hφ : Integrable φ := (memLp_two_iff_integrable_sq_norm
    g.continuous.aestronglyMeasurable).1 (g.memLp 2 volume)
  refine ⟨hφ.comp_mul_left' (inv_ne_zero (neg_ne_zero.mpr
    (ne_of_gt (by positivity : 0 < 2 * Real.pi)))), ?_⟩
  rw [Measure.integral_comp_inv_mul_left φ, abs_neg,
    abs_of_pos (by positivity : 0 < 2 * Real.pi), smul_eq_mul]
  unfold φ g
  rw [SchwartzMap.integral_norm_sq_fourier]
  simp_rw [norm_logMoment_sq]

/-- Squared edge seminorm for the actual Mellin derivative using `du/(2π)`. -/
@[expose] public noncomputable def logMellinEdgeEnergy
    (f : logWeightedProfiles univ) (a : ℝ) (k : ℕ) : ℝ :=
  (∫ u : ℝ, ‖iteratedDeriv k (logMellin f) ((a : ℂ) + (u : ℂ) * Complex.I)‖ ^ 2) /
    (2 * Real.pi)

private theorem logMellinEdgeEnergy_eq_moment (f : logWeightedProfiles univ) (a : ℝ) (k : ℕ) :
    logMellinEdgeEnergy f a k = ∫ x : ℝ, ‖logMoment a k f x‖ ^ 2 := by
  rw [logMellinEdgeEnergy, (logMellin_edge_parseval f a k).2, mul_comm,
    mul_div_cancel_right₀ _ (by positivity)]
  simp_rw [norm_logMoment_sq]

private theorem integrable_moment_sq (f : logWeightedProfiles univ) (a : ℝ) (k : ℕ) :
    Integrable (fun x : ℝ ↦ ‖logMoment a k f x‖ ^ 2) :=
  (memLp_two_iff_integrable_sq_norm (logMoment a k f).continuous.aestronglyMeasurable).1
    ((logMoment a k f).memLp 2 volume)

private theorem sum_moment_sq (f : logWeightedProfiles univ) (a : ℝ) (n : ℕ) (x : ℝ) :
    (∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ) * ‖logMoment a k f x‖ ^ 2) =
      Real.exp (2 * a * x) * (1 + x ^ 2) ^ n * ‖f.1 x‖ ^ 2 := by
  simp_rw [norm_logMoment_sq]
  rw [add_comm 1, add_pow (x ^ 2) 1 n, Finset.mul_sum, Finset.sum_mul]
  simp only [one_pow, mul_one]
  exact Finset.sum_congr rfl (fun k _ ↦ by ring)

/-- At degree `s = 2*n`, the binomially weighted **one-edge** sum is exactly
its exponential times polynomial weighted integral. No maximum is involved here. -/
public theorem sum_choose_logMellinEdgeEnergy (f : logWeightedProfiles univ) (a : ℝ) (n : ℕ) :
    (∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ) * logMellinEdgeEnergy f a k) =
      ∫ x : ℝ, Real.exp (2 * a * x) * (1 + x ^ 2) ^ n * ‖f.1 x‖ ^ 2 := by
  simp_rw [logMellinEdgeEnergy_eq_moment, ← integral_const_mul]
  rw [← integral_finsetSum (Finset.range (n + 1))
    (fun k _ ↦ (integrable_moment_sq f a k).const_mul (n.choose k : ℝ))]
  exact integral_congr_ae (ae_of_all _ (sum_moment_sq f a n))

private theorem integrable_edgeWeight (f : logWeightedProfiles univ) (a : ℝ) (n : ℕ) :
    Integrable (fun x : ℝ ↦ Real.exp (2 * a * x) * (1 + x ^ 2) ^ n * ‖f.1 x‖ ^ 2) := by
  simp_rw [← sum_moment_sq]
  exact integrable_finsetSum _ (fun k _ ↦ (integrable_moment_sq f a k).const_mul _)

private theorem integrable_logSobolevAllWeight (a b : ℝ) (hab : a ≤ b) (n : ℕ)
    (f : logWeightedProfiles univ) :
    Integrable (fun x : ℝ ↦ max (Real.exp (2 * a * x)) (Real.exp (2 * b * x)) *
      (1 + x ^ 2) ^ n * ‖f.1 x‖ ^ 2) := by
  have hf : f.1 ∈ logWeightedProfiles (Icc a b) :=
    ⟨f.property.1, fun w ↦ f.property.2 ⟨w, mem_univ _⟩⟩
  simpa only [logSobolevWeight, mul_comm 2 (n : ℝ),
    mul_div_cancel_right₀ _ (by norm_num : (2 : ℝ) ≠ 0), Real.rpow_natCast] using
    integrable_logSobolevWeight_mul_norm_sq (s := 2 * (n : ℝ)) hab hf

private theorem logSobolevAll_sq (a b : ℝ) (hab : a ≤ b) (n : ℕ)
    (f : logWeightedProfiles univ) :
    ‖logSobolevAllToLp hab (2 * (n : ℝ)) f‖ ^ 2 =
      ∫ x : ℝ, max (Real.exp (2 * a * x)) (Real.exp (2 * b * x)) *
        (1 + x ^ 2) ^ n * ‖f.1 x‖ ^ 2 := by
  let fI : logWeightedProfiles (Icc a b) := ⟨f.1, f.property.1,
    fun w ↦ f.property.2 ⟨w, mem_univ _⟩⟩
  have hEq : logSobolevAllToLp hab (2 * (n : ℝ)) f = logSobolevToLp hab (2 * (n : ℝ)) fI :=
    Lp.ext ((logSobolevAllToLp_ae_eq hab _ f).trans (logSobolevToLp_ae_eq hab _ fI).symm)
  rw [hEq, norm_logSobolevToLp, Real.sq_sqrt (integral_nonneg fun x ↦ by
    unfold logSobolevWeight; positivity)]
  simp only [logSobolevWeight, mul_comm 2 (n : ℝ), mul_div_cancel_right₀ _ (by norm_num : (2 : ℝ) ≠ 0),
    Real.rpow_natCast]
  rfl

private theorem edgeWeight_bounds (a b : ℝ) (hab : a ≤ b) (n : ℕ)
    (f : logWeightedProfiles univ) :
    let W := ‖logSobolevAllToLp hab (2 * (n : ℝ)) f‖ ^ 2
    let B := ∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ) *
      (logMellinEdgeEnergy f a k + logMellinEdgeEnergy f b k)
    W ≤ B ∧ B ≤ 2 * W := by
  dsimp only
  rw [logSobolevAll_sq]
  simp_rw [mul_add, Finset.sum_add_distrib, sum_choose_logMellinEdgeEnergy]
  let F (c x : ℝ) := Real.exp (2 * c * x) * (1 + x ^ 2) ^ n * ‖f.1 x‖ ^ 2
  let M (x : ℝ) := max (Real.exp (2 * a * x)) (Real.exp (2 * b * x)) *
    (1 + x ^ 2) ^ n * ‖f.1 x‖ ^ 2
  change (∫ x, M x) ≤ (∫ x, F a x) + (∫ x, F b x) ∧
    (∫ x, F a x) + (∫ x, F b x) ≤ 2 * ∫ x, M x
  have hF (c : ℝ) : Integrable (F c) := integrable_edgeWeight f c n
  have hM : Integrable M := integrable_logSobolevAllWeight a b hab n f
  rw [← integral_add (hF a) (hF b), ← integral_const_mul]
  constructor
  · apply integral_mono hM ((hF a).add (hF b))
    intro x
    change M x ≤ F a x + F b x
    simp only [M, F, ← add_mul]
    gcongr
    exact max_le_add_of_nonneg (Real.exp_pos _).le (Real.exp_pos _).le
  · apply integral_mono ((hF a).add (hF b)) (hM.const_mul 2)
    intro x
    have ha : F a x ≤ M x := by dsimp [F, M]; gcongr; exact le_max_left ..
    have hb : F b x ≤ M x := by dsimp [F, M]; gcongr; exact le_max_right ..
    change F a x + F b x ≤ 2 * M x
    linarith

private theorem edgeEnergy_nonneg (f : logWeightedProfiles univ) (a : ℝ) (k : ℕ) :
    0 ≤ logMellinEdgeEnergy f a k := by
  rw [logMellinEdgeEnergy_eq_moment]
  exact integral_nonneg (fun _ ↦ sq_nonneg _)

/-- The finite **unweighted** edge family `0 ≤ k ≤ n` yields an equivalent
norm at degree `2*n`; the comparison is for the sum of squared seminorms. -/
public theorem logMellin_edgeEnergy_equivalent {a b : ℝ} (hab : a ≤ b) (n : ℕ)
    (f : logWeightedProfiles univ) :
    let W := ‖logSobolevAllToLp hab (2 * (n : ℝ)) f‖ ^ 2
    let S := ∑ k ∈ Finset.range (n + 1),
      (logMellinEdgeEnergy f a k + logMellinEdgeEnergy f b k)
    W ≤ 2 ^ n * S ∧ S ≤ 2 * W := by
  dsimp only
  have h := edgeWeight_bounds a b hab n f
  dsimp only at h
  let T k := logMellinEdgeEnergy f a k + logMellinEdgeEnergy f b k
  have hT (k : ℕ) : 0 ≤ T k := add_nonneg (edgeEnergy_nonneg ..) (edgeEnergy_nonneg ..)
  change _ ≤ 2 ^ n * (∑ k ∈ Finset.range (n + 1), T k) ∧
    (∑ k ∈ Finset.range (n + 1), T k) ≤ _
  rw [Finset.mul_sum]
  refine ⟨h.1.trans (Finset.sum_le_sum fun k hk ↦ ?_),
    le_trans (Finset.sum_le_sum fun k hk ↦ ?_) h.2⟩
  · apply mul_le_mul_of_nonneg_right _ (hT k)
    exact_mod_cast (Nat.sum_range_choose n ▸ Finset.single_le_sum
      (f := fun j ↦ n.choose j) (fun j _ ↦ Nat.zero_le (n.choose j)) hk : n.choose k ≤ 2 ^ n)
  · have hc : 1 ≤ n.choose k := Nat.choose_pos (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))
    have hc' : (1 : ℝ) ≤ n.choose k := by exact_mod_cast hc
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hc' (hT k)

private noncomputable def mellinEdgeToLp (c : ℝ) (k : ℕ) :
    logWeightedProfiles univ →ₗ[ℂ] Lp ℂ 2 (volume : Measure ℝ) :=
  (SchwartzMap.toLpCLM ℂ ℂ 2 volume).toLinearMap.comp
    ((SchwartzMap.fourierTransformCLM ℂ).toLinearMap.comp (logMoment c k))

private theorem norm_mellinEdgeToLp_sq (c : ℝ) (k : ℕ) (f : logWeightedProfiles univ) :
    ‖mellinEdgeToLp c k f‖ ^ 2 = ∫ x : ℝ, ‖logMoment c k f x‖ ^ 2 := by
  let g := 𝓕 (logMoment c k f)
  change ‖g.toLp 2 volume‖ ^ 2 = _
  change ‖(g.memLp 2 volume).toLp g‖ ^ 2 = _
  rw [Lp.norm_toLp, toReal_eLpNorm,
    lpNorm_eq_integral_norm_rpow_toReal (by norm_num) (by simp) g.continuous.aestronglyMeasurable]
  norm_num only [ENNReal.toReal_ofNat, Real.rpow_two, ← Real.sqrt_eq_rpow, Real.sq_sqrt
    (integral_nonneg fun _ ↦ sq_nonneg _)]
  exact SchwartzMap.integral_norm_sq_fourier (logMoment c k f)

private theorem norm_mellinEdgeToLp_le {a b c : ℝ} (hab : a ≤ b) (hc : c = a ∨ c = b)
    {n k : ℕ} (hk : k ≤ n) (f : logWeightedProfiles univ) :
    ‖mellinEdgeToLp c k f‖ ≤ ‖logSobolevAllToLp hab (2 * (n : ℝ)) f‖ := by
  apply le_of_pow_le_pow_left₀ (by decide : 2 ≠ 0) (norm_nonneg _)
  rw [norm_mellinEdgeToLp_sq, logSobolevAll_sq]
  refine integral_mono (integrable_moment_sq f c k) (integrable_logSobolevAllWeight a b hab n f)
    (fun x ↦ ?_)
  rw [norm_logMoment_sq]
  have hx : (x ^ 2) ^ k ≤ (1 + x ^ 2) ^ n :=
    (pow_le_pow_left₀ (sq_nonneg x) (le_add_of_nonneg_left zero_le_one) k).trans
      (pow_le_pow_right₀ (le_add_of_nonneg_right (sq_nonneg x)) hk)
  have he : Real.exp (2 * c * x) ≤ max (Real.exp (2 * a * x)) (Real.exp (2 * b * x)) := by
    rcases hc with rfl | rfl
    · exact le_max_left ..
    · exact le_max_right ..
  gcongr

/-- The weighted completion defined by the accepted all-weight image closure. -/
@[expose] public noncomputable def logMellinCompletion {a b : ℝ} (hab : a ≤ b) (n : ℕ) :
    Submodule ℂ (Lp ℂ 2 (logSobolevMeasure a b (2 * (n : ℝ)))) :=
  (logSobolevAllToLp hab (2 * (n : ℝ))).range.topologicalClosure

private noncomputable def mellinCompletionInclusion {a b : ℝ} (hab : a ≤ b) (n : ℕ) :
    logWeightedProfiles univ →ₗ[ℂ] logMellinCompletion hab n :=
  (logSobolevAllToLp hab (2 * (n : ℝ))).codRestrict _
    (fun f ↦ subset_closure ⟨f, rfl⟩)

private theorem denseRange_mellinCompletionInclusion {a b : ℝ} (hab : a ≤ b) (n : ℕ) :
    DenseRange (mellinCompletionInclusion hab n) := by
  intro Y
  rw [closure_subtype]
  have heq : ((↑) : logMellinCompletion hab n → Lp ℂ 2 (logSobolevMeasure a b (2 * (n : ℝ)))) ''
      range (mellinCompletionInclusion hab n) = range (logSobolevAllToLp hab (2 * (n : ℝ))) := by
    rw [← range_comp]
    rfl
  rw [heq]
  exact Y.property

/-- Each order `k ≤ n` on either endpoint has a contractive complex-linear
`L²` trace on the weighted completion. On test profiles it represents the
actual Mellin derivative at ordinate `u = -2πξ` (so `dξ` is `du/(2π)`).
The representative identity is an a.e. identity on tests, not a boundary
point-evaluation or a claim about limits of interior-line representatives. -/
public theorem exists_logMellin_edgeTrace {a b c : ℝ} (hab : a ≤ b) (hc : c = a ∨ c = b)
    (n k : ℕ) (hk : k ≤ n) :
    ∃ T : logMellinCompletion hab n →L[ℂ] Lp ℂ 2 (volume : Measure ℝ),
      (∀ Y, ‖T Y‖ ≤ ‖Y‖) ∧
      ∀ (f : logWeightedProfiles univ) (Y : logMellinCompletion hab n),
        Y.1 = logSobolevAllToLp hab (2 * (n : ℝ)) f →
        (T Y : ℝ → ℂ) =ᵐ[volume] fun ξ ↦ iteratedDeriv k (logMellin f)
          ((c : ℂ) + ((-(2 * Real.pi) * ξ : ℝ) : ℂ) * Complex.I) := by
  let e := mellinCompletionInclusion hab n
  let A := mellinEdgeToLp c k
  have hNorm (f : logWeightedProfiles univ) : ‖A f‖ ≤ 1 * ‖e f‖ := by
    rw [one_mul]
    exact norm_mellinEdgeToLp_le hab hc hk f
  have hDense : DenseRange e := denseRange_mellinCompletionInclusion hab n
  refine ⟨A.extendOfNorm e, fun Y ↦ by simpa only [one_mul] using
    LinearMap.norm_extendOfNorm_apply_le hDense 1 hNorm Y, fun f Y hY ↦ ?_⟩
  have hEq : Y = e f := Subtype.ext hY
  rw [hEq, LinearMap.extendOfNorm_eq hDense ⟨1, hNorm⟩]
  change (((𝓕 (logMoment c k f)).toLp 2 volume : Lp ℂ 2 _) : ℝ → ℂ) =ᵐ[volume] _
  apply ((𝓕 (logMoment c k f)).coeFn_toLp 2 volume).trans
  refine ae_of_all _ fun ξ ↦ ?_
  have hξ : - (-(2 * Real.pi) * ξ) / (2 * Real.pi) = ξ := by
    field_simp [Real.pi_ne_zero]
  simpa only [hξ] using fourier_logMoment f c k (-(2 * Real.pi) * ξ)

end Masullo
