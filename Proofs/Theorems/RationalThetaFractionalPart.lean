module

public import Theorems.RationalThetaUnramified
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
import Mathlib.NumberTheory.AbelSummation

/-!
# The fractional-part representation of rational theta

Abel summation supplies the floor term and the product rule supplies the linear term.
Evenness pairs the two lattice rays and identifies the positive half-line integral
with half the Fourier zero mode.
-/

open MeasureTheory Set
open scoped FourierTransform SchwartzMap

namespace Masullo

private theorem rationalTheta_one_div_two_eq_tsum_nat (b : 𝓢(ℝ, ℂ))
    (he : Function.Even (⇑b)) (h0 : b 0 = 0) :
    rationalTheta b 1 / 2 = ∑' n : ℕ, b n := by
  have hs := (summable_norm_schwartz_int_mul b (t := 1) one_ne_zero).of_norm
  have he' : Function.Even (fun n : ℤ ↦ b (1 * (n : ℝ))) := by
    intro n
    change b (1 * ((-n : ℤ) : ℝ)) = b (1 * (n : ℝ))
    rw [Int.cast_neg, mul_neg, he]
  have h := tsum_int_eq_zero_add_two_mul_tsum_pnat he' hs
  rw [tsum_schwartz_int_mul_eq_zero_add b one_ne_zero] at h
  change b 0 + rationalTheta b 1 = b (1 * ((0 : ℤ) : ℝ)) + _ at h
  simp only [Int.cast_zero, mul_zero, h0, zero_add, Int.cast_natCast, one_mul,
    two_nsmul, ← two_mul] at h
  have hn : Summable (fun n : ℕ ↦ b (n : ℝ)) := by
    simpa only [Function.comp_def, Int.cast_natCast, one_mul] using
      hs.comp_injective (show Function.Injective (fun n : ℕ ↦ (n : ℤ)) from Nat.cast_injective)
  rw [h, mul_comm, mul_div_cancel_right₀ _ (by norm_num : (2 : ℂ) ≠ 0)]
  simpa only [Nat.cast_zero, h0, zero_add] using (tsum_zero_pnat_eq_tsum_nat hn)

private theorem integral_Ioi_eq_zero_of_fourier_zero (b : 𝓢(ℝ, ℂ))
    (he : Function.Even (⇑b)) (hf : (𝓕 b) 0 = 0) : ∫ x in Ioi 0, b x = 0 := by
  have hfull : ∫ x, b x = 0 := by
    simpa [SchwartzMap.fourier_coe, Real.fourier_real_eq_integral_exp_smul] using hf
  have hray : (∫ x in Iic (0 : ℝ), b x) = ∫ x in Ioi 0, b x := by
    have h := integral_comp_neg_Iic 0 (⇑b)
    simp_rw [show ∀ x, b (-x) = b x from he, neg_zero] at h
    exact h
  have h := integral_add_compl (s := Ioi (0 : ℝ)) measurableSet_Ioi
    (b.integrable : Integrable (⇑b))
  rw [compl_Ioi, hray, hfull, ← two_mul, mul_eq_zero] at h
  exact h.resolve_left (by norm_num)

private theorem sum_positive_coefficients (m : ℕ) :
    (∑ k ∈ Finset.Icc 0 m, (if k = 0 then 0 else 1 : ℂ)) = m := by
  rw [Finset.Icc_eq_cons_Ioc (Nat.zero_le m), Finset.sum_cons]
  simp only [ite_true, zero_add]
  calc
    _ = ∑ _k ∈ Finset.Ioc 0 m, (1 : ℂ) :=
      Finset.sum_congr rfl fun k hk ↦ ite_eq_right (Finset.mem_Ioc.mp hk).1.ne'
    _ = m := by simp

/-- At unit scale, the fractional part subtracts the floor integral from the linear
integral. The cutoff lies strictly beyond the support, so the tails vanish exactly. -/
private theorem tsum_nat_eq_integral_fract_add (b : 𝓢(ℝ, ℂ))
    (hc : HasCompactSupport (⇑b)) (h0 : b 0 = 0) :
    (∑' n : ℕ, b n) = (∫ x in Ioi 0, Int.fract x • deriv (⇑b) x) + ∫ x in Ioi 0, b x := by
  obtain ⟨M, hM⟩ := hc.isCompact.bddAbove
  obtain ⟨N, hN⟩ := exists_nat_gt M
  have hsupport {x : ℝ} (hx : (N : ℝ) ≤ x) : x ∉ tsupport (⇑b) :=
    fun h ↦ (hN.trans_le hx).not_ge (hM h)
  have hb {x : ℝ} (hx : (N : ℝ) ≤ x) : b x = 0 :=
    image_eq_zero_of_notMem_tsupport (hsupport hx)
  have hd {x : ℝ} (hx : (N : ℝ) ≤ x) : deriv (⇑b) x = 0 :=
    image_eq_zero_of_notMem_tsupport (fun h ↦ hsupport hx (tsupport_deriv_subset h))
  have hdcont : Continuous (deriv (⇑b)) := by
    have hEq : ⇑(SchwartzMap.derivCLM ℂ ℂ b) = deriv (⇑b) :=
      funext (SchwartzMap.derivCLM_apply ℂ b)
    rw [← hEq]
    exact (SchwartzMap.derivCLM ℂ ℂ b).continuous
  let c (k : ℕ) : ℂ := if k = 0 then 0 else 1
  let L (x : ℝ) : ℂ := x • deriv (⇑b) x
  let F (x : ℝ) : ℂ := (Nat.floor x : ℝ) • deriv (⇑b) x
  have hAbelIntegrand (x : ℝ) :
      deriv (⇑b) x * (∑ k ∈ Finset.Icc 0 ⌊x⌋₊, c k) = F x := by
    change _ = (Nat.floor x : ℝ) • deriv (⇑b) x
    rw [show (∑ k ∈ Finset.Icc 0 ⌊x⌋₊, c k) = (⌊x⌋₊ : ℂ) from sum_positive_coefficients _,
      Complex.real_smul, Complex.ofReal_natCast, mul_comm]
  have hAbel := sum_mul_eq_sub_integral_mul' (f := ⇑b) c N
    (fun _ _ ↦ b.differentiableAt) hdcont.integrableOn_Icc
  simp_rw [hAbelIntegrand] at hAbel
  rw [hb le_rfl, zero_mul, zero_sub] at hAbel
  have hsum : (∑' n : ℕ, b n) = ∑ k ∈ Finset.Icc 0 N, b k * c k := by
    calc
      _ = ∑ k ∈ Finset.Icc 0 N, b k := by
        apply tsum_eq_sum
        intro k hk
        apply hb
        exact_mod_cast (le_of_lt (not_le.mp (by simpa using hk : ¬ k ≤ N)))
      _ = _ := by
        apply Finset.sum_congr rfl
        intro k _
        by_cases hk : k = 0 <;> simp [c, hk, h0]
  have hlin : (∫ x in (0 : ℝ)..↑N, L x) = -(∫ x in (0 : ℝ)..↑N, b x) := by
    simpa [L, hb le_rfl] using
      (intervalIntegral.integral_smul_deriv_eq_deriv_smul
        (u := id) (u' := fun _ ↦ (1 : ℝ)) (v := ⇑b) (v' := deriv (⇑b))
        (a := 0) (b := (N : ℝ)) (fun x _ ↦ hasDerivAt_id x) (fun x _ ↦ b.hasDerivAt x)
        (continuous_const.intervalIntegrable _ _) (hdcont.intervalIntegrable _ _))
  rw [intervalIntegral.integral_of_le (Nat.cast_nonneg N),
    intervalIntegral.integral_of_le (Nat.cast_nonneg N)] at hlin
  have htail {x : ℝ} (hx : x ∈ Ioi (0 : ℝ) \ Ioc 0 ↑N) : (N : ℝ) ≤ x :=
    (not_le.mp fun h ↦ hx.2 ⟨hx.1, h⟩).le
  have hrestrict {g : ℝ → ℂ} (hg : ∀ x ∈ Ioi (0 : ℝ) \ Ioc 0 ↑N, g x = 0) :
      (∫ x in Ioi 0, g x) = ∫ x in Ioc 0 ↑N, g x :=
    setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi Ioc_subset_Ioi_self hg
  have hLtail : ∀ x ∈ Ioi (0 : ℝ) \ Ioc 0 ↑N, L x = 0 := fun x hx ↦ by
    simp [L, hd (htail hx)]
  have hFtail : ∀ x ∈ Ioi (0 : ℝ) \ Ioc 0 ↑N, F x = 0 := fun x hx ↦ by
    simp [F, hd (htail hx)]
  have hLi : IntegrableOn L (Ioi 0) := by
    have hcont : Continuous L := continuous_id.smul hdcont
    exact (hcont.integrableOn_Icc.mono_set (Ioc_subset_Icc_self (a := 0) (b := (N : ℝ))))
      |>.of_forall_sdiff_eq_zero measurableSet_Ioi hLtail
  have hFi : IntegrableOn F (Ioi 0) := by
    have hi := integrableOn_mul_sum_Icc (m := 0) (a := (0 : ℝ)) (b := (N : ℝ)) c
      le_rfl hdcont.integrableOn_Icc
    simp_rw [hAbelIntegrand] at hi
    exact (hi.mono_set Ioc_subset_Icc_self).of_forall_sdiff_eq_zero measurableSet_Ioi hFtail
  have hfract : (∫ x in Ioi 0, Int.fract x • deriv (⇑b) x) =
      (∫ x in Ioi 0, L x) - ∫ x in Ioi 0, F x := by
    rw [← integral_sub hLi hFi]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    change (x - (⌊x⌋ : ℝ)) • deriv (⇑b) x = L x - F x
    have hfloor : (⌊x⌋ : ℝ) = (⌊x⌋₊ : ℝ) := by
      exact_mod_cast (Int.natCast_floor_eq_floor (le_of_lt hx)).symm
    simp only [hfloor, sub_smul, L, F]
  rw [hfract, hrestrict hLtail, hrestrict hFtail, hrestrict (fun x hx ↦ hb (htail hx)),
    hlin, hsum, hAbel]
  abel

/-- The two-ray rational theta sum, divided by two, is the fractional-part integral
for a compactly supported even Schwartz function with both zero modes vanishing. -/
public theorem rationalTheta_div_two_eq_integral_fract (b : 𝓢(ℝ, ℂ))
    (hc : HasCompactSupport (⇑b)) (he : Function.Even (⇑b))
    (h0 : b 0 = 0) (hf : (𝓕 b) 0 = 0) {u : ℝ} (hu : 0 < u) :
    rationalTheta b u / 2 = ∫ x in Ioi 0, Complex.ofReal (Int.fract (x / u)) * deriv (⇑b) x := by
  let g := dilateSchwartz b u hu.ne'
  have hg (x : ℝ) : g x = b (u * x) := dilateSchwartz_apply b u hu.ne' x
  have hgc : HasCompactSupport (⇑g) := by
    convert hc.comp_smul hu.ne' using 1
    funext x
    exact hg x
  have hge : Function.Even (⇑g) := by
    intro x
    rw [hg, hg, mul_neg, he]
  have hg0 : g 0 = 0 := by rw [hg, mul_zero, h0]
  have hgf : (𝓕 g) 0 = 0 := by
    simp [g, fourier_dilateSchwartz b hu, hf]
  have htheta : rationalTheta g 1 = rationalTheta b u := by
    simp only [rationalTheta, one_mul, hg]
  have hderiv (x : ℝ) : deriv (⇑g) x = u • deriv (⇑b) (u * x) := by
    rw [show ⇑g = (fun y ↦ b (u * y)) from funext hg]
    have h := (b.hasDerivAt (u * x)).scomp x ((hasDerivAt_id x).const_mul u)
    simpa only [Function.comp_def, id_eq, mul_one] using h.deriv
  rw [← htheta, rationalTheta_one_div_two_eq_tsum_nat g hge hg0,
    tsum_nat_eq_integral_fract_add g hgc hg0, integral_Ioi_eq_zero_of_fourier_zero g hge hgf,
    add_zero]
  let f (x : ℝ) : ℂ := Int.fract (x / u) • deriv (⇑b) x
  have hscale := integral_comp_mul_left_Ioi' f 0 hu
  rw [mul_zero] at hscale
  simp_rw [← Complex.real_smul, hderiv]
  rw [← hscale, ← integral_smul]
  congr 1
  funext x
  simp [f, mul_div_cancel_left₀ _ hu.ne', mul_left_comm]

/-- The weight-one-half normalization of the two-ray theta sum. -/
@[expose] public noncomputable def rationalThetaNormalized (b : 𝓢(ℝ, ℂ)) (u : ℝ) : ℂ :=
  u ^ (1 / 2 : ℝ) • (rationalTheta b u / 2)

/-- The fractional-part kernel in the coordinate `u = exp (-v)`. -/
@[expose] public noncomputable def rationalThetaLogKernel (w : ℝ) : ℝ :=
  Real.exp (-w / 2) * Int.fract (Real.exp w)

/-- The derivative profile in the coordinate `x = exp (-t)`. -/
@[expose] public noncomputable def rationalThetaLogProfile (b : 𝓢(ℝ, ℂ)) (t : ℝ) : ℂ :=
  Real.exp (-3 * t / 2) • deriv (⇑b) (Real.exp (-t))

/-- At `u = exp (-v)`, normalized rational theta is the convolution of the
fractional-part kernel with the log-coordinate derivative profile. -/
public theorem rationalThetaNormalized_exp_neg_eq_integral_logKernel (b : 𝓢(ℝ, ℂ))
    (hc : HasCompactSupport (⇑b)) (he : Function.Even (⇑b))
    (h0 : b 0 = 0) (hf : (𝓕 b) 0 = 0) (v : ℝ) :
    rationalThetaNormalized b (Real.exp (-v)) =
      ∫ t, rationalThetaLogKernel (v - t) • rationalThetaLogProfile b t := by
  let f (x : ℝ) : ℂ := Int.fract (x / Real.exp (-v)) • deriv (⇑b) x
  have hpow : Real.exp (-v) ^ (1 / 2 : ℝ) = Real.exp (-v / 2) := by
    rw [← Real.exp_mul, mul_one_div]
  have hreflect : (∫ t : ℝ, Real.exp (-t) • f (Real.exp (-t))) =
      ∫ t : ℝ, Real.exp t • f (Real.exp t) :=
    (Measure.measurePreserving_neg (volume : Measure ℝ)).integral_comp
      (Homeomorph.neg ℝ).measurableEmbedding (fun t ↦ Real.exp t • f (Real.exp t))
  rw [rationalThetaNormalized,
    rationalTheta_div_two_eq_integral_fract b hc he h0 hf (Real.exp_pos _), hpow]
  simp_rw [← Complex.real_smul]
  change Real.exp (-v / 2) • (∫ x in Ioi 0, f x) = _
  rw [← integral_comp_exp f, ← hreflect, ← integral_smul]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun t ↦ by
    have harg : Real.exp (-t) / Real.exp (-v) = Real.exp (v - t) := by
      rw [← Real.exp_sub]
      congr 1
      ring
    have hweight : Real.exp (-v / 2) * Real.exp (-t) =
        Real.exp (-(v - t) / 2) * Real.exp (-3 * t / 2) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    simp only [f, rationalThetaLogKernel, rationalThetaLogProfile, harg, smul_smul, ← mul_assoc]
    rw [hweight, mul_right_comm (Real.exp (-(v - t) / 2))]

end Masullo
