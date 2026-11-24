module

public import Lemmas.NonnegativeMellinAbscissa
public import Lemmas.PrimePowerRampMellin
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # Mellin transform of the compensated von Mangoldt ramp

Source: Bob, `5f22f5a60aef:.godel/bob/unsigned-edge-rh.md:24–30`, with the ramp
as defined there at line 15. This is the exact convergent tail identity on `1 < s.re`,
not a sign assertion, an analytic continuation, or the subsequent Landau argument.
Owning check session: `01a20fa3-d781-7816-bdbd-149ebe36b7b4`.
-/

open Complex Filter MeasureTheory Set
open scoped Topology

namespace PrimeSquareRamp

-- The quadratic Laplace moment, including absolute convergence for a complex rate.
private theorem quadratic_laplace {a : ℂ} (ha : 0 < a.re) :
    IntegrableOn (fun t : ℝ ↦ (t : ℂ) ^ 2 * Complex.exp (-a * t)) (Ioi 0) ∧
      (∫ t : ℝ in Ioi 0, (t : ℂ) ^ 2 * Complex.exp (-a * t)) = 2 / a ^ 3 := by
  let e (t : ℝ) := Complex.exp (-a * (t : ℂ))
  have hnorm (n : ℕ) {t : ℝ} (ht : 0 ≤ t) :
      ‖(t : ℂ) ^ n * e t‖ = t ^ n * Real.exp (-a.re * t) := by
    simp [e, norm_pow, abs_of_nonneg ht, Complex.norm_exp, Complex.mul_re]
  have hi : IntegrableOn (fun t : ℝ ↦ (t : ℂ) ^ 2 * e t) (Ioi 0) := by
    have h : IntegrableOn (fun t : ℝ ↦ t ^ (2 : ℕ) * Real.exp (-a.re * t)) (Ioi 0) := by
      simpa only [Real.rpow_two, Real.rpow_one] using
        (integrableOn_rpow_mul_exp_neg_mul_rpow (s := 2) (p := 1)
          (by norm_num) zero_lt_one ha)
    have hc : Continuous (fun t : ℝ ↦ (t : ℂ) ^ 2 * e t) := by unfold e; fun_prop
    exact (integrable_norm_iff hc.aestronglyMeasurable).mp
      (h.congr_fun (fun _ ht ↦ (hnorm 2 (mem_Ioi.mp ht).le).symm) measurableSet_Ioi)
  have hl (n : ℕ) : Tendsto (fun t : ℝ ↦ (t : ℂ) ^ n * e t) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    have h := ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero n).comp
      (tendsto_id.const_mul_atTop ha)).div_const (a.re ^ n)
    simp only [zero_div] at h
    refine h.congr' ?_
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    rw [hnorm n ht]
    simp only [Function.comp_apply, id_eq, mul_pow, neg_mul]
    field_simp [ha.ne']
  let p (t : ℝ) : ℂ := (t : ℂ) ^ 2 / a + 2 * t / a ^ 2 + 2 / a ^ 3
  let F (t : ℝ) := -(e t * p t)
  have ha₀ : a ≠ 0 := by rintro rfl; simp at ha
  have hF (t : ℝ) : HasDerivAt F ((t : ℂ) ^ 2 * e t) t := by
    have ht := (hasDerivAt_id (t : ℂ)).comp_ofReal
    have he : HasDerivAt e (e t * -a) t := by
      simpa only [e, id_eq, mul_one, Function.comp_def] using!
        (Complex.hasDerivAt_exp _).comp t (ht.const_mul (-a))
    have hp : HasDerivAt p (2 * (t : ℂ) / a + 2 / a ^ 2) t := by
      simpa [p, id] using
        (((ht.pow 2).div_const a).add ((ht.const_mul (2 : ℂ)).div_const (a ^ 2))).add_const
          (2 / a ^ 3)
    convert ((he.mul hp).neg) using 1
    dsimp only [p]
    field_simp [ha₀]
    ring
  have hFtop : Tendsto F atTop (𝓝 0) := by
    have h2 := (hl 2).div_const a
    have h1 := ((hl 1).const_mul (2 : ℂ)).div_const (a ^ 2)
    have h0 := ((hl 0).const_mul (2 : ℂ)).div_const (a ^ 3)
    have h := ((h2.add h1).add h0).neg
    simp only [zero_div, mul_zero, zero_add, neg_zero] at h
    refine h.congr (fun t ↦ ?_)
    simp only [F, p, pow_one, pow_zero, one_mul]
    ring
  refine ⟨hi, ?_⟩
  change (∫ t : ℝ in Ioi 0, (t : ℂ) ^ 2 * e t) = _
  rw [integral_Ioi_of_hasDerivAt_of_tendsto (hF 0).continuousAt.continuousWithinAt
    (fun t _ ↦ hF t) hi hFtop]
  simp [F, e, p]

private theorem majorant_mellin {s : ℂ} (hs : 1 / 2 < s.re) :
    IntegrableOn (fun x : ℝ ↦ ((Real.sqrt x * Real.log x ^ 2 : ℝ) : ℂ) *
      (x : ℂ) ^ (-(s + 1))) (Ioi 1) ∧
    (∫ x : ℝ in Ioi 1, ((Real.sqrt x * Real.log x ^ 2 : ℝ) : ℂ) *
      (x : ℂ) ^ (-(s + 1))) = 2 / (s - 1 / 2) ^ 3 := by
  let f (x : ℝ) : ℂ := ((Real.sqrt x * Real.log x ^ 2 : ℝ) : ℂ) * (x : ℂ) ^ (-(s + 1))
  have hsub (t : ℝ) : Real.exp t • f (Real.exp t) =
      (t : ℂ) ^ 2 * Complex.exp (-(s - 1 / 2) * t) := by
    have ht := Real.exp_pos t
    have hlog : Complex.log (Real.exp t : ℂ) = (t : ℂ) := by
      rw [← Complex.ofReal_log ht.le, Real.log_exp]
    have hpow : (Real.exp t : ℂ) ^ (-(s + 1)) = Complex.exp ((t : ℂ) * (-(s + 1))) := by
      rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr ht.ne'), hlog]
    dsimp only [f]
    rw [Complex.real_smul, Complex.ofReal_mul, Complex.ofReal_pow, Real.log_exp,
      Real.sqrt_eq_rpow, ← Real.exp_mul, hpow, Complex.ofReal_exp, Complex.ofReal_exp]
    push_cast
    calc
      _ = (t : ℂ) ^ 2 *
          (Complex.exp (t : ℂ) * Complex.exp ((t : ℂ) * (1 / 2)) *
            Complex.exp ((t : ℂ) * (-(s + 1)))) := by ring
      _ = _ := by
        rw [← Complex.exp_add, ← Complex.exp_add]
        congr 2
        ring
  have ha : 0 < (s - 1 / 2).re := by simpa using sub_pos.mpr hs
  obtain ⟨hi, hI⟩ := quadratic_laplace ha
  have hfi := integrableOn_comp_exp_Ioi f 0
  have hfI := integral_comp_exp_Ioi f 0
  simp only [Real.exp_zero, hsub] at hfi hfI
  exact ⟨hfi.mp hi, hfI.symm.trans hI⟩

/-- The compensated von Mangoldt ramp has an absolutely convergent Mellin tail on `Re s > 1`.
Subtracting the initial interval from the full transform gives the stated tail formula.
The convergence identity itself does not use nonnegativity of `K` or of the tail. -/
public theorem compensated_vonMangoldt_logRamp_mellin {K A : ℝ} (_hK : 0 ≤ K) (hA : 2 ≤ A)
    {s : ℂ} (hs : 1 < s.re) :
    let B (x : ℝ) :=
      ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ArithmeticFunction.vonMangoldt n * Real.log (x / n)
    let g (x : ℝ) := K * Real.sqrt x * Real.log x ^ 2 - (B x - x)
    IntegrableOn (fun x : ℝ ↦ (g x : ℂ) * (x : ℂ) ^ (-(s + 1))) (Ioi A) ∧
      Masullo.nonnegativeMellinTail g A s =
        2 * (K : ℂ) / (s - 1 / 2) ^ 3 + logDeriv riemannZeta s / s ^ 2 + 1 / (s - 1) -
          ∫ x in (1 : ℝ)..A, (g x : ℂ) * (x : ℂ) ^ (-(s + 1)) := by
  intro B g
  let M (x : ℝ) : ℂ := ((Real.sqrt x * Real.log x ^ 2 : ℝ) : ℂ) * (x : ℂ) ^ (-(s + 1))
  let R (x : ℝ) : ℂ := ((B x : ℂ) - (x : ℂ)) * (x : ℂ) ^ (-(s + 1))
  let f (x : ℝ) : ℂ := (g x : ℂ) * (x : ℂ) ^ (-(s + 1))
  obtain ⟨hMi, hM⟩ := majorant_mellin (show 1 / 2 < s.re by linarith)
  obtain ⟨hRi, hR⟩ := vonMangoldt_logRamp_mellin hs
  change IntegrableOn R (Ici 1) at hRi
  change (∫ x in Ici 1, R x) = _ at hR
  rw [integrableOn_Ici_iff_integrableOn_Ioi] at hRi
  rw [integral_Ici_eq_integral_Ioi] at hR
  have hsplit (x : ℝ) : f x = (K : ℂ) * M x - R x := by
    simp only [f, g, M, R, Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_pow]
    ring
  have hKi : IntegrableOn (fun x ↦ (K : ℂ) * M x) (Ioi 1) := hMi.const_mul _
  have hfi : IntegrableOn f (Ioi 1) :=
    (hKi.sub hRi).congr_fun (fun x _ ↦ (hsplit x).symm) measurableSet_Ioi
  have hI : (∫ x in Ioi 1, f x) =
      2 * (K : ℂ) / (s - 1 / 2) ^ 3 + logDeriv riemannZeta s / s ^ 2 + 1 / (s - 1) := by
    change (∫ x in Ioi 1, M x) = _ at hM
    simp_rw [hsplit]
    rw [integral_sub hKi hRi, integral_const_mul, hM, hR]
    ring
  have hA' : 1 ≤ A := le_trans (by norm_num) hA
  have htail := hfi.mono_set (Ioi_subset_Ioi hA')
  have hinit : IntegrableOn f (Ioc 1 A) := hfi.mono_set (fun _ hx ↦ hx.1)
  have hdis : Disjoint (Ioc (1 : ℝ) A) (Ioi A) :=
    Set.disjoint_left.mpr fun _ hx hy ↦ (mem_Ioi.mp hy).not_ge hx.2
  refine ⟨htail, ?_⟩
  change (∫ x in Ioi A, f x) = _ - (∫ x in (1 : ℝ)..A, f x)
  rw [intervalIntegral.integral_of_le hA', ← hI, ← Ioc_union_Ioi_eq_Ioi hA',
    setIntegral_union hdis measurableSet_Ioi hinit htail]
  ring

end PrimeSquareRamp
