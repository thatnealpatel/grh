module

public import Lemmas.EndpointConvolutionPairing
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic.Ring

/-!
# Desmoothing the fixed shifted endpoint convolution pairing

Sources: `daee96a91397:.godel/bob/endpoint-convolution-lift.md:36–48` and
`874eb9a:.godel/bob/long-cutoff-moments.md:14–35`.
Owning check session: `01a21012-2ca1-71e9-a51f-6efd061fa400`.

The order and shift are fixed. After the smoothed endpoint pairing has been identified,
its signed multiplier is bounded by `exp 1` and tends pointwise to one as `ε → 0+`.
We assume only the stated tilted integrability and transform of the real signed kernels,
not positivity or an unsmoothed spectral convergence hypothesis. This does not unsmooth a
finite prime sum, interchange limits, or assert uniformity in the order or shift.
-/

open Complex Filter MeasureTheory
open scoped Topology

namespace Masullo

noncomputable section

private def desmoothingMultiplier (ε x : ℝ) : ℂ :=
  exp (1 - cos ((ε : ℂ) * endpointPairingParameter x))

private theorem continuous_desmoothingMultiplier (x : ℝ) :
    Continuous (fun ε ↦ desmoothingMultiplier ε x) :=
  Complex.continuous_exp.comp (continuous_const.sub
    (Complex.continuous_cos.comp (Complex.continuous_ofReal.mul continuous_const)))

private theorem norm_desmoothingMultiplier_le {ε : ℝ} (hε : ε ∈ Set.Ioo (0 : ℝ) 1)
    (x : ℝ) : ‖desmoothingMultiplier ε x‖ ≤ Real.exp 1 := by
  have hcos : 0 ≤ Real.cos (ε / 2) := by
    obtain ⟨hpos, hlt⟩ := hε
    apply Real.cos_nonneg_of_mem_Icc
    constructor <;> linarith [Real.two_le_pi]
  have hcos_re (a b : ℝ) : (cos ((a : ℂ) + (b : ℂ) * I)).re =
      Real.cos a * Real.cosh b := by
    rw [cos_add_mul_I, ← ofReal_cos, ← ofReal_cosh, ← ofReal_sin, ← ofReal_sinh,
      ← ofReal_mul, ← ofReal_mul, sub_re, ofReal_re, mul_I_re, ofReal_im, neg_zero, sub_zero]
  have hw : (ε : ℂ) * endpointPairingParameter x =
      ((ε / 2 : ℝ) : ℂ) + ((ε * x : ℝ) : ℂ) * I := by
    unfold endpointPairingParameter
    push_cast
    ring
  rw [desmoothingMultiplier, norm_exp, Real.exp_le_exp, sub_re, one_re, hw, hcos_re]
  exact sub_le_self _ (mul_nonneg hcos (Real.cosh_pos _).le)

private theorem tendsto_desmoothingMultiplier (x : ℝ) :
    Tendsto (fun ε ↦ desmoothingMultiplier ε x) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
  have hzero : desmoothingMultiplier 0 x = 1 := by simp [desmoothingMultiplier]
  rw [← hzero]
  exact ((continuous_desmoothingMultiplier x).tendsto 0).mono_left nhdsWithin_le_nhds

-- The unsmoothed integrand is bounded, and the spectral measure is finite.
private theorem endpointPairingMeasure_finite : IsFiniteMeasure endpointPairingMeasure := by
  let d (x : ℝ) := 1 / (2 * Real.pi * ‖endpointPairingParameter x‖ ^ 2)
  have hd (x : ℝ) : 0 ≤ d x := by dsimp [d]; positivity
  have hdInt : Integrable d := by
    have hi := (integrable_comp_mul_right_iff _ (show (2 : ℝ) ≠ 0 by norm_num)).2
      integrable_inv_one_add_sq
    refine (hi.const_mul (Real.pi / 2)⁻¹).congr (ae_of_all _ fun x ↦ ?_)
    have hw : ‖endpointPairingParameter x‖ ^ 2 = 1 / 4 + x ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      simp [endpointPairingParameter, Complex.mul_re, Complex.mul_im]
      ring
    change (Real.pi / 2)⁻¹ * (1 + (x * 2) ^ 2)⁻¹ = d x
    dsimp only [d]
    rw [hw, show 2 * Real.pi * (1 / 4 + x ^ 2) = (Real.pi / 2) * (1 + (x * 2) ^ 2) by ring]
    simp only [one_div, mul_inv]
  refine ⟨?_⟩
  change (volume.withDensity fun x ↦ ENNReal.ofReal (d x)) Set.univ < ⊤
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  simpa only [Real.norm_of_nonneg (hd _)] using (hasFiniteIntegral_iff_norm d).mp hdInt.2

private theorem integrable_desmoothingHalfTilt {Y : ℝ → ℝ} (hY : Measurable Y)
    {a M : ℝ} (hzero : ∀ z < a, Y z = 0) (hbound : ∀ z, ‖Y z‖ ≤ M) :
    Integrable (fun z ↦ Real.exp (-z / 2) * Y z) := by
  have he : IntegrableOn (fun z : ℝ ↦ Real.exp (-z / 2)) (Set.Ici a) := by
    rw [integrableOn_Ici_iff_integrableOn_Ioi]
    convert integrableOn_exp_mul_Ioi (a := -(1 / 2)) (by norm_num) a using 1
    ext z
    congr 1
    ring
  have hm := (Real.continuous_exp.comp (continuous_neg.div_const (2 : ℝ))).measurable.mul hY
  refine ((he.integrable_indicator measurableSet_Ici).mul_const M).mono'
    hm.aestronglyMeasurable (ae_of_all _ fun z ↦ ?_)
  by_cases hz : a ≤ z
  · rw [Set.indicator_of_mem (show z ∈ Set.Ici a from hz), norm_mul,
      Real.norm_of_nonneg (Real.exp_pos _).le]
    exact mul_le_mul_of_nonneg_left (hbound z) (Real.exp_pos _).le
  · simp [Set.indicator_of_notMem (show z ∉ Set.Ici a from hz), hzero z (lt_of_not_ge hz)]

private theorem norm_endpointAngularFourier_integrand (x z : ℝ) (f : ℝ → ℝ) :
    ‖exp (-(x : ℂ) * I * (z : ℂ)) * (f z : ℂ)‖ = ‖f z‖ := by
  rw [show -(x : ℂ) * I * (z : ℂ) = (-(x : ℂ) * (z : ℂ)) * I by ring,
    norm_mul, norm_exp_mul_I]
  simp [Complex.mul_im]

private theorem continuous_endpointAngularFourier {f : ℝ → ℝ} (hf : Integrable f) :
    Continuous (endpointAngularFourier f) := by
  unfold endpointAngularFourier
  refine continuous_of_dominated (bound := fun z ↦ ‖f z‖) (fun x ↦ ?_)
    (fun x ↦ ae_of_all _ fun z ↦ (norm_endpointAngularFourier_integrand x z f).le)
    hf.norm (ae_of_all _ fun z ↦ ?_)
  · exact ((Complex.continuous_exp.comp
        ((continuous_const.mul Complex.continuous_ofReal) :
          Continuous (fun z : ℝ ↦ (-(x : ℂ) * I) * (z : ℂ)))).aestronglyMeasurable).mul hf.ofReal.1
  · exact (Complex.continuous_exp.comp
        ((Complex.continuous_ofReal.neg.mul continuous_const).mul continuous_const)).mul_const _

/-- Desmooth the pinned convolution pairing at each fixed positive order and real shift.
The right-hand limit is absolutely integrable with the same spectral density and has the
same minus sign at every order. The kernel premises are only on `0 < ε < 1`. -/
public theorem endpoint_convolution_desmoothing {Y : ℝ → ℝ} {k : ℝ → ℝ → ℝ}
    (hY : Measurable Y) {a M : ℝ} (hzero : ∀ z < a, Y z = 0) (hbound : ∀ z, ‖Y z‖ ≤ M)
    (hk : ∀ ε ∈ Set.Ioo (0 : ℝ) 1, Integrable (fun v ↦ k ε v * Real.exp (v / 2)))
    (htransform : ∀ ε ∈ Set.Ioo (0 : ℝ) 1, ∀ x : ℝ,
      (∫ v : ℝ, (k ε v : ℂ) * exp (endpointPairingParameter x * (v : ℂ))) =
        exp (1 - cos ((ε : ℂ) * endpointPairingParameter x)))
    {j : ℕ} (hj : 1 ≤ j) (s : ℝ) {C₁ : ℝ} (hC₁ : 0 < C₁) (Cj α : ℝ) :
    let Jhat := endpointAngularFourier (fun z ↦ Real.exp (-z / 2) * Y z);
    let m := (fun x ↦
      let w := endpointPairingParameter x;
      -((starRingEnd ℂ) w / w) * (starRingEnd ℂ) (Jhat x) / (C₁ : ℂ));
    let F := (fun z ↦ ((-1 : ℝ) ^ (j + 1) * Cj * α / C₁ ^ j) * endpointConvolutionPower Y j z);
    let P := (fun x : ℝ ↦ exp ((s : ℂ) * (x : ℂ) * I) * ((α : ℂ) * m x ^ j));
    Integrable P endpointPairingMeasure ∧
      Tendsto (fun ε : ℝ ↦ Real.exp (-s / 2) * (∫ z : ℝ, Real.exp (-z) * F z *
        (∫ v : ℝ, k ε v * longCutoffProfile j (z + s + v))))
        (𝓝[>] (0 : ℝ)) (𝓝 (-Cj * (∫ x, P x ∂endpointPairingMeasure).re)) := by
  intro Jhat m F P
  let J (z : ℝ) := Real.exp (-z / 2) * Y z
  have hJ : Integrable J := integrable_desmoothingHalfTilt hY hzero hbound
  have hJhat : Continuous Jhat := continuous_endpointAngularFourier hJ
  have hJhatBound (x : ℝ) : ‖Jhat x‖ ≤ ∫ z : ℝ, ‖J z‖ :=
    norm_integral_le_of_norm_le hJ.norm
      (ae_of_all _ fun z ↦ (norm_endpointAngularFourier_integrand x z J).le)
  have hw : Continuous endpointPairingParameter := by
    unfold endpointPairingParameter
    exact continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
  have hw_ne (x : ℝ) : endpointPairingParameter x ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num [endpointPairingParameter, Complex.mul_re] at hre
  have hm : Continuous m :=
    (((Complex.continuous_conj.comp hw).div hw hw_ne).neg.mul
      (Complex.continuous_conj.comp hJhat)).div_const _
  have hphase : Continuous (fun x : ℝ ↦ exp ((s : ℂ) * (x : ℂ) * I)) :=
    Complex.continuous_exp.comp ((continuous_const.mul Complex.continuous_ofReal).mul continuous_const)
  have hP : Continuous P := hphase.mul (continuous_const.mul (hm.pow j))
  have hPBound (x : ℝ) : ‖P x‖ ≤ ‖α‖ * ((∫ z : ℝ, ‖J z‖) / ‖C₁‖) ^ j := by
    have hw_norm : ‖(starRingEnd ℂ) (endpointPairingParameter x) / endpointPairingParameter x‖ = 1 := by
      rw [norm_div, norm_conj, div_self (norm_ne_zero_iff.mpr (hw_ne x))]
    have hm_norm : ‖m x‖ = ‖Jhat x‖ / ‖C₁‖ := by
      dsimp only [m]
      rw [norm_div, norm_mul, norm_neg, hw_norm, norm_conj, one_mul, norm_real]
    dsimp only [P]
    rw [norm_mul, norm_exp_mul_I, Complex.mul_im, Complex.ofReal_im, Complex.ofReal_im,
      mul_zero, zero_mul, add_zero, neg_zero, Real.exp_zero, one_mul, norm_mul, norm_real,
      norm_pow, hm_norm]
    gcongr
    exact hJhatBound x
  let _ : IsFiniteMeasure endpointPairingMeasure := endpointPairingMeasure_finite
  have hPInt : Integrable P endpointPairingMeasure :=
    Integrable.of_bound hP.aestronglyMeasurable _ (ae_of_all _ hPBound)
  have hε : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), ε ∈ Set.Ioo (0 : ℝ) 1 :=
    Ioo_mem_nhdsGT (by norm_num)
  let Q (ε x : ℝ) :=
    exp ((s : ℂ) * (x : ℂ) * I) * desmoothingMultiplier ε x * ((α : ℂ) * m x ^ j)
  have hQFactor (ε x : ℝ) : Q ε x = desmoothingMultiplier ε x * P x := by
    dsimp only [Q, P]
    rw [mul_comm (exp ((s : ℂ) * (x : ℂ) * I)), mul_assoc]
  have hpair (ε : ℝ) (hε : ε ∈ Set.Ioo (0 : ℝ) 1) :
      Integrable (Q ε) endpointPairingMeasure ∧
        Real.exp (-s / 2) * (∫ z : ℝ, Real.exp (-z) * F z *
          (∫ v : ℝ, k ε v * longCutoffProfile j (z + s + v))) =
          -Cj * (∫ x, Q ε x ∂endpointPairingMeasure).re := by
    have h := (endpoint_convolution_pairing hY hzero hbound (hk ε hε) hj s hC₁ Cj α).2
    simp_rw [htransform ε hε] at h
    exact h
  have hQ : Tendsto (fun ε ↦ ∫ x, Q ε x ∂endpointPairingMeasure) (𝓝[>] (0 : ℝ))
      (𝓝 (∫ x, P x ∂endpointPairingMeasure)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun x ↦ Real.exp 1 * ‖P x‖)
      ?_ ?_ (hPInt.norm.const_mul _) (ae_of_all _ fun x ↦ ?_)
    · exact hε.mono fun ε hε ↦ (hpair ε hε).1.aestronglyMeasurable
    · filter_upwards [hε] with ε hε
      exact ae_of_all _ fun x ↦ by
        rw [hQFactor, norm_mul]
        exact mul_le_mul_of_nonneg_right (norm_desmoothingMultiplier_le hε x) (norm_nonneg _)
    · simpa only [hQFactor, one_mul] using (tendsto_desmoothingMultiplier x).mul_const (P x)
  refine ⟨hPInt, ?_⟩
  have hreal := ((Complex.continuous_re.tendsto _).comp hQ).const_mul (-Cj)
  exact hreal.congr' (hε.mono fun ε hε ↦ (hpair ε hε).2.symm)

end

end Masullo
