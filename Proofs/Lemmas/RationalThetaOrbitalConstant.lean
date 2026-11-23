module

public import Lemmas.RationalThetaOrbitalPeriod
import Lemmas.SchwartzBandCorrection
import Mathlib.Algebra.BigOperators.Group.Finset.Interval
import Mathlib.Order.Filter.AtTopBot.Interval

/-! # A constant orbital period from a two-moment band input -/

open Filter MeasureTheory
open scoped ContDiff FourierTransform SchwartzMap Topology

namespace Masullo

/-- Build the uncorrected precursor by inverse Fourier transform of two reflected
bumps. Normalize its spatial zero mode to `-1` before taking the dilation difference. -/
private theorem exists_uncorrected_band_precursor {D : ℝ} (hD : 0 < D) :
    ∃ g : 𝓢(ℝ, ℂ), Function.Even g ∧ g 0 = -1 ∧ (𝓕 g) 0 = 0 ∧
      ∀ ξ : ℝ, D < |ξ| → (𝓕 g) ξ = 0 := by
  let β : ContDiffBump (D / 2) := ⟨D / 8, D / 4, by positivity, by linarith⟩
  let φ : ℝ → ℝ := fun x ↦ β x + β (-x)
  have hφ : ContDiff ℝ ∞ φ := β.contDiff.add (β.contDiff.comp contDiff_neg)
  have hc : HasCompactSupport φ :=
    β.hasCompactSupport.add (β.hasCompactSupport.comp_homeomorph (Homeomorph.neg ℝ))
  have hφpos : 0 < ∫ x : ℝ, φ x := by
    refine hφ.continuous.integral_pos_of_hasCompactSupport_nonneg_ne_zero hc
      (fun x ↦ add_nonneg (β.nonneg' x) (β.nonneg' (-x))) (x := D / 2) ?_
    have hcenter : β (D / 2) = 1 := β.one_of_mem_closedBall (by simp [β]; positivity)
    exact (show 0 < φ (D / 2) by
      dsimp [φ]
      rw [hcenter]
      linarith [β.nonneg' (-(D / 2))]).ne'
  let f : 𝓢(ℝ, ℂ) := (hc.comp_left Complex.ofReal_zero).toSchwartzMap
    (Complex.ofRealCLM.contDiff.comp hφ)
  have hf (x : ℝ) : f x = (φ x : ℂ) := rfl
  have hm : bandSchwartzMass f ≠ 0 := by
    change (∫ x : ℝ, (φ x : ℂ)) ≠ 0
    exact (integral_ofReal (𝕜 := ℂ) (μ := volume) (f := φ)).trans_ne
      (Complex.ofReal_ne_zero.mpr hφpos.ne')
  let f' : 𝓢(ℝ, ℂ) := (- (bandSchwartzMass f)⁻¹) • f
  let g : 𝓢(ℝ, ℂ) := 𝓕⁻ f'
  have hFg : 𝓕 g = f' := FourierTransform.fourier_fourierInv_eq f'
  have hβ (x : ℝ) (hx : D < |x|) : β x = 0 := by
    apply β.zero_of_le_dist
    rw [Real.dist_eq]
    have h := abs_add_le (x - D / 2) (D / 2)
    rw [sub_add_cancel, abs_of_pos (half_pos hD)] at h
    change D / 4 ≤ |x - D / 2|
    linarith
  refine ⟨g, fourierInv_preserves_realSchwartz_even (f := f') ?_, ?_, ?_, ?_⟩
  · intro x
    simp only [f', smul_apply, hf, φ, neg_neg, add_comm (β (-x))]
  · rw [show g = 𝓕⁻ f' by rfl, fourierInv_zero_eq_bandSchwartzMass]
    simp only [f', map_smul, smul_eq_mul, neg_mul, inv_mul_cancel₀ hm]
  · have hβ₀ : β 0 = 0 := by
      apply β.zero_of_le_dist
      rw [Real.dist_eq, zero_sub, abs_neg, abs_of_pos (half_pos hD)]
      change D / 4 ≤ D / 2
      linarith
    rw [hFg]
    simp [f', hf, φ, hβ₀]
  · intro ξ hξ
    rw [hFg]
    simp [f', hf, φ, hβ ξ hξ, hβ (-ξ) (by simpa only [abs_neg] using hξ)]

/-- Below the first reciprocal-lattice frequency in the band, Poisson leaves
only the negative spatial zero mode. -/
private theorem rationalTheta_eq_neg_zero_at_small_scale {D t : ℝ} (g : 𝓢(ℝ, ℂ))
    (hF₀ : (𝓕 g) 0 = 0) (hband : ∀ ξ : ℝ, D < |ξ| → (𝓕 g) ξ = 0)
    (ht : 0 < t) (hDt : D < t⁻¹) : rationalTheta g t = -g 0 := by
  have hz : rationalTheta (𝓕 g) t⁻¹ = 0 := by
    suffices h : ∀ n : {n : ℤ // n ≠ 0}, (𝓕 g) (t⁻¹ * (n : ℤ)) = 0 by
      simp [rationalTheta, h]
    intro n
    apply hband
    rw [abs_mul, abs_of_pos (inv_pos.mpr ht)]
    have hn : (1 : ℝ) ≤ |((n : ℤ) : ℝ)| := by exact_mod_cast Int.one_le_abs n.property
    exact hDt.trans_le (le_mul_of_one_le_right (inv_nonneg.mpr ht.le) hn)
  simp [rationalTheta_inversion g ht, hF₀, hz]

private theorem rationalTheta_tendsto_zero_atTop (g : 𝓢(ℝ, ℂ)) :
    Tendsto (rationalTheta g) atTop (𝓝 0) := by
  obtain ⟨C, _, h⟩ := rationalTheta_uniform_tail_bounds
    (Bornology.isVonNBounded_singleton (𝕜 := ℂ) g) 1
  refine squeeze_zero_norm' ?_ (tendsto_id.const_div_atTop C)
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
  simpa only [pow_one, id_eq] using (h g (Set.mem_singleton g)).1 t ht

private theorem precursor_logOrbit_limits {D L : ℝ} (hD : 0 < D) (hL : 0 < L)
    (g : 𝓢(ℝ, ℂ)) (hg₀ : g 0 = -1) (hFg₀ : (𝓕 g) 0 = 0)
    (hband : ∀ ξ : ℝ, D < |ξ| → (𝓕 g) ξ = 0) (u : ℝ) :
    let v (k : ℤ) := rationalTheta g (Real.exp (u + (k : ℝ) * L))
    Tendsto (fun n : ℕ ↦ v n) atTop (𝓝 0) ∧ Tendsto (fun n : ℕ ↦ v (-(n : ℤ))) atTop (𝓝 1) := by
  dsimp
  have hlin : Tendsto (fun n : ℕ ↦ (n : ℝ) * L) atTop atTop :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).atTop_mul_const hL
  have hpos := Real.tendsto_exp_atTop.comp (tendsto_atTop_add_const_left atTop u hlin)
  have hneg := Real.tendsto_exp_atBot.comp
    (tendsto_atBot_add_const_left atTop u (tendsto_neg_atBot_iff.mpr hlin))
  constructor
  · simpa only [Function.comp_def, Int.cast_natCast] using
      (rationalTheta_tendsto_zero_atTop g).comp hpos
  · refine tendsto_const_nhds.congr' ?_
    filter_upwards [hneg.eventually (gt_mem_nhds (inv_pos.mpr hD))] with n hn
    change Real.exp (u + -((n : ℝ) * L)) < D⁻¹ at hn
    simp only [Int.cast_neg, Int.cast_natCast, neg_mul]
    have hscale := Real.exp_pos (u + -((n : ℝ) * L))
    have hedge := (lt_inv_comm₀ hD hscale).mpr hn
    rw [rationalTheta_eq_neg_zero_at_small_scale g hFg₀ hband hscale hedge, hg₀, neg_neg]

/-- The difference cancels the spatial zero mode without enlarging the band
past the bound for the dilated precursor. -/
private theorem precursor_dilation_difference {p B : ℝ} (hp : 1 < p) (hB : 0 < B)
    {g : 𝓢(ℝ, ℂ)} (hg : Function.Even g) (hFg₀ : (𝓕 g) 0 = 0)
    (hband : ∀ ξ : ℝ, B / p < |ξ| → (𝓕 g) ξ = 0) :
    let b := g - dilateSchwartz g p (zero_lt_one.trans hp).ne'
    b ∈ rationalThetaBandInput B ∧ ∀ t : ℝ, 0 < t →
      rationalTheta b t = rationalTheta g t - rationalTheta g (p * t) := by
  have hp₀ := zero_lt_one.trans hp
  let d := dilateSchwartz g p hp₀.ne'
  change g - d ∈ rationalThetaBandInput B ∧ _
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · intro x
    simp only [_root_.sub_apply, d, dilateSchwartz_apply, hg x, mul_neg, hg (p * x)]
  · simp [d, dilateSchwartz_apply]
  · simp [FourierTransform.fourier_sub, d, fourier_dilateSchwartz _ hp₀, hFg₀]
  · intro ξ hξ
    have hsmall : B / p < |ξ| := (div_le_self hB.le hp.le).trans_lt hξ
    have hlarge : B / p < |p⁻¹ * ξ| := by
      rw [abs_mul, abs_of_pos (inv_pos.mpr hp₀), ← div_eq_inv_mul]
      exact div_lt_div_of_pos_right hξ hp₀
    simp [FourierTransform.fourier_sub, d, fourier_dilateSchwartz _ hp₀,
      hband ξ hsmall, hband _ hlarge]
  · intro t ht
    have hs (a : 𝓢(ℝ, ℂ)) :=
      (summable_norm_schwartz_int_mul a ht.ne').of_norm.subtype (fun n : ℤ ↦ n ≠ 0)
    simpa only [rationalTheta, _root_.sub_apply, d, dilateSchwartz_apply, mul_assoc,
      Function.comp_def] using (hs g).tsum_sub (hs d)

/-- Use summability to compare the bilateral sum to the limit of the cofinal
windows `[-n, n)`, whose sums telescope to the two surviving endpoints. -/
private theorem hasSum_int_sub_succ (v : ℤ → ℂ) {a : ℂ}
    (hpos : Tendsto (fun n : ℕ ↦ v n) atTop (𝓝 0))
    (hneg : Tendsto (fun n : ℕ ↦ v (-(n : ℤ))) atTop (𝓝 a))
    (hs : Summable (fun k : ℤ ↦ v k - v (k + 1))) :
    HasSum (fun k : ℤ ↦ v k - v (k + 1)) a := by
  obtain ⟨s, hs⟩ := hs
  have hwin : Tendsto (fun n : ℕ ↦ Finset.Ico (-(n : ℤ)) (n : ℤ)) atTop atTop :=
    Finset.tendsto_Ico_neg
  have hsum : Tendsto (fun n : ℕ ↦ v (-(n : ℤ)) - v n) atTop (𝓝 s) := by
    simpa only [Function.comp_def, Finset.sum_Ico_int_sub] using hs.comp hwin
  have hlimits : Tendsto (fun n : ℕ ↦ v (-(n : ℤ)) - v n) atTop (𝓝 a) := by
    simpa only [sub_zero] using hneg.sub hpos
  exact (tendsto_nhds_unique hsum hlimits) ▸ hs

/-- In every positive band, a single two-moment input has constant periodization
one on all orbits of every fixed dilation `p > 1`. -/
public theorem exists_rationalThetaBand_logPeriod_hasSum_one {p B : ℝ} (hp : 1 < p) (hB : 0 < B) :
    ∃ b ∈ rationalThetaBandInput B, ∀ u : ℝ,
      HasSum (fun k : ℤ ↦ rationalTheta b (Real.exp (u + (k : ℝ) * Real.log p))) 1 := by
  have hp₀ := zero_lt_one.trans hp
  have hD : 0 < B / p := div_pos hB hp₀
  obtain ⟨g, hg, hg₀, hFg₀, hband⟩ := exists_uncorrected_band_precursor hD
  let b := g - dilateSchwartz g p hp₀.ne'
  obtain ⟨hb, hθ⟩ := precursor_dilation_difference hp hB hg hFg₀ hband
  refine ⟨b, hb, fun u ↦ ?_⟩
  let v (k : ℤ) := rationalTheta g (Real.exp (u + (k : ℝ) * Real.log p))
  have hL := Real.log_pos hp
  obtain ⟨hpos, hneg⟩ := precursor_logOrbit_limits hD hL g hg₀ hFg₀ hband u
  have hdiff (k : ℤ) : rationalTheta b (Real.exp (u + (k : ℝ) * Real.log p)) =
      v k - v (k + 1) := by
    have hstep : Real.exp (u + ((k + 1 : ℤ) : ℝ) * Real.log p) =
        p * Real.exp (u + (k : ℝ) * Real.log p) := by
      rw [Int.cast_add, Int.cast_one, add_mul, one_mul, ← add_assoc, Real.exp_add,
        Real.exp_log hp₀, mul_comm]
    simp only [v, hstep]
    exact hθ _ (Real.exp_pos _)
  have hs := summable_rationalTheta_log_translates hL hb u
  rw [funext hdiff]
  exact hasSum_int_sub_succ v hpos hneg (hs.congr hdiff)

end Masullo
