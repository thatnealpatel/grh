module

public import Theorems.RationalRadialStripTrace
public import Props.OmittedZetaTraceSeparation
import all Theorems.RationalRadialStripTrace
import Lemmas.RealLogHaarFold
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Short log windows in the normalized rational scalar formula

The finite shells in (B.4.4.22), p. 625, or the prime-power samples in
(B.4.2.10–11), p. 615, cannot see a test at norms strictly between `1/2`
and `1`. For the real term in (12.5.1.1), p. 519, we use the checked fold
of half of full Haar, with no identity counterterm on this support.
These evaluations give the full trace of a positive-log profile in the short
window. In the reflected orientation they also make the normalized scalar
identity zero on the conditional omitted-divisor witness. Its modeled projected
density pairing is nevertheless nonzero. The deduction does not identify either
pairing with a common global diagonal in (12.5.1.4), p. 520.
-/

open Filter MeasureTheory NumberField IsDedekindDomain Set
open scoped ContDiff Topology

namespace Masullo

local notation "J" => (fun t : ℝ ↦ Real.exp ((-1 / 2) * t) / (1 - Real.exp (-2 * t)))

private theorem realCutoff_eq_short {F : ℝ → ℂ} {f : ℝ → ℝ} {L ε : ℝ}
    (hε : 0 < ε) (hεL : ε ≤ L) (hz : ∀ t ≤ L, f t = 0)
    (hfold : ∀ t > 0, F t + F (-t) = (f t : ℂ))
    (hf : ContDiff ℝ ∞ F) (hc : HasCompactSupport F) :
    rationalRadialRealCutoff F ε = ((∫ t, J t * f t : ℝ) : ℂ) := by
  obtain ⟨hd, hk, _⟩ := real_log_profile_additive_test hf hc
  have hi : Integrable (realLogProfileAdditive F) :=
    (hk.toSchwartzMap hd).integrable
  rw [rationalRadialRealCutoff, (RealLogHaarFold.fold hi hε).2,
    ← integral_complex_ofReal]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Ioi ε) (f := fun t ↦ (↑(J t * f t) : ℂ))
    (fun t ht ↦ by simp [hz t ((not_lt.mp ht).trans hεL)])]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  dsimp only
  rw [hfold t (hε.trans ht)]
  push_cast [Complex.ofReal_exp]
  rw [show -(t : ℂ) / 2 = -1 / 2 * (t : ℂ) by ring]
  ring

private theorem finiteTerm_eq_zero_short {F : ℝ → ℂ}
    (h₀ : F 0 = 0) (hz₂ : ∀ t ≥ Real.log 2, F t = 0 ∧ F (-t) = 0)
    (hc : HasCompactSupport F) (v : HeightOneSpectrum (𝓞 ℚ)) : rationalRadialFiniteTerm v F = 0 := by
  let : MeasurableSpace (HeightOneSpectrum.adicCompletion ℚ v)ˣ := borel _
  let : BorelSpace (HeightOneSpectrum.adicCompletion ℚ v)ˣ := ⟨rfl⟩
  rw [finiteTerm_eq hc h₀ v, rationalLocalRadialFourier,
    (rationalLocalRadialFourier_eq_primeSamples v hc).2.2]
  refine (tsum_congr (g := fun _ : ℕ ↦ (0 : ℂ)) ?_).trans tsum_zero
  intro m
  let p : ℕ := Rat.HeightOneSpectrum.primesEquiv v
  have hp : 2 ≤ p := (Rat.HeightOneSpectrum.primesEquiv v).property.two_le
  have hn : 2 ≤ p ^ (m + 1) := hp.trans (Nat.le_self_pow (Nat.succ_ne_zero m) p)
  let n : ℝ := (p : ℝ) ^ (m + 1)
  have hn' : 2 ≤ n := by
    dsimp only [n]
    exact_mod_cast hn
  let x := Real.log n
  have hx : Real.log 2 ≤ x := Real.log_le_log (by norm_num) hn'
  change (Real.log (p : ℝ) : ℂ) *
    (Complex.exp (-(x : ℂ) / 2) * F x +
      Complex.exp (-((-x : ℝ) : ℂ) / 2) * F (-x) / (n : ℂ)) = 0
  rw [(hz₂ _ hx).1, (hz₂ _ hx).2]
  simp

/-- The real exponents of the half-Haar geometric series, including its first term. -/
@[expose] public noncomputable def rationalShortArchExponent (n : ℕ) : ℝ := -2 * n - 1 / 2

private theorem archSeries {f : ℝ → ℝ} {L : ℝ} (hL : 0 < L)
    (hz : ∀ t ≤ L, f t = 0) (hf : Continuous f) (hc : HasCompactSupport f) :
    HasSum (fun n ↦ compactLogMellin (fun t ↦ (f t : ℂ)) (rationalShortArchExponent n))
      ((∫ t, J t * f t : ℝ) : ℂ) := by
  let r := Real.exp (-2 * L)
  have hr : r < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hs : Summable (fun n : ℕ ↦ r ^ n) := summable_geometric_of_lt_one (by positivity) hr
  have hexp (n : ℕ) (t : ℝ) :
      Real.exp (rationalShortArchExponent n * t) = Real.exp ((-1 / 2) * t) * Real.exp (-2 * t) ^ n := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    unfold rationalShortArchExponent
    ring
  have hreal : HasSum (fun n : ℕ ↦ ∫ t, f t * Real.exp (rationalShortArchExponent n * t))
      (∫ t, J t * f t) := by
    apply hasSum_integral_of_dominated_convergence (fun n t ↦ ‖f t‖ * r ^ n)
    · intro n
      exact (hf.mul (Real.continuous_exp.comp (continuous_const.mul continuous_id))).aestronglyMeasurable
    · intro n
      exact .of_forall fun t ↦ by
        by_cases ht : t ≤ L
        · simp [hz t ht]
        rw [norm_mul, Real.norm_of_nonneg (Real.exp_pos _).le, hexp]
        refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
        have hpos : 0 < t := hL.trans (lt_of_not_ge ht)
        refine mul_le_of_le_one_left (by positivity) ?_ |>.trans ?_
        · exact (Real.exp_le_one_iff.mpr (by linarith))
        · exact pow_le_pow_left₀ (Real.exp_pos _).le (Real.exp_le_exp.mpr (by linarith)) _
    · exact .of_forall fun t ↦ hs.mul_left _
    · simp_rw [tsum_mul_left]
      exact (hf.integrable_of_hasCompactSupport hc).norm.mul_const _
    · exact .of_forall fun t ↦ by
        by_cases ht : t ≤ L
        · simp [hz t ht]
        have hpos : 0 < t := hL.trans (lt_of_not_ge ht)
        simp_rw [hexp, ← mul_assoc]
        have hg := hasSum_geometric_of_lt_one (Real.exp_pos (-2 * t)).le
          (Real.exp_lt_one_iff.mpr (by linarith : -2 * t < 0))
        convert hg.mul_left (f t * Real.exp ((-1 / 2) * t)) using 1
        simp only [div_eq_mul_inv]
        ring
  refine (Complex.hasSum_ofReal.mpr hreal).congr_fun fun n ↦ ?_
  simp only [compactLogMellin, ← Complex.ofReal_mul, ← Complex.ofReal_exp, integral_complex_ofReal]

set_option linter.concreteInstances false

variable [MeasurableSpace RationalIdeleClasses] [BorelSpace RationalIdeleClasses]

/-- In the positive log coordinate the normalized radial Mellin sample is
the ordinary log Mellin sample shifted by `-1/2`. -/
public theorem rationalIdeleRadialMellin_eq_shiftedCompactLogMellin {F : ℝ → ℂ}
    (hF : Continuous F) (hc : HasCompactSupport F) (s : ℂ) :
    rationalIdeleRadialMellin F s = compactLogMellin F (s - 1 / 2) := by
  rw [(rationalIdeleRadialMellin_eq_compactLogMellin hF hc s).2]
  unfold compactLogMellin
  apply integral_congr_ae
  filter_upwards with t
  rw [mul_comm (Complex.exp _), mul_assoc, ← Complex.exp_add]
  congr 2
  ring

/-- Below the first prime power, the full-order zero sum is absolutely
convergent. In the negative sum the zeroth half-Haar term cancels the pole at
`-1/2`, so only the geometric tail and the pole at `1/2` remain. -/
public theorem rationalShortWindow_fullTrace {L : ℝ} {f : ℝ → ℝ}
    (hL : 0 < L) (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    (hsupp : tsupport f ⊆ Ioo L (Real.log 2)) :
    let M := compactLogMellin (fun t ↦ (f t : ℂ))
    Summable (fun ρ : criticalStripZetaZeros ↦ ‖(zetaZeroOrder ρ : ℂ) * M (shiftedZetaZero ρ)‖) ∧
    HasSum (fun n ↦ M (rationalShortArchExponent (n + 1)))
      (M (1 / 2) - ∑' ρ : criticalStripZetaZeros, (zetaZeroOrder ρ : ℂ) * M (shiftedZetaZero ρ)) := by
  let F : ℝ → ℂ := fun t ↦ (f t : ℂ)
  have hF : ContDiff ℝ ∞ F := Complex.ofRealCLM.contDiff.comp hf
  have hFc : HasCompactSupport F := hc.comp_left Complex.ofReal_zero
  have hz (t : ℝ) (ht : t ≤ L) : f t = 0 :=
    image_eq_zero_of_notMem_tsupport (fun h ↦ ht.not_gt (hsupp h).1)
  have hz₂ (t : ℝ) (ht : Real.log 2 ≤ t) : f t = 0 :=
    image_eq_zero_of_notMem_tsupport (fun h ↦ ht.not_gt (hsupp h).2)
  have h0 : F 0 = 0 := by simp [F, hz 0 hL.le]
  have hR : Tendsto (rationalRadialRealCutoff F) (𝓝[>] 0) (𝓝 (((∫ t, J t * f t) : ℝ) : ℂ)) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_mem_nhdsWithin (a := (0 : ℝ)) (s := Ioi 0),
      nhdsWithin_le_nhds (eventually_lt_nhds hL)] with ε hε hεL
    exact (realCutoff_eq_short hε hεL.le hz (fun t ht ↦ by simp [F, hz (-t) (by linarith)]) hF hFc).symm
  have hfin (v) : rationalRadialFiniteTerm v F = 0 :=
    finiteTerm_eq_zero_short h0 (fun t ht ↦ by
      simp [F, hz₂ t ht, hz (-t) (by linarith [Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)])]) hFc v
  have hM := rationalIdeleRadialMellin_eq_shiftedCompactLogMellin hF.continuous hFc
  obtain ⟨R, hR', _, hs⟩ := rationalRadial_fullTrace hF hFc h0
  rw [tendsto_nhds_unique hR' hR] at hs
  simp only [hfin, tsum_zero, sub_zero, hM] at hs
  obtain ⟨_, _, hn, _⟩ := rationalIdeleRadial_explicit_formula hF hFc
  simp only [hM] at hn
  refine ⟨hn, ?_⟩
  change HasSum (fun n ↦ compactLogMellin F (rationalShortArchExponent (n + 1)))
    (compactLogMellin F (1 / 2) - ∑' ρ : criticalStripZetaZeros,
      (zetaZeroOrder ρ : ℂ) * compactLogMellin F ((ρ : ℂ) - 1 / 2)) at ⊢
  have harch := (hasSum_nat_add_iff' 1).mpr (archSeries hL hz hf.continuous hc)
  simp only [Finset.sum_range_one] at harch
  rw [hs.tsum_eq]
  convert harch using 1
  have hzero : (0 : ℂ) - 1 / 2 = (rationalShortArchExponent 0 : ℂ) := by
    norm_num [rationalShortArchExponent]
  have hone : (1 : ℂ) - 1 / 2 = 1 / 2 := by ring
  rw [hzero, hone]
  ring

/-- Under the fixed-width count, a test in any short below-one log window
makes every canonical local term and both poles zero, and the full-order
open-strip series actually sums to zero. The projected pairing at
`β = 2 * α` is nonzero on that same test. -/
public theorem exists_rationalShortWindow_stripTrace_separation {α C q : ℝ}
    (hα : 0 < α) (hαhalf : α < 1 / 2) (hq₀ : 0 ≤ q) (hq₂ : q < 2)
    (hcount : ∀ (j : ℕ) (A : Finset criticalStripZetaZeros),
      (∀ ρ ∈ A, 1 / 2 + α ≤ (ρ : ℂ).re ∧ 0 < (ρ : ℂ).im ∧
        (ρ : ℂ).im < (2 : ℝ) ^ (j + 1)) → (A.card : ℝ) ≤ C * q ^ j)
    {L U : ℝ} (hL : 0 ≤ L) (hLU : L < U) (hU : U ≤ Real.log 2) :
    ∃ f : ℝ → ℝ, ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧ tsupport f ⊆ Ioo L U ∧
      let F : ℝ → ℂ := fun x ↦ (f (-x) : ℂ)
      Tendsto (rationalRadialRealCutoff F) (𝓝[>] 0) (𝓝 0) ∧
      (∀ v, rationalRadialFiniteTerm v F = 0) ∧
      rationalIdeleRadialMellin F 0 = 0 ∧ rationalIdeleRadialMellin F 1 = 0 ∧
      HasSum (fun ρ : rationalRadialStripZeros α ↦
        (zetaZeroOrder ρ.val : ℂ) * rationalIdeleRadialMellin F ρ.val) 0 ∧
      (∫ t : ℝ, (Real.exp ((2 * α - 5 / 2) * t) / (1 - Real.exp (-2 * t))) * f t) ≠ 0 := by
  let l := (L + U) / 2
  have hLl : L < l := by dsimp [l]; linarith
  have hl : 0 < l := hL.trans_lt hLl
  have hlU : l < U := by dsimp [l]; linarith
  obtain ⟨f, hf, hsupp, ⟨_, hJ⟩, ⟨_, hproj⟩, hp, hm, hkill⟩ :=
    exists_compactLogMellin_omittedZeta_trace_separation hq₀ hq₂ hcount
      (β := 2 * α) (by linarith) (by linarith) hl.le hlU hU
  have hc : HasCompactSupport f := isCompact_Icc.of_isClosed_subset isClosed_closure
    (hsupp.trans Ioo_subset_Icc_self)
  let g : ℝ → ℂ := fun t ↦ (f t : ℂ)
  let F : ℝ → ℂ := fun x ↦ (f (-x) : ℂ)
  have hg : ContDiff ℝ ∞ g := Complex.ofRealCLM.contDiff.comp hf
  have hgc : HasCompactSupport g := hc.comp_left Complex.ofReal_zero
  have hF : ContDiff ℝ ∞ F := hg.comp contDiff_neg
  have hFc : HasCompactSupport F := hgc.comp_homeomorph (Homeomorph.neg ℝ)
  have hz (t : ℝ) (ht : t ≤ l) : f t = 0 :=
    image_eq_zero_of_notMem_tsupport (fun h ↦ ht.not_gt (hsupp h).1)
  have hz₂ (t : ℝ) (ht : Real.log 2 ≤ t) : f t = 0 :=
    image_eq_zero_of_notMem_tsupport (fun h ↦ (hU.trans ht).not_gt (hsupp h).2)
  -- The folded real term is exactly J. The finite places have no sample in the window.
  have hR : Tendsto (rationalRadialRealCutoff F) (𝓝[>] 0) (𝓝 0) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_mem_nhdsWithin (a := (0 : ℝ)) (s := Ioi 0),
      nhdsWithin_le_nhds (eventually_lt_nhds hl)] with ε hε hεl
    have he := realCutoff_eq_short hε hεl.le hz (F := F) (fun t ht ↦ by
      simp [F, hz (-t) (by linarith)]) hF hFc
    rw [hJ, Complex.ofReal_zero] at he
    exact he.symm
  have hF₀ : F 0 = 0 := by simp [F, hz 0 hl.le]
  have hfin (v) : rationalRadialFiniteTerm v F = 0 :=
    finiteTerm_eq_zero_short hF₀ (fun t ht ↦ by
      simp [F, hz₂ t ht, hz (-t) (by linarith [Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)])]) hFc v
  -- Reflect the Mellin samples, then discard the exact zeros in the full series.
  have hM (s : ℂ) : rationalIdeleRadialMellin F s = compactLogMellin g (-(s - 1 / 2)) :=
    rationalIdeleRadialMellin_reflect hg.continuous hgc s
  have hM₀ : rationalIdeleRadialMellin F 0 = 0 := by rw [hM]; simpa using hp
  have hM₁ : rationalIdeleRadialMellin F 1 = 0 := by
    rw [hM, show -((1 : ℂ) - 1 / 2) = -1 / 2 by ring]; exact hm
  obtain ⟨R, hR', _, hs⟩ := rationalRadial_stripTrace_of_omitted_mellin_zero hF hFc hF₀
    (a := α) (fun ρ hρ ↦ (hM ρ).trans (hkill ρ hρ))
  have hR₀ : R = 0 := tendsto_nhds_unique hR' hR
  refine ⟨f, hf, hc, hsupp.trans (fun _ h ↦ ⟨hLl.trans h.1, h.2⟩), hR, hfin, hM₀, hM₁, ?_, hproj⟩
  simpa only [hM₀, hM₁, hR₀, hfin, tsum_zero, add_zero, sub_zero] using hs

end Masullo
