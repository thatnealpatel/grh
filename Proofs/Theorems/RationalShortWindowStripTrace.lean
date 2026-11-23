module

public import Theorems.RationalRadialStripTrace
public import Props.OmittedZetaTraceSeparation
import all Theorems.RationalRadialStripTrace
import Lemmas.RealLogHaarFold
import Mathlib.Tactic.Linarith

/-!
# The below-one witness in the normalized rational scalar formula

The finite shells in (B.4.4.22), p. 625, or the prime-power samples in
(B.4.2.10–11), p. 615, cannot see a test at norms strictly between `1/2`
and `1`. For the real term in (12.5.1.1), p. 519, we use the checked fold
of half of full Haar, with no identity counterterm on this support.
These two evaluations make the normalized scalar identity zero on the
conditional omitted-divisor witness. Its modeled projected density
pairing is nevertheless nonzero. The deduction does not identify either
pairing with a common global diagonal in (12.5.1.4), p. 520.
-/

open Filter MeasureTheory NumberField IsDedekindDomain Set
open scoped ContDiff Topology

namespace Masullo

local notation "J" => (fun t : ℝ ↦ Real.exp ((-1 / 2) * t) / (1 - Real.exp (-2 * t)))

private theorem realCutoff_reflect_eq {f : ℝ → ℝ} {L ε : ℝ}
    (hε : 0 < ε) (hεL : ε ≤ L) (hz : ∀ t ≤ L, f t = 0)
    (hf : ContDiff ℝ ∞ (fun x ↦ (f (-x) : ℂ)))
    (hc : HasCompactSupport (fun x ↦ (f (-x) : ℂ))) :
    rationalRadialRealCutoff (fun x ↦ (f (-x) : ℂ)) ε = ((∫ t, J t * f t : ℝ) : ℂ) := by
  obtain ⟨hd, hk, _⟩ := real_log_profile_additive_test hf hc
  have hi : Integrable (realLogProfileAdditive (fun x ↦ (f (-x) : ℂ))) :=
    (hk.toSchwartzMap hd).integrable
  rw [rationalRadialRealCutoff, (RealLogHaarFold.fold hi hε).2,
    ← integral_complex_ofReal]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Ioi ε) (f := fun t ↦ (↑(J t * f t) : ℂ))
    (fun t ht ↦ by simp [hz t ((not_lt.mp ht).trans hεL)])]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  have hneg : f (-t) = 0 := hz _ (by linarith [mem_Ioi.mp ht])
  push_cast [Complex.ofReal_exp]
  simp only [neg_neg, hneg, Complex.ofReal_zero, zero_add]
  rw [show -(t : ℂ) / 2 = -1 / 2 * (t : ℂ) by ring]
  ring

private theorem finiteTerm_reflect_eq_zero {f : ℝ → ℝ}
    (hz₀ : ∀ t ≤ 0, f t = 0) (hz₂ : ∀ t ≥ Real.log 2, f t = 0)
    (hc : HasCompactSupport (fun x ↦ (f (-x) : ℂ)))
    (v : HeightOneSpectrum (𝓞 ℚ)) : rationalRadialFiniteTerm v (fun x ↦ (f (-x) : ℂ)) = 0 := by
  let : MeasurableSpace (HeightOneSpectrum.adicCompletion ℚ v)ˣ := borel _
  let : BorelSpace (HeightOneSpectrum.adicCompletion ℚ v)ˣ := ⟨rfl⟩
  rw [finiteTerm_eq hc (by simp [hz₀ 0 le_rfl]) v, rationalLocalRadialFourier,
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
  have hneg : -x ≤ 0 := by linarith [Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)]
  change (Real.log (p : ℝ) : ℂ) *
    (Complex.exp (-(x : ℂ) / 2) * (f (-x) : ℂ) +
      Complex.exp (-((-x : ℝ) : ℂ) / 2) * (f (- -x) : ℂ) / (n : ℂ)) = 0
  simp only [neg_neg, hz₀ _ hneg, hz₂ _ hx, Complex.ofReal_zero, mul_zero, zero_div, add_zero]

set_option linter.concreteInstances false

variable [MeasurableSpace RationalIdeleClasses] [BorelSpace RationalIdeleClasses]

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
    have he := realCutoff_reflect_eq hε hεl.le hz hF hFc
    rw [hJ, Complex.ofReal_zero] at he
    exact he.symm
  have hfin (v) : rationalRadialFiniteTerm v F = 0 :=
    finiteTerm_reflect_eq_zero (fun t ht ↦ hz t (ht.trans hl.le)) hz₂ hFc v
  have hF₀ : F 0 = 0 := by simp [F, hz 0 hl.le]
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
