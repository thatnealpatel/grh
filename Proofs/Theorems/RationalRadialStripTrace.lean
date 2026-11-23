module

public import Theorems.RationalIdeleRadialExplicitFormula
public import Props.ZetaTestSumComparison
import all Theorems.RationalLocalRadialSum
import all Theorems.RationalIdeleRadialExplicitFormula
import Lemmas.RationalLocalRadialTest
import Mathlib.Tactic.Linarith

/-!
# The open-strip radial trace identity and RH

We specialize the displayed sides of (12.5.1.1–3), pp. 519–520, to the
trivial compact character over `ℚ` and profiles `F` of log norm with `F 0 = 0`.
We use half of full Haar at the real place and unit-mass Haar times `log p`
at a finite place. The classical full-zero formula gives these same local
terms. Replacing its sum by the interior-strip sum preserves the identity on
all these tests exactly when every nontrivial zeta zero is in the open strip.
This compares scalar formulas; it neither evaluates the manuscript's global
kernel nor treats nontrivial Hecke characters.
-/

open Complex Filter MeasureTheory NumberField IsDedekindDomain Set
open scoped ContDiff ENNReal FourierTransform Topology

namespace Masullo

local notation "V" => HeightOneSpectrum (𝓞 ℚ)
local notation "K[" v "]" => HeightOneSpectrum.adicCompletion ℚ v

/-- The finite-place integral in (12.5.1.2) with integral units of mass one. -/
@[expose] public noncomputable def rationalRadialFiniteTerm (v : V) (F : ℝ → ℂ) : ℂ :=
  letI : MeasurableSpace K[v]ˣ := borel _
  letI : BorelSpace K[v]ˣ := ⟨rfl⟩
  let p : ℕ := Rat.HeightOneSpectrum.primesEquiv v
  (Real.log (p : ℝ) : ℂ) * ∫ y, rationalLocalRadialKernel v F y ∂rationalLocalMultiplicativeHaar v

private theorem finiteTerm_eq {F : ℝ → ℂ} (hc : HasCompactSupport F) (h₀ : F 0 = 0) (v : V) :
    rationalRadialFiniteTerm v F = rationalLocalRadialFourier v F := by
  let : MeasurableSpace K[v]ˣ := borel _
  let : BorelSpace K[v]ˣ := ⟨rfl⟩
  let f := fun y : K[v]ˣ ↦ F (Real.log ‖(y : K[v])‖)
  obtain ⟨hf, hfc⟩ := rationalLocalRadialTest_properties v hc
  have h := (rationalLocalShifted_principal_value v f hf hfc).2.2
  simpa [rationalRadialFiniteTerm, rationalLocalRadialFourier, rationalLocalRadialKernel,
    f, h₀, integral_const_mul, Real.sqrt_eq_rpow] using h.symm

/-- Real principal-value cutoff from (12.5.1.1). For `F 0 = 0` both the
logarithmic counterterm and the contact term vanish. -/
@[expose] public noncomputable def rationalRadialRealCutoff (F : ℝ → ℂ) (ε : ℝ) : ℂ :=
  ∫ y in {y : ℝˣ | ε ≤ |Real.log (|(y : ℝ)|)|}, realLogProfileHaarKernel F y
    ∂((1 / 2 : ℝ≥0∞) • realMultiplicativeHaar)

set_option linter.concreteInstances false

variable [MeasurableSpace RationalIdeleClasses] [BorelSpace RationalIdeleClasses]

/-- The distinct zeta zeros interior to the window of half-width `a`. -/
public abbrev rationalRadialStripZeros (a : ℝ) : Set criticalStripZetaZeros :=
  {ρ | |(shiftedZetaZero ρ).re| < a}

local notation "term(" F "," ρ ")" => (zetaZeroOrder ρ : ℂ) * rationalIdeleRadialMellin F ρ
local notation "balance(" F "," R ")" => rationalIdeleRadialMellin F 0 + rationalIdeleRadialMellin F 1 -
  R - ∑' v, rationalRadialFiniteTerm v F

/-- The normalized geometric expression equals the poles minus the full-order
sum over the **open** strip, for every norm-one-vanishing radial test.
`HasSum` requires actual convergence, not just equality of two `tsum`s. -/
@[expose] public def RationalRadialStripTrace (a : ℝ) : Prop :=
  ∀ F : ℝ → ℂ, ContDiff ℝ ∞ F → HasCompactSupport F → F 0 = 0 →
    ∃ R : ℂ, Tendsto (rationalRadialRealCutoff F) (𝓝[>] 0) (𝓝 R) ∧
      Function.HasFiniteSupport (fun v ↦ rationalRadialFiniteTerm v F) ∧
      HasSum (fun ρ : rationalRadialStripZeros a ↦ term(F, ρ.val)) (balance(F, R))

/-- The classical all-zero identity in exactly the same Haar normalizations. -/
public theorem rationalRadial_fullTrace {F : ℝ → ℂ} (hf : ContDiff ℝ ∞ F) (hc : HasCompactSupport F)
    (h₀ : F 0 = 0) :
    ∃ R : ℂ, Tendsto (rationalRadialRealCutoff F) (𝓝[>] 0) (𝓝 R) ∧
      Function.HasFiniteSupport (fun v ↦ rationalRadialFiniteTerm v F) ∧
      HasSum (fun ρ : criticalStripZetaZeros ↦ term(F, ρ)) (balance(F, R)) := by
  obtain ⟨_, hfin, hs, he⟩ := rationalIdeleRadial_explicit_formula hf hc
  refine ⟨-(∫ ξ : ℝ, (Real.log |ξ| : ℂ) * 𝓕 (realLogProfileAdditive F) ξ), ?_, ?_, ?_⟩
  · unfold rationalRadialRealCutoff
    simpa only [h₀, mul_zero, add_zero, sub_zero] using real_log_profile_haar_log_principalValue hf hc
  · simpa only [finiteTerm_eq hc h₀] using hfin
  · simp only [finiteTerm_eq hc h₀]
    rw [← he]
    exact hs.of_norm.hasSum

/-- On a test killing every omitted Mellin sample, the full explicit
formula gives the open-strip scalar identity of (12.5.1.3–4), pp. 519–520.
Exact vanishing kills any omitted order, including at the edges. This is a
one-test assertion, not an evaluation of the Chapter 12 diagonal. -/
public theorem rationalRadial_stripTrace_of_omitted_mellin_zero {a : ℝ} {F : ℝ → ℂ}
    (hf : ContDiff ℝ ∞ F) (hc : HasCompactSupport F) (h₀ : F 0 = 0)
    (hkill : ∀ ρ : criticalStripZetaZeros, a ≤ |(shiftedZetaZero ρ).re| →
      rationalIdeleRadialMellin F ρ = 0) :
    ∃ R : ℂ, Tendsto (rationalRadialRealCutoff F) (𝓝[>] 0) (𝓝 R) ∧
      Function.HasFiniteSupport (fun v ↦ rationalRadialFiniteTerm v F) ∧
      HasSum (fun ρ : rationalRadialStripZeros a ↦ term(F, ρ.val)) (balance(F, R)) := by
  classical
  obtain ⟨R, hR, hfin, hall⟩ := rationalRadial_fullTrace hf hc h₀
  refine ⟨R, hR, hfin, (hasSum_subtype_iff_indicator (s := rationalRadialStripZeros a)
    (f := fun ρ ↦ term(F, ρ))).mpr (hall.congr_fun fun ρ ↦ ?_)⟩
  by_cases hi : ρ ∈ rationalRadialStripZeros a
  · exact indicator_of_mem hi _
  · rw [indicator_of_notMem hi, hkill ρ (le_of_not_gt hi), mul_zero]

private theorem mellin_eq_positive {F : ℝ → ℂ} (hf : Continuous F) (hc : HasCompactSupport F)
    (ht : tsupport F ⊆ Ioi (0 : ℝ)) (ρ : criticalStripZetaZeros) :
    rationalIdeleRadialMellin F ρ = positiveLaplaceTest (shiftedZetaZero ρ) F := by
  let g (x : ℝ) := F x * exp (shiftedZetaZero ρ * (x : ℂ))
  have hg : Continuous g := hf.mul (continuous_exp.comp (continuous_const.mul continuous_ofReal))
  change (∫ c, g (Real.log (ideleClassNorm c)) ∂rationalIdeleClassHaar) = _
  rw [integral_rationalIdeleClass_logNorm (hg.integrable_of_hasCompactSupport hc.mul_right)]
  unfold positiveLaplaceTest
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx ↦
    mul_eq_zero_of_right _ (image_eq_zero_of_notMem_tsupport (mt (@ht x) hx)))]
  simp only [g, mul_comm]

/-- Positive-log profiles suffice to detect every omitted zero at this width. -/
public theorem zeros_mem_strip_of_positive_radial_trace {a : ℝ} (ha : 0 < a)
    (h : ∀ F : ℝ → ℂ, ContDiff ℝ ∞ F → HasCompactSupport F → tsupport F ⊆ Ioi (0 : ℝ) →
      ∃ R : ℂ, Tendsto (rationalRadialRealCutoff F) (𝓝[>] 0) (𝓝 R) ∧
        HasSum (fun ρ : rationalRadialStripZeros a ↦ term(F, ρ.val)) (balance(F, R))) :
    ∀ ρ : criticalStripZetaZeros, |(shiftedZetaZero ρ).re| < a := by
  classical
  let m (ρ : criticalStripZetaZeros) :=
    if ρ ∈ rationalRadialStripZeros a then zetaZeroOrder ρ else 0
  have hm (ρ) : m ρ ≤ zetaZeroOrder ρ := by
    dsimp only [m]; split <;> simp
  have agree := zetaZeroOrder_eq_of_test_sum_eq (m := m) hm (by
    intro F hf hc ht _
    have h₀ : F 0 = 0 := image_eq_zero_of_notMem_tsupport (fun h ↦ (lt_irrefl 0) (ht h))
    obtain ⟨R, hR, _, hall⟩ := rationalRadial_fullTrace hf hc h₀
    obtain ⟨R', hR', hsub⟩ := h F hf hc ht
    obtain rfl := tendsto_nhds_unique hR hR'
    have hmask := (hasSum_subtype_iff_indicator (s := rationalRadialStripZeros a)
      (f := fun ρ ↦ term(F, ρ))).mp hsub
    simp_rw [← mellin_eq_positive hf.continuous hc ht]
    refine hall.tsum_eq.trans (HasSum.tsum_eq (hmask.congr_fun fun ρ ↦ ?_)).symm
    by_cases hi : ρ ∈ rationalRadialStripZeros a
    · simp only [m, ite_eq_left hi, indicator_of_mem hi]
    · simp only [m, ite_eq_right hi, indicator_of_notMem hi, Nat.cast_zero, zero_mul])
  intro ρ
  by_contra hout
  have hne : (ρ : ℂ) ≠ 1 / 2 := by
    intro he
    exact hout (by simpa [shiftedZetaZero, he] using ha)
  have he := agree ρ hne
  exact (zetaZeroOrder_pos ρ).ne' (by simpa [m, hout] using he)
/-- At a single positive width, the scalar trace identity detects every
omitted zero, including zeros *on* a boundary of the strip. -/
public theorem rationalRadialStripTrace_iff {a : ℝ} (ha : 0 < a) :
    RationalRadialStripTrace a ↔ ∀ ρ : criticalStripZetaZeros, |(shiftedZetaZero ρ).re| < a := by
  classical
  constructor
  · intro h
    apply zeros_mem_strip_of_positive_radial_trace ha
    intro F hf hc ht
    have h₀ : F 0 = 0 := image_eq_zero_of_notMem_tsupport (fun h ↦ (lt_irrefl 0) (ht h))
    obtain ⟨R, hR, _, hs⟩ := h F hf hc h₀
    exact ⟨R, hR, hs⟩
  · intro hin F hf hc h₀
    obtain ⟨R, hR, hfin, hall⟩ := rationalRadial_fullTrace hf hc h₀
    refine ⟨R, hR, hfin, (hasSum_subtype_iff_indicator (s := rationalRadialStripZeros a)
      (f := fun ρ ↦ term(F, ρ))).mpr (hall.congr_fun fun ρ ↦ ?_)⟩
    exact indicator_of_mem (hin ρ) _

/-- RH is equivalent to this rational, trivial-character specialization at
all positive half-widths. No identity at width zero is asserted or used. -/
public theorem riemannHypothesis_iff_rationalRadialStripTrace :
    RiemannHypothesis ↔ ∀ a : ℝ, 0 < a → RationalRadialStripTrace a := by
  constructor
  · intro h a ha
    apply (rationalRadialStripTrace_iff ha).2
    intro ρ
    obtain ⟨hz, hp, hlt⟩ := mem_criticalStripZetaZeros.mp ρ.property
    have hline := h ρ hz (by
      rintro ⟨n, hn⟩
      rw [hn] at hp
      norm_num at hp
      linarith [Nat.cast_nonneg (α := ℝ) n]) (by intro he; simp [he] at hlt)
    simpa [shiftedZetaZero, hline] using ha
  · intro h
    apply riemannHypothesis_of_strip_test_agreement
    intro ε hε
    have ha : 0 < ε / 2 := half_pos hε
    have hin := (rationalRadialStripTrace_iff ha).1 (h _ ha)
    exact ⟨ε / 2, ⟨ha, half_lt_self hε⟩, zetaZeroOrder, fun _ ↦ le_rfl,
      fun ρ hρ ↦ False.elim ((hin ρ).asymm hρ), by intros; rfl⟩

end Masullo
