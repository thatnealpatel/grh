module

public import Theorems.IndentationShellSupport
public import Theorems.RationalOrbitalPrimeTwo
public import Theorems.MonogenicPeriodizationSection
public import Lemmas.RationalThetaOrbitalConstant
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# A common base-normalized Haar shell misses a genuine prime-two mode

Proposition 12.2.2.4, pp. 512–514, gives full and base orbit normalization
for its increasing filtration. With both normalizations, the double-leg
lift (12.2.2.1–2), p. 508, vanishes on the off-base input block. The
constant band mode below is our test for using this lift to identify that
block with the orbital action of Theorem 7.4.2.1, p. 367, cited by
(11.3.2.5), p. 496. This is not a claim that the literal Chapter 11
indentation has both normalizations, or about its use with short-support
tests in the scalar calculation on p. 520.
-/

open MeasureTheory NumberField Set
open scoped SchwartzMap

namespace Masullo

noncomputable section

local notation "J" => IdeleGroup (𝓞 ℚ) ℚ
local notation "C" => IdeleClassGroup (𝓞 ℚ) ℚ
local notation "H" => IdeleGroup.principalSubgroup (𝓞 ℚ) ℚ
local notation "D₀" => MonoidHom.range (rationalIdeleFiniteStageEmbedding ∅)
local notation "D₂" => MonoidHom.range
  (rationalIdeleFiniteStageEmbedding (Singleton.singleton rationalOrbitalPrimeTwoPlace))
local notation "σ" => rationalIdeleLogSection
local notation "π" => QuotientGroup.mk (s := H)

set_option linter.concreteInstances false

/-- The signed input shell for the step adding 2, formed from the *same*
quotient kernel `K` by the double-leg counting-Haar lift. -/
@[expose] public def rationalBasePrimeTwoShell [MeasurableSpace J]
    (μ : Measure J) (w : J → ℝ) (K : C → C → ℂ) (v : C → ℂ) (x : J) : ℂ :=
  -∫ y in (D₂ : Set J) \ D₀,
    ((∑' h : H, w ((h : J)⁻¹ * x) * w ((h : J)⁻¹ * y) : ℝ) : ℂ) * K (π x) (π y) * v (π y) ∂μ

/-- The orbital convolution with twist `a` (half twist for `a = 1/2`),
using the above-one prime-two test on log profiles of period `log 2`. -/
@[expose] public def rationalPrimeTwoOrbitalConvolution (a : ℝ) (v : ℝ → ℂ) (u : ℝ) : ℂ :=
  ∫ y : ℝ, ((rationalOrbitalPrimeTwoBump (Real.exp y) * Real.exp (-a * y) : ℝ) : ℂ) * v (u - y)

private theorem primeTwoOrbitalConvolution_one_ne_zero (a : ℝ) (u : ℝ) :
    rationalPrimeTwoOrbitalConvolution a 1 u ≠ 0 := by
  let g (y : ℝ) := rationalOrbitalPrimeTwoBump (Real.exp y) * Real.exp (-a * y)
  have hcont : Continuous g := (rationalOrbitalPrimeTwoBump.continuous.comp Real.continuous_exp).mul
    (Real.continuous_exp.comp (continuous_const.mul continuous_id))
  have hcomp : HasCompactSupport g := by
    refine HasCompactSupport.of_support_subset_isCompact
      (isCompact_Icc (a := Real.log (5 / 3)) (b := Real.log (7 / 3))) ?_
    intro y hy
    have hs : Real.exp y ∈ tsupport rationalOrbitalPrimeTwoBump := subset_tsupport _
      (fun h ↦ hy (by simp [g, h]))
    rw [rationalOrbitalPrimeTwoBump_tsupport] at hs
    exact ⟨(Real.log_le_iff_le_exp (by norm_num)).mpr hs.1,
      (Real.le_log_iff_exp_le (by norm_num)).mpr hs.2⟩
  have hpos : 0 < ∫ y : ℝ, g y := by
    apply integral_pos_of_integrable_nonneg_ne_zero (x := Real.log 2) hcont
      (hcont.integrable_of_hasCompactSupport hcomp)
    · exact fun y ↦ mul_nonneg rationalOrbitalPrimeTwoBump.nonneg (Real.exp_pos _).le
    · simp [g, Real.exp_log (by norm_num : (0 : ℝ) < 2), rationalOrbitalPrimeTwoBump_two,
        (Real.exp_pos _).ne']
  change (∫ y : ℝ, (g y : ℂ) * 1) ≠ 0
  simp only [mul_one, integral_complex_ofReal]
  exact Complex.ofReal_ne_zero.mpr hpos.ne'

private theorem section_mem_base (u : ℝ) : σ (Multiplicative.ofAdd u) ∈ D₀ := by
  change σ (Multiplicative.ofAdd u) ∈ range (rationalIdeleFiniteStageEmbedding ∅)
  rw [range_rationalIdeleFiniteStageEmbedding]
  intro v _
  rw [← map_inv, rationalIdeleLogSection_finite, rationalIdeleLogSection_finite]
  exact ⟨Subring.one_mem _, Subring.one_mem _⟩

/-- At every real band there is an actual constant prime-two orbital mode.
For the two orbit normalizations of Proposition 12.2.2.4, its shell output
on the positive section is zero for every input and every quotient Haar
kernel, including one carrying the finite level and position cutoffs.
The genuine orbital convolution acts nontrivially on this same mode. -/
public theorem rationalBasePrimeTwoShell_misses_band_constant [MeasurableSpace J]
    (μ : Measure J) (w : J → ℝ) (hw : ∀ x, 0 ≤ w x)
    (hfull : ∀ x ∈ D₀, HasSum (fun h : H ↦ w ((h : J)⁻¹ * x)) 1)
    (hbase : ∀ x ∈ D₀, HasSum (fun h : {h : H | (h : J) ∈ D₀} ↦ w ((h.1 : J)⁻¹ * x)) 1)
    {B : ℝ} (hB : 0 < B) (a : ℝ) :
    ∃ b ∈ rationalThetaBandInput B,
      (∀ u : ℝ, HasSum (fun k : ℤ ↦ rationalTheta b (Real.exp (u + (k : ℝ) * Real.log 2))) 1) ∧
      (∀ (K : C → C → ℂ) (v : C → ℂ) (u : ℝ),
        rationalBasePrimeTwoShell μ w K v (σ (Multiplicative.ofAdd u)) = 0) ∧
      (∀ u : ℝ, rationalPrimeTwoOrbitalConvolution a
        (logPeriodization (Real.log 2) (fun x ↦ rationalTheta b (Real.exp x))) u ≠ 0) := by
  obtain ⟨b, hb, hperiod⟩ :=
    exists_rationalThetaBand_logPeriod_hasSum_one (by norm_num : (1 : ℝ) < 2) hB
  refine ⟨b, hb, hperiod, ?_, ?_⟩
  · intro K v u
    unfold rationalBasePrimeTwoShell
    apply neg_eq_zero.mpr
    apply setIntegral_eq_zero_of_forall_eq_zero
    intro y hy
    have hzero := (rationalIdeleFiniteStage_indentation_pair_weight_hasSum_zero ∅ w hw
      hfull hbase (section_mem_base u) hy.2).tsum_eq
    rw [hzero, Complex.ofReal_zero, zero_mul, zero_mul]
  · have heq : logPeriodization (Real.log 2) (fun x ↦ rationalTheta b (Real.exp x)) = 1 :=
      funext fun u ↦ (hperiod u).tsum_eq
    rw [heq]
    exact primeTwoOrbitalConvolution_one_ne_zero a

end
end Masullo
