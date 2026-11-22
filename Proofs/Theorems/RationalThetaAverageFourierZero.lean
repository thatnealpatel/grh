module

public import Theorems.RationalThetaFiniteUnitAverage
public import Theorems.RationalAdeleLiteralTwoCut

/-! # The Fourier zero mode of averaged rational theta

The small-norm tail identifies the Fourier zero mode from the averaged class
function, without a spatial moment condition. For the literal prime-two cut
in Masullo, §1.3.2, this rules out every two-moment LF representative of the
averaged cut output in the project model.
-/

open Bornology Filter MeasureTheory NumberField
open scoped Topology

namespace Masullo

local notation "A" => AdeleRing (𝓞 ℚ) ℚ
local notation "E" => RationalAdeleSchwartzLF
local notation "τ" x:max => rationalIdeleClassLogSection (Multiplicative.ofAdd x)
local notation "av" => rationalAdeleClassThetaFiniteUnitAverage
local notation "F₀[" f "]" => rationalAdeleFourier (Subtype.val (RationalAdeleSchwartzLF.toUnion f)) 0

set_option linter.concreteInstances false
variable [MeasurableSpace A] [BorelSpace A]

/-- The corrected averaged theta remainder is bounded on the nonpositive
log section without any zero-moment assumptions. -/
private theorem bounded_average_remainder (f : E) : ∃ K : ℝ, ∀ x : ℝ, x ≤ 0 →
    ‖av f (τ x) - (Real.exp x)⁻¹ • F₀[f] + f.toUnion.val 0‖ ≤ K := by
  let : MeasurableSpace (A ⧸ rationalDiagonal) := borel _
  let : BorelSpace (A ⧸ rationalDiagonal) := ⟨rfl⟩
  let g := rationalAdeleLFFiniteUnitAverage f
  obtain ⟨K, _, ht⟩ := rationalAdeleLF_uniform_theta_tails 0 (isVonNBounded_singleton (𝕜 := ℂ) g)
  have h := (ht g (Set.mem_singleton g)).2
  obtain ⟨h₀, hF⟩ := rationalAdeleLFFiniteUnitAverage_zero_modes f
  rw [rationalAdeleClassTheta_LFFiniteUnitAverage f, h₀, hF] at h
  refine ⟨K, fun x hx ↦ ?_⟩
  have hn : ideleClassNorm (τ x) = Real.exp x := by
    rw [rationalIdeleClassLogSection_apply, ideleClassNorm_mk, ideleNorm_logSection]
    rfl
  have hle : ideleClassNorm (τ x) ≤ 1 := hn ▸ Real.exp_le_one_iff.mpr hx
  simpa only [hn, pow_zero, mul_one] using h (τ x) hle

/-- Scaling averaged theta by the section norm and sending log norm to
negative infinity recovers the Fourier zero mode of any rational LF test. -/
public theorem tendsto_rationalAdeleClassThetaFiniteUnitAverage_exp_mul (f : E) :
    Tendsto (fun x : ℝ ↦ Real.exp x • av f (τ x)) atBot (𝓝 (F₀[f])) := by
  let R (x : ℝ) := av f (τ x) - (Real.exp x)⁻¹ • F₀[f] + f.toUnion.val 0
  obtain ⟨K, hK⟩ := bounded_average_remainder f
  have hlim : Tendsto (fun x : ℝ ↦ Real.exp x • R x) atBot (𝓝 (0 : ℂ)) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero' (g := fun x ↦ Real.exp x * K) (.of_forall fun _ ↦ norm_nonneg _) ?_ ?_
    · filter_upwards [eventually_le_atBot (0 : ℝ)] with x hx
      rw [norm_smul, Real.norm_of_nonneg (Real.exp_pos x).le]
      exact mul_le_mul_of_nonneg_left (hK x hx) (Real.exp_pos x).le
    · simpa only [zero_mul] using Real.tendsto_exp_atBot.mul_const K
  have hsp : Tendsto (fun x : ℝ ↦ Real.exp x • f.toUnion.val 0) atBot (𝓝 (0 : ℂ)) := by
    simpa only [zero_smul] using Real.tendsto_exp_atBot.smul
      (tendsto_const_nhds (x := f.toUnion.val 0))
  have h := (hlim.sub hsp).add (tendsto_const_nhds (x := F₀[f]))
  simp only [sub_zero, zero_add] at h
  refine h.congr fun x ↦ ?_
  dsimp only [R]
  rw [smul_add, smul_sub, smul_inv_smul₀ (Real.exp_ne_zero x), add_sub_cancel_right,
    sub_add_cancel]

/-- The Fourier zero mode depends only on the represented averaged theta
function, not on the choice of test. -/
public theorem rationalAdeleClassThetaFiniteUnitAverage_fourier_zero_eq {f g : E}
    (h : av f = av g) : F₀[f] = F₀[g] := by
  have hf := tendsto_rationalAdeleClassThetaFiniteUnitAverage_exp_mul f
  rw [h] at hf
  exact tendsto_nhds_unique hf (tendsto_rationalAdeleClassThetaFiniteUnitAverage_exp_mul g)

/-- An actual prime-two cut of a two-moment rational LF test has an averaged
theta function outside the entire averaged two-moment range. -/
public theorem rationalAdeleLiteralTwoCut_averagedTheta_not_mem_range :
    ∃ f : RationalThetaTwoModeInput, ∃ g : E,
      g.toUnion.val = (rationalAdelePrimeUnits ⟨2, Nat.prime_two⟩).indicator f.val.toUnion.val ∧
      av g ∉ Set.range (fun h : RationalThetaTwoModeInput ↦ av h.val) := by
  obtain ⟨f, g, hcut, hf₀, hfF, hgF⟩ := rationalAdeleLiteralTwoCut_loses_moment
  refine ⟨⟨f, hf₀, hfF⟩, g, hcut, ?_⟩
  rintro ⟨h, hh⟩
  exact hgF ((rationalAdeleClassThetaFiniteUnitAverage_fourier_zero_eq hh.symm).trans h.property.2)

end Masullo
