module

public import Lemmas.SchwartzWeightedDilation
public import Mathlib.Topology.UniformSpace.UniformConvergence
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-! # Uniform passage of the profile estimate to the Schwartz topology -/

open Bornology Filter Set
open scoped SchwartzMap Topology

namespace Masullo

/-- Uniform convergence is convergence to zero of the error along the
parameter filter times the principal filter of the input family. -/
public theorem tendstoUniformlyOn_iff_sub {ι X Y : Type*} [UniformSpace Y] [AddCommGroup Y]
    [IsUniformAddGroup Y] {l : Filter ι} {B : Set X} {F : ι → X → Y} {g : X → Y} :
    TendstoUniformlyOn F g l B ↔
      Tendsto (fun z : ι × X ↦ F z.1 z.2 - g z.2) (l ×ˢ 𝓟 B) (𝓝 0) := by
  rw [tendstoUniformlyOn_iff_tendsto, uniformity_eq_comap_nhds_zero, tendsto_comap_iff]
  rfl

local notation "S" => 𝓢(ℝ, ℂ)
local notation "U" => schwartzWeightedInverseDilation
local notation "G" => schwartzInverseDilationGenerator
local notation "p" => SchwartzMap.seminorm ℂ

private theorem seminorm_real_smul (a d : ℕ) (r : ℝ) (b : S) :
    p a d (r • b) = |r| * p a d b := by
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ), map_smul_eq_mul]
  change ‖(r : ℂ)‖ * _ = _
  rw [Complex.norm_real, Real.norm_eq_abs]

/-- A change of parameter preserves the limit if its log increment goes to
zero and the quotient rescaling tends to one. -/
public theorem tendstoUniformlyOn_schwartzWeightedInverseDilation {ι : Type*} {l : Filter ι}
    {s r : ι → ℝ} (hs : Tendsto s l (𝓝[≠] 0))
    (hr : Tendsto (fun t ↦ r t * s t) l (𝓝 1))
    {B : Set S} (hB : IsVonNBounded ℂ B) :
    TendstoUniformlyOn (fun t b ↦ r t • (U (s t) b - b)) G l B := by
  let w := schwartz_withSeminorms ℂ ℝ ℂ
  let q (t : ι) := r t * s t
  have hs₀ := hs.mono_right nhdsWithin_le_nhds
  have hnear : ∀ᶠ t in l, s t ≠ 0 ∧ |s t| ≤ 1 := by
    have h1 : ∀ᶠ t in l, |s t| < 1 := by
      have h := hs₀.abs.eventually (gt_mem_nhds (show |(0 : ℝ)| < 1 by simp))
      exact h
    filter_upwards [hs self_mem_nhdsWithin, h1] with t ht ha
    exact ⟨ht, ha.le⟩
  rw [tendstoUniformlyOn_iff_sub, w.hasBasis_zero_ball.tendsto_right_iff]
  rintro ⟨I, ε⟩ hε
  rw [Seminorm.ball_finset_sup_eq_iInter _ _ _ hε]
  simp only [mem_iInter₂, Seminorm.mem_ball_zero]
  rw [Filter.eventually_all_finset]
  rintro ⟨a, d⟩ _
  obtain ⟨C, _, hC⟩ := w.isVonNBounded_iff_seminorm_bounded.mp
    (hB.image (ContinuousLinearMap.comp G G)) (a, d)
  obtain ⟨D, _, hD⟩ := w.isVonNBounded_iff_seminorm_bounded.mp (hB.image G) (a, d)
  let K := Real.exp (|(a : ℝ) - d - 1|)
  have hsmall : ∀ᶠ t in l, |q t| * (K * |s t| * C) + |q t - 1| * D < ε := by
    have hTaylor := ((tendsto_const_nhds (x := K)).mul hs₀.abs).mul
      (tendsto_const_nhds (x := C))
    have h := (hr.abs.mul hTaylor).add
      ((hr.sub_const 1).abs.mul (tendsto_const_nhds (x := D)))
    simp only [abs_zero, mul_zero, zero_mul, sub_self, add_zero] at h
    exact h.eventually (gt_mem_nhds hε)
  have hmem : ∀ᶠ b in 𝓟 B, b ∈ B := mem_principal_self B
  filter_upwards [(hnear.and hsmall).prod_mk hmem] with z hz
  obtain ⟨⟨⟨hz₀, hz₁⟩, hzε⟩, hb⟩ := hz
  rcases z with ⟨t, b⟩
  have he : r t • (U (s t) b - b) - G b =
      q t • ((s t)⁻¹ • (U (s t) b - b) - G b) + (q t - 1) • G b := by
    simp only [smul_sub, smul_smul, show q t * (s t)⁻¹ = r t by simp [q, hz₀], sub_smul, one_smul]
    abel
  change p a d (r t • (U (s t) b - b) - G b) < ε
  rw [he]
  apply lt_of_le_of_lt (map_add_le_add _ _ _) (lt_of_le_of_lt ?_ hzε)
  rw [seminorm_real_smul, seminorm_real_smul]
  apply add_le_add
  · apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    refine (seminorm_weightedInverseDilation_difference_quotient a d b hz₀ hz₁).trans ?_
    exact mul_le_mul_of_nonneg_left (hC _ ⟨b, hb, rfl⟩).le (by positivity)
  · exact mul_le_mul_of_nonneg_left (hD _ ⟨b, hb, rfl⟩).le (abs_nonneg _)

/-- At positive scales near one, `log t` tends to zero without meeting zero. -/
public theorem tendsto_log_nhdsNE_one : Tendsto Real.log (𝓝[≠] 1) (𝓝[≠] 0) := by
  have h : ContinuousAt Real.log 1 := (Real.hasDerivAt_log one_ne_zero).continuousAt
  rw [tendsto_nhdsWithin_iff]
  refine ⟨by simpa using h.tendsto.mono_left nhdsWithin_le_nhds, ?_⟩
  have hp : ∀ᶠ t : ℝ in 𝓝[≠] 1, 0 < t := nhdsWithin_le_nhds (Ioi_mem_nhds zero_lt_one)
  filter_upwards [self_mem_nhdsWithin, hp] with t ht hp'
  change Real.log t ≠ 0
  intro he
  exact ht (by rw [← Real.exp_log hp', he, Real.exp_zero]; rfl)

/-- The scale quotient differs from the log quotient by a factor tending to one. -/
public theorem tendsto_log_div_sub_one :
    Tendsto (fun t : ℝ ↦ (t - 1)⁻¹ * Real.log t) (𝓝[≠] 1) (𝓝 1) := by
  have h := (Real.hasDerivAt_log one_ne_zero).tendsto_slope
  rw [show slope Real.log 1 = (fun t : ℝ ↦ (t - 1)⁻¹ * Real.log t) by
    funext t
    rw [slope_def_module, Real.log_one, sub_zero, smul_eq_mul]] at h
  simpa only [inv_one] using h

end Masullo
