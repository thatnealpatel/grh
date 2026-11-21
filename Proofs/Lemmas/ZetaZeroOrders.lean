module

public import Lemmas.ShiftedZetaZeros
public import Mathlib.Analysis.Meromorphic.Divisor
import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# Transferring zeta orders to an entire function

The multiplicities in Masullo's (B.4.2.2), p. 614, enter as orders of zeros.
This project bridge preserves the rational critical-strip orders in an entire
function to which Jensen's inequality can be applied independently of the trace.
-/

open Complex Filter MeromorphicOn Set
open scoped Topology

namespace Masullo

/-- Clear the two poles of the completed zeta function, without dividing by two. -/
@[expose] public noncomputable def entireZeta (s : ℂ) : ℂ :=
  1 + s * (s - 1) * completedRiemannZeta₀ s

public theorem entireZeta_analyticOnNhd : AnalyticOnNhd ℂ entireZeta univ := by
  have hconst : Differentiable ℂ (fun _ : ℂ ↦ (1 : ℂ)) := differentiable_const 1
  have hd : Differentiable ℂ entireZeta := hconst.add
    ((differentiable_id.mul (differentiable_id.sub hconst)).mul differentiable_completedZeta₀)
  exact fun s _ ↦ hd.analyticAt s

@[simp] public theorem entireZeta_one : entireZeta 1 = 1 := by
  simp [entireZeta]

private theorem entireZeta_eq_mul_riemannZeta {s : ℂ} (hpos : 0 < s.re) (hlt : s.re < 1) :
    entireZeta s = s * (s - 1) * Gammaℝ s * riemannZeta s := by
  have h₀ : s ≠ 0 := by rintro rfl; simp at hpos
  have h₁ : s ≠ 1 := by rintro rfl; simp at hlt
  have hγ := Gammaℝ_ne_zero_of_re_pos hpos
  rw [riemannZeta_def_of_ne_zero h₀, mul_assoc (s * (s - 1)), mul_div_cancel₀ _ hγ,
    completedRiemannZeta_eq, entireZeta]
  field_simp [sub_ne_zero.mpr h₁, sub_ne_zero.mpr h₁.symm]
  ring

/-- The analytic, nonvanishing factor relating the two functions on the open strip
has order zero. The comparison is of germs, not just of values. -/
public theorem analyticOrderAt_entireZeta_eq {s : ℂ} (hpos : 0 < s.re) (hlt : s.re < 1) :
    analyticOrderAt entireZeta s = analyticOrderAt riemannZeta s := by
  let g : ℂ → ℂ := fun z ↦ z * (z - 1) * Gammaℝ z
  have hgZ : entireZeta =ᶠ[𝓝 s] g * riemannZeta := by
    have hstrip : IsOpen {z : ℂ | 0 < z.re ∧ z.re < 1} :=
      (isOpen_lt continuous_const continuous_re).inter (isOpen_lt continuous_re continuous_const)
    filter_upwards [hstrip.mem_nhds ⟨hpos, hlt⟩] with z hz
    exact entireZeta_eq_mul_riemannZeta hz.1 hz.2
  have h₀ : s ≠ 0 := by rintro rfl; simp at hpos
  have h₁ : s ≠ 1 := by rintro rfl; simp at hlt
  have hγ := Gammaℝ_ne_zero_of_re_pos hpos
  have hγan : AnalyticAt ℂ Gammaℝ s := by
    have han := (differentiable_Gammaℝ_inv.analyticAt s).inv (inv_ne_zero hγ)
    change AnalyticAt ℂ (fun z ↦ ((Gammaℝ z)⁻¹)⁻¹) s at han
    simpa using han
  have hgan : AnalyticAt ℂ g s := (analyticAt_id.mul (analyticAt_id.sub analyticAt_const)).mul hγan
  have hg₀ : g s ≠ 0 := mul_ne_zero (mul_ne_zero h₀ (sub_ne_zero.mpr h₁)) hγ
  have hζ := (differentiableOn_riemannZeta.analyticOnNhd isOpen_compl_singleton) s h₁
  rw [analyticOrderAt_congr hgZ, analyticOrderAt_mul hgan hζ,
    hgan.analyticOrderAt_eq_zero.mpr hg₀, zero_add]

/-- An infinite order would force the entire function to vanish identically,
contradicting its value at one. -/
public theorem analyticOrderAt_entireZeta_ne_top (s : ℂ) :
    analyticOrderAt entireZeta s ≠ ⊤ := by
  intro h
  have hzero : entireZeta =ᶠ[𝓝 s] 0 := analyticOrderAt_eq_top.mp h
  have heq := entireZeta_analyticOnNhd.eqOn_zero_of_preconnected_of_eventuallyEq_zero
    isPreconnected_univ (mem_univ s) hzero (mem_univ (1 : ℂ))
  simp at heq

/-- The natural multiplicity of a distinct zero in the open critical strip. -/
public noncomputable def zetaZeroOrder (ρ : criticalStripZetaZeros) : ℕ :=
  (analyticOrderAt riemannZeta (ρ : ℂ)).toNat

public theorem zetaZeroOrder_pos (ρ : criticalStripZetaZeros) : 0 < zetaZeroOrder ρ := by
  obtain ⟨hzero, hpos, hlt⟩ := mem_criticalStripZetaZeros.mp ρ.property
  have h₁ : (ρ : ℂ) ≠ 1 := by intro h; simp [h] at hlt
  have hζ := (differentiableOn_riemannZeta.analyticOnNhd isOpen_compl_singleton) (ρ : ℂ) h₁
  refine ENat.toNat_pos (fun h ↦ hζ.analyticOrderAt_eq_zero.mp h hzero) ?_
  rw [← analyticOrderAt_entireZeta_eq hpos hlt]
  exact analyticOrderAt_entireZeta_ne_top _

/-- The natural multiplicity loses no information about the finite analytic order. -/
public theorem zetaZeroOrder_cast_eq (ρ : criticalStripZetaZeros) :
    (zetaZeroOrder ρ : ℕ∞) = analyticOrderAt riemannZeta (ρ : ℂ) := by
  obtain ⟨_, hpos, hlt⟩ := mem_criticalStripZetaZeros.mp ρ.property
  have horder := analyticOrderAt_entireZeta_eq hpos hlt
  unfold zetaZeroOrder
  rw [← horder]
  exact ENat.natCast_toNat (analyticOrderAt_entireZeta_ne_top _)

/-- At each critical-strip zero inside the counting set, the divisor used by
Jensen's inequality records the actual zeta multiplicity. -/
public theorem divisor_entireZeta_apply {U : Set ℂ} (ρ : criticalStripZetaZeros)
    (hρ : (ρ : ℂ) ∈ U) : divisor entireZeta U (ρ : ℂ) = (zetaZeroOrder ρ : ℤ) := by
  have han : AnalyticOnNhd ℂ entireZeta U := entireZeta_analyticOnNhd.mono (subset_univ _)
  obtain ⟨_, hpos, hlt⟩ := mem_criticalStripZetaZeros.mp ρ.property
  have horder := analyticOrderAt_entireZeta_eq hpos hlt
  rw [han.divisor_apply hρ, horder, ← zetaZeroOrder_cast_eq ρ]
  simp

end Masullo
