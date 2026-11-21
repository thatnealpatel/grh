module

public import Props.RationalAdeleSchwartzBounded
public import Theorems.RationalAdeleThetaTails

/-! # Uniform theta estimates on the rational Schwartz LF space

Theorem 2.2.3.4(1)–(5), pp. 82–86, for the rational adelic model.
A bounded family has one common stage, so the fixed-box estimates apply
with bounded sets of real profiles. This argument does not identify the
LF topology with the manuscript's tensor topology.
-/

open Bornology NumberField
open scoped SchwartzMap

namespace Masullo

local notation "A" => AdeleRing (𝓞 ℚ) ℚ
local notation "J" => IdeleGroup (𝓞 ℚ) ℚ
local notation "C" => IdeleClassGroup (𝓞 ℚ) ℚ
local notation "E" => RationalAdeleSchwartzLF
local notation "L" => rationalAdeleFactorialLevel
local notation "Profiles" n => Fin ((L n) ^ 2) → 𝓢(ℝ, ℂ)

/-- Boundedness fixes the stage and box geometry before the function is chosen. -/
private theorem exists_bounded_box_profiles {B : Set E} (hB : IsVonNBounded ℂ B) :
    ∃ (n : ℕ) (a : Fin ((L n) ^ 2) → A) (g : Fin ((L n) ^ 2) → J) (P : Set (Profiles n)),
      IsVonNBounded ℂ P ∧ ∀ f ∈ B, ∃ b ∈ P,
        f.toUnion.val = rationalAdeleBoxSum Finset.univ (fun _ ↦ 1) b a g := by
  obtain ⟨n, P, hP, h⟩ := rationalAdeleLF_bounded_iff.mp hB
  obtain ⟨a, g, hbox⟩ :=
    exists_rationalAdeleStageCoordinates_symm_eq_boxSum (rationalAdeleFactorialLevel_pos n)
  refine ⟨n, a, g, P, hP, ?_⟩
  rw [h]
  rintro _ ⟨b, hb, rfl⟩
  exact ⟨b, hb, by rw [rationalAdeleLFAssembly_toUnion, rationalAdeleFactorialStageAssembly_val,
    hbox]⟩

set_option linter.concreteInstances false
variable [MeasurableSpace A] [BorelSpace A]
  [MeasurableSpace (A ⧸ rationalDiagonal)] [BorelSpace (A ⧸ rationalDiagonal)]

/-- A single constant works for both tails of every family bounded in the
rational LF space. At small norm the estimate retains both zero modes. -/
public theorem rationalAdeleLF_uniform_theta_tails (m : ℕ) {B : Set E} (hB : IsVonNBounded ℂ B) :
    ∃ K : ℝ, 0 < K ∧ ∀ f ∈ B,
      (∀ d : C, 1 ≤ ideleClassNorm d →
        ‖rationalAdeleClassTheta f.toUnion.val d‖ ≤ K / ideleClassNorm d ^ m) ∧
      (∀ d : C, ideleClassNorm d ≤ 1 →
        ‖rationalAdeleClassTheta f.toUnion.val d -
          (ideleClassNorm d)⁻¹ • rationalAdeleFourier f.toUnion.val 0 + f.toUnion.val 0‖ ≤ K * ideleClassNorm d ^ m) := by
  obtain ⟨n, a, g, P, hP, hbox⟩ := exists_bounded_box_profiles hB
  obtain ⟨K, hK, ht⟩ := rationalAdeleBoxSum_uniform_theta_tails Finset.univ (fun _ ↦ 1) a g m
    (B := fun j ↦ (fun b : Profiles n ↦ b j) '' P)
    (fun j _ ↦ hP.image (ContinuousLinearMap.proj j))
  refine ⟨K, hK, fun f hf ↦ ?_⟩
  obtain ⟨b, hb, he⟩ := hbox f hf
  rw [he]
  exact ht b fun j _ ↦ ⟨b, hb, rfl⟩

/-- On the subfamily with both zero modes zero, one log-norm decay constant
works on the entire rational idele class group. -/
public theorem rationalAdeleLF_uniform_theta_log_bound (m : ℕ) {B : Set E}
    (hB : IsVonNBounded ℂ B) :
    ∃ K : ℝ, 0 < K ∧ ∀ f ∈ B, f.toUnion.val 0 = 0 → rationalAdeleFourier f.toUnion.val 0 = 0 →
      ∀ d : C, ‖rationalAdeleClassTheta f.toUnion.val d‖ ≤
        K * Real.exp (-(m : ℝ) * |Real.log (ideleClassNorm d)|) := by
  obtain ⟨n, a, g, P, hP, hbox⟩ := exists_bounded_box_profiles hB
  obtain ⟨K, hK, ht⟩ := rationalAdeleBoxSum_uniform_theta_log_bound Finset.univ (fun _ ↦ 1) a g m
    (B := fun j ↦ (fun b : Profiles n ↦ b j) '' P)
    (fun j _ ↦ hP.image (ContinuousLinearMap.proj j))
  refine ⟨K, hK, fun f hf ↦ ?_⟩
  obtain ⟨b, hb, he⟩ := hbox f hf
  rw [he]
  exact ht b fun j _ ↦ ⟨b, hb, rfl⟩

end Masullo
