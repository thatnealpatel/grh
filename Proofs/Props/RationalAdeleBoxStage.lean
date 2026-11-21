module

public import Theorems.RationalAdeleBoxSumPoisson
import Lemmas.RationalAdeleResidues
import Mathlib.Tactic.FieldSimp

/-! # Box coordinates for a finite rational adelic stage

The stages in the proof of Proposition 2.1.3.2, pp. 69–70, have separate
support and invariance subgroups. Here we use the rational pair
`M ℤ̂ ⊂ M⁻¹ ℤ̂`. We work on the full adeles, with no restriction on their
real coordinate. Neither cofinality nor the LF topology enters this result.
-/

open NumberField IsDedekindDomain Set
open scoped SchwartzMap

namespace Masullo

local notation "A" => AdeleRing (𝓞 ℚ) ℚ
local notation "J" => IdeleGroup (𝓞 ℚ) ℚ
local notation "W" => rationalIntegralAdeles
local notation "ι" => algebraMap ℚ A

/-- The inverse image of the support subgroup `M⁻¹ ℤ̂` on the full adeles. -/
@[expose] public def rationalAdeleStageSupport (M : ℕ) : Set A :=
  {x | (M : A) * x ∈ W}

/-- The cylinder over the coset `j/M + M ℤ̂`, with unrestricted real coordinate. -/
@[expose] public noncomputable def rationalAdeleStageCell (M : ℕ) (j : Fin (M ^ 2)) : Set A :=
  {x | ι (M : ℚ)⁻¹ * x - ι ((j.val : ℚ) / (M : ℚ)^2) ∈ W}

private theorem clear_stage_scale {M : ℕ} (hM : 0 < M) (x : A) :
    ι ((M ^ 2 : ℕ) : ℚ) * (ι (M : ℚ)⁻¹ * x) = (M : A) * x := by
  have hMq : (M : ℚ) ≠ 0 := by exact_mod_cast hM.ne'
  rw [← mul_assoc, ← map_mul, Nat.cast_pow, ← map_natCast ι M]
  congr 2
  field_simp

private theorem mem_cell_iff {M : ℕ} (x : A) (j : Fin (M ^ 2)) :
    x ∈ rationalAdeleStageCell M j ↔
      ι (M : ℚ)⁻¹ * x - ι ((j.val : ℚ) / (↑(M ^ 2 : ℕ) : ℚ)) ∈ W := by
  rw [Nat.cast_pow]; rfl

/-- A cell lies in the support cylinder. -/
public theorem rationalAdeleStageCell_subset_support {M : ℕ} (hM : 0 < M) (j : Fin (M ^ 2)) :
    rationalAdeleStageCell M j ⊆ rationalAdeleStageSupport M := by
  intro x hx
  change (M : A) * x ∈ W
  rw [← clear_stage_scale hM]
  exact rationalAdele_residue_mem _ ((mem_cell_iff x j).mp hx)

/-- Exactly one of the `M²` cylinders lies over each point of the support
stage, and none meets its complement. -/
public theorem mem_rationalAdeleStageSupport_iff_existsUnique_cell {M : ℕ} (hM : 0 < M) (x : A) :
    x ∈ rationalAdeleStageSupport M ↔ ∃! j, x ∈ rationalAdeleStageCell M j := by
  constructor
  · intro hx
    change (M : A) * x ∈ W at hx
    rw [← clear_stage_scale hM] at hx
    obtain ⟨j, hj⟩ := rationalAdele_residue_exists (by positivity : 0 < M ^ 2) _ hx
    exact ⟨j, (mem_cell_iff x j).mpr hj, fun k hk ↦
      rationalAdele_residue_unique _ _ ((mem_cell_iff x k).mp hk) hj⟩
  · rintro ⟨j, hj, _⟩
    exact rationalAdeleStageCell_subset_support hM j hj

private noncomputable def stageScale (M : ℕ) (hM : 0 < M) : J where
  val := (1, (ι (M : ℚ)).2)
  inv := (1, (ι (M : ℚ)⁻¹).2)
  val_inv := by
    have hMq : (M : ℚ) ≠ 0 := by exact_mod_cast hM.ne'
    refine Prod.ext (mul_one 1) ?_
    change (ι (M : ℚ) * ι (M : ℚ)⁻¹).2 = _
    rw [← map_mul, mul_inv_cancel₀ hMq, map_one]
  inv_val := by
    have hMq : (M : ℚ) ≠ 0 := by exact_mod_cast hM.ne'
    refine Prod.ext (mul_one 1) ?_
    change (ι (M : ℚ)⁻¹ * ι (M : ℚ)).2 = _
    rw [← map_mul, inv_mul_cancel₀ hMq, map_one]

/-- A cell indicator times an arbitrary real Schwartz factor is a translated
adelic box. For each cell the center and scale are independent of the factor;
the real coordinate is unchanged. -/
public theorem exists_rationalAdeleBox_eq_stageCell {M : ℕ} (hM : 0 < M) (j : Fin (M ^ 2)) :
    ∃ (a : A) (g : J), rationalAdeleReal a = 0 ∧ rationalAdeleReal (g : A) = 1 ∧
      ∀ b : 𝓢(ℝ, ℂ), rationalAdeleBox b a g = (rationalAdeleStageCell M j).indicator
        (fun x ↦ b (rationalAdeleReal x)) := by
  let q : ℚ := (j.val : ℚ) / M
  let a : A := (0, (ι q).2)
  let g := stageScale M hM
  let e := InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace
  refine ⟨a, g, ?_, ?_, fun b ↦ ?_⟩
  · rw [rationalAdeleReal_apply]
    exact map_zero e
  · rw [rationalAdeleReal_apply]
    exact map_one e
  · funext x
    let y : A := (↑g⁻¹ : A) * (x - a)
    have hreal : rationalAdeleReal y = rationalAdeleReal x := by
      rw [rationalAdeleReal_apply y]
      change e (1 * (x.1 Rat.infinitePlace - 0)) = _
      rw [sub_zero, one_mul, rationalAdeleReal_apply]
    have hfin : y ∈ W ↔ x ∈ rationalAdeleStageCell M j := by
      have hq : (M : ℚ)⁻¹ * q = (j.val : ℚ) / (M : ℚ)^2 := by
        simp [q, div_eq_mul_inv, pow_two, mul_left_comm]
      have hf : y.2 = (ι (M : ℚ)⁻¹ * x - ι ((j.val : ℚ) / (M : ℚ)^2)).2 := by
        change (ι (M : ℚ)⁻¹ * (x - ι q)).2 = _
        rw [mul_sub, ← map_mul (ι), hq]
      change (∀ v : HeightOneSpectrum (𝓞 ℚ), y.2 v ∈ v.adicCompletionIntegers ℚ) ↔ _
      rw [hf]
      rfl
    change rationalAdeleUnramified b y = _
    rw [rationalAdeleUnramified]
    by_cases hy : y ∈ W
    · rw [indicator_of_mem hy, indicator_of_mem (hfin.mp hy), hreal]
    · rw [indicator_of_notMem hy, indicator_of_notMem (mt hfin.mpr hy)]

/-- The fixed boxes reconstruct one Schwartz profile per coset on this stage,
with zero extension off the support. Neither centers nor scales vary with the
profiles, so bounded coordinate sets can be used directly in the box estimates. -/
public theorem exists_rationalAdeleBoxSum_stage_coordinates {M : ℕ} (hM : 0 < M) :
    ∃ (a : Fin (M ^ 2) → A) (g : Fin (M ^ 2) → J),
      ∀ b : Fin (M ^ 2) → 𝓢(ℝ, ℂ),
        (∀ j x, x ∈ rationalAdeleStageCell M j →
          rationalAdeleBoxSum Finset.univ (fun _ ↦ 1) b a g x = b j (rationalAdeleReal x)) ∧
        (∀ x, x ∉ rationalAdeleStageSupport M →
          rationalAdeleBoxSum Finset.univ (fun _ ↦ 1) b a g x = 0) := by
  classical
  choose a g _ _ hbox using exists_rationalAdeleBox_eq_stageCell hM
  refine ⟨a, g, fun b ↦ ⟨?_, ?_⟩⟩
  · intro j x hx
    have hj : ∀ k, x ∈ rationalAdeleStageCell M k → k = j := by
      obtain ⟨i, _, hi⟩ := (mem_rationalAdeleStageSupport_iff_existsUnique_cell hM x).mp
        (rationalAdeleStageCell_subset_support hM j hx)
      exact fun k hk ↦ (hi k hk).trans (hi j hx).symm
    simp only [rationalAdeleBoxSum, one_mul, hbox]
    rw [Finset.sum_eq_single_of_mem j (Finset.mem_univ _) (fun k _ hkj ↦
      indicator_of_notMem (fun hk ↦ hkj (hj k hk)) _), indicator_of_mem hx]
  · intro x hx
    simp only [rationalAdeleBoxSum, one_mul, hbox]
    exact Finset.sum_eq_zero fun j _ ↦
      indicator_of_notMem (fun hj ↦ hx (rationalAdeleStageCell_subset_support hM j hj)) _

end Masullo
