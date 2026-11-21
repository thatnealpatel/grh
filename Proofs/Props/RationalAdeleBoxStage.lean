module

public import Theorems.RationalAdeleBoxSumPoisson
public import Lemmas.RationalAdeleBoxCofinality
import Lemmas.RationalAdeleResidues
import Mathlib.Tactic.FieldSimp

/-! # Box coordinates for a finite rational adelic stage

The stages in the proof of Proposition 2.1.3.2, pp. 69–70, have separate
support and invariance subgroups. Here we use the rational pair
`M ℤ̂ ⊂ M⁻¹ ℤ̂`. We work on the full adeles, with no restriction on their
real coordinate. The rational pairs are cofinal among the compact-open
pairs of finite adeles. No identification of LF topologies is needed.
-/

open NumberField IsDedekindDomain Set
open scoped SchwartzMap

namespace Masullo

local notation "F" => FiniteAdeleRing (𝓞 ℚ) ℚ
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

/-- At the finite places this idele is the diagonal `M`; at the real place it is one. -/
@[expose] public noncomputable def rationalAdeleStageScale (M : ℕ) (hM : 0 < M) : J where
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

/-- The center of a cell box has real coordinate zero and finite coordinate `j/M`. -/
@[expose] public noncomputable def rationalAdeleStageCenter (M : ℕ) (j : Fin (M ^ 2)) : A :=
  (0, (ι ((j.val : ℚ) / M)).2)

@[simp] public theorem rationalAdeleReal_stageCenter (M : ℕ) (j : Fin (M ^ 2)) :
    rationalAdeleReal (rationalAdeleStageCenter M j) = 0 := by
  rw [rationalAdeleReal_apply]
  exact map_zero _

@[simp] public theorem rationalAdeleReal_stageScale (M : ℕ) (hM : 0 < M) :
    rationalAdeleReal (rationalAdeleStageScale M hM : A) = 1 := by
  rw [rationalAdeleReal_apply]
  exact map_one _

-- Integrality only depends on the finite coordinate, where the box calculation takes place.
private theorem mem_integral_iff_fin {x y : A} (h : x.2 = y.2) : x ∈ W ↔ y ∈ W := by
  change x.2 ∈ rationalFiniteIntegralAdeles ↔ y.2 ∈ rationalFiniteIntegralAdeles
  rw [h]

private theorem stageCell_box_mem {M : ℕ} (hM : 0 < M) (j : Fin (M ^ 2)) (x : A) :
    (↑(rationalAdeleStageScale M hM)⁻¹ : A) * (x - rationalAdeleStageCenter M j) ∈ W ↔
      x ∈ rationalAdeleStageCell M j := by
  let q : ℚ := (j.val : ℚ) / M
  have hq : (M : ℚ)⁻¹ * q = (j.val : ℚ) / (M : ℚ)^2 := by
    simp [q, div_eq_mul_inv, pow_two, mul_left_comm]
  apply mem_integral_iff_fin
  let ρ := algebraMap ℚ F
  change ρ (M : ℚ)⁻¹ * (x.2 - ρ q) = ρ (M : ℚ)⁻¹ * x.2 - ρ ((j.val : ℚ) / (M : ℚ)^2)
  rw [mul_sub, ← map_mul ρ, hq]

/-- A cell indicator times a real Schwartz factor is the canonical translated box. -/
public theorem rationalAdeleBox_stageCell {M : ℕ} (hM : 0 < M) (j : Fin (M ^ 2))
    (b : 𝓢(ℝ, ℂ)) : rationalAdeleBox b (rationalAdeleStageCenter M j)
      (rationalAdeleStageScale M hM) = (rationalAdeleStageCell M j).indicator
        (fun x ↦ b (rationalAdeleReal x)) := by
  let a := rationalAdeleStageCenter M j
  let g := rationalAdeleStageScale M hM
  let e := InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace
  funext x
  let y : A := (↑g⁻¹ : A) * (x - a)
  have hreal : rationalAdeleReal y = rationalAdeleReal x := by
    rw [rationalAdeleReal_apply y]
    change e (1 * (x.1 Rat.infinitePlace - 0)) = _
    rw [sub_zero, one_mul, rationalAdeleReal_apply]
  have hfin : y ∈ W ↔ x ∈ rationalAdeleStageCell M j := stageCell_box_mem hM j x
  change rationalAdeleUnramified b y = _
  rw [rationalAdeleUnramified]
  by_cases hy : y ∈ W
  · rw [indicator_of_mem hy, indicator_of_mem (hfin.mp hy), hreal]
  · rw [indicator_of_notMem hy, indicator_of_notMem (mt hfin.mpr hy)]

/-- The fixed boxes reconstruct one Schwartz profile per coset on this stage,
with zero extension off the support. Neither centers nor scales vary with the
profiles, so bounded coordinate sets can be used directly in the box estimates. -/
public theorem rationalAdeleBoxSum_stage_coordinates {M : ℕ} (hM : 0 < M)
    (b : Fin (M ^ 2) → 𝓢(ℝ, ℂ)) :
    let f := rationalAdeleBoxSum Finset.univ (fun _ ↦ 1) b (rationalAdeleStageCenter M)
      (fun _ ↦ rationalAdeleStageScale M hM)
    (∀ j x, x ∈ rationalAdeleStageCell M j → f x = b j (rationalAdeleReal x)) ∧
      (∀ x, x ∉ rationalAdeleStageSupport M → f x = 0) := by
  classical
  refine ⟨?_, ?_⟩
  · intro j x hx
    have hj : ∀ k, x ∈ rationalAdeleStageCell M k → k = j := by
      obtain ⟨i, _, hi⟩ := (mem_rationalAdeleStageSupport_iff_existsUnique_cell hM x).mp
        (rationalAdeleStageCell_subset_support hM j hx)
      exact fun k hk ↦ (hi k hk).trans (hi j hx).symm
    simp only [rationalAdeleBoxSum, one_mul, rationalAdeleBox_stageCell]
    rw [Finset.sum_eq_single_of_mem j (Finset.mem_univ _) (fun k _ hkj ↦
      indicator_of_notMem (fun hk ↦ hkj (hj k hk)) _), indicator_of_mem hx]
  · intro x hx
    simp only [rationalAdeleBoxSum, one_mul, rationalAdeleBox_stageCell]
    exact Finset.sum_eq_zero fun j _ ↦
      indicator_of_notMem (fun hj ↦ hx (rationalAdeleStageCell_subset_support hM j hj)) _

/-- Existential form of the canonical box assembly, recording its real geometry. -/
public theorem exists_rationalAdeleBoxSum_stage_coordinates_real {M : ℕ} (hM : 0 < M) :
    ∃ (a : Fin (M ^ 2) → A) (g : Fin (M ^ 2) → J),
      (∀ j, rationalAdeleReal (a j) = 0) ∧ (∀ j, rationalAdeleReal (g j : A) = 1) ∧
      ∀ b : Fin (M ^ 2) → 𝓢(ℝ, ℂ),
        (∀ j x, x ∈ rationalAdeleStageCell M j →
          rationalAdeleBoxSum Finset.univ (fun _ ↦ 1) b a g x = b j (rationalAdeleReal x)) ∧
        (∀ x, x ∉ rationalAdeleStageSupport M →
          rationalAdeleBoxSum Finset.univ (fun _ ↦ 1) b a g x = 0) :=
  ⟨_, _, rationalAdeleReal_stageCenter M, fun _ ↦ rationalAdeleReal_stageScale M hM,
    rationalAdeleBoxSum_stage_coordinates hM⟩

/-- Fixed-geometry assembly, forgetting the real coordinates of the boxes. -/
public theorem exists_rationalAdeleBoxSum_stage_coordinates {M : ℕ} (hM : 0 < M) :
    ∃ (a : Fin (M ^ 2) → A) (g : Fin (M ^ 2) → J),
      ∀ b : Fin (M ^ 2) → 𝓢(ℝ, ℂ),
        (∀ j x, x ∈ rationalAdeleStageCell M j →
          rationalAdeleBoxSum Finset.univ (fun _ ↦ 1) b a g x = b j (rationalAdeleReal x)) ∧
        (∀ x, x ∉ rationalAdeleStageSupport M →
          rationalAdeleBoxSum Finset.univ (fun _ ↦ 1) b a g x = 0) := by
  obtain ⟨a, g, _, _, h⟩ := exists_rationalAdeleBoxSum_stage_coordinates_real hM
  exact ⟨a, g, h⟩

/-- The pair `M ℤ̂ ⊂ M⁻¹ ℤ̂` can accommodate any prescribed support subgroup
`K` and invariance subgroup `H`, in particular when `H ⊆ K`.
Compactness bounds denominators in `K`;
openness shrinks the translations into `H`. -/
public theorem exists_rationalAdeleBoxStage_cofinal (H K : AddSubgroup F)
    (hH : IsOpen (H : Set F)) (hK : IsCompact (K : Set F)) :
    ∃ M : ℕ, 0 < M ∧
      ((M : F) * ·) '' (rationalFiniteIntegralAdeles : Set F) ⊆ H ∧
      (K : Set F) ⊆ ((M : F) * ·) ⁻¹' (rationalFiniteIntegralAdeles : Set F) := by
  obtain ⟨N, hN, hi⟩ := exists_rationalFinite_invariance_bound (hH.mem_nhds H.zero_mem)
  obtain ⟨D, hD, hs⟩ := exists_rationalFinite_support_bound hK
  refine ⟨N * D, mul_pos hN hD, ?_, hs.trans (rationalFinite_support_mono (dvd_mul_left D N))⟩
  rintro _ ⟨x, hx, rfl⟩
  apply hi
  refine ⟨(D : F) * x, ?_, ?_⟩
  · change (D : F) * x ∈ rationalFiniteIntegralAdeles
    simpa only [nsmul_eq_mul] using rationalFiniteIntegralAdeles.nsmul_mem hx D
  · change (N : F) * ((D : F) * x) = ((N * D : ℕ) : F) * x
    rw [Nat.cast_mul, mul_assoc]

/-- Both finite stages are compact and open. The invariance stage is contained
in the support stage. Multiplication by the positive rational `M` is an
additive homeomorphism of the finite adeles. -/
public theorem rationalAdeleBoxStage_isCompact_isOpen {M : ℕ} (hM : 0 < M) :
    let H := ((M : F) * ·) '' (rationalFiniteIntegralAdeles : Set F)
    let K := ((M : F) * ·) ⁻¹' (rationalFiniteIntegralAdeles : Set F)
    IsCompact H ∧ IsOpen H ∧ IsCompact K ∧ IsOpen K ∧ H ⊆ K := by
  have hMq : (M : ℚ) ≠ 0 := by exact_mod_cast hM.ne'
  have hu : IsUnit (M : F) := by
    simpa only [map_natCast] using hMq.isUnit.map (algebraMap ℚ F)
  obtain ⟨u, hu⟩ := hu
  let e := (ContinuousAddEquiv.mulLeft u).toHomeomorph
  have he : (e : F → F) = ((M : F) * ·) := by
    funext x
    change (u : F) * x = (M : F) * x
    rw [hu]
  dsimp only
  rw [← he]
  refine ⟨e.isCompact_image.mpr isCompact_rationalFiniteIntegralAdeles,
    e.isOpenMap _ isOpen_rationalFiniteIntegralAdeles,
    e.isCompact_preimage.mpr isCompact_rationalFiniteIntegralAdeles,
    isOpen_rationalFiniteIntegralAdeles.preimage e.continuous, ?_⟩
  rw [he]
  rintro _ ⟨x, hx, rfl⟩
  change (M : F) * ((M : F) * x) ∈ rationalFiniteIntegralAdeles
  simpa only [nsmul_eq_mul] using
    rationalFiniteIntegralAdeles.nsmul_mem (rationalFiniteIntegralAdeles.nsmul_mem hx M) M

/-- The finite support subgroup pulls back to the support cylinder used for the
box coordinates. -/
public theorem rationalAdeleStageSupport_eq_preimage (M : ℕ) :
    rationalAdeleStageSupport M =
      Prod.snd ⁻¹' (((M : F) * ·) ⁻¹' (rationalFiniteIntegralAdeles : Set F)) := rfl

end Masullo
