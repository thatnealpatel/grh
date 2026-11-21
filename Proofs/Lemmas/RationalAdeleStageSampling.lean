module

public import Props.RationalAdeleBoxStage

/-! # Sampling and assembly on a fixed rational adelic stage -/

open NumberField IsDedekindDomain Set
open scoped SchwartzMap

namespace Masullo

local notation "F" => FiniteAdeleRing (𝓞 ℚ) ℚ
local notation "A" => AdeleRing (𝓞 ℚ) ℚ
local notation "W" => rationalFiniteIntegralAdeles
local notation "κ" => algebraMap ℚ F

private noncomputable def archEquiv : InfiniteAdeleRing ℚ ≃+* ℝ :=
  (RingEquiv.piUnique InfinitePlace.Completion).trans
    (InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace)

/-- Assemble a real coordinate and a rational finite adele. -/
public noncomputable def rationalAdeleAt (t : ℝ) (z : F) : A :=
  (archEquiv.symm t, z)

@[simp] public theorem rationalAdeleReal_at (t : ℝ) (z : F) :
    rationalAdeleReal (rationalAdeleAt t z) = t := by
  rw [rationalAdeleReal_apply]
  exact archEquiv.apply_symm_apply _

@[simp] public theorem rationalAdeleAt_finite (t : ℝ) (z : F) :
    (rationalAdeleAt t z).2 = z := by rw [rationalAdeleAt]

/-- The finite part of the representative `j/M` of a stage cell. -/
@[expose] public noncomputable def rationalAdeleStageRepresentative (M : ℕ)
    (j : Fin (M ^ 2)) : F := κ ((j.val : ℚ) / M)

/-- Membership in a stage cell means that the finite part differs from its
representative by an integral finite adele scaled by `M`. -/
public theorem mem_rationalAdeleStageCell_iff {M : ℕ} (hM : 0 < M)
    (j : Fin (M ^ 2)) (x : A) : x ∈ rationalAdeleStageCell M j ↔
      ∃ z ∈ W, x.2 = rationalAdeleStageRepresentative M j + (M : F) * z := by
  have hn : (M : ℚ) ≠ 0 := by exact_mod_cast hM.ne'
  have hu : κ (M : ℚ)⁻¹ * (M : F) = 1 := by
    rw [← map_natCast κ, ← map_mul, inv_mul_cancel₀ hn, map_one]
  have hq : (M : ℚ)⁻¹ * ((j.val : ℚ) / M) = (j.val : ℚ) / (M : ℚ)^2 := by
    simp [div_eq_mul_inv, pow_two, mul_left_comm]
  change (κ (M : ℚ)⁻¹ * x.2 - κ ((j.val : ℚ) / (M : ℚ)^2) ∈ W) ↔ _
  rw [← hq, map_mul, ← mul_sub]
  change κ (M : ℚ)⁻¹ * (x.2 - rationalAdeleStageRepresentative M j) ∈ W ↔ _
  constructor
  · intro hx
    refine ⟨_, hx, ?_⟩
    rw [← mul_assoc, mul_comm (M : F), hu, one_mul, add_sub_cancel]
  · rintro ⟨z, hz, hz'⟩
    rw [hz']
    rw [add_sub_cancel_left, ← mul_assoc, hu, one_mul]
    exact hz

private theorem representative_mem_cell {M : ℕ} (hM : 0 < M) (j : Fin (M ^ 2)) (t : ℝ) :
    rationalAdeleAt t (rationalAdeleStageRepresentative M j) ∈ rationalAdeleStageCell M j :=
  (mem_rationalAdeleStageCell_iff hM j _).mpr
    ⟨0, rationalFiniteIntegralAdeles.zero_mem, by simp⟩

private theorem cell_add_shift {M : ℕ} (hM : 0 < M) (j : Fin (M ^ 2)) (x : A)
    {z : F} (hz : z ∈ W) :
    x + rationalAdeleAt 0 ((M : F) * z) ∈ rationalAdeleStageCell M j ↔
      x ∈ rationalAdeleStageCell M j := by
  rw [mem_rationalAdeleStageCell_iff hM, mem_rationalAdeleStageCell_iff hM]
  change (∃ w ∈ W, x.2 + (M : F) * z = rationalAdeleStageRepresentative M j + (M : F) * w) ↔ _
  constructor
  · rintro ⟨w, hw, h⟩
    refine ⟨w - z, rationalFiniteIntegralAdeles.sub_mem hw hz, ?_⟩
    rw [mul_sub, ← add_sub_assoc, ← h, add_sub_cancel_right]
  · rintro ⟨w, hw, h⟩
    refine ⟨w + z, rationalFiniteIntegralAdeles.add_mem hw hz, ?_⟩
    rw [h, mul_add, add_assoc]

/-- An adelic stage consists of functions zero off `M⁻¹ ℤ̂` in the finite
coordinate, invariant under translations by the finite subgroup `M ℤ̂`,
and Schwartz in the real coordinate for each fixed finite adele. -/
@[expose] public noncomputable def rationalAdeleSchwartzStage (M : ℕ) : Submodule ℂ (A → ℂ) where
  carrier := {f | (∀ x, x ∉ rationalAdeleStageSupport M → f x = 0) ∧
    (∀ (x : A) (z : F), z ∈ W → f (x + rationalAdeleAt 0 ((M : F) * z)) = f x) ∧
    (∀ z : F, ∃ b : 𝓢(ℝ, ℂ), ∀ t, b t = f (rationalAdeleAt t z))}
  zero_mem' := ⟨fun _ _ ↦ rfl, fun _ _ _ ↦ rfl, fun _ ↦ ⟨0, fun _ ↦ rfl⟩⟩
  add_mem' := by
    rintro f g ⟨hf₀, hfi, hfs⟩ ⟨hg₀, hgi, hgs⟩
    refine ⟨fun x hx ↦ ?_, fun x z hz ↦ ?_, fun z ↦ ?_⟩
    · simp [hf₀ x hx, hg₀ x hx]
    · simp [hfi x z hz, hgi x z hz]
    · obtain ⟨b, hb⟩ := hfs z
      obtain ⟨c, hc⟩ := hgs z
      exact ⟨b + c, fun t ↦ by simp [hb t, hc t]⟩
  smul_mem' := by
    rintro a f ⟨hf₀, hfi, hfs⟩
    refine ⟨fun x hx ↦ ?_, fun x z hz ↦ ?_, fun z ↦ ?_⟩
    · simp [hf₀ x hx]
    · simp [hfi x z hz]
    · obtain ⟨b, hb⟩ := hfs z
      exact ⟨a • b, fun t ↦ by simp [hb t]⟩

private noncomputable def sample {M : ℕ} (f : rationalAdeleSchwartzStage M)
    (j : Fin (M ^ 2)) : 𝓢(ℝ, ℂ) :=
  (f.property.2.2 (rationalAdeleStageRepresentative M j)).choose

private theorem sample_apply {M : ℕ} (f : rationalAdeleSchwartzStage M) (j : Fin (M ^ 2)) (t : ℝ) :
    sample f j t = f.val (rationalAdeleAt t (rationalAdeleStageRepresentative M j)) :=
  (f.property.2.2 (rationalAdeleStageRepresentative M j)).choose_spec t

private theorem sample_eq_on_cell {M : ℕ} (hM : 0 < M) (f : rationalAdeleSchwartzStage M)
    {x : A} {j : Fin (M ^ 2)} (hx : x ∈ rationalAdeleStageCell M j) :
    sample f j (rationalAdeleReal x) = f.val x := by
  obtain ⟨z, hz, hx⟩ := (mem_rationalAdeleStageCell_iff hM j x).mp hx
  rw [sample_apply]
  have heq : rationalAdeleAt (rationalAdeleReal x) (rationalAdeleStageRepresentative M j) +
      rationalAdeleAt 0 ((M : F) * z) = x := by
    refine Prod.ext ?_ hx.symm
    rw [rationalAdeleReal_apply]
    change archEquiv.symm (archEquiv x.1) + archEquiv.symm 0 = x.1
    rw [map_zero, add_zero, archEquiv.symm_apply_apply]
  rw [← f.property.2.1 _ z hz, heq]

private theorem sample_injective {M : ℕ} (hM : 0 < M) :
    Function.Injective (sample (M := M)) := by
  intro f g heq
  apply Subtype.ext
  funext x
  by_cases hx : x ∈ rationalAdeleStageSupport M
  · obtain ⟨j, hj, _⟩ := (mem_rationalAdeleStageSupport_iff_existsUnique_cell hM x).mp hx
    rw [← sample_eq_on_cell hM f hj, ← sample_eq_on_cell hM g hj, heq]
  · rw [f.property.1 x hx, g.property.1 x hx]

private theorem assembled_mem {M : ℕ} (hM : 0 < M) (f : A → ℂ) (b : Fin (M ^ 2) → 𝓢(ℝ, ℂ))
    (hcell : ∀ j x, x ∈ rationalAdeleStageCell M j → f x = b j (rationalAdeleReal x))
    (hzero : ∀ x, x ∉ rationalAdeleStageSupport M → f x = 0) :
    f ∈ rationalAdeleSchwartzStage M := by
  refine ⟨hzero, fun x z hz ↦ ?_, fun z ↦ ?_⟩
  · by_cases hx : x ∈ rationalAdeleStageSupport M
    · obtain ⟨j, hj, _⟩ := (mem_rationalAdeleStageSupport_iff_existsUnique_cell hM x).mp hx
      rw [hcell j _ ((cell_add_shift hM j x hz).mpr hj), hcell j x hj]
      simp only [rationalAdeleReal_apply]
      change b j (archEquiv (x.1 + archEquiv.symm 0)) = b j (archEquiv x.1)
      rw [map_zero, add_zero]
    · rw [hzero x hx, hzero _]
      intro hy
      obtain ⟨j, hj, _⟩ := (mem_rationalAdeleStageSupport_iff_existsUnique_cell hM _).mp hy
      exact hx (rationalAdeleStageCell_subset_support hM j ((cell_add_shift hM j x hz).mp hj))
  · by_cases hx : rationalAdeleAt 0 z ∈ rationalAdeleStageSupport M
    · obtain ⟨j, hj, _⟩ := (mem_rationalAdeleStageSupport_iff_existsUnique_cell hM _).mp hx
      refine ⟨b j, fun t ↦ ?_⟩
      have ht : rationalAdeleAt t z ∈ rationalAdeleStageCell M j :=
        (mem_rationalAdeleStageCell_iff hM j _).mpr ((mem_rationalAdeleStageCell_iff hM j _).mp hj)
      rw [hcell j _ ht, rationalAdeleReal_at]
    · exact ⟨0, fun t ↦ (hzero (rationalAdeleAt t z) hx).symm⟩

/-- Sample each real Schwartz slice at its fixed finite representative. -/
public noncomputable def rationalAdeleStageSample (M : ℕ) :
    rationalAdeleSchwartzStage M →ₗ[ℂ] (Fin (M ^ 2) → 𝓢(ℝ, ℂ)) where
  toFun := sample
  map_add' := fun f g ↦ funext fun j ↦ SchwartzMap.ext fun t ↦ by
    rw [Pi.add_apply, add_apply, sample_apply, sample_apply, sample_apply]
    rfl
  map_smul' := fun a f ↦ funext fun j ↦ SchwartzMap.ext fun t ↦ by
    rw [RingHom.id_apply, Pi.smul_apply, smul_apply, sample_apply, sample_apply]
    rfl

public theorem rationalAdeleStageSample_apply {M : ℕ} (f : rationalAdeleSchwartzStage M)
    (j : Fin (M ^ 2)) (t : ℝ) :
    rationalAdeleStageSample M f j t =
      f.val (rationalAdeleAt t (rationalAdeleStageRepresentative M j)) :=
  sample_apply f j t

public theorem rationalAdeleStageSample_injective {M : ℕ} (hM : 0 < M) :
    Function.Injective (rationalAdeleStageSample M) := sample_injective hM

/-- If assembly has the prescribed values on each cell and vanishes off the
support, then it is a stage function with the prescribed samples. -/
public theorem exists_rationalAdeleStageSample_eq_of_assembled {M : ℕ} (hM : 0 < M)
    (f : A → ℂ) (b : Fin (M ^ 2) → 𝓢(ℝ, ℂ))
    (hcell : ∀ j x, x ∈ rationalAdeleStageCell M j → f x = b j (rationalAdeleReal x))
    (hzero : ∀ x, x ∉ rationalAdeleStageSupport M → f x = 0) :
    ∃ u : rationalAdeleSchwartzStage M, u.val = f ∧ rationalAdeleStageSample M u = b := by
  refine ⟨⟨f, assembled_mem hM f b hcell hzero⟩, rfl, ?_⟩
  funext j
  ext t
  rw [rationalAdeleStageSample_apply]
  exact (hcell j _ (representative_mem_cell hM j t)).trans
    (congrArg (b j) (rationalAdeleReal_at t _))

end Masullo
