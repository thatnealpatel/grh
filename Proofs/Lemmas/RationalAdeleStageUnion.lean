module

public import Props.RationalAdeleStageTransition

/-! # Algebraic union and sampling of rational adelic stages

Factorial levels make the divisibility filtration into an increasing
sequence. Sampling on a representative line is defined on the entire
union, regardless of whether the function belongs to the sampled stage.
Continuity here is tested only on the individual product Schwartz stages.
-/

open NumberField IsDedekindDomain
open scoped SchwartzMap

namespace Masullo

local notation "A" => AdeleRing (𝓞 ℚ) ℚ

/-- The positive factorial levels form a chain cofinal for divisibility. -/
@[expose] public def rationalAdeleFactorialLevel (n : ℕ) : ℕ := (n + 1).factorial

local notation "L" => rationalAdeleFactorialLevel
local notation "Stage" n => rationalAdeleSchwartzStage (L n)
local notation "Profiles" n => Fin ((L n) ^ 2) → 𝓢(ℝ, ℂ)

public theorem rationalAdeleFactorialLevel_pos (n : ℕ) : 0 < L n :=
  Nat.factorial_pos _

public theorem rationalAdeleFactorialLevel_dvd {m n : ℕ} (h : m ≤ n) : L m ∣ L n :=
  Nat.factorial_dvd_factorial (Nat.succ_le_succ h)

local notation "pos" => rationalAdeleFactorialLevel_pos

/-- The algebraic union of the factorial stages, with no topology specified. -/
@[expose] public noncomputable def rationalAdeleSchwartzStageUnion : Submodule ℂ (A → ℂ) :=
  ⨆ n : ℕ, Stage n

local notation "U" => rationalAdeleSchwartzStageUnion

public theorem mem_rationalAdeleSchwartzStageUnion {f : A → ℂ} :
    f ∈ U ↔ ∃ n, f ∈ Stage n := by
  apply Submodule.mem_iSup_of_directed
  intro m n
  exact ⟨max m n,
    rationalAdeleSchwartzStage_mono (rationalAdeleFactorialLevel_dvd (le_max_left m n)),
    rationalAdeleSchwartzStage_mono (rationalAdeleFactorialLevel_dvd (le_max_right m n))⟩

/-- The union contains every positive integer stage, not only the factorial levels. -/
public theorem rationalAdeleSchwartzStage_le_union {M : ℕ} (hM : 0 < M) :
    rationalAdeleSchwartzStage M ≤ U :=
  (rationalAdeleSchwartzStage_mono (Nat.dvd_factorial hM (Nat.le_succ M))).trans
    (le_iSup (fun n ↦ Stage n) M)

/-- Assemble the tuple into a function in the algebraic union. -/
public noncomputable def rationalAdeleFactorialStageAssembly (n : ℕ) :
    (Profiles n) →ₗ[ℂ] U :=
  (Submodule.inclusion (le_iSup (fun n ↦ Stage n) n)).comp
    (rationalAdeleStageCoordinates (pos n)).symm.toLinearMap

public theorem rationalAdeleFactorialStageAssembly_val (n : ℕ) (b : Profiles n) :
    (rationalAdeleFactorialStageAssembly n b).val =
      ((rationalAdeleStageCoordinates (pos n)).symm b).val := by rfl

private theorem exists_sample (n : ℕ) (f : U) (j : Fin ((L n) ^ 2)) :
    ∃ b : 𝓢(ℝ, ℂ), ∀ t, b t = f.val (rationalAdeleAt t (rationalAdeleStageRepresentative (L n) j)) := by
  obtain ⟨m, hm⟩ := mem_rationalAdeleSchwartzStageUnion.mp f.property
  exact hm.2.2 _

private noncomputable def sample (n : ℕ) (f : U) (j : Fin ((L n) ^ 2)) : 𝓢(ℝ, ℂ) :=
  (exists_sample n f j).choose

private theorem sample_apply (n : ℕ) (f : U) (j : Fin ((L n) ^ 2)) (t : ℝ) :
    sample n f j t = f.val (rationalAdeleAt t (rationalAdeleStageRepresentative (L n) j)) :=
  (exists_sample n f j).choose_spec t

/-- Read the Schwartz profiles on the given factorial level's representative
lines. This is well-defined for every member of the union. -/
public noncomputable def rationalAdeleFactorialStageRead (n : ℕ) : U →ₗ[ℂ] (Profiles n) where
  toFun := sample n
  map_add' f g := by
    funext j
    ext t
    simp only [sample_apply, Submodule.coe_add, Pi.add_apply, add_apply]
  map_smul' c f := by
    funext j
    ext t
    simp only [sample_apply, Submodule.coe_smul, Pi.smul_apply, smul_apply,
      RingHom.id_apply]

public theorem rationalAdeleFactorialStageRead_apply (n : ℕ) (f : U)
    (j : Fin ((L n) ^ 2)) (t : ℝ) : rationalAdeleFactorialStageRead n f j t =
      f.val (rationalAdeleAt t (rationalAdeleStageRepresentative (L n) j)) :=
  sample_apply n f j t

/-- If the function is in stage `n`, reading at `n` is its coordinate map. -/
public theorem rationalAdeleFactorialStageRead_eq_coordinates (n : ℕ) (f : U)
    (hf : f.val ∈ Stage n) :
    rationalAdeleFactorialStageRead n f = rationalAdeleStageCoordinates (pos n) ⟨f.val, hf⟩ := by
  funext j
  ext t
  rw [rationalAdeleFactorialStageRead_apply, rationalAdeleStageCoordinates_apply]

/-- On every source stage, sampling at any other stage is continuous:
Transition to a common finer stage and restrict to the target lines. -/
public theorem rationalAdeleFactorialStageRead_continuous_on_stage (m n : ℕ) :
    Continuous (fun b : Profiles m ↦
      rationalAdeleFactorialStageRead n (rationalAdeleFactorialStageAssembly m b)) := by
  let k := max m n
  have hm : L m ∣ L k := rationalAdeleFactorialLevel_dvd (le_max_left m n)
  have hn : L n ∣ L k := rationalAdeleFactorialLevel_dvd (le_max_right m n)
  suffices he : ∀ b : Profiles m,
      rationalAdeleFactorialStageRead n (rationalAdeleFactorialStageAssembly m b) =
        rationalAdeleStageRetract (pos k) hn
          (rationalAdeleStageTransition (pos m) (pos k) hm b) by
    simp only [he]
    exact (rationalAdeleStageRetract (pos k) hn).continuous.comp
      (rationalAdeleStageTransition (pos m) (pos k) hm).continuous
  intro b
  funext j
  ext t
  rw [rationalAdeleStageRetract_apply, rationalAdeleFactorialStageRead_apply,
    rationalAdeleFactorialStageAssembly_val,
    rationalAdeleStageTransition_eq_coordinates, rationalAdeleStageCoordinates_apply,
    rationalAdeleStageRepresentative_oldIndex (pos n) (pos k) hn, Submodule.inclusion_apply]

end Masullo
