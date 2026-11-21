module

public import Props.RationalAdeleStageCoordinates

/-! # Split inclusions of rational Schwartz stages

For `M ∣ N`, the level-`N` stage has weaker support and invariance
conditions than level `M`. In the coordinates of the two stages, the
underlying inclusion repeats old profiles and inserts zeros. Restricting
to the old representative lines is a continuous linear retraction.
This is the rational product-coordinate version of the split transitions
in the proof of Proposition 2.1.3.2, pp. 69–70. No topology on the union
of the stages is asserted here.
-/

open NumberField IsDedekindDomain
open scoped SchwartzMap

namespace Masullo

local notation "F" => FiniteAdeleRing (𝓞 ℚ) ℚ
local notation "Profiles" M => Fin (M ^ 2) → 𝓢(ℝ, ℂ)

/-- Increasing the level by divisibility enlarges the support and shrinks
the subgroup of finite translations fixing the stage functions. -/
public theorem rationalAdeleSchwartzStage_mono {M N : ℕ} (h : M ∣ N) :
    rationalAdeleSchwartzStage M ≤ rationalAdeleSchwartzStage N := by
  intro f hf
  refine ⟨fun x hx ↦ hf.1 x ?_, fun x z hz ↦ ?_, hf.2.2⟩
  · exact fun hx' ↦ hx (rationalFinite_support_mono h hx')
  · obtain ⟨d, rfl⟩ := h
    have hd : (d : F) * z ∈ rationalFiniteIntegralAdeles := by
      simpa only [nsmul_eq_mul] using rationalFiniteIntegralAdeles.nsmul_mem hz d
    simpa only [Nat.cast_mul, mul_assoc] using hf.2.1 x ((d : F) * z) hd

private noncomputable def transitionLinear {M N : ℕ} (hM : 0 < M) (hN : 0 < N) (h : M ∣ N) :
    (Profiles M) →ₗ[ℂ] (Profiles N) :=
  (rationalAdeleStageCoordinates hN).toLinearMap.comp
    ((Submodule.inclusion (rationalAdeleSchwartzStage_mono h)).comp
      (rationalAdeleStageCoordinates hM).symm.toLinearMap)

private theorem transitionLinear_apply {M N : ℕ} (hM : 0 < M) (hN : 0 < N) (h : M ∣ N)
    (b : Profiles M) (k : Fin (N ^ 2)) (t : ℝ) : transitionLinear hM hN h b k t =
      ((rationalAdeleStageCoordinates hM).symm b).val
        (rationalAdeleAt t (rationalAdeleStageRepresentative N k)) :=
  rationalAdeleStageCoordinates_apply hN _ k t

private theorem transitionLinear_apply_of_mem_cell {M N : ℕ} (hM : 0 < M) (hN : 0 < N)
    (h : M ∣ N) (b : Profiles M) {j : Fin (M ^ 2)} {k : Fin (N ^ 2)}
    (hk : rationalAdeleAt 0 (rationalAdeleStageRepresentative N k) ∈ rationalAdeleStageCell M j) :
    transitionLinear hM hN h b k = b j := by
  ext t
  let x := rationalAdeleAt t (rationalAdeleStageRepresentative N k)
  have hx : x ∈ rationalAdeleStageCell M j := by
    rw [mem_rationalAdeleStageCell_iff hM] at hk ⊢
    simpa only [x, rationalAdeleAt_finite] using hk
  let f := (rationalAdeleStageCoordinates hM).symm b
  have hb : rationalAdeleStageCoordinates hM f = b :=
    (rationalAdeleStageCoordinates hM).apply_symm_apply b
  rw [transitionLinear_apply, ← rationalAdeleStageCoordinates_eq_on_cell hM f hx, hb,
    rationalAdeleReal_at]

private theorem transitionLinear_apply_of_notMem_support {M N : ℕ} (hM : 0 < M) (hN : 0 < N)
    (h : M ∣ N) (b : Profiles M) {k : Fin (N ^ 2)}
    (hk : rationalAdeleAt 0 (rationalAdeleStageRepresentative N k) ∉ rationalAdeleStageSupport M) :
    transitionLinear hM hN h b k = 0 := by
  ext t
  rw [transitionLinear_apply]
  apply ((rationalAdeleStageCoordinates hM).symm b).property.1
  simpa only [rationalAdeleStageSupport_eq_preimage, Set.mem_preimage, rationalAdeleAt_finite] using hk

/-- The actual stage inclusion in product Schwartz coordinates. At a fine
coordinate outside the coarse support the output is zero; inside it, the
output is the profile at the unique containing coarse cell. -/
public noncomputable def rationalAdeleStageTransition {M N : ℕ}
    (hM : 0 < M) (hN : 0 < N) (h : M ∣ N) : (Profiles M) →L[ℂ] (Profiles N) where
  toLinearMap := transitionLinear hM hN h
  cont := by
    apply continuous_pi
    intro k
    change Continuous (fun b : Profiles M ↦ transitionLinear hM hN h b k)
    by_cases hk : rationalAdeleAt 0 (rationalAdeleStageRepresentative N k) ∈ rationalAdeleStageSupport M
    · obtain ⟨j, hj, _⟩ := (mem_rationalAdeleStageSupport_iff_existsUnique_cell hM _).mp hk
      simp only [transitionLinear_apply_of_mem_cell hM hN h _ hj]
      exact continuous_apply j
    · simp only [transitionLinear_apply_of_notMem_support hM hN h _ hk]
      exact continuous_const

/-- A fine line inside a coarse cell copies that cell's entire Schwartz profile. -/
public theorem rationalAdeleStageTransition_apply_of_mem_cell {M N : ℕ}
    (hM : 0 < M) (hN : 0 < N) (h : M ∣ N) (b : Profiles M)
    {j : Fin (M ^ 2)} {k : Fin (N ^ 2)}
    (hk : rationalAdeleAt 0 (rationalAdeleStageRepresentative N k) ∈ rationalAdeleStageCell M j) :
    rationalAdeleStageTransition hM hN h b k = b j :=
  transitionLinear_apply_of_mem_cell hM hN h b hk

/-- A fine line outside the coarse support has the zero Schwartz profile. -/
public theorem rationalAdeleStageTransition_apply_of_notMem_support {M N : ℕ}
    (hM : 0 < M) (hN : 0 < N) (h : M ∣ N) (b : Profiles M) {k : Fin (N ^ 2)}
    (hk : rationalAdeleAt 0 (rationalAdeleStageRepresentative N k) ∉ rationalAdeleStageSupport M) :
    rationalAdeleStageTransition hM hN h b k = 0 :=
  transitionLinear_apply_of_notMem_support hM hN h b hk

/-- Re-expressing a coarse function at the finer level agrees with the
continuous transition in product Schwartz coordinates. -/
public theorem rationalAdeleStageTransition_eq_coordinates {M N : ℕ} (hM : 0 < M) (hN : 0 < N) (h : M ∣ N)
    (b : Profiles M) :
    rationalAdeleStageTransition hM hN h b = rationalAdeleStageCoordinates hN
      (Submodule.inclusion (rationalAdeleSchwartzStage_mono h)
        ((rationalAdeleStageCoordinates hM).symm b)) := by rfl

/-- The transition changes only the coordinates, not the underlying adelic
function. -/
public theorem rationalAdeleStageTransition_assemble {M N : ℕ}
    (hM : 0 < M) (hN : 0 < N) (h : M ∣ N) (b : Profiles M) :
    ((rationalAdeleStageCoordinates hN).symm (rationalAdeleStageTransition hM hN h b)).val =
      ((rationalAdeleStageCoordinates hM).symm b).val := by
  simp only [rationalAdeleStageTransition_eq_coordinates, LinearEquiv.symm_apply_apply, Submodule.inclusion_apply]

/-- The fine label for the old representative `j/M` is `(N/M)j`. -/
public def rationalAdeleStageOldIndex {M N : ℕ} (hN : 0 < N) (h : M ∣ N)
    (j : Fin (M ^ 2)) : Fin (N ^ 2) :=
  ⟨(N / M) * j.val, by
    have hdM := Nat.div_mul_cancel h
    have hd : 0 < N / M := Nat.pos_of_ne_zero fun hz ↦ hN.ne' (by simpa [hz] using hdM.symm)
    calc
      (N / M) * j.val < (N / M) * M ^ 2 := Nat.mul_lt_mul_of_pos_left j.isLt hd
      _ = N * M := by rw [pow_two, ← mul_assoc, hdM]
      _ ≤ N ^ 2 := by simpa only [pow_two] using Nat.mul_le_mul_left N (Nat.le_of_dvd hN h)⟩

/-- The selected fine representative is exactly the old finite adele. -/
public theorem rationalAdeleStageRepresentative_oldIndex {M N : ℕ}
    (hM : 0 < M) (hN : 0 < N) (h : M ∣ N) (j : Fin (M ^ 2)) :
    rationalAdeleStageRepresentative N (rationalAdeleStageOldIndex hN h j) =
      rationalAdeleStageRepresentative M j := by
  have hdM : (↑(N / M) : ℚ) * (M : ℚ) = (N : ℚ) := by exact_mod_cast Nat.div_mul_cancel h
  have hn : (N : ℚ) ≠ 0 := by exact_mod_cast hN.ne'
  have hm : (M : ℚ) ≠ 0 := by exact_mod_cast hM.ne'
  rw [rationalAdeleStageRepresentative, rationalAdeleStageRepresentative]
  congr 1
  change (↑((N / M) * j.val) : ℚ) / (N : ℚ) = (j.val : ℚ) / (M : ℚ)
  apply (div_eq_div_iff hn hm).mpr
  rw [Nat.cast_mul, ← hdM]
  ring

/-- Restrict the fine tuple to the old representative lines. This map is
continuous in the product of Schwartz topologies. -/
public def rationalAdeleStageRetract {M N : ℕ} (hN : 0 < N) (h : M ∣ N) :
    (Profiles N) →L[ℂ] (Profiles M) where
  toFun b j := b (rationalAdeleStageOldIndex hN h j)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  cont := continuous_pi fun j ↦ continuous_apply (rationalAdeleStageOldIndex hN h j)

public theorem rationalAdeleStageRetract_apply {M N : ℕ} (hN : 0 < N) (h : M ∣ N)
    (b : Profiles N) (j : Fin (M ^ 2)) :
    rationalAdeleStageRetract hN h b j = b (rationalAdeleStageOldIndex hN h j) := by rfl

/-- Restriction to the old lines is a left inverse to the actual inclusion. -/
public theorem rationalAdeleStageRetract_leftInverse {M N : ℕ}
    (hM : 0 < M) (hN : 0 < N) (h : M ∣ N) :
    Function.LeftInverse (rationalAdeleStageRetract hN h) (rationalAdeleStageTransition hM hN h) := by
  intro b
  funext j
  apply rationalAdeleStageTransition_apply_of_mem_cell hM hN h b
  rw [rationalAdeleStageRepresentative_oldIndex hM hN h]
  exact rationalAdeleStageRepresentative_mem_cell hM j 0

/-- The fine product Schwartz topology induces the coarse product Schwartz
topology along the stage inclusion. -/
public theorem rationalAdeleStageTransition_isEmbedding {M N : ℕ}
    (hM : 0 < M) (hN : 0 < N) (h : M ∣ N) :
    Topology.IsEmbedding (rationalAdeleStageTransition hM hN h) :=
  (rationalAdeleStageRetract_leftInverse hM hN h).isEmbedding
    (rationalAdeleStageRetract hN h).continuous (rationalAdeleStageTransition hM hN h).continuous

end Masullo
