module

public import Lemmas.RationalAdeleStageSampling
import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.Topology.Piecewise
import Mathlib.Topology.UniformSpace.HeineCantor

/-! # Uniform sampling of continuous rational adelic tests

Sampling on rational finite cells preserves a single compact bound for
support, even as the stage grows. This is the finite-coordinate step
in a density proof for the rational version of (D.1.1.10), p. 747.
-/

open NumberField IsDedekindDomain Filter Set Topology

namespace Masullo

local notation "A" => AdeleRing (𝓞 ℚ) ℚ
local notation "F" => FiniteAdeleRing (𝓞 ℚ) ℚ
local notation "W" => rationalFiniteIntegralAdeles

/-- Assemble arbitrary real profiles on the disjoint finite cells of a stage. -/
public noncomputable def rationalAdeleAssembleProfiles (M : ℕ)
    (b : Fin (M ^ 2) → ℝ → ℂ) (x : A) : ℂ :=
  ∑ j, (rationalAdeleStageCell M j).indicator (fun y ↦ b j (rationalAdeleReal y)) x

public theorem rationalAdeleAssembleProfiles_on_cell {M : ℕ} (hM : 0 < M)
    (b : Fin (M ^ 2) → ℝ → ℂ) {x : A} {j : Fin (M ^ 2)} (hx : x ∈ rationalAdeleStageCell M j) :
    rationalAdeleAssembleProfiles M b x = b j (rationalAdeleReal x) := by
  obtain ⟨k, _, hk⟩ := (mem_rationalAdeleStageSupport_iff_existsUnique_cell hM x).mp
    (rationalAdeleStageCell_subset_support hM j hx)
  unfold rationalAdeleAssembleProfiles
  rw [Finset.sum_eq_single_of_mem j (Finset.mem_univ j), indicator_of_mem hx]
  intro i _ hij
  exact indicator_of_notMem (fun hi ↦ hij ((hk i hi).trans (hk j hx).symm)) _

public theorem rationalAdeleAssembleProfiles_off_stage {M : ℕ} (hM : 0 < M)
    (b : Fin (M ^ 2) → ℝ → ℂ) {x : A} (hx : x ∉ rationalAdeleStageSupport M) :
    rationalAdeleAssembleProfiles M b x = 0 :=
  Finset.sum_eq_zero fun j _ ↦ indicator_of_notMem
    (fun hj ↦ hx (rationalAdeleStageCell_subset_support hM j hj)) _

/-- Each cell is clopen: It is a continuous affine preimage of the open
additive subgroup of integral-finite adeles. -/
public theorem isClopen_rationalAdeleStageCell (M : ℕ) (j : Fin (M ^ 2)) :
    IsClopen (rationalAdeleStageCell M j) := by
  have h : IsClopen (rationalIntegralAdeles : Set A) :=
    ⟨rationalIntegralAdeles.isClosed_of_isOpen isOpen_rationalIntegralAdeles,
      isOpen_rationalIntegralAdeles⟩
  exact h.preimage ((continuous_const.mul continuous_id).sub continuous_const)

/-- Clopen cells have no boundary across which the profiles must match. -/
public theorem continuous_rationalAdeleAssembleProfiles {M : ℕ} {b : Fin (M ^ 2) → ℝ → ℂ}
    (hb : ∀ j, Continuous (b j)) : Continuous (rationalAdeleAssembleProfiles M b) := by
  classical
  unfold rationalAdeleAssembleProfiles
  apply continuous_finsetSum
  intro j _
  rw [← Set.piecewise_eq_indicator]
  refine ((hb j).comp continuous_rationalAdeleReal).piecewise ?_ continuous_const
  simp [(isClopen_rationalAdeleStageCell M j).frontier_eq]

private theorem exists_small_finite_shift {f : A → ℂ} (hc : Continuous f)
    (hs : HasCompactSupport f) {ε : ℝ} (hε : 0 < ε) :
    ∃ U ∈ 𝓝 (0 : F), ∀ x y : A, y - x ∈ (fun z : F ↦ ((0, z) : A)) '' U →
      ‖f y - f x‖ < ε := by
  let := IsTopologicalAddGroup.rightUniformSpace A
  have h := uniformContinuous_iff_eventually.mp (hs.uniformContinuous_of_continuous hc)
  obtain ⟨V, hV, hclose⟩ := h _ (Metric.dist_mem_uniformity hε)
  refine ⟨(fun z : F ↦ ((0, z) : A)) ⁻¹' V,
    (continuous_const.prodMk continuous_id).continuousAt.preimage_mem_nhds hV, ?_⟩
  rintro x y ⟨z, hz, hzy⟩
  rw [← dist_eq_norm, dist_comm]
  apply @hclose ⟨x, y⟩
  change y + -x ∈ V
  rw [← sub_eq_add_neg, ← hzy]
  exact hz

/-- Every compactly supported continuous adelic test can be approximated
uniformly by taking its representative-line values on a sufficiently fine
stage. Both the input and all these approximants vanish off one compact
set, chosen before the tolerance. -/
public theorem exists_rationalAdeleStage_uniform_sample {f : A → ℂ} (hc : Continuous f)
    (hs : HasCompactSupport f) :
    ∃ K : Set A, IsCompact K ∧ (∀ x, x ∉ K → f x = 0) ∧
      ∀ ε : ℝ, 0 < ε → ∃ (M : ℕ), 0 < M ∧
        let b := fun (j : Fin (M ^ 2)) (t : ℝ) ↦
          f (rationalAdeleAt t (rationalAdeleStageRepresentative M j))
        let g := rationalAdeleAssembleProfiles M b
        (∀ j, Continuous (b j) ∧ HasCompactSupport (b j)) ∧
          (∀ x, x ∉ K → g x = 0) ∧ ∀ x, ‖f x - g x‖ ≤ ε := by
  let C := Prod.fst '' tsupport f
  obtain ⟨D, hD, hDmem⟩ := exists_rationalFinite_support_bound (hs.image continuous_snd)
  let Kf := ((D : F) * ·) ⁻¹' (W : Set F)
  let K : Set A := C ×ˢ Kf
  have hK : IsCompact K := (hs.image continuous_fst).prod
    (rationalAdeleBoxStage_isCompact_isOpen hD).2.2.1
  have hsup : tsupport f ⊆ K := fun x hx ↦ ⟨mem_image_of_mem _ hx, hDmem (mem_image_of_mem _ hx)⟩
  have hzero : ∀ x, x ∉ K → f x = 0 := fun x hx ↦ image_eq_zero_of_notMem_tsupport
    (fun hx' ↦ hx (hsup hx'))
  refine ⟨K, hK, hzero, ?_⟩
  intro ε hε
  obtain ⟨U, hU, hclose⟩ := exists_small_finite_shift hc hs hε
  obtain ⟨N, hN, hNmem⟩ := exists_rationalFinite_invariance_bound hU
  let M := N * D
  have hM : 0 < M := mul_pos hN hD
  have hDK : K ⊆ rationalAdeleStageSupport M := fun x hx ↦
    rationalFinite_support_mono (dvd_mul_left D N) hx.2
  refine ⟨M, hM, ?_, ?_, ?_⟩
  · intro j
    refine ⟨hc.comp (continuous_rationalAdeleAt _), ?_⟩
    apply exists_compact_iff_hasCompactSupport.mp
    refine ⟨rationalAdeleReal '' tsupport f, hs.image continuous_rationalAdeleReal, ?_⟩
    intro t ht
    apply image_eq_zero_of_notMem_tsupport
    intro hy
    exact ht ⟨_, hy, rationalAdeleReal_at _ _⟩
  · intro x hx
    by_cases hstage : x ∈ rationalAdeleStageSupport M
    · obtain ⟨j, hj, _⟩ := (mem_rationalAdeleStageSupport_iff_existsUnique_cell hM x).mp hstage
      rw [rationalAdeleAssembleProfiles_on_cell hM _ hj]
      apply hzero
      intro hy
      obtain ⟨z, hz, he⟩ := (mem_rationalAdeleStageCell_iff hM j x).mp hj
      apply hx
      refine ⟨rationalAdeleAt_fst_real x _ ▸ hy.1, ?_⟩
      change (D : F) * x.2 ∈ W
      rw [he, mul_add]
      have hrep := hy.2
      rw [rationalAdeleAt_finite] at hrep
      exact rationalFiniteIntegralAdeles.add_mem hrep (by
        simpa only [nsmul_eq_mul] using
          rationalFiniteIntegralAdeles.nsmul_mem (rationalFiniteIntegralAdeles.nsmul_mem hz M) D)
    · exact rationalAdeleAssembleProfiles_off_stage hM _ hstage
  · intro x
    by_cases hstage : x ∈ rationalAdeleStageSupport M
    · obtain ⟨j, hj, _⟩ := (mem_rationalAdeleStageSupport_iff_existsUnique_cell hM x).mp hstage
      rw [rationalAdeleAssembleProfiles_on_cell hM _ hj]
      apply le_of_lt (hclose _ _ ?_)
      obtain ⟨z, hz, he⟩ := (mem_rationalAdeleStageCell_iff hM j x).mp hj
      have hzD : (D : F) * z ∈ W := by
        simpa only [nsmul_eq_mul] using rationalFiniteIntegralAdeles.nsmul_mem hz D
      have hshift : (M : F) * z ∈ U := hNmem ⟨_, hzD, by rw [Nat.cast_mul, mul_assoc]⟩
      refine ⟨_, hshift, Prod.ext ?_ ?_⟩
      · change 0 = x.1 - _
        rw [rationalAdeleAt_fst_real, sub_self]
      · change (M : F) * z = x.2 - (rationalAdeleAt _ _).2
        rw [rationalAdeleAt_finite, he, add_sub_cancel_left]
    · rw [rationalAdeleAssembleProfiles_off_stage hM _ hstage,
        hzero x (fun hx ↦ hstage (hDK hx)), sub_zero, norm_zero]
      exact hε.le

end Masullo
