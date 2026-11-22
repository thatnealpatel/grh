module

public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem

import Mathlib.Topology.Algebra.Group.Units

/-! # Norm, logarithms, and compact windows on Archimedean adele units -/

open NumberField Set Topology
open NumberField.Units.dirichletUnitTheorem (w₀ logSpace)

namespace Masullo

variable {K : Type*} [Field K] [NumberField K]

local notation "A∞" => InfiniteAdeleRing K
local notation "U∞" => (InfiniteAdeleRing K)ˣ

/-- The normalized Archimedean product, with multiplicity one at real places and two at
complex places. -/
public noncomputable def archimedeanNorm : U∞ →* ℝ where
  toFun g := ‖(g : A∞)‖
  map_one' := by
    change (∏ v : InfinitePlace K, ‖(1 : v.Completion)‖ ^ v.mult) = 1
    simp
  map_mul' g h := by
    change (∏ v : InfinitePlace K, ‖(g : A∞) v * (h : A∞) v‖ ^ v.mult) = _
    simp only [InfiniteAdeleRing.norm_def, norm_mul, mul_pow, Finset.prod_mul_distrib]

public theorem archimedeanNorm_apply (g : U∞) :
    archimedeanNorm g = ∏ v : InfinitePlace K, ‖(g : A∞) v‖ ^ v.mult := by
  unfold archimedeanNorm
  rfl

/-- Masullo's (A.2.3.2), with the topology induced from the units of the infinite adele ring. -/
public noncomputable def archimedeanNormOne : Subgroup U∞ :=
  (archimedeanNorm (K := K)).ker

public theorem mem_archimedeanNormOne (g : U∞) :
    g ∈ archimedeanNormOne ↔ archimedeanNorm g = 1 := Iff.rfl

local notation "G∞" => archimedeanNormOne (K := K)

private noncomputable def archimedeanDiagonal : (𝓞 K)ˣ →* U∞ :=
  (Units.map (algebraMap K A∞).toMonoidHom).comp
    (Units.map (algebraMap (𝓞 K) K).toMonoidHom)

/-- The Archimedean image of a global integral unit belongs to the norm-one group. -/
public noncomputable def archimedeanDiagonalUnit : (𝓞 K)ˣ →* G∞ :=
  (archimedeanDiagonal (K := K)).codRestrict G∞ fun u ↦ by
    apply (mem_archimedeanNormOne _).mpr
    change ‖algebraMap K A∞ (u : K)‖ = 1
    rw [InfiniteAdeleRing.coe_norm_eq_abs_norm, NumberField.Units.norm K u, Rat.cast_one]

public theorem coe_archimedeanDiagonalUnit (u : (𝓞 K)ˣ) :
    (archimedeanDiagonalUnit u : U∞) =
      Units.map (algebraMap K A∞).toMonoidHom
        (Units.map (algebraMap (𝓞 K) K).toMonoidHom u) := by
  unfold archimedeanDiagonalUnit archimedeanDiagonal
  rfl

omit [NumberField K] in
private theorem local_ne_zero (g : U∞) (v : InfinitePlace K) : (g : A∞) v ≠ 0 :=
  ((Pi.isUnit_iff.mp g.isUnit) v).ne_zero

omit [NumberField K] in
private theorem continuous_local_norm (v : InfinitePlace K) :
    Continuous (fun g : U∞ ↦ ‖(g : A∞) v‖) :=
  ((continuous_apply v).comp Units.continuous_val).norm

private theorem continuous_archimedeanNorm : Continuous (archimedeanNorm (K := K)) := by
  change Continuous (fun g : U∞ ↦ archimedeanNorm g)
  simp only [archimedeanNorm_apply]
  exact continuous_finsetProd _ fun v _ ↦ (continuous_local_norm v).pow _

/-- Masullo's (A.2.3.4) in full coordinates, using the normalized norm at each place. -/
private noncomputable def archimedeanLog (g : U∞) (v : InfinitePlace K) : ℝ :=
  v.mult * Real.log ‖(g : A∞) v‖

omit [NumberField K] in
private theorem archimedeanLog_mul (g h : U∞) (v : InfinitePlace K) :
    archimedeanLog (g * h) v = archimedeanLog g v + archimedeanLog h v := by
  change v.mult * Real.log ‖(g : A∞) v * (h : A∞) v‖ = _
  rw [norm_mul, Real.log_mul (norm_ne_zero_iff.mpr (local_ne_zero g v))
    (norm_ne_zero_iff.mpr (local_ne_zero h v)), mul_add]
  rfl

private theorem archimedeanLog_sum (g : G∞) :
    ∑ v : InfinitePlace K, archimedeanLog (g : U∞) v = 0 := by
  have hg := (mem_archimedeanNormOne (g : U∞)).mp g.property
  rw [archimedeanNorm_apply] at hg
  have hlog := congrArg Real.log hg
  rw [Real.log_prod (fun v _ ↦ pow_ne_zero _ (norm_ne_zero_iff.mpr (local_ne_zero g v))),
    Real.log_one] at hlog
  simpa only [archimedeanLog, Real.log_pow] using hlog

/-- The logarithm (A.2.3.3) in coordinates on the sum-zero hyperplane, obtained by dropping
Mathlib's distinguished place. -/
public noncomputable def archimedeanDroppedLog (g : G∞) : logSpace K :=
  fun v ↦ archimedeanLog (g : U∞) v.1

public theorem archimedeanDroppedLog_apply (g : G∞) (v : {v : InfinitePlace K // v ≠ w₀}) :
    archimedeanDroppedLog g v = v.1.mult * Real.log ‖((g : U∞) : A∞) v.1‖ := by
  unfold archimedeanDroppedLog archimedeanLog
  rfl

public theorem archimedeanDroppedLog_diagonalUnit (u : (𝓞 K)ˣ) :
    archimedeanDroppedLog (archimedeanDiagonalUnit u) =
      NumberField.Units.logEmbedding K (Additive.ofMul u) := by
  funext v
  change v.1.mult * Real.log ‖algebraMap K A∞ (u : K) v.1‖ =
    v.1.mult * Real.log (v.1 (u : K))
  rw [InfiniteAdeleRing.algebraMap_apply, AbsoluteValue.Completion.norm_coe]
  rfl

public theorem archimedeanDroppedLog_inv_mul (a g : G∞) :
    archimedeanDroppedLog (a⁻¹ * g) = archimedeanDroppedLog g - archimedeanDroppedLog a := by
  funext v
  have h : archimedeanLog (a : U∞) v.1 + archimedeanLog (↑(a⁻¹ * g) : U∞) v.1 =
      archimedeanLog (g : U∞) v.1 := by
    rw [← archimedeanLog_mul, ← Subgroup.coe_mul, mul_inv_cancel_left]
  change archimedeanLog (↑(a⁻¹ * g) : U∞) v.1 =
    archimedeanLog (g : U∞) v.1 - archimedeanLog (a : U∞) v.1
  linarith

private theorem continuous_archimedeanDroppedLog :
    Continuous (archimedeanDroppedLog (K := K)) := by
  refine continuous_pi fun v ↦ continuous_const.mul ?_
  refine continuous_iff_continuousAt.mpr fun g ↦ ?_
  exact ((continuous_local_norm v.1).comp continuous_subtype_val).continuousAt.log
    (norm_ne_zero_iff.mpr (local_ne_zero (g : U∞) v.1))

/-- At the omitted place, the weighted log is minus the sum of the retained weighted logs. -/
private noncomputable def restoreLog (v : InfinitePlace K) (x : logSpace K) : ℝ := by
  classical
  exact if hv : v ≠ w₀ then x ⟨v, hv⟩ else -∑ w, x w

private theorem continuous_restoreLog (v : InfinitePlace K) :
    Continuous (restoreLog (K := K) v) := by
  classical
  unfold restoreLog
  split
  · exact continuous_apply _
  · exact (continuous_finsetSum _ fun w _ ↦ continuous_apply w).neg

private theorem restoreLog_droppedLog (v : InfinitePlace K) (g : G∞) :
    restoreLog v (archimedeanDroppedLog g) = archimedeanLog (g : U∞) v := by
  classical
  unfold restoreLog
  split
  · rfl
  · rename_i hv
    have hv' : v = w₀ := not_ne_iff.mp hv
    subst v
    have hs := archimedeanLog_sum g
    rw [Fintype.sum_eq_add_sum_subtype_ne _ w₀] at hs
    change -(∑ w : {w : InfinitePlace K // w ≠ w₀}, archimedeanLog (g : U∞) w.1) = _
    linarith

private theorem exp_restoreLog (v : InfinitePlace K) (g : G∞) :
    Real.exp (restoreLog v (archimedeanDroppedLog g) / v.mult) = ‖((g : U∞) : A∞) v‖ := by
  rw [restoreLog_droppedLog, archimedeanLog, mul_comm, mul_div_cancel_right₀ _
    InfinitePlace.mult_coe_ne_zero]
  exact Real.exp_log (norm_pos_iff.mpr (local_ne_zero (g : U∞) v))

omit [NumberField K] in
private theorem norm_local_inv (v : InfinitePlace K) (g : U∞) :
    ‖((g⁻¹ : U∞) : A∞) v‖ = ‖(g : A∞) v‖⁻¹ := by
  have h : (g : A∞) v * ((g⁻¹ : U∞) : A∞) v = 1 :=
    congrArg (fun x : A∞ ↦ x v) (Units.mul_inv g)
  rw [← inv_eq_of_mul_eq_one_right h, norm_inv]

private theorem exists_local_bounds (v : InfinitePlace K) {W : Set (logSpace K)}
    (hW : IsCompact W) : ∃ R : ℝ, ∀ g : G∞, archimedeanDroppedLog g ∈ W →
    ‖((g : U∞) : A∞) v‖ ≤ R ∧ ‖(((g : U∞)⁻¹ : U∞) : A∞) v‖ ≤ R := by
  let f : logSpace K → ℝ := fun x ↦ Real.exp (restoreLog v x / v.mult)
  have hlog : Continuous (fun x ↦ restoreLog v x / (v.mult : ℝ)) :=
    (continuous_restoreLog v).div_const _
  have hf : Continuous f := Real.continuous_exp.comp hlog
  have hfinv : Continuous (fun x ↦ (f x)⁻¹) :=
    hf.inv₀ fun _ ↦ (Real.exp_pos _).ne'
  obtain ⟨R, hR⟩ := ((hW.image hf).union (hW.image hfinv)).bddAbove
  refine ⟨R, fun g hg ↦ ⟨?_, ?_⟩⟩
  · rw [← exp_restoreLog v g]
    exact hR (Or.inl (mem_image_of_mem f hg))
  · rw [norm_local_inv, ← exp_restoreLog v g]
    exact hR (Or.inr (mem_image_of_mem (fun x ↦ (f x)⁻¹) hg))

omit [NumberField K] in
private theorem isCompact_local_closedBall (v : InfinitePlace K) (R : ℝ) :
    IsCompact (Metric.closedBall (0 : v.Completion) R) := by
  let f := InfinitePlace.Completion.extensionEmbedding v
  have hf : Isometry f := InfinitePlace.Completion.isometry_extensionEmbedding v
  have hclosed : IsClosedEmbedding f :=
    ⟨hf.isEmbedding, InfinitePlace.Completion.isClosed_image_extensionEmbedding v⟩
  rw [← hf.preimage_closedBall]
  exact hclosed.isCompact_preimage (isCompact_closedBall (f 0) R)

/-- A compact dropped-log window pulls back to a compact subset of the norm-one subgroup.
The bounds for both the value and its inverse are needed for the actual units topology. -/
public theorem isCompact_preimage_archimedeanDroppedLog {W : Set (logSpace K)}
    (hW : IsCompact W) : IsCompact (archimedeanDroppedLog ⁻¹' W) := by
  classical
  choose R hR using fun v ↦ exists_local_bounds (K := K) v hW
  let B : Set A∞ := Set.univ.pi fun v ↦ Metric.closedBall (0 : v.Completion) (R v)
  have hB : IsCompact B := isCompact_univ_pi fun v ↦ isCompact_local_closedBall v (R v)
  have hG : IsClosed (G∞ : Set U∞) := by
    change IsClosed ((archimedeanNorm (K := K)).ker : Set U∞)
    exact isClosed_singleton.preimage continuous_archimedeanNorm
  let : T1Space A∞ :=
    show T1Space ((v : InfinitePlace K) → v.Completion) from inferInstance
  have he : IsClosedEmbedding (Units.embedProduct A∞ ∘ ((↑) : G∞ → U∞)) :=
    Units.isClosedEmbedding_embedProduct.comp hG.isClosedEmbedding_subtypeVal
  have hbox : IsCompact ((Units.embedProduct A∞ ∘ ((↑) : G∞ → U∞)) ⁻¹'
      (B ×ˢ (MulOpposite.opHomeomorph.symm ⁻¹' B))) :=
    he.isCompact_preimage (hB.prod (MulOpposite.opHomeomorph.symm.isCompact_preimage.mpr hB))
  refine hbox.of_isClosed_subset (hW.isClosed.preimage continuous_archimedeanDroppedLog) ?_
  intro g hg
  change ((g : U∞) : A∞) ∈ B ∧ (((g : U∞)⁻¹ : U∞) : A∞) ∈ B
  exact ⟨fun v _ ↦ mem_closedBall_zero_iff.mpr (hR v g hg).1,
    fun v _ ↦ mem_closedBall_zero_iff.mpr (hR v g hg).2⟩

end Masullo
