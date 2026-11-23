module

public import Theorems.RationalThetaRadialCore
public import Theorems.RationalIdeleClassHaar
import Lemmas.RationalAdeleAffineIntegral
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Group.Integral

/-! # Finite-unit averaging of rational adelic theta

On a box stage, finite units act on the cells of `M⁻¹ ℤ̂ / M ℤ̂`. We average
through this finite permutation image, without imposing a topology on the
algebraic theta image. Pointwise on idele classes this mean agrees with
probability Haar averaging over the compact norm-one group.
-/

open NumberField IsDedekindDomain MeasureTheory
open scoped SchwartzMap

namespace Masullo

noncomputable section

local notation "A" => AdeleRing (𝓞 ℚ) ℚ
local notation "F" => FiniteAdeleRing (𝓞 ℚ) ℚ
local notation "C" => IdeleClassGroup (𝓞 ℚ) ℚ
local notation "E" => RationalAdeleSchwartzLF
local notation "W" => rationalFiniteIntegralAdeles
local notation "U" => RationalFiniteUnits
local notation "ι" => rationalFiniteUnitIdele
local notation "Θ[" f "]" => rationalAdeleClassTheta (Subtype.val (RationalAdeleSchwartzLF.toUnion f))

private def act (u : U) (x : A) : A := (ι u : A) * x

private theorem act_one (x : A) : act (1 : U) x = x := by simp [act]

private theorem act_mul (u v : U) (x : A) : act (u * v) x = act u (act v x) := by
  simp only [act, map_mul, Units.val_mul, mul_assoc]

private theorem act_real (u : U) (x : A) : rationalAdeleReal (act u x) = rationalAdeleReal x := by
  rw [rationalAdeleReal_apply, rationalAdeleReal_apply]
  change InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace
    (((ι u : A).1 * x.1) Rat.infinitePlace) = _
  rw [rationalFiniteUnitIdele_fst, one_mul]

private theorem finite_integral_mul (u : U) {z : F} (hz : z ∈ W) : (ι u : A).2 * z ∈ W := by
  intro v
  change (ι u : A).2 v * z v ∈ v.adicCompletionIntegers ℚ
  rw [rationalFiniteUnitIdele_apply_finite]
  exact (v.adicCompletionIntegers ℚ).mul_mem _ _ (u v).val.property (hz v)

private theorem act_mem_support (u : U) {M : ℕ} {x : A}
    (hx : x ∈ rationalAdeleStageSupport M) : act u x ∈ rationalAdeleStageSupport M := by
  change (M : F) * x.2 ∈ W at hx
  change (M : F) * ((ι u : A).2 * x.2) ∈ W
  rw [mul_left_comm]
  exact finite_integral_mul u hx

private theorem act_mem_support_iff (u : U) {M : ℕ} {x : A} :
    act u x ∈ rationalAdeleStageSupport M ↔ x ∈ rationalAdeleStageSupport M := by
  refine ⟨fun hx ↦ ?_, act_mem_support u⟩
  have h := act_mem_support u⁻¹ hx
  rwa [← act_mul, inv_mul_cancel, act_one] at h

private def cellRep (M : ℕ) (j : Fin (M ^ 2)) : A :=
  rationalAdeleAt 0 (rationalAdeleStageRepresentative M j)

private theorem exists_cell {M : ℕ} (hM : 0 < M) (u : U) (j : Fin (M ^ 2)) :
    ∃ k, act u (cellRep M j) ∈ rationalAdeleStageCell M k :=
  ((mem_rationalAdeleStageSupport_iff_existsUnique_cell hM _).mp
    (act_mem_support u (rationalAdeleStageCell_subset_support hM j
      (rationalAdeleStageRepresentative_mem_cell hM j 0)))).exists

private def cellMap {M : ℕ} (hM : 0 < M) (u : U) (j : Fin (M ^ 2)) : Fin (M ^ 2) :=
  (exists_cell hM u j).choose

private theorem act_mem_cell {M : ℕ} (hM : 0 < M) (u : U) {x : A} {j : Fin (M ^ 2)}
    (hx : x ∈ rationalAdeleStageCell M j) :
    act u x ∈ rationalAdeleStageCell M (cellMap hM u j) := by
  obtain ⟨z, hz, he⟩ := (mem_rationalAdeleStageCell_iff hM j x).mp hx
  obtain ⟨w, hw, hr⟩ := (mem_rationalAdeleStageCell_iff hM _ _).mp
    (exists_cell hM u j).choose_spec
  have hr' : (ι u : A).2 * rationalAdeleStageRepresentative M j =
      rationalAdeleStageRepresentative M (cellMap hM u j) + (M : F) * w := by
    change (ι u : A).2 * (rationalAdeleAt 0 (rationalAdeleStageRepresentative M j)).2 = _ at hr
    rwa [rationalAdeleAt_finite] at hr
  refine (mem_rationalAdeleStageCell_iff hM _ _).mpr
    ⟨w + (ι u : A).2 * z, rationalFiniteIntegralAdeles.add_mem hw (finite_integral_mul u hz), ?_⟩
  change (ι u : A).2 * x.2 = _
  rw [he, mul_add, hr', mul_left_comm (ι u : A).2 (M : F), add_assoc, ← mul_add]

private theorem cell_unique {M : ℕ} (hM : 0 < M) {x : A} {j k : Fin (M ^ 2)}
    (hj : x ∈ rationalAdeleStageCell M j) (hk : x ∈ rationalAdeleStageCell M k) : j = k := by
  obtain ⟨i, _, hi⟩ := (mem_rationalAdeleStageSupport_iff_existsUnique_cell hM x).mp
    (rationalAdeleStageCell_subset_support hM j hj)
  exact (hi j hj).trans (hi k hk).symm

private theorem cellMap_one {M : ℕ} (hM : 0 < M) (j : Fin (M ^ 2)) :
    cellMap hM 1 j = j := by
  have hj := rationalAdeleStageRepresentative_mem_cell hM j 0
  have h := act_mem_cell hM (1 : U) hj
  rw [act_one] at h
  exact cell_unique hM h hj

private theorem cellMap_mul {M : ℕ} (hM : 0 < M) (u v : U) (j : Fin (M ^ 2)) :
    cellMap hM (u * v) j = cellMap hM u (cellMap hM v j) := by
  have hj := rationalAdeleStageRepresentative_mem_cell hM j 0
  have h := act_mem_cell hM (u * v) hj
  rw [act_mul] at h
  exact cell_unique hM h (act_mem_cell hM u (act_mem_cell hM v hj))

-- The inverse unit acts by the inverse permutation.
private def cellPerm {M : ℕ} (hM : 0 < M) : U →* Equiv.Perm (Fin (M ^ 2)) where
  toFun u :=
    { toFun := cellMap hM u
      invFun := cellMap hM u⁻¹
      left_inv j := by rw [← cellMap_mul, inv_mul_cancel, cellMap_one]
      right_inv j := by rw [← cellMap_mul, mul_inv_cancel, cellMap_one] }
  map_one' := Equiv.ext (cellMap_one hM)
  map_mul' u v := Equiv.ext (cellMap_mul hM u v)

-- Reindex the Schwartz profiles and reassemble at the same stage.
private def stagePull {M : ℕ} (hM : 0 < M) (u : U) (f : rationalAdeleSchwartzStage M) :
    rationalAdeleSchwartzStage M :=
  (rationalAdeleStageCoordinates hM).symm (rationalAdeleStageCoordinates hM f ∘ cellPerm hM u)

private theorem stagePull_apply {M : ℕ} (hM : 0 < M) (u : U)
    (f : rationalAdeleSchwartzStage M) (x : A) : (stagePull hM u f).val x = f.val (act u x) := by
  by_cases hx : x ∈ rationalAdeleStageSupport M
  · obtain ⟨j, hj, _⟩ := (mem_rationalAdeleStageSupport_iff_existsUnique_cell hM x).mp hx
    rw [← rationalAdeleStageCoordinates_eq_on_cell hM _ hj,
      ← rationalAdeleStageCoordinates_eq_on_cell hM _ (act_mem_cell hM u hj), act_real]
    simp only [stagePull, LinearEquiv.apply_symm_apply, Function.comp_apply]
    rfl
  · rw [(stagePull hM u f).property.1 _ hx, f.property.1 _ (mt (act_mem_support_iff u).mp hx)]

local notation "L" => rationalAdeleFactorialLevel
local notation "pos" => rationalAdeleFactorialLevel_pos

private theorem exists_pull (u : U) (f : E) :
    ∃ g : E, g.toUnion.val = fun x ↦ f.toUnion.val (act u x) := by
  obtain ⟨n, hf⟩ := mem_rationalAdeleSchwartzStageUnion.mp f.toUnion.property
  let e := rationalAdeleStageCoordinates (pos n)
  let g := stagePull (pos n) u ⟨f.toUnion.val, hf⟩
  refine ⟨rationalAdeleLFAssembly n (e g), ?_⟩
  rw [rationalAdeleLFAssembly_toUnion, rationalAdeleFactorialStageAssembly_val]
  change (e.symm (e g)).val = _
  rw [e.symm_apply_apply]
  exact funext (stagePull_apply (pos n) u ⟨f.toUnion.val, hf⟩)

/-- Pull back an LF test by multiplication by the idele `(1, u)`. -/
public def rationalAdeleLFFiniteUnitPull (u : U) (f : E) : E := (exists_pull u f).choose

public theorem rationalAdeleLFFiniteUnitPull_apply (u : U) (f : E) (x : A) :
    (rationalAdeleLFFiniteUnitPull u f).toUnion.val x = f.toUnion.val ((ι u : A) * x) :=
  congrFun (exists_pull u f).choose_spec x

-- Equal cell permutations have identical pullbacks on this stage,
-- irrespective of which representative was used in `exists_pull`.
private theorem pull_congr {n : ℕ} {f : E}
    (hf : f.toUnion.val ∈ rationalAdeleSchwartzStage (L n)) {u v : U}
    (h : cellPerm (pos n) u = cellPerm (pos n) v) :
    rationalAdeleLFFiniteUnitPull u f = rationalAdeleLFFiniteUnitPull v f := by
  apply RationalAdeleSchwartzLF.ext
  funext x
  rw [rationalAdeleLFFiniteUnitPull_apply, rationalAdeleLFFiniteUnitPull_apply]
  change f.toUnion.val (act u x) = f.toUnion.val (act v x)
  let g : rationalAdeleSchwartzStage (L n) := ⟨f.toUnion.val, hf⟩
  change g.val (act u x) = g.val (act v x)
  rw [← stagePull_apply (pos n), ← stagePull_apply (pos n)]
  simp only [stagePull, h]

private abbrev StageGroup (n : ℕ) := (cellPerm (pos n)).range

private instance (n : ℕ) : Fintype (StageGroup n) := Fintype.ofFinite _

private def stageLift {n : ℕ} (g : StageGroup n) : U := (MonoidHom.mem_range.mp g.property).choose

private theorem stageLift_spec {n : ℕ} (g : StageGroup n) :
    cellPerm (pos n) (stageLift g) = g.val := (MonoidHom.mem_range.mp g.property).choose_spec

private def mean {ι₀ D : Type*} [Fintype ι₀] [AddCommMonoid D] [Module ℂ D]
    (b : ι₀ → D) : D := (Fintype.card ι₀ : ℂ)⁻¹ • ∑ i, b i

private theorem mean_const {ι₀ D : Type*} [Fintype ι₀] [Nonempty ι₀]
    [AddCommMonoid D] [Module ℂ D] (d : D) : mean (fun _ : ι₀ ↦ d) = d := by
  have h : (Fintype.card ι₀ : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  rw [mean, Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℂ, inv_smul_smul₀ h]

private theorem map_mean {ι₀ D D' : Type*} [Fintype ι₀]
    [AddCommMonoid D] [Module ℂ D] [AddCommMonoid D'] [Module ℂ D']
    (T : D →ₗ[ℂ] D') (b : ι₀ → D) : T (mean b) = mean (fun i ↦ T (b i)) := by
  simp only [mean, map_smul, map_sum]

private theorem mean_perm {ι₀ D : Type*} [Fintype ι₀] [AddCommMonoid D] [Module ℂ D]
    (p : Equiv.Perm ι₀) (b : ι₀ → D) : mean (fun i ↦ b (p i)) = mean b := by
  rw [mean, mean, Equiv.sum_comp p b]

private theorem mean_swap {ι₀ κ D : Type*} [Fintype ι₀] [Fintype κ]
    [AddCommMonoid D] [Module ℂ D] (b : ι₀ → κ → D) :
    mean (fun i ↦ mean (b i)) = mean (fun j ↦ mean (fun i ↦ b i j)) := by
  simp only [mean, ← Finset.smul_sum, smul_smul]
  rw [mul_comm (Fintype.card ι₀ : ℂ)⁻¹, Finset.sum_comm]

private def stageAverage (n : ℕ) (f : E) : E :=
  mean fun g : StageGroup n ↦ rationalAdeleLFFiniteUnitPull (stageLift g) f

private def valueAt (x : A) : E →ₗ[ℂ] ℂ :=
  (LinearMap.proj x).comp (rationalAdeleSchwartzStageUnion.subtype.comp
    RationalAdeleSchwartzLF.toUnion)

private theorem stageAverage_apply (n : ℕ) (f : E) (x : A) :
    (stageAverage n f).toUnion.val x = mean fun g : StageGroup n ↦ f.toUnion.val (act (stageLift g) x) := by
  change valueAt x (stageAverage n f) = _
  rw [stageAverage, map_mean]
  simp only [valueAt, LinearMap.comp_apply, Submodule.subtype_apply, LinearMap.proj_apply,
    rationalAdeleLFFiniteUnitPull_apply, act]

private theorem stageAverage_invariant {n : ℕ} {f : E}
    (hf : f.toUnion.val ∈ rationalAdeleSchwartzStage (L n)) (u : U) (x : A) :
    (stageAverage n f).toUnion.val (act u x) = (stageAverage n f).toUnion.val x := by
  let p := Equiv.mulRight ((cellPerm (pos n)).rangeRestrict u)
  rw [stageAverage_apply, stageAverage_apply,
    ← mean_perm p (fun g ↦ f.toUnion.val (act (stageLift g) x))]
  congr 1
  funext g
  rw [← act_mul]
  have h : cellPerm (pos n) (stageLift g * u) = cellPerm (pos n) (stageLift (p g)) := by
    rw [map_mul, stageLift_spec, stageLift_spec]
    rfl
  simpa only [rationalAdeleLFFiniteUnitPull_apply, act] using
    congrArg (fun t : E ↦ t.toUnion.val x) (pull_congr hf h)

private theorem stageAverage_of_invariant (n : ℕ) (f : E)
    (hf : ∀ u x, f.toUnion.val (act u x) = f.toUnion.val x) : stageAverage n f = f := by
  apply RationalAdeleSchwartzLF.ext
  funext x
  rw [stageAverage_apply]
  simp only [hf, mean_const]

private theorem stageAverage_comm (m n : ℕ) (f : E) :
    stageAverage m (stageAverage n f) = stageAverage n (stageAverage m f) := by
  apply RationalAdeleSchwartzLF.ext
  funext x
  simp only [stageAverage_apply]
  rw [mean_swap]
  simp only [← act_mul]
  congr 1
  funext i
  congr 1
  funext j
  rw [mul_comm]

-- Two stage averages commute by commutativity of finite-unit multiplication.
-- On a test belonging to both stages, either average fixes the other's output.
private theorem stageAverage_eq {m n : ℕ} {f : E}
    (hm : f.toUnion.val ∈ rationalAdeleSchwartzStage (L m))
    (hn : f.toUnion.val ∈ rationalAdeleSchwartzStage (L n)) : stageAverage m f = stageAverage n f := by
  calc
    stageAverage m f = stageAverage n (stageAverage m f) :=
      (stageAverage_of_invariant n _ (stageAverage_invariant hm)).symm
    _ = stageAverage m (stageAverage n f) := stageAverage_comm n m f
    _ = stageAverage n f := stageAverage_of_invariant m _ (stageAverage_invariant hn)

private def stageIndex (f : E) : ℕ :=
  (mem_rationalAdeleSchwartzStageUnion.mp f.toUnion.property).choose

private theorem mem_stageIndex (f : E) : f.toUnion.val ∈ rationalAdeleSchwartzStage (L (stageIndex f)) :=
  (mem_rationalAdeleSchwartzStageUnion.mp f.toUnion.property).choose_spec

/-- Average a represented test over the finite unit permutation image at any
factorial stage containing it. The averages at all such stages agree. -/
public def rationalAdeleLFFiniteUnitAverage (f : E) : E := stageAverage (stageIndex f) f

/-- Finite-unit averaging produces a unit-invariant representative. -/
public theorem rationalAdeleLFFiniteUnitAverage_invariant (f : E) (u : U) (x : A) :
    (rationalAdeleLFFiniteUnitAverage f).toUnion.val ((ι u : A) * x) =
      (rationalAdeleLFFiniteUnitAverage f).toUnion.val x := by
  unfold rationalAdeleLFFiniteUnitAverage
  exact stageAverage_invariant (mem_stageIndex f) u x

/-- Pullback on tests translates class theta in the same direction. -/
public theorem rationalAdeleClassTheta_LFFiniteUnitPull (u : U) (f : E) (d : C) :
    Θ[rationalAdeleLFFiniteUnitPull u f] d = Θ[f] ((rationalFiniteUnitClass u : C) * d) := by
  obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective d
  rw [rationalFiniteUnitClass_coe, ← QuotientGroup.mk_mul]
  simp only [rationalAdeleClassTheta_mk, rationalAdeleTheta, rationalAdeleLFFiniteUnitPull_apply]
  congr 1
  funext q
  simp only [Units.val_mul]
  ac_rfl

private def classStageAverage (n : ℕ) (T : C → ℂ) (d : C) : ℂ :=
  mean fun g : StageGroup n ↦ T ((rationalFiniteUnitClass (stageLift g) : C) * d)

/-- Average the class translates of the theta of `f` over the finite unit
permutation image of a stage containing `f`. -/
public def rationalAdeleClassThetaFiniteUnitAverage (f : E) : C → ℂ :=
  classStageAverage (stageIndex f) Θ[f]

set_option linter.concreteInstances false
variable [MeasurableSpace A] [BorelSpace A]

private theorem theta_stageAverage (n : ℕ) (f : E) :
    Θ[stageAverage n f] = classStageAverage n Θ[f] := by
  funext d
  let T := (LinearMap.proj d).comp rationalAdeleClassThetaLFLinear
  have h (b : E) : T b = Θ[b] d := by
    simp only [T, LinearMap.comp_apply, LinearMap.proj_apply, rationalAdeleClassThetaLFLinear_apply]
  rw [← h (stageAverage n f), stageAverage, map_mean, classStageAverage]
  simp only [h, rationalAdeleClassTheta_LFFiniteUnitPull]

/-- Class theta intertwines the finite average of tests with the average of
class translates. -/
public theorem rationalAdeleClassTheta_LFFiniteUnitAverage (f : E) :
    Θ[rationalAdeleLFFiniteUnitAverage f] = rationalAdeleClassThetaFiniteUnitAverage f := by
  unfold rationalAdeleLFFiniteUnitAverage rationalAdeleClassThetaFiniteUnitAverage
  exact theta_stageAverage _ f

private theorem classAverage_eq_stage {n : ℕ} {f : E}
    (hf : f.toUnion.val ∈ rationalAdeleSchwartzStage (L n)) :
    rationalAdeleClassThetaFiniteUnitAverage f = classStageAverage n Θ[f] := by
  rw [← rationalAdeleClassTheta_LFFiniteUnitAverage]
  unfold rationalAdeleLFFiniteUnitAverage
  rw [stageAverage_eq (mem_stageIndex f) hf, theta_stageAverage]

/-- On represented theta functions the average depends only on the theta
output, not the LF test chosen to represent it. -/
public theorem rationalAdeleClassThetaFiniteUnitAverage_congr {f g : E}
    (h : Θ[f] = Θ[g]) :
    rationalAdeleClassThetaFiniteUnitAverage f = rationalAdeleClassThetaFiniteUnitAverage g := by
  let n := max (stageIndex f) (stageIndex g)
  have hf : f.toUnion.val ∈ rationalAdeleSchwartzStage (L n) :=
    rationalAdeleSchwartzStage_mono
      (rationalAdeleFactorialLevel_dvd (le_max_left _ _)) (mem_stageIndex f)
  have hg : g.toUnion.val ∈ rationalAdeleSchwartzStage (L n) :=
    rationalAdeleSchwartzStage_mono
      (rationalAdeleFactorialLevel_dvd (le_max_right _ _)) (mem_stageIndex g)
  rw [classAverage_eq_stage hf, classAverage_eq_stage hg, h]

omit [MeasurableSpace A] [BorelSpace A] in
/-- Averaging fixes norm-one invariant theta outputs, whether or not the input
function is itself invariant. -/
public theorem rationalAdeleClassThetaFiniteUnitAverage_of_invariant (f : E)
    (hf : ∀ (k : rationalIdeleClassNormOne) (d : C), Θ[f] ((k : C) * d) = Θ[f] d) :
    rationalAdeleClassThetaFiniteUnitAverage f = Θ[f] := by
  funext d
  unfold rationalAdeleClassThetaFiniteUnitAverage classStageAverage
  simp only [hf, mean_const]

private theorem fourier_pull_zero (u : U) (f : E) :
    rationalAdeleFourier (rationalAdeleLFFiniteUnitPull u f).toUnion.val 0 =
      rationalAdeleFourier f.toUnion.val 0 := by
  simp only [rationalAdeleFourier, mul_zero, AddChar.map_zero_eq_one, map_one, mul_one,
    rationalAdeleLFFiniteUnitPull_apply]
  symm
  simpa only [ideleNorm_rationalFiniteUnitIdele, zero_add, one_smul] using
    integral_rationalAdele_affine f.toUnion.val 0 (ι u)

private def fourierAtZero : E →ₗ[ℂ] ℂ :=
  (valueAt 0).comp rationalAdeleLFFourier.toLinearMap

private theorem fourierAtZero_apply (f : E) :
    fourierAtZero f = rationalAdeleFourier f.toUnion.val 0 := by
  change (rationalAdeleLFFourier f).toUnion.val 0 = _
  rw [rationalAdeleLFFourier_eq]

/-- Both zero-mode evaluations are unchanged by finite-unit averaging. -/
public theorem rationalAdeleLFFiniteUnitAverage_zero_modes (f : E) :
    (rationalAdeleLFFiniteUnitAverage f).toUnion.val 0 = f.toUnion.val 0 ∧
      rationalAdeleFourier (rationalAdeleLFFiniteUnitAverage f).toUnion.val 0 =
        rationalAdeleFourier f.toUnion.val 0 := by
  unfold rationalAdeleLFFiniteUnitAverage
  refine ⟨?_, ?_⟩
  · simp only [stageAverage_apply, act, mul_zero, mean_const]
  · rw [← fourierAtZero_apply (stageAverage (stageIndex f) f), ← fourierAtZero_apply f,
      stageAverage, map_mean]
    simp only [fourierAtZero_apply, fourier_pull_zero, mean_const]

/-- Represented rational adelic LF tests with the spatial and Fourier zero
modes removed, with no invariance imposed. -/
public abbrev RationalThetaTwoModeInput :=
  {f : E // f.toUnion.val 0 = 0 ∧ rationalAdeleFourier f.toUnion.val 0 = 0}

omit [MeasurableSpace A] [BorelSpace A] in
private theorem theta_average_invariant (f : E) (k : rationalIdeleClassNormOne) (d : C) :
    Θ[rationalAdeleLFFiniteUnitAverage f] ((k : C) * d) =
      Θ[rationalAdeleLFFiniteUnitAverage f] d := by
  let g := rationalAdeleLFFiniteUnitAverage f
  apply (rationalIdeleClass_normOne_invariant_iff_finiteUnits Θ[g]).mpr _ k d
  intro u c
  have h : rationalAdeleLFFiniteUnitPull u g = g := by
    apply RationalAdeleSchwartzLF.ext
    funext x
    rw [rationalAdeleLFFiniteUnitPull_apply, rationalAdeleLFFiniteUnitAverage_invariant]
  rw [← rationalAdeleClassTheta_LFFiniteUnitPull, h]

omit [MeasurableSpace A] [BorelSpace A] in
/-- The finite-unit theta mean equals the compact Haar average at each class,
without any assumptions on the two zero modes. -/
public theorem rationalAdeleClassThetaFiniteUnitAverage_eq_integral
    [MeasurableSpace C] [BorelSpace C] (f : E) (d : C) :
    rationalAdeleClassThetaFiniteUnitAverage f d =
      ∫ k : rationalIdeleClassNormOne, Θ[f] ((k : C) * d) ∂rationalNormOneHaar := by
  let : MeasurableSpace A := borel A
  let : BorelSpace A := ⟨rfl⟩
  let : CompactSpace rationalIdeleClassNormOne := compactSpace_rationalIdeleClassNormOne
  let := isHaarMeasure_rationalNormOneHaar
  let := isProbabilityMeasure_rationalNormOneHaar
  let T (k : rationalIdeleClassNormOne) := Θ[f] ((k : C) * d)
  let b (i : StageGroup (stageIndex f)) := rationalFiniteUnitClass (stageLift i)
  have hcoe : Continuous (fun k : rationalIdeleClassNormOne ↦ (k : C)) := continuous_subtype_val
  have hd : Continuous (fun _ : rationalIdeleClassNormOne ↦ d) := continuous_const
  have hT : Continuous T := (continuous_rationalAdeleClassTheta_LF f).comp (hcoe.mul hd)
  have hInt (i : StageGroup (stageIndex f)) :
      Integrable (fun k ↦ T (b i * k)) rationalNormOneHaar :=
    (hT.comp (continuous_const.mul continuous_id)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  -- View each finite translate as a left translation on the compact group.
  have hmean (k : rationalIdeleClassNormOne) :
      rationalAdeleClassThetaFiniteUnitAverage f ((k : C) * d) =
        mean (fun i ↦ T (b i * k)) := by
    unfold rationalAdeleClassThetaFiniteUnitAverage classStageAverage
    congr 1
    funext i
    exact congrArg Θ[f] (mul_assoc (b i : C) (k : C) d).symm
  calc
    _ = ∫ k : rationalIdeleClassNormOne,
        rationalAdeleClassThetaFiniteUnitAverage f ((k : C) * d) ∂rationalNormOneHaar := by
      simp only [← rationalAdeleClassTheta_LFFiniteUnitAverage, theta_average_invariant]
      simp
    _ = ∫ k : rationalIdeleClassNormOne, T k ∂rationalNormOneHaar := by
      simp only [hmean, mean]
      rw [integral_smul, integral_finsetSum _ (fun i _ ↦ hInt i)]
      simp only [integral_mul_left_eq_self]
      exact mean_const _

/-- The two-mode average is represented in the existing radial input space. -/
public theorem rationalAdeleLFFiniteUnitAverage_mem_radial (f : RationalThetaTwoModeInput) :
    rationalAdeleLFFiniteUnitAverage f.val ∈ rationalThetaRadialInputSubmodule := by
  obtain ⟨h₀, hF⟩ := rationalAdeleLFFiniteUnitAverage_zero_modes f.val
  exact (mem_rationalThetaRadialInputSubmodule _).mpr
    ⟨h₀.trans f.property.1, hF.trans f.property.2, theta_average_invariant f.val⟩

/-- The class-theta image of all represented two-mode tests after finite-unit
averaging is exactly the class-theta image of the radial input space. -/
public theorem range_rationalAdeleClassThetaFiniteUnitAverage :
    Set.range (fun f : RationalThetaTwoModeInput ↦ rationalAdeleClassThetaFiniteUnitAverage f.val) =
      Set.range (fun f : RationalThetaRadialInput ↦ Θ[f.val]) := by
  refine Set.Subset.antisymm ?_ ?_
  · rintro _ ⟨f, rfl⟩
    exact ⟨⟨_, rationalAdeleLFFiniteUnitAverage_mem_radial f⟩,
      rationalAdeleClassTheta_LFFiniteUnitAverage f.val⟩
  · rintro _ ⟨f, rfl⟩
    obtain ⟨h₀, hF, hi⟩ := (mem_rationalThetaRadialInputSubmodule f.val).mp f.property
    exact ⟨⟨f.val, h₀, hF⟩, rationalAdeleClassThetaFiniteUnitAverage_of_invariant f.val hi⟩

end

end Masullo
