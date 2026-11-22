module

public import Lemmas.SchwartzLineComplete
public import Mathlib.Topology.Algebra.IsUniformGroup.Basic
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient
public import Mathlib.Topology.Algebra.Module.Equiv.Basic
public import Mathlib.Topology.ContinuousMap.Algebra
public import Mathlib.Topology.Algebra.InfiniteSum.UniformOn
import Mathlib.Algebra.Ring.Int.Units
import Mathlib.Topology.Algebra.Field
import Mathlib.Topology.Metrizable.Uniformity

/-! # The S-local theta quotient for the real place of ℚ

For `F = ℚ` and `S = {∞}`, the local additive group is `ℝ`, the local ideles are
`ℝˣ`, and the S-unit group is `ℤˣ = {1, -1}`. The local theta function is the
restriction to `ℝˣ` of the sum of a Schwartz function and its reflection. The
quotient by the kernel of this restriction is continuously linearly isomorphic
to the complemented subspace of even Schwartz functions, with its subspace
topology. Here the forward map is the sum, not the average.
-/

open scoped SchwartzMap

namespace Masullo

local notation "V" => 𝓢(ℝ, ℂ)

/-- The S-unit theta operator for `F = ℚ`, `S = {∞}`, on the actual local
ideles. The two terms correspond to the units `1` and `-1` of `ℤ`. -/
@[expose] public noncomputable def rationalRealTheta : V →ₗ[ℂ] C(ℝˣ, ℂ) where
  toFun f := ⟨fun x ↦ f x + f (-(x : ℝ)),
    (f.continuous.comp Units.continuous_val).add
      (f.continuous.comp Units.continuous_val.neg)⟩
  map_add' f g := by
    ext x
    simp only [ContinuousMap.coe_add, Pi.add_apply, ContinuousMap.coe_mk, add_apply]
    abel
  map_smul' c f := by
    ext x
    simp [mul_add]

/-- Evaluation of the local theta operator at a real idele. -/
@[simp] public theorem rationalRealTheta_apply (f : V) (x : ℝˣ) :
    rationalRealTheta f x = f x + f (-(x : ℝ)) := rfl

@[instance_reducible] private noncomputable def intUnitFintype : Fintype ℤˣ := by
  classical
  refine ⟨{1, -1}, fun u ↦ ?_⟩
  simpa using Int.units_eq_one_or u

/-- The defining S-unit sum converges uniformly on every subset of the local
ideles, hence on compact subsets. The finite sum is already exact after the
terms for `1` and `-1` have both been included. -/
public theorem rationalRealTheta_hasSumUniformlyOn (f : V) (K : Set ℝˣ) :
    HasSumUniformlyOn (fun (u : ℤˣ) (x : ℝˣ) ↦ f ((u : ℤ) * (x : ℝ)))
      (rationalRealTheta f) K := by
  classical
  let := intUnitFintype
  unfold HasSumUniformlyOn
  convert hasSum_fintype (UniformOnFun.ofFun {K} ∘
    fun (u : ℤˣ) (x : ℝˣ) ↦ f ((u : ℤ) * (x : ℝ))) using 1
  have hu : (Finset.univ : Finset ℤˣ) = {1, -1} := by
    ext u
    simp [Int.units_eq_one_or u]
  rw [hu, Finset.sum_pair (by decide : (1 : ℤˣ) ≠ -1)]
  apply (UniformOnFun.ofFun {K}).symm.injective
  funext x
  change rationalRealTheta f x = f (((1 : ℤˣ) : ℤ) * (x : ℝ)) +
    f (((-1 : ℤˣ) : ℤ) * (x : ℝ))
  simp

/-- The S-unit sum is absolutely convergent, since the index group is finite. -/
public theorem rationalRealTheta_summable_norm (f : V) (x : ℝˣ) :
    Summable (fun u : ℤˣ ↦ ‖f ((u : ℤ) * (x : ℝ))‖) := by
  let := intUnitFintype
  exact (hasSum_fintype _).summable

/-- Multiplication by a rational S-unit does not change the local theta value. -/
public theorem rationalRealTheta_mul_unit (f : V) (u : ℤˣ) (x : ℝˣ) :
    rationalRealTheta f (Units.map (Int.castRingHom ℝ).toMonoidHom u * x) =
      rationalRealTheta f x := by
  obtain rfl | rfl := Int.units_eq_one_or u
  · simp
  · simp [add_comm]

private noncomputable def reflect : V →L[ℂ] V :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (LinearIsometryEquiv.neg ℝ (E := ℝ))

/-- Extend the local two-term sum to a Schwartz function on the whole line. -/
public noncomputable def rationalRealSymmetrize : V →L[ℂ] V :=
  ContinuousLinearMap.id ℂ V + reflect

/-- Evaluation of the full-line two-term sum, including at zero. -/
@[simp] public theorem rationalRealSymmetrize_apply (f : V) (x : ℝ) :
    rationalRealSymmetrize f x = f x + f (-x) := by
  rfl

/-- Vanishing on the local ideles and vanishing on the entire line give the
same submodule. Continuity and density supply the value at zero. -/
public theorem rationalRealTheta_ker :
    rationalRealTheta.ker = rationalRealSymmetrize.toLinearMap.ker := by
  ext f
  change rationalRealTheta f = 0 ↔ rationalRealSymmetrize f = 0
  constructor
  · intro h
    have hd : Dense ({(0 : ℝ)}ᶜ : Set ℝ) := dense_compl_singleton 0
    refine SchwartzMap.ext fun x ↦ congrFun (Continuous.ext_on hd
      (rationalRealSymmetrize f).continuous (0 : V).continuous ?_) x
    intro t ht
    have he := DFunLike.congr_fun h (Units.mk0 t (by simpa using ht))
    simpa using he
  · intro h
    ext x
    simpa using DFunLike.congr_fun h (x : ℝ)

/-- The closed submodule of even complex-valued Schwartz functions on `ℝ`. -/
@[expose] public def rationalRealEvenSchwartz : Submodule ℂ V where
  carrier := {f | ∀ x : ℝ, f (-x) = f x}
  zero_mem' := by simp
  add_mem' {f g} hf hg := by
    intro x
    simp only [add_apply, hf x, hg x]
  smul_mem' c f hf := by
    intro x
    simp only [smul_apply, hf x]

/-- Membership of the even submodule is pointwise evenness. -/
@[simp] public theorem mem_rationalRealEvenSchwartz (f : V) :
    f ∈ rationalRealEvenSchwartz ↔ ∀ x : ℝ, f (-x) = f x := Iff.rfl

/-- The even Schwartz space carries the closed subspace topology. -/
public theorem isClosed_rationalRealEvenSchwartz : IsClosed (rationalRealEvenSchwartz : Set V) := by
  have heq : (rationalRealEvenSchwartz : Set V) = {f | reflect f = f} := by
    ext f
    exact ⟨fun h ↦ SchwartzMap.ext h, fun h x ↦ DFunLike.congr_fun h x⟩
  rw [heq]
  exact isClosed_eq reflect.continuous continuous_id

private noncomputable def sumEven : V →L[ℂ] rationalRealEvenSchwartz :=
  rationalRealSymmetrize.codRestrict _ fun f x ↦ by
    simp [add_comm]

/-- Continuous projection onto the even subspace; the factor `1/2` gives a
retraction of the subspace inclusion. -/
public noncomputable def rationalRealEvenProject : V →L[ℂ] rationalRealEvenSchwartz :=
  ((2 : ℂ)⁻¹) • sumEven

/-- The normalized sum fixes the included even functions. -/
@[simp] public theorem rationalRealEvenProject_apply_even (g : rationalRealEvenSchwartz) :
    rationalRealEvenProject g.1 = g := by
  have hg (x : ℝ) : g.1 (-x) = g.1 x := g.2 x
  apply Subtype.ext
  ext x
  change (2 : ℂ)⁻¹ * (g.1 x + g.1 (-x)) = g.1 x
  rw [hg x, ← two_mul, ← mul_assoc, inv_mul_cancel₀ (by norm_num), one_mul]

/-- The manuscript's quotient by the kernel of theta on `ℝˣ`, with the
ordinary topological module quotient topology. -/
public noncomputable abbrev RationalRealThetaQuotient := V ⧸ rationalRealTheta.ker

private noncomputable def toEven : RationalRealThetaQuotient →L[ℂ] rationalRealEvenSchwartz :=
  rationalRealTheta.ker.liftQL sumEven <| by
    intro f hf
    rw [rationalRealTheta_ker] at hf
    exact Subtype.ext hf

private noncomputable def fromEven : rationalRealEvenSchwartz →L[ℂ] RationalRealThetaQuotient :=
  rationalRealTheta.ker.mkQL.comp (((2 : ℂ)⁻¹) • rationalRealEvenSchwartz.subtypeL)

/-- The actual local theta quotient is continuously linearly isomorphic to
its even Schwartz model. The forward map descends the unnormalized sum;
the inverse takes the class of half the even function. -/
public noncomputable def rationalRealThetaEquiv :
    RationalRealThetaQuotient ≃L[ℂ] rationalRealEvenSchwartz :=
  ContinuousLinearEquiv.equivOfInverse toEven fromEven
    (by
      intro y
      obtain ⟨f, rfl⟩ := rationalRealTheta.ker.mkQ_surjective y
      apply (Submodule.Quotient.eq _).2
      change ((2 : ℂ)⁻¹ • rationalRealSymmetrize f - f) ∈ rationalRealTheta.ker
      rw [rationalRealTheta_ker, LinearMap.mem_ker]
      have h := congrArg Subtype.val (rationalRealEvenProject_apply_even (sumEven f))
      change rationalRealSymmetrize
        (((2 : ℂ)⁻¹) • rationalRealSymmetrize f - f) = 0
      change ((2 : ℂ)⁻¹) • rationalRealSymmetrize (rationalRealSymmetrize f) =
        rationalRealSymmetrize f at h
      simpa only [map_sub, map_smul, sub_eq_zero] using h)
    (by
      intro g
      change sumEven (((2 : ℂ)⁻¹) • g.1) = g
      rw [map_smul]
      exact rationalRealEvenProject_apply_even g)

/-- The quotient identification recovers the full-line sum on representatives. -/
@[simp] public theorem rationalRealThetaEquiv_mkQ_apply (f : V) (x : ℝ) :
    (rationalRealThetaEquiv (rationalRealTheta.ker.mkQ f)).1 x = f x + f (-x) := by
  rfl

/-- On local ideles, the quotient identification recovers the actual theta
operator without any normalization. -/
public theorem rationalRealThetaEquiv_mkQ_apply_unit (f : V) (x : ℝˣ) :
    (rationalRealThetaEquiv (rationalRealTheta.ker.mkQ f)).1 x = rationalRealTheta f x := by
  rw [rationalRealThetaEquiv_mkQ_apply, rationalRealTheta_apply]

/-- An even function represents a local theta image by taking half of it
as a Schwartz test function. -/
@[simp] public theorem rationalRealThetaEquiv_symm_apply (g : rationalRealEvenSchwartz) :
    rationalRealThetaEquiv.symm g = rationalRealTheta.ker.mkQ (((2 : ℂ)⁻¹) • g.1) := by
  rfl

/-- The local theta kernel is closed in the genuine Schwartz topology. -/
public theorem isClosed_rationalRealTheta_ker : IsClosed (rationalRealTheta.ker : Set V) := by
  rw [rationalRealTheta_ker]
  exact isClosed_eq rationalRealSymmetrize.continuous continuous_const

/-- The quotient has the complete Hausdorff, metrizable, locally convex topology
of a Fréchet space. Convexity is over the underlying real field, as usual for a
complex locally convex space. -/
public theorem rationalRealThetaQuotient_frechet :
    @CompleteSpace RationalRealThetaQuotient
      (IsTopologicalAddGroup.rightUniformSpace RationalRealThetaQuotient) ∧
      T2Space RationalRealThetaQuotient ∧ TopologicalSpace.MetrizableSpace RationalRealThetaQuotient ∧
      LocallyConvexSpace ℝ RationalRealThetaQuotient := by
  let : UniformSpace RationalRealThetaQuotient := IsTopologicalAddGroup.rightUniformSpace _
  let : IsUniformAddGroup RationalRealThetaQuotient := isUniformAddGroup_of_addCommGroup
  let : CompleteSpace V := completeSpace_schwartzLine
  let : IsUniformAddGroup rationalRealEvenSchwartz :=
    IsUniformInducing.isUniformAddGroup rationalRealEvenSchwartz.subtype.toAddMonoidHom ⟨rfl⟩
  let : CompleteSpace rationalRealEvenSchwartz :=
    isClosed_rationalRealEvenSchwartz.isComplete.completeSpace_coe
  let := IsUniformAddGroup.uniformity_countably_generated (α := V)
  let : TopologicalSpace.MetrizableSpace V := UniformSpace.metrizableSpace
  let : TopologicalSpace.MetrizableSpace rationalRealEvenSchwartz :=
    Topology.IsEmbedding.subtypeVal.metrizableSpace
  let : LocallyConvexSpace ℝ rationalRealEvenSchwartz := by
    change LocallyConvexSpace ℝ (rationalRealEvenSchwartz.restrictScalars ℝ)
    infer_instance
  let e := rationalRealThetaEquiv
  exact ⟨e.isUniformEmbedding.completeSpace_congr e.surjective |>.2 inferInstance,
    e.toHomeomorph.isEmbedding.t2Space,
    e.toHomeomorph.isEmbedding.metrizableSpace,
    Topology.IsInducing.locallyConvexSpace (f := e.toLinearEquiv.toLinearMap.restrictScalars ℝ)
      e.toHomeomorph.isEmbedding.isInducing⟩

/-- The even model maps into the quotient as a closed stage and fills it.
Thus its one-stage presentation induces the actual quotient topology. -/
public theorem rationalRealThetaQuotient_closedStage :
    Topology.IsClosedEmbedding rationalRealThetaEquiv.symm ∧
      Function.Surjective rationalRealThetaEquiv.symm :=
  ⟨rationalRealThetaEquiv.symm.toHomeomorph.isClosedEmbedding,
    rationalRealThetaEquiv.symm.surjective⟩

end Masullo
