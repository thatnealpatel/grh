module

public import Theorems.IdeleIdealClass
public import Lemmas.IdeleFiniteStageMeasure
public import Mathlib.Algebra.Exact.Basic
import Mathlib.Topology.Algebra.OpenSubgroup

/-!
# Strict exactness of the ideal-class sequences

Proposition A.2.3.9, (A.2.3.23)–(24), PDF p. 552, asserts strict short
exactness. The classical quotient description in §A.1.5.3, pp. 544–545,
and the algebraic lifting in `Theorems.IdeleIdealClass` identify the arrows
and kernels. To supply the topology, we identify the integral-unit subgroup
with the empty finite stage of the restricted product (Lemma A.1.3.3,
p. 541). It is open, so the larger kernel is open as well. The norm-one
kernel inherits openness by restriction. This gives closed embeddings on
the left and open quotient maps to the discrete ideal class group on the
right. The independent presentation (A.2.3.22) is not used here.
-/

open Filter IsDedekindDomain NumberField Set Topology
open scoped Masullo

namespace Masullo

variable {K : Type*} [Field K] [NumberField K]

local notation "A" => AdeleRing (𝓞 K) K
local notation "I" => IdeleGroup (𝓞 K) K
local notation "I₁" => ideleNormOne (K := K)
local notation "P" => ClassGroup (𝓞 K)

/-- The class group in (A.2.3.23) and (A.2.3.24) carries the discrete topology. -/
public scoped instance topologicalSpace_idealClassGroup : TopologicalSpace P := ⊥

public scoped instance discreteTopology_idealClassGroup : DiscreteTopology P :=
  discreteTopology_bot _

/-- The compact calibration box has nonempty interior in the actual ideles. -/
public scoped instance locallyCompact_ideleGroup : LocallyCompactSpace I :=
  let B := Classical.choice (nonempty_archimedeanUnitBoxes K)
  (ideleCalibrationBox K B).locallyCompactSpace_of_group

/-- The norm-one ideles form a closed subgroup of the locally compact ideles. -/
public scoped instance locallyCompact_ideleNormOne : LocallyCompactSpace I₁ := by
  apply IsClosed.locallyCompactSpace
  rw [show (I₁ : Set I) = ideleNorm (K := K) ⁻¹' {1} from
    Set.ext (mem_ideleNormOne (K := K))]
  exact isClosed_singleton.preimage continuous_ideleNorm

/-- The empty stage imposes precisely the integral-unit condition at every finite place. -/
public theorem range_ideleFiniteStageEmbedding_empty :
    range (ideleFiniteStageEmbedding K ∅) = (ideleFiniteUnits (K := K) : Set I) := by
  rw [range_ideleFiniteStageEmbedding K]
  ext g
  simp only [mem_ofPred_eq, Finset.notMem_empty, not_false_eq_true, true_implies, SetLike.mem_coe,
    mem_ideleFiniteUnits, HeightOneSpectrum.mem_adicCompletionIntegers]
  apply forall_congr'
  intro v
  have hinv : Valued.v ((↑(g⁻¹) : A).2 v) * Valued.v ((g : A).2 v) = 1 := by
    rw [← map_mul]
    have h := congrArg (fun a : A ↦ a.2 v) (Units.inv_mul g)
    rw [show (↑(g⁻¹) : A).2 v * (g : A).2 v = 1 from h, map_one]
  constructor
  · rintro ⟨h, h'⟩
    apply le_antisymm h
    calc
      1 = Valued.v ((↑(g⁻¹) : A).2 v) * Valued.v ((g : A).2 v) := hinv.symm
      _ ≤ 1 * Valued.v ((g : A).2 v) := mul_le_mul_of_nonneg_right h' zero_le
      _ = _ := one_mul _
  · intro h
    rw [h, mul_one] at hinv
    exact ⟨h.le, hinv.le⟩

/-- The final arrow of (A.2.3.24) is the restriction of the ideal class map. -/
public noncomputable def ideleIdealClassNormOne : I₁ →* P :=
  ideleIdealClass.comp (ideleNormOne (K := K)).subtype

public theorem ideleIdealClassNormOne_apply (g : I₁) :
    ideleIdealClassNormOne g = ideleIdealClass (g : I) := by
  unfold ideleIdealClassNormOne
  rfl

private theorem isOpen_ker_ideleIdealClass : IsOpen ((ideleIdealClass (K := K)).ker : Set I) := by
  apply Subgroup.isOpen_mono (H₁ := ideleFiniteUnits)
  · intro g hg
    exact (ideleIdealClass_eq_one_iff g).mpr ⟨1, g, hg, by simp⟩
  · rw [← range_ideleFiniteStageEmbedding_empty]
    exact (isOpenEmbedding_ideleFiniteStageEmbedding K ∅).isOpen_range

private theorem strictExactOfOpenKernel {G H : Type*} [Group G] [Group H]
    [TopologicalSpace G] [IsTopologicalGroup G] [TopologicalSpace H] [DiscreteTopology H]
    (f : G →* H) (hf : Function.Surjective f) (hker : IsOpen (f.ker : Set G)) :
    IsClosedEmbedding (f.ker.subtype : f.ker → G) ∧
      Function.MulExact f.ker.subtype f ∧ IsOpenQuotientMap f := by
  have hcont : Continuous f := by
    apply continuous_of_continuousAt_one f
    rw [ContinuousAt, nhds_discrete H, map_one, tendsto_pure]
    exact hker.mem_nhds (map_one f)
  refine ⟨(f.ker.isClosed_of_isOpen hker).isClosedEmbedding_subtypeVal, ?_,
    ⟨hf, hcont, fun _ _ ↦ isOpen_discrete _⟩⟩
  rw [MonoidHom.mulExact_iff, Subgroup.range_subtype]

/-- Strict exactness of (A.2.3.23). `ideleIdealClass_eq_one_iff` identifies the
left term with the principal ideles times the empty finite stage. -/
public theorem ideleIdealClass_strictExact :
    IsClosedEmbedding (ideleIdealClass.ker.subtype : (ideleIdealClass (K := K)).ker → I) ∧
      Function.MulExact ideleIdealClass.ker.subtype (ideleIdealClass (K := K)) ∧
      IsOpenQuotientMap (ideleIdealClass (K := K)) :=
  strictExactOfOpenKernel _ ideleIdealClass_surjective isOpen_ker_ideleIdealClass

/-- Strict exactness of (A.2.3.24). `ideleIdealClass_normOne_eq_one_iff`
identifies the left term with the principal ideles times the norm-one part
of the empty finite stage. -/
public theorem ideleIdealClassNormOne_strictExact :
    IsClosedEmbedding (ideleIdealClassNormOne.ker.subtype :
      (ideleIdealClassNormOne (K := K)).ker → I₁) ∧
      Function.MulExact ideleIdealClassNormOne.ker.subtype (ideleIdealClassNormOne (K := K)) ∧
      IsOpenQuotientMap (ideleIdealClassNormOne (K := K)) :=
  strictExactOfOpenKernel _ ideleIdealClass_normOne_surjective
    (isOpen_ker_ideleIdealClass.preimage continuous_subtype_val)

end Masullo
