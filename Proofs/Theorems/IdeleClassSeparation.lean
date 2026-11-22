module

public import Theorems.IdeleIdealClassStrict
import Mathlib.Topology.Algebra.ProperAction.Basic

/-!
# Discreteness of principal ideles

Masullo, Lemma A.1.3.4(1)–(2), PDF p. 542, states that the
principal subgroup is discrete and the quotient Hausdorff. We supply
an identity neighborhood in the actual idelic topology: Require
integral finite units, and make the Archimedean norm of the difference
from one strictly less than one. The nonzero diagonal difference would
contradict the product formula for the product in (A.1.3.3), p. 541.
This is the multiplicative separation step, not the additive quotient
assertion of Lemma A.1.2.1, p. 540.
-/

open IsDedekindDomain NumberField Set
open scoped Masullo

namespace Masullo

variable {K : Type*} [Field K] [NumberField K]

local notation "A" => AdeleRing (𝓞 K) K
local notation "I" => IdeleGroup (𝓞 K) K
local notation "V" => HeightOneSpectrum (𝓞 K)
local notation "P" => IdeleGroup.principalSubgroup (𝓞 K) K

private noncomputable def principalIdeleWindow : Set I :=
  (ideleFiniteUnits (K := K) : Set I) ∩
    {g | (∏ w : InfinitePlace K, ‖(g : A).1 w - 1‖ ^ w.mult) < 1}

private theorem isOpen_principalIdeleWindow : IsOpen (principalIdeleWindow (K := K)) := by
  classical
  apply IsOpen.inter
  · rw [← range_ideleFiniteStageEmbedding_empty]
    exact (isOpenEmbedding_ideleFiniteStageEmbedding K ∅).isOpen_range
  · apply isOpen_lt _ continuous_const
    exact continuous_finsetProd _ fun w _ ↦
      (((continuous_apply w).comp (continuous_fst.comp Units.continuous_val)).sub
        continuous_const).norm.pow _

private theorem one_mem_principalIdeleWindow : (1 : I) ∈ principalIdeleWindow := by
  classical
  refine ⟨(ideleFiniteUnits (K := K)).one_mem, ?_⟩
  change (∏ w : InfinitePlace K, ‖(1 : w.Completion) - 1‖ ^ w.mult) < 1
  simp [zero_pow, InfinitePlace.mult_ne_zero]

private theorem eq_one_of_diagonal_mem_principalIdeleWindow (a : Kˣ)
    (ha : IdeleGroup.unitEmbedding (𝓞 K) K a ∈ principalIdeleWindow) : a = 1 := by
  by_contra h
  let x : K := (a : K) - 1
  have hx : x ≠ 0 := sub_ne_zero.mpr fun hx ↦ h (Units.ext hx)
  let d := IdeleGroup.unitEmbedding (𝓞 K) K (Units.mk0 x hx)
  have hd : (d : A) = algebraMap K A x := rfl
  have hax : (∏ w : InfinitePlace K, ‖(d : A).1 w‖ ^ w.mult) < 1 := by
    have hh := ha.2
    change (∏ w : InfinitePlace K, ‖(algebraMap K A (a : K)).1 w - 1‖ ^ w.mult) < 1 at hh
    rw [hd, show x = (a : K) - 1 from rfl, map_sub, map_one]
    exact hh
  have hfx (v : V) : ‖(d : A).2 v‖ ≤ 1 := by
    have hv := (mem_ideleFiniteUnits _).mp ha.1 v
    change Valued.v ((algebraMap K A (a : K)).2 v) = 1 at hv
    apply Valued.toNormedField.norm_le_one_iff.mpr
    rw [hd, show x = (a : K) - 1 from rfl, map_sub, map_one]
    change Valued.v ((algebraMap K A (a : K)).2 v - 1) ≤ 1
    refine ((Valued.v (R := v.adicCompletion K)).map_sub _ _).trans ?_
    rw [hv, map_one, max_self]
  have hf : (∏ᶠ v : V, ‖(d : A).2 v‖) ≤ 1 := by
    rw [← finprod_one (α := V) (M := ℝ)]
    apply finprod_le_finprod₀
    · exact FiniteAdeleRing.hasFiniteMulSupport_norm
        (Units.map (MonoidHom.snd (InfiniteAdeleRing K) (FiniteAdeleRing (𝓞 K) K)) d)
    · exact fun _ ↦ norm_nonneg _
    · exact Function.hasFiniteMulSupport_one
    · exact hfx
  have hnorm := AdeleRing.norm_algebraMap_eq_one_of_ne_zero hx
  rw [← hd, AdeleRing.norm_apply_of_isUnit d.isUnit] at hnorm
  have hn : 0 ≤ (∏ w : InfinitePlace K, ‖(d : A).1 w‖ ^ w.mult) :=
    Finset.prod_nonneg fun _ _ ↦ pow_nonneg (norm_nonneg _) _
  have hlt := (mul_le_mul_of_nonneg_left hf hn).trans_lt (by simpa using hax)
  exact (lt_irrefl (1 : ℝ)) (hnorm ▸ hlt)

/-- Lemma A.1.3.4(1): The principal ideles have the discrete induced topology. -/
public theorem discreteTopology_principalIdeles : DiscreteTopology P := by
  rw [discreteTopology_iff_isOpen_singleton_one]
  suffices h : ((↑) : P → I) ⁻¹' principalIdeleWindow = {1} by
    rw [← h]
    exact isOpen_principalIdeleWindow.preimage continuous_subtype_val
  ext a
  change (a : I) ∈ principalIdeleWindow ↔ a = 1
  constructor
  · intro ha
    obtain ⟨b, hb⟩ := a.property
    have hb1 := eq_one_of_diagonal_mem_principalIdeleWindow b (hb ▸ ha)
    exact Subtype.ext (by simpa [hb1] using hb.symm)
  · rintro rfl
    exact one_mem_principalIdeleWindow

/-- The discrete principal subgroup of the Hausdorff idele group is closed. -/
public theorem isClosed_principalIdeles : IsClosed (P : Set I) := by
  let := discreteTopology_principalIdeles (K := K)
  exact Subgroup.isClosed_of_discreteTopology

/-- The Hausdorff assertion in Lemma A.1.3.4(2), for the actual quotient topology. -/
public theorem t2Space_ideleClassGroup : T2Space (IdeleClassGroup (𝓞 K) K) := by
  let := isClosed_principalIdeles (K := K)
  infer_instance

end Masullo
