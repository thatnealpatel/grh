module

public import Mathlib.NumberTheory.NumberField.HeckeLFunction
import Lemmas.ComplexMultiplicativeNeighborhood
import Lemmas.IdeleStageSinglePlace

/-! # Finite ramification of a Hecke character

Masullo recalls finite ramification in §B.6.1.2, PDF p. 636, and uses it
in (3.4.3.8), p. 152. We prove it using continuity on the product of
finite integral units and a small neighborhood of `1` in `ℂ` containing
no nontrivial subgroup. These locators are provisional (Markdown and
numbered PDF layout, not rendered pages).
-/

open Filter IsDedekindDomain NumberField Set Topology

namespace Masullo

variable {K : Type*} [Field K] [NumberField K]

local notation "V" => HeightOneSpectrum (𝓞 K)
local notation "O" v => HeightOneSpectrum.adicCompletionIntegers K v

/-- Every continuous Hecke character is trivial on the local integral unit
subgroup at all but finitely many finite places. -/
public theorem exists_finset_isUnramifiedAt (χ : HeckeCharacter (𝓞 K) K) :
    ∃ S : Finset V, ∀ v ∉ S, χ.IsUnramifiedAt v := by
  classical
  -- Restrict to the all-integral finite stage with infinite coordinates one.
  let P := {v : V // v ∉ (∅ : Finset V)}
  let j : ((v : P) → (O v.val)ˣ) →* IdeleFiniteStage K ∅ :=
    { toFun := fun x ↦ (1, 1, x)
      map_one' := rfl
      map_mul' := fun _ _ ↦ by simp [Prod.mul_def] }
  let q := QuotientGroup.mk' (IdeleGroup.principalSubgroup (𝓞 K) K)
  let f := χ.toMonoidHom.comp (q.comp ((ideleFiniteStageEmbedding K ∅).comp j))
  have hj : Continuous j := continuous_const.prodMk
    (continuous_const.prodMk continuous_id)
  have hf : Continuous f := χ.continuous.comp (QuotientGroup.continuous_mk.comp
    ((isOpenEmbedding_ideleFiniteStageEmbedding K ∅).continuous.comp hj))
  -- A finite cylinder lies inside the preimage of the small complex ball.
  have hball : f ⁻¹' Metric.ball 1 (1 / 2) ∈ 𝓝 1 :=
    hf.continuousAt.preimage_mem_nhds (by rw [map_one]; exact Metric.ball_mem_nhds _ (by norm_num))
  rw [nhds_pi] at hball
  obtain ⟨S, U, hU, hsmall⟩ := Filter.mem_pi'.mp hball
  let e : P ↪ V := ⟨Subtype.val, Subtype.val_injective⟩
  refine ⟨S.map e, fun v hv ↦ HeckeCharacter.isUnramifiedAt_iff.mpr (fun x ↦ ?_)⟩
  let p : P := ⟨v, Finset.notMem_empty v⟩
  have hp : p ∉ S := fun h ↦ hv (Finset.mem_map_of_mem e h)
  have hnear (n : ℕ) : ‖(f (Pi.mulSingle p x)) ^ n - 1‖ < 1 / 2 := by
    rw [← map_pow]
    have hm : f ((Pi.mulSingle p x) ^ n) ∈ Metric.ball 1 (1 / 2) :=
      hsmall (show (Pi.mulSingle p x) ^ n ∈ Set.pi (↑S) U from fun w hw ↦ by
        have hwp : w ≠ p := fun h ↦ hp (h ▸ hw)
        simpa [Pi.pow_apply, Pi.mulSingle_eq_of_ne hwp] using mem_of_mem_nhds (hU w))
    simpa only [Metric.mem_ball, dist_eq_norm] using hm
  have htriv := complex_eq_one_of_norm_pow_sub_one_lt _ hnear
  -- The single-coordinate subgroup is the insertion defining the local restriction.
  change χ (q (ideleFiniteStageEmbedding K ∅ (1, 1, Pi.mulSingle p x))) = 1 at htriv
  rw [ideleFiniteStageEmbedding_single_inactive K ∅ p x] at htriv
  exact (MulChar.ofUnitHom_coe _ (Units.map (O v).subtype.toMonoidHom x)).trans htriv

end Masullo
