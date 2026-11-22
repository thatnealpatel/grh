module

public import Theorems.IdeleFiniteStage
import Lemmas.IdeleStageSinglePlace
public import Mathlib.NumberTheory.NumberField.HeckeLFunction
import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.Order.Filter.AtTopBot.Finset
import Mathlib.Algebra.BigOperators.Pi

/-! # Character factorization on open idele stages

Masullo gives the character tensor formula in §3.1.2, p. 120, defines
restriction by the single-place insertion in (3.1.2.4), p. 121, and
specifies unramifiedness off the active places in (3.1.2.6), p. 121.
For the use in (3.4.1.6), pp. 143–144, we check that those local
restrictions really determine the character on the whole open stage.
Triviality on each inactive coordinate is not an algebraic argument
for triviality on their infinite product: Here the finite truncations
converge in the product topology, and we use continuity of the character.
This is the character step, not the norm, test, or integral factorization.
Source readings are provisional (Markdown and PDF layout).
-/

open Filter IsDedekindDomain NumberField Topology
open scoped Classical

namespace Masullo

variable (K : Type*) [Field K] [NumberField K]

local notation "V" => HeightOneSpectrum (𝓞 K)
local notation "F" v => HeightOneSpectrum.adicCompletion K v
local notation "O" v => HeightOneSpectrum.adicCompletionIntegers K v
local notation "J" S => {v : V // v ∈ S}
local notation "U" S => {v : V // v ∉ S}

/-- The value on an open stage is the product of the actual infinite-place
restrictions and active finite-place restrictions. The entire inactive
unit tuple contributes one when the character is unramified off `S`. -/
public theorem ideleFiniteStage_character_factor (χ : HeckeCharacter (𝓞 K) K) (S : Finset V)
    (hu : ∀ v ∉ S, χ.IsUnramifiedAt v) (x : IdeleFiniteStage K S) :
    χ (QuotientGroup.mk' (IdeleGroup.principalSubgroup (𝓞 K) K) (ideleFiniteStageEmbedding K S x)) =
      (∏ v : InfinitePlace K, χ (IdeleClassGroup.ofCompletion (𝓞 K) K v (x.1 v))) *
      (∏ v : J S, χ.restrict v (x.2.1 v : F v.val)) := by
  let q : IdeleFiniteStage K S →* ℂ := χ.toMonoidHom.comp <|
    (QuotientGroup.mk' (IdeleGroup.principalSubgroup (𝓞 K) K)).comp (ideleFiniteStageEmbedding K S)
  let i : ((v : InfinitePlace K) → v.Completionˣ) →* IdeleFiniteStage K S :=
    (MonoidHom.id _).prod (1 : _ →* _)
  let a : ((v : J S) → (F v.val)ˣ) →* IdeleFiniteStage K S :=
    (1 : _ →* _).prod ((MonoidHom.id _).prod (1 : _ →* _))
  let u : ((v : U S) → (O v.val)ˣ) →* IdeleFiniteStage K S :=
    (1 : _ →* _).prod ((1 : _ →* _).prod (MonoidHom.id _))
  have hq : Continuous q := χ.continuous.comp (QuotientGroup.continuous_mk.comp
    (isOpenEmbedding_ideleFiniteStageEmbedding K S).continuous)
  have hqr (v : V) (z : (F v)ˣ) :
      χ (IdeleClassGroup.ofAdicCompletion (𝓞 K) K v z) = χ.restrict v (z : F v) :=
    by rw [HeckeCharacter.restrict, MulChar.ofUnitHom_coe]; rfl
  -- First remove the inactive tuple using the net of its finite truncations.
  have hu1 : q (u x.2.2) = 1 := by
    let trunc (T : Finset (U S)) := ∏ v ∈ T, Pi.mulSingle v (x.2.2 v)
    have ht : Tendsto trunc atTop (𝓝 x.2.2) := by
      refine tendsto_pi_nhds.mpr fun v ↦ tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_finset_mem_atTop v] with T hv
      simp [trunc, Finset.prod_apply, Finset.prod_pi_mulSingle, hv]
    have hqu : Continuous fun y ↦ q (u y) := hq.comp (continuous_const.prodMk
      (continuous_const.prodMk continuous_id))
    have h1 (T : Finset (U S)) : q (u (trunc T)) = 1 := by
      simp only [trunc, map_prod]
      apply Finset.prod_eq_one
      intro v _
      change χ (QuotientGroup.mk' _ (ideleFiniteStageEmbedding K S
        (1, 1, Pi.mulSingle v (x.2.2 v)))) = 1
      rw [ideleFiniteStageEmbedding_single_inactive]
      change χ (IdeleClassGroup.ofAdicCompletion (𝓞 K) K v _) = 1
      rw [hqr]
      exact (hu v v.property).restrict_apply_unit_eq_one (x.2.2 v)
    exact tendsto_nhds_unique (hqu.continuousAt.tendsto.comp ht)
      (tendsto_const_nhds.congr fun T ↦ (h1 T).symm)
  -- The two remaining tuples are finite products of single-place insertions.
  have hi : q (i x.1) = ∏ v : InfinitePlace K, χ (IdeleClassGroup.ofCompletion (𝓞 K) K v (x.1 v)) := by
    conv_lhs => rw [← Finset.univ_prod_mulSingle x.1, map_prod, map_prod]
    apply Finset.prod_congr rfl
    intro v _
    change χ (QuotientGroup.mk' _ (ideleFiniteStageEmbedding K S (Pi.mulSingle v (x.1 v), 1, 1))) = _
    rw [ideleFiniteStageEmbedding_single_infinite]
    rfl
  have ha : q (a x.2.1) = ∏ v : J S, χ.restrict v (x.2.1 v : F v.val) := by
    conv_lhs => rw [← Finset.univ_prod_mulSingle x.2.1, map_prod, map_prod]
    apply Finset.prod_congr rfl
    intro v _
    change χ (QuotientGroup.mk' _ (ideleFiniteStageEmbedding K S (1, Pi.mulSingle v (x.2.1 v), 1))) = _
    rw [ideleFiniteStageEmbedding_single_active]
    exact hqr v (x.2.1 v)
  have hx : x = i x.1 * a x.2.1 * u x.2.2 := by
    rcases x with ⟨b, c, d⟩
    change (b, c, d) = (b, 1, 1) * (1, c, 1) * (1, 1, d)
    simp
  change q x = _
  calc
    q x = q (i x.1) * q (a x.2.1) * q (u x.2.2) := by rw [← map_mul, ← map_mul, ← hx]
    _ = _ := by rw [hi, ha, hu1, mul_one]

end Masullo
