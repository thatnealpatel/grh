module

public import Theorems.RationalIdeleFiniteStage
public import Theorems.RationalIdeleFundamentalDomain
public import Mathlib.Topology.Algebra.InfiniteSum.Order
public import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Support of a base-normalized indentation

Proposition 12.2.2.4, pp. 512–514, gives an indentation on the full group
whose restriction to the base subgroup is also normalized. For counting
Haar on the principal subgroup, these two normalizations and nonnegativity
force the indentation to vanish off the base. Consequently the double-leg
lift (12.2.2.1–2), p. 508, has no input block from outside the base to
outputs inside the base. Cutting that lift into input shells outside the
base gives zero on outputs represented inside it, even before any band or
position limit. This is not an orbital quotient
evaluation or an identification of the remaining base operator.
-/

namespace Masullo

variable {G : Type*} [Group G]

/-- If each orbit meets `B`, normalizing a nonnegative indentation both on
full orbits and on the `H ∩ B` orbits inside `B` leaves no mass outside `B`.
The index of the restricted sum is the subtype of `H` lying in `B`. -/
public theorem indentation_eq_zero_off_base (H B : Subgroup G) (a : G → ℝ)
    (ha : ∀ x, 0 ≤ a x)
    (hcover : ∀ x : G, ∃ h : H, (h : G)⁻¹ * x ∈ B)
    (hfull : ∀ x ∈ B, HasSum (fun h : H ↦ a ((h : G)⁻¹ * x)) 1)
    (hbase : ∀ x ∈ B, HasSum (fun h : {h : H | (h : G) ∈ B} ↦ a ((h.1 : G)⁻¹ * x)) 1)
    {x : G} (hx : x ∉ B) : a x = 0 := by
  obtain ⟨k, hk⟩ := hcover x
  let y := (k : G)⁻¹ * x
  have hy : y ∈ B := hk
  have hk' : (↑(k⁻¹) : G) ∉ B := by
    intro h
    apply hx
    simpa [y] using B.mul_mem (B.inv_mem h) hy
  let f : H → ℝ := fun h ↦ a ((h : G)⁻¹ * y)
  let s : Set H := {h | (h : G) ∈ B}
  have hf : HasSum f 1 := hfull y hy
  have hsplit := hf.summable.tsum_subtype_add_tsum_subtype_compl s
  have hbase_y : (∑' h : s, f h.1) = 1 := (hbase y hy).tsum_eq
  rw [hbase_y, hf.tsum_eq, add_eq_left] at hsplit
  have hle := (hf.summable.subtype (· ∈ sᶜ)).le_tsum
    (⟨k⁻¹, hk'⟩ : ↑(sᶜ)) (fun h _ ↦ ha _)
  change f (k⁻¹ : H) ≤ ∑' h : ↑(sᶜ), f h.1 at hle
  rw [hsplit] at hle
  exact le_antisymm (by simpa [f, y] using hle) (ha x)

/-- A double-leg lift from a base-supported indentation has no mixed block
from inputs outside `B` to outputs inside `B`. All terms of the weight in
(12.2.2.1) vanish, not just their sum after taking cutoffs. -/
public theorem indentation_pair_weight_hasSum_zero (H B : Subgroup G) (a : G → ℝ)
    (ha : ∀ z ∉ B, a z = 0) {x y : G} (hx : x ∈ B) (hy : y ∉ B) :
    HasSum (fun h : H ↦ a ((h : G)⁻¹ * x) * a ((h : G)⁻¹ * y)) 0 := by
  have hterm (h : H) : a ((h : G)⁻¹ * x) * a ((h : G)⁻¹ * y) = 0 := by
    by_cases hh : (h : G) ∈ B
    · have hny : (h : G)⁻¹ * y ∉ B := fun h' ↦ hy (by simpa using B.mul_mem hh h')
      rw [ha _ hny, mul_zero]
    · have hnx : (h : G)⁻¹ * x ∉ B := fun h' ↦ hh (B.inv_mem_iff.mp (by
        simpa only [mul_assoc, mul_inv_cancel, mul_one] using B.mul_mem h' (B.inv_mem hx)))
      rw [ha _ hnx, zero_mul]
  simpa only [hterm] using (hasSum_zero (α := ℝ) (β := H))

open NumberField IsDedekindDomain

local notation "RationalIdeles" => IdeleGroup (𝓞 ℚ) ℚ
local notation "Principal" => IdeleGroup.principalSubgroup (𝓞 ℚ) ℚ

/-- Rational specialization for any base subgroup containing the clopen
positive-real finite-unit window. In particular, any base imposing only
finite-unit conditions outside a given set contains that window. -/
public theorem rationalIdele_indentation_pair_weight_hasSum_zero
    (B : Subgroup RationalIdeles) (hwindow : rationalIdeleUnitWindow ⊆ (B : Set RationalIdeles))
    (a : RationalIdeles → ℝ) (ha : ∀ x, 0 ≤ a x)
    (hfull : ∀ x ∈ B, HasSum (fun h : Principal ↦ a ((h : RationalIdeles)⁻¹ * x)) 1)
    (hbase : ∀ x ∈ B, HasSum (fun h : {h : Principal | (h : RationalIdeles) ∈ B} ↦
      a ((h.1 : RationalIdeles)⁻¹ * x)) 1)
    {x y : RationalIdeles} (hx : x ∈ B) (hy : y ∉ B) :
    HasSum (fun h : Principal ↦ a ((h : RationalIdeles)⁻¹ * x) * a ((h : RationalIdeles)⁻¹ * y)) 0 := by
  apply indentation_pair_weight_hasSum_zero Principal B a _ hx hy
  refine fun z hz ↦ indentation_eq_zero_off_base Principal B a ha ?_ hfull hbase hz
  intro t
  obtain ⟨b, hb⟩ := rationalIdeleUnitWindowHomeomorph.surjective (QuotientGroup.mk t)
  rw [rationalIdeleUnitWindowHomeomorph_apply] at hb
  let h : Principal := ⟨t / b.val, QuotientGroup.eq_iff_div_mem.mp hb.symm⟩
  exact ⟨h, by simpa [h, div_eq_mul_inv, mul_assoc] using hwindow b.property⟩

/-- The double-leg lift of a base-normalized indentation has no off-stage input
block for a rational finite stage, including the archimedean-only stage `S = ∅`.
Membership is in the image subgroup in the full ideles, not in its quotient. -/
public theorem rationalIdeleFiniteStage_indentation_pair_weight_hasSum_zero
    (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (a : RationalIdeles → ℝ) (ha : ∀ x, 0 ≤ a x)
    (hfull : ∀ x ∈ (rationalIdeleFiniteStageEmbedding S).range,
      HasSum (fun h : Principal ↦ a ((h : RationalIdeles)⁻¹ * x)) 1)
    (hbase : ∀ x ∈ (rationalIdeleFiniteStageEmbedding S).range,
      HasSum (fun h : {h : Principal | (h : RationalIdeles) ∈ (rationalIdeleFiniteStageEmbedding S).range} ↦
        a ((h.1 : RationalIdeles)⁻¹ * x)) 1)
    {x y : RationalIdeles} (hx : x ∈ (rationalIdeleFiniteStageEmbedding S).range)
    (hy : y ∉ (rationalIdeleFiniteStageEmbedding S).range) :
    HasSum (fun h : Principal ↦ a ((h : RationalIdeles)⁻¹ * x) * a ((h : RationalIdeles)⁻¹ * y)) 0 := by
  apply rationalIdele_indentation_pair_weight_hasSum_zero (rationalIdeleFiniteStageEmbedding S).range
    _ a ha hfull hbase hx hy
  rw [MonoidHom.coe_range, range_rationalIdeleFiniteStageEmbedding]
  exact fun _ ht v _ ↦ ⟨ht.2.1 v, ht.2.2 v⟩

end Masullo
