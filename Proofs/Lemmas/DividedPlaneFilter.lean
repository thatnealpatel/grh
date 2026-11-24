module

public import Mathlib.Data.Finset.Card
public import Mathlib.GroupTheory.Index
import Lemmas.MaskedGapDirections
import Mathlib.Data.ZMod.QuotientGroup
import Mathlib.LinearAlgebra.Basis.Fin
import Mathlib.LinearAlgebra.FreeModule.Finite.CardQuotient
import Mathlib.Tactic.FinCases

/-!
# Divided-coordinate filters on an integral plane lattice

Source: `d62a81b9e592:.godel/alice/denominator-pair-gap-regions.md:23–27,39–47`,
unchanged in these ranges at writer base `be4a426e2d1c`. In the nonvertical
case, `Γ` denotes the **whole** lattice `P ∩ Λ` in the coordinates `(m,(x,y))`.
Injectivity of the gap projection and finite index of its image are the
abstract plane hypotheses. The normalized coordinate is the surjective map
`r = m / j₀`, where `j₀ > 0` generates the image of `m`.

Scope: filtering by `f ∣ r` multiplies the projected index by `f`; mutual gap
determinants are multiples of this index. A finite set of filtered triples
with pairwise determinants strictly below that index in absolute value has
at most two members if each original pair `(m,x)` is primitive. The index is
not computed on the span of the sampled points. No bounds on plane or filter
occurrence, divisor enumeration, or global occupancy are asserted.

Owning check session: `01a20e21-be35-7bb8-b792-768105414492`.
-/

namespace DividedPlaneFilter

variable {Γ : AddSubgroup (ℤ × ℤ × ℤ)}

/-- The gap projection of a lattice triple, forgetting its `m` coordinate. -/
@[expose] public def gapProjection (Γ : AddSubgroup (ℤ × ℤ × ℤ)) : Γ →+ (ℤ × ℤ) :=
  (AddMonoidHom.snd ℤ (ℤ × ℤ)).comp Γ.subtype

/-- A positive generator of the `m` image and the corresponding divided coordinate. -/
public structure NormalizedCoordinate (Γ : AddSubgroup (ℤ × ℤ × ℤ)) where
  j₀ : ℤ
  j₀_pos : 0 < j₀
  r : Γ →+ ℤ
  r_surjective : Function.Surjective r
  m_eq : ∀ v : Γ, v.val.1 = j₀ * r v

/-- The full subgroup of `Γ` cut out by divisibility of the divided coordinate. -/
@[expose] public def dividedFilter (a : NormalizedCoordinate Γ) (f : ℕ) : AddSubgroup Γ :=
  (AddSubgroup.zmultiples (f : ℤ)).comap a.r

public theorem mem_dividedFilter {a : NormalizedCoordinate Γ} {f : ℕ} {v : Γ} :
    v ∈ dividedFilter a f ↔ (f : ℤ) ∣ a.r v :=
  Int.mem_zmultiples_iff

/-- The image of the full divided filter in the ambient gap group `ℤ²`. -/
@[expose] public def projectedFilter (a : NormalizedCoordinate Γ) (f : ℕ) : AddSubgroup (ℤ × ℤ) :=
  (dividedFilter a f).map (gapProjection Γ)

/-- The filter has index `f` in the whole plane lattice. -/
public theorem dividedFilter_index (a : NormalizedCoordinate Γ) (f : ℕ) :
    (dividedFilter a f).index = f := by
  rw [dividedFilter, AddSubgroup.index_comap_of_surjective _ a.r_surjective,
    Int.index_zmultiples, Int.natAbs_natCast]

/-- If the gap projection is injective, the ambient projected index is `C*f`,
where `C` is the index of the image of the whole plane lattice. For `C,f > 0`
this is a finite index; the formula also respects Lean's infinite-index value `0`. -/
public theorem projectedFilter_index (a : NormalizedCoordinate Γ) (f : ℕ)
    (hπ : Function.Injective (gapProjection Γ)) :
    (projectedFilter a f).index = (gapProjection Γ).range.index * f := by
  have hle : projectedFilter a f ≤ (gapProjection Γ).range := by
    rw [← AddSubgroup.map_top]
    exact AddSubgroup.map_mono le_top
  rw [← AddSubgroup.relIndex_mul_index hle, ← AddSubgroup.map_top (gapProjection Γ),
    projectedFilter, AddSubgroup.relIndex_map_map_of_injective _ _ hπ,
    AddSubgroup.relIndex_top_right, dividedFilter_index, mul_comm]

/-- The signed determinant of two gap vectors. -/
@[expose] public def gapDet (p q : ℤ × ℤ) : ℤ := p.1 * q.2 - q.1 * p.2

private theorem index_dvd_det {H : AddSubgroup (ℤ × ℤ)} {p q : ℤ × ℤ}
    (hp : p ∈ H) (hq : q ∈ H) : (H.index : ℤ) ∣ gapDet p q := by
  by_cases hdet : gapDet p q = 0
  · rw [hdet]
    exact dvd_zero _
  let v : Fin 2 → ℤ × ℤ := ![p, q]
  let b := Module.Basis.finTwoProd ℤ
  let A := b.toMatrix v
  have hA : A.det = gapDet p q := by
    simp [A, b, v, gapDet, Matrix.det_fin_two, Module.Basis.toMatrix_apply]
  have hv : LinearIndependent ℤ v := by
    have hcols := Matrix.linearIndependent_cols_of_det_ne_zero (hA.trans_ne hdet)
    have hmap := hcols.map' b.equivFun.symm.toLinearMap b.equivFun.symm.ker
    convert hmap using 1
    funext j
    change v j = b.equivFun.symm (b.equivFun (v j))
    exact (b.equivFun.symm_apply_apply _).symm
  -- This pair spans a sublattice of `H`, not necessarily all of `H`.
  let L := Submodule.span ℤ (Set.range v)
  have hle : L.toAddSubgroup ≤ H := by
    change L ≤ H.toIntSubmodule
    apply Submodule.span_le.mpr
    rintro _ ⟨j, rfl⟩
    fin_cases j
    · exact hp
    · exact hq
  have hindex : L.toAddSubgroup.index = (gapDet p q).natAbs := by
    let bL : Module.Basis (Fin 2) ℤ L.toAddSubgroup := Module.Basis.span hv
    rw [AddSubgroup.index_eq_natAbs_det b _ bL, ← hA, Module.Basis.det_apply]
    congr 3
    funext j
    exact congrArg Subtype.val (Module.Basis.span_apply hv j)
  apply Int.natAbs_dvd_natAbs.mp
  rw [Int.natAbs_natCast, ← hindex]
  exact AddSubgroup.index_dvd_of_le hle

/-- Every pair of gaps in the projected divided filter has determinant divisible by `C*f`. -/
public theorem gapDet_dvd {a : NormalizedCoordinate Γ} {f : ℕ}
    (hπ : Function.Injective (gapProjection Γ)) {p q : ℤ × ℤ}
    (hp : p ∈ projectedFilter a f) (hq : q ∈ projectedFilter a f) :
    (((gapProjection Γ).range.index * f : ℕ) : ℤ) ∣ gapDet p q := by
  rw [← projectedFilter_index a f hπ]
  exact index_dvd_det hp hq

-- Lift the two cross-multiplications in the gaps by injectivity. No division by
-- a gap coordinate is needed, even if one or both of those coordinates vanish.
private theorem lift_gap_collinearity (hπ : Function.Injective (gapProjection Γ))
    {p q : Γ} (hdet : gapDet (gapProjection Γ p) (gapProjection Γ q) = 0) :
    q.val.2.1 * p.val.1 = p.val.2.1 * q.val.1 ∧
      q.val.2.2 * p.val.1 = p.val.2.2 * q.val.1 := by
  have hd : p.val.2.1 * q.val.2.2 = q.val.2.1 * p.val.2.2 := sub_eq_zero.mp hdet
  have hx : q.val.2.1 • p = p.val.2.1 • q := by
    apply hπ
    exact Prod.ext (mul_comm _ _) hd.symm
  have hy : q.val.2.2 • p = p.val.2.2 • q := by
    apply hπ
    refine Prod.ext ?_ (mul_comm _ _)
    change q.val.2.2 * p.val.2.1 = p.val.2.2 * q.val.2.1
    rw [mul_comm q.val.2.2, mul_comm p.val.2.2]
    exact hd
  exact ⟨congrArg (fun v : Γ => v.val.1) hx, congrArg (fun v : Γ => v.val.1) hy⟩

/-- A finite set in the filter with pairwise gap determinants of absolute value
less than `C*f` contains at most two triples primitive in the original `(m,x)`
coordinates. The bound allows both signs. -/
public theorem card_le_two_of_small_gapDet {a : NormalizedCoordinate Γ} {f : ℕ}
    (hπ : Function.Injective (gapProjection Γ)) {S : Finset Γ}
    (hfilter : ∀ p ∈ S, p ∈ dividedFilter a f)
    (hprim : ∀ p ∈ S, Int.gcd p.val.1 p.val.2.1 = 1)
    (hsmall : ∀ p ∈ S, ∀ q ∈ S, (gapDet (gapProjection Γ p) (gapProjection Γ q)).natAbs <
      (gapProjection Γ).range.index * f) : S.card ≤ 2 := by
  have hzero (p) (hp : p ∈ S) (q) (hq : q ∈ S) :
      gapDet (gapProjection Γ p) (gapProjection Γ q) = 0 := by
    have hdiv := gapDet_dvd hπ (a := a) (f := f)
      (AddSubgroup.mem_map.mpr ⟨p, hfilter p hp, rfl⟩)
      (AddSubgroup.mem_map.mpr ⟨q, hfilter q hq, rfl⟩)
    exact Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hdiv
      (by simpa only [Int.natAbs_natCast] using hsmall p hp q hq)
  let mx : Γ → ℤ × ℤ := fun p => (p.val.1, p.val.2.1)
  -- On this collinear set, losing `y` does not identify two distinct triples.
  have hmx : Set.InjOn mx ↑S := by
    intro p hp q hq he
    have hm : p.val.1 = q.val.1 := congrArg (Prod.fst : ℤ × ℤ → ℤ) he
    have hx : p.val.2.1 = q.val.2.1 := congrArg (Prod.snd : ℤ × ℤ → ℤ) he
    have hy : p.val.2.2 = q.val.2.2 := by
      by_cases hm₀ : p.val.1 = 0
      · have hx₀ : p.val.2.1 ≠ 0 := by
          intro hx₀
          simpa [hm₀, hx₀] using hprim p hp
        have h : p.val.2.1 * q.val.2.2 = q.val.2.1 * p.val.2.2 :=
          sub_eq_zero.mp (hzero p hp q hq)
        rw [← hx] at h
        exact (mul_left_cancel₀ hx₀ h).symm
      · have h := (lift_gap_collinearity hπ (hzero p hp q hq)).2
        rw [← hm] at h
        exact (mul_right_cancel₀ hm₀ h).symm
    exact Subtype.ext (Prod.ext hm (Prod.ext hx hy))
  rw [← Finset.card_image_of_injOn hmx]
  apply MaskedGapDirections.card_le_two_of_primitive_collinear
  · intro p hp
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hp
    exact Int.isCoprime_iff_gcd_eq_one.mpr (hprim v hv)
  · intro p hp q hq
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hq
    apply sub_eq_zero.mpr
    change v.val.1 * w.val.2.1 = w.val.1 * v.val.2.1
    simpa only [mul_comm] using (lift_gap_collinearity hπ (hzero v hv w hw)).1

end DividedPlaneFilter
