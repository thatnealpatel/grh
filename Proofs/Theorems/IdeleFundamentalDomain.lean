module

public import Lemmas.IdeleUnitWindow
public import Mathlib.MeasureTheory.Group.FundamentalDomain
import Mathlib.NumberTheory.NumberField.ClassNumber

/-!
# The norm-one idelic fundamental domain

Definition A.2.3.6, (A.2.3.12)–(16), PDF pp. 549–550, takes one norm-one lift per
ideal class and translates the product of `E₀` with all finite integral units.
Proposition A.2.3.10(2), (A.2.3.25)–(26), p. 552, uses the norm-one exact sequence
(A.2.3.28) to prove coverage and invokes the integral-unit test for disjointness.
We use the norm-one infinite factor supplied by (A.2.3.24) and Lemma A.2.3.8(2),
not an unrestricted infinite factor in that step. Lean proves the integral-unit
test via the principal fractional ideal and its inverse, and proves Borel
measurability in the actual subgroup topology. This does not compute Haar mass.

Source reading: Pinned Markdown and numbered PDF text, not rendered pages.
-/

open MeasureTheory NumberField Set

namespace Masullo

variable {K : Type*} [Field K] [NumberField K]

local notation "I" => IdeleGroup (𝓞 K) K
local notation "I₁" => ideleNormOne (K := K)
local notation "P" => ClassGroup (𝓞 K)
local notation "U∞" => (InfiniteAdeleRing K)ˣ
local notation "G∞" => archimedeanNormOne (K := K)
local notation "d" => idelePrincipalNormOne (K := K)
local notation "ι" => Units.map (RingHom.toMonoidHom (algebraMap (𝓞 K) K))

/-- Masullo's `E_F¹`, the union of the class lifts' translates of the unit window. -/
@[expose] public noncomputable def ideleFundamentalDomain (v : InfinitePlace K) (r : P → I₁) :
    Set I₁ :=
  ⋃ p : P, (fun g : I₁ ↦ (r p)⁻¹ * g) ⁻¹' ideleUnitWindow v

/-- A translated unit window is Borel, without a section hypothesis. -/
public theorem measurableSet_ideleFundamentalDomain_piece [MeasurableSpace I₁] [BorelSpace I₁]
    (v : InfinitePlace K) (r : P → I₁) (p : P) :
    MeasurableSet ((fun g : I₁ ↦ (r p)⁻¹ * g) ⁻¹' ideleUnitWindow v) :=
  (measurableSet_ideleUnitWindow v).preimage (continuous_const.mul continuous_id).measurable

/-- A finite union of Borel translates gives a Borel idelic domain. -/
public theorem measurableSet_ideleFundamentalDomain [MeasurableSpace I₁] [BorelSpace I₁]
    (v : InfinitePlace K) (r : P → I₁) : MeasurableSet (ideleFundamentalDomain v r) := by
  exact MeasurableSet.iUnion (measurableSet_ideleFundamentalDomain_piece v r)

private theorem class_eq_one_of_mem_window {v : InfinitePlace K} {g : I₁}
    (hg : g ∈ ideleUnitWindow v) : ideleIdealClassNormOne g = 1 :=
  (ideleIdealClassNormOne_apply g).trans
    ((ideleIdealClass_eq_one_iff (g : I)).mpr ⟨1, g, hg.1, by simp⟩)

/-- Each translated piece lies in its given ideal class, hence the pieces are disjoint. -/
public theorem ideleFundamentalDomain_piece_subset (v : InfinitePlace K) (r : P → I₁)
    (hr : ∀ p, ideleIdealClassNormOne (r p) = p) (p : P) :
    (fun g : I₁ ↦ (r p)⁻¹ * g) ⁻¹' ideleUnitWindow v ⊆ ideleIdealClassNormOne ⁻¹' {p} := by
  intro g hg
  have h := class_eq_one_of_mem_window hg
  rw [map_mul, map_inv, hr p, inv_mul_eq_one] at h
  exact h.symm

/-- Pieces attached to different ideal classes are disjoint before taking the quotient. -/
public theorem pairwiseDisjoint_ideleFundamentalDomain_pieces (v : InfinitePlace K) (r : P → I₁)
    (hr : ∀ p, ideleIdealClassNormOne (r p) = p) :
    Pairwise (fun p q : P ↦ Disjoint
      ((fun g : I₁ ↦ (r p)⁻¹ * g) ⁻¹' ideleUnitWindow v)
      ((fun g : I₁ ↦ (r q)⁻¹ * g) ⁻¹' ideleUnitWindow v)) := by
  intro p q hpq
  refine Set.disjoint_left.mpr fun g hp hq ↦ hpq ?_
  exact (ideleFundamentalDomain_piece_subset v r hr p hp).symm.trans
    (ideleFundamentalDomain_piece_subset v r hr q hq)

private theorem class_principal (a : Kˣ) : ideleIdealClassNormOne (d a) = 1 :=
  (ideleIdealClassNormOne_apply _).trans (ideleIdealClass_diagonal a)

private theorem infinite_principal_integral (t : (𝓞 K)ˣ) :
    ideleInfinitePart (d (ι t) : I) = (archimedeanDiagonalUnit t : U∞) := by
  rw [coe_idelePrincipalNormOne, coe_archimedeanDiagonalUnit]
  exact ideleInfinitePart_integralUnit t

/-- In the identity-class window, no nontrivial principal multiplier can send one point
of the window to another. The finite factors first force an integral multiplier. -/
private theorem principal_eq_one_of_mem_windows (v : InfinitePlace K) (a : Kˣ) (b : I₁)
    (hb : b ∈ ideleUnitWindow v) (hab : d a * b ∈ ideleUnitWindow v) : a = 1 := by
  have hfinite : (d a : I) ∈ ideleFiniteUnits := by
    have h := ideleFiniteUnits.mul_mem hab.1 (ideleFiniteUnits.inv_mem hb.1)
    change (d a : I) * (b : I) * (b : I)⁻¹ ∈ ideleFiniteUnits at h
    rwa [mul_inv_cancel_right] at h
  obtain ⟨t, rfl⟩ := (idelePrincipalNormOne_mem_finiteUnits_iff a).mp hfinite
  obtain ⟨x, hx, heqx⟩ := hb.2
  obtain ⟨y, hy, heqy⟩ := hab.2
  have hxy : archimedeanDiagonalUnit t * x = y := by
    apply Subtype.ext
    change (archimedeanDiagonalUnit t : U∞) * (x : U∞) = (y : U∞)
    rw [heqy, Subgroup.coe_mul, map_mul, infinite_principal_integral, heqx]
  have htu := (existsUnique_archimedeanUnit_translate v x).unique
    (show archimedeanDiagonalUnit t * x ∈ archimedeanUnitDomain v from hxy ▸ hy)
    (show archimedeanDiagonalUnit 1 * x ∈ archimedeanUnitDomain v by simpa using hx)
  rw [htu, map_one]

/-- Proposition A.2.3.10(2): Exactly one diagonal field unit sends each actual
norm-one idele into the domain, including all half-open boundaries. -/
public theorem existsUnique_idelePrincipal_translate (v : InfinitePlace K) (r : P → I₁)
    (hr : ∀ p, ideleIdealClassNormOne (r p) = p) (g : I₁) :
    ∃! a : Kˣ, d a * g ∈ ideleFundamentalDomain v r := by
  -- Remove the matching class lift. The norm-one kernel factorization supplies `a` and `b`.
  let p := ideleIdealClassNormOne g
  let x := (r p)⁻¹ * g
  have hx : ideleIdealClassNormOne x = 1 := by
    change ideleIdealClassNormOne ((r p)⁻¹ * g) = 1
    rw [map_mul, map_inv, hr p, inv_mul_eq_one]
  obtain ⟨a, b, hb, hab⟩ := (ideleIdealClass_normOne_eq_one_iff x).mp
    ((ideleIdealClassNormOne_apply x).symm.trans hx)
  have hxb : x = d a * b := Subtype.ext hab
  -- The residual `b` has integral finite units. Reduce its infinite factor into `E₀`.
  let z : G∞ := ⟨ideleInfinitePart (b : I), ideleInfinitePart_mem_archimedeanNormOne b hb⟩
  obtain ⟨t, ht, _⟩ := existsUnique_archimedeanUnit_translate v z
  have hb' : d (ι t) * b ∈ ideleUnitWindow v := by
    refine ⟨ideleFiniteUnits.mul_mem ((idelePrincipalNormOne_mem_finiteUnits_iff _).mpr ⟨t, rfl⟩) hb,
      ⟨archimedeanDiagonalUnit t * z, ht, ?_⟩⟩
    change (archimedeanDiagonalUnit t : U∞) * ideleInfinitePart (b : I) =
      ideleInfinitePart ((d (ι t) : I) * (b : I))
    rw [map_mul, infinite_principal_integral]
  let a₀ := ι t * a⁻¹
  have hmul (c : Kˣ) : (r p)⁻¹ * (d c * g) = d c * x := by
    dsimp only [x]
    ac_rfl
  have h₀ : (r p)⁻¹ * (d a₀ * g) ∈ ideleUnitWindow v := by
    rw [hmul, hxb, show a₀ = ι t * a⁻¹ from rfl, map_mul, map_inv, mul_assoc, inv_mul_cancel_left]
    exact hb'
  refine ⟨a₀, mem_iUnion.mpr ⟨p, h₀⟩, ?_⟩
  -- A competitor reaches the same class piece. Its ratio to `a₀` relates two window points.
  intro c hc
  obtain ⟨q, hq⟩ := mem_iUnion.mp hc
  have hpq : p = q := by
    have h := ideleFundamentalDomain_piece_subset v r hr q hq
    change ideleIdealClassNormOne (d c * g) = q at h
    rwa [map_mul, class_principal, one_mul] at h
  subst q
  have heq : d (c * a₀⁻¹) * ((r p)⁻¹ * (d a₀ * g)) = (r p)⁻¹ * (d c * g) := by
    rw [hmul, hmul, map_mul, map_inv, mul_assoc, inv_mul_cancel_left]
  have hone := principal_eq_one_of_mem_windows v (c * a₀⁻¹) _ h₀ (heq ▸ hq)
  exact mul_inv_eq_one.mp hone

/-- The pointwise domain is a Mathlib fundamental domain for the principal subgroup,
for every Borel measure on the norm-one ideles. The opposite subgroup acts by right
translation, which is the same as left translation here. -/
public theorem isFundamentalDomain_ideleFundamentalDomain [MeasurableSpace I₁] [BorelSpace I₁]
    (v : InfinitePlace K) (r : P → I₁) (hr : ∀ p, ideleIdealClassNormOne (r p) = p)
    (μ : Measure I₁) : IsFundamentalDomain (d).range.op (ideleFundamentalDomain v r) μ := by
  apply IsFundamentalDomain.mk' (measurableSet_ideleFundamentalDomain v r).nullMeasurableSet
  intro g
  obtain ⟨a, ha, huniq⟩ := existsUnique_idelePrincipal_translate v r hr g
  let t : (d).range.op := ⟨MulOpposite.op (d a), ⟨a, rfl⟩⟩
  refine ⟨t, ?_, ?_⟩
  · change g * d a ∈ ideleFundamentalDomain v r
    simpa only [mul_comm g] using ha
  · intro s hs
    obtain ⟨b, hb⟩ := s.property
    have h : g * d b ∈ ideleFundamentalDomain v r := by
      change g * MulOpposite.unop s.val ∈ _ at hs
      rwa [hb]
    have hba : b = a := huniq b (by simpa only [mul_comm g] using h)
    exact Subtype.ext (MulOpposite.unop_injective (by rw [← hb, hba]; rfl))

end Masullo
