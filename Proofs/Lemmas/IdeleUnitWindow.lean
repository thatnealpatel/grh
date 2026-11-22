module

public import Theorems.ArchimedeanUnitDomain
public import Theorems.IdeleClassCompact

/-! # The integral-finite window in the norm-one ideles

These lemmas implement the product in (A.2.3.14), PDF p. 549, in the actual idele
group, and prove the global-unit criterion used in Proposition A.2.3.10(2), p. 552.
-/

open IsDedekindDomain MeasureTheory NumberField Set
open scoped nonZeroDivisors

namespace Masullo

variable {K : Type*} [Field K] [NumberField K]

local notation "A" => AdeleRing (𝓞 K) K
local notation "I" => IdeleGroup (𝓞 K) K
local notation "I₁" => ideleNormOne (K := K)
local notation "U∞" => (InfiniteAdeleRing K)ˣ
local notation "G∞" => archimedeanNormOne (K := K)
local notation "ι" => Units.map (RingHom.toMonoidHom (algebraMap (𝓞 K) K))

/-- The diagonal field units have idelic norm one by the product formula. -/
@[expose] public noncomputable def idelePrincipalNormOne : Kˣ →* I₁ :=
  (IdeleGroup.unitEmbedding (𝓞 K) K).codRestrict I₁ fun a ↦ by
    apply (mem_ideleNormOne _).mpr
    rw [ideleNorm_apply]
    exact AdeleRing.norm_algebraMap_eq_one_of_ne_zero a.ne_zero

public theorem coe_idelePrincipalNormOne (a : Kˣ) :
    (idelePrincipalNormOne a : I) = IdeleGroup.unitEmbedding (𝓞 K) K a := rfl

public theorem idelePrincipalNormOne_injective :
    Function.Injective (idelePrincipalNormOne (K := K)) := fun _ _ h ↦
  Units.map_injective (AdeleRing.algebraMap_injective (R := 𝓞 K) (K := K)) (congrArg Subtype.val h)

/-- A diagonal lies in the empty finite stage exactly when it comes from an integral unit. -/
public theorem idelePrincipalNormOne_mem_finiteUnits_iff (a : Kˣ) :
    (idelePrincipalNormOne a : I) ∈ ideleFiniteUnits ↔ ∃ u : (𝓞 K)ˣ, ι u = a := by
  constructor
  · intro h
    have h : finiteIdeleIdeal K (FiniteAdeleRing.unitEmbedding (𝓞 K) K a) = 1 := by
      apply (finiteIdeleIdeal_eq_one_iff _).mpr
      intro v
      exact (mem_ideleFiniteUnits _).mp h v
    have h' : FractionalIdeal.spanSingleton (𝓞 K)⁰ (a : K) = 1 := by
      rw [← finiteIdeleIdeal_unitEmbedding, h]
      rfl
    have hi : finiteIdeleIdeal K (FiniteAdeleRing.unitEmbedding (𝓞 K) K a⁻¹) = 1 := by
      rw [map_inv, map_inv, h, inv_one]
    have hi' : FractionalIdeal.spanSingleton (𝓞 K)⁰ (↑(a⁻¹) : K) = 1 := by
      rw [← finiteIdeleIdeal_unitEmbedding, hi]
      rfl
    have ha := FractionalIdeal.mem_spanSingleton_self (𝓞 K)⁰ (a : K)
    have hb := FractionalIdeal.mem_spanSingleton_self (𝓞 K)⁰ (↑(a⁻¹) : K)
    rw [h', FractionalIdeal.mem_one_iff] at ha
    rw [hi', FractionalIdeal.mem_one_iff] at hb
    obtain ⟨x, hx⟩ := ha
    obtain ⟨y, hy⟩ := hb
    have hxy : x * y = 1 := by
      apply IsFractionRing.injective (𝓞 K) K
      rw [map_mul, hx, hy, ← Units.val_mul, mul_inv_cancel, map_one, Units.val_one]
    exact ⟨⟨x, y, hxy, by rw [mul_comm, hxy]⟩, Units.ext hx⟩
  · rintro ⟨u, rfl⟩
    rw [coe_idelePrincipalNormOne]
    exact integralUnit_mem_ideleFiniteUnits u

/-- The infinite component of a norm-one idele in the empty finite stage has norm one. -/
public theorem ideleInfinitePart_mem_archimedeanNormOne (g : I₁)
    (hg : (g : I) ∈ ideleFiniteUnits) : ideleInfinitePart (g : I) ∈ archimedeanNormOne := by
  simp only [mem_archimedeanNormOne, archimedeanNorm_apply, ideleInfinitePart_val]
  change (∏ w : InfinitePlace K, ‖(((g : I) : A).1 w)‖ ^ w.mult) = 1
  rw [← ideleNorm_of_mem_ideleFiniteUnits hg]
  exact (mem_ideleNormOne _).mp g.property

/-- The set `E₀ × Ōˣ` on the norm-one subgroup, using the actual infinite projection. -/
@[expose] public noncomputable def ideleUnitWindow (v : InfinitePlace K) : Set I₁ :=
  {g | (g : I) ∈ ideleFiniteUnits ∧
    ideleInfinitePart (g : I) ∈ ((↑) : G∞ → U∞) '' archimedeanUnitDomain v}

/-- The integral-finite window for `E₀` is Borel in the actual norm-one ideles. -/
public theorem measurableSet_ideleUnitWindow [MeasurableSpace I₁] [BorelSpace I₁]
    (v : InfinitePlace K) : MeasurableSet (ideleUnitWindow v) := by
  classical
  let : MeasurableSpace U∞ := borel _
  let : BorelSpace U∞ := ⟨rfl⟩
  have hfinite : IsOpen (ideleFiniteUnits (K := K) : Set I) := by
    rw [← range_ideleFiniteStageEmbedding_empty]
    exact (isOpenEmbedding_ideleFiniteStageEmbedding K ∅).isOpen_range
  have hnorm : IsClosed (archimedeanNormOne (K := K) : Set U∞) := by
    rw [show (G∞ : Set U∞) = archimedeanNorm (K := K) ⁻¹' {1} from
      Set.ext (mem_archimedeanNormOne (K := K))]
    apply isClosed_singleton.preimage
    change Continuous (fun g : U∞ ↦ archimedeanNorm g)
    simp only [archimedeanNorm_apply]
    exact continuous_finsetProd _ fun w _ ↦
      (((continuous_apply w).comp Units.continuous_val).norm).pow _
  exact (hfinite.preimage continuous_subtype_val).measurableSet.inter
    (((MeasurableEmbedding.subtype_coe hnorm.measurableSet).measurableSet_image.mpr
      (measurableSet_archimedeanUnitDomain v)).preimage
      (continuous_ideleInfinitePart.comp continuous_subtype_val).measurable)

end Masullo
