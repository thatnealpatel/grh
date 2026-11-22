module

public import Theorems.FiniteIdeleIdeal
public import Theorems.IdeleLogSplit
public import Mathlib.RingTheory.ClassGroup.Basic

/-!
# The idelic map to the ideal class group

Masullo, Proposition A.2.3.9, (A.2.3.23) and (A.2.3.24), PDF p. 552,
asserts strict exactness and uses it in Proposition A.2.3.10. The classical
quotient description in §A.1.5.3, pp. 544–545, does not give a placewise
construction of the arrow. We take the class of the
fractional ideal of the finite part, and use the diagonal formula to
identify its kernel. For the norm-one restriction we correct each lift
by the section from (A.2.2.10), p. 547, without changing its finite part.
Here we prove the algebraic assertions, not strict topological exactness.
-/

open IsDedekindDomain NumberField
open scoped nonZeroDivisors

namespace Masullo

variable {K : Type*} [Field K] [NumberField K]

local notation "A" => AdeleRing (𝓞 K) K
local notation "F" => FiniteAdeleRing (𝓞 K) K
local notation "I" => IdeleGroup (𝓞 K) K
local notation "C" => IdeleClassGroup (𝓞 K) K
local notation "P" => ClassGroup (𝓞 K)
local notation "V" => HeightOneSpectrum (𝓞 K)

/-- Project an idele onto its finite part. -/
public noncomputable def ideleFinitePart : I →* Fˣ :=
  Units.map (MonoidHom.snd (InfiniteAdeleRing K) F)

private theorem ideleFinitePart_surjective : Function.Surjective (ideleFinitePart (K := K)) := by
  intro f
  refine ⟨MulEquiv.prodUnits.symm (1, f), ?_⟩
  exact congrArg Prod.snd (MulEquiv.prodUnits.apply_symm_apply (1, f))

/-- The subgroup with an integral unit at each finite place and arbitrary infinite part. -/
public noncomputable def ideleFiniteUnits : Subgroup I :=
  ((finiteIdeleIdeal K).comp ideleFinitePart).ker

public theorem mem_ideleFiniteUnits (g : I) : g ∈ ideleFiniteUnits ↔
    ∀ v : V, Valued.v ((g : A).2 v) = 1 :=
  finiteIdeleIdeal_eq_one_iff (ideleFinitePart g)

/-- On this subgroup the idelic norm is exactly the normalized Archimedean product. -/
public theorem ideleNorm_of_mem_ideleFiniteUnits {u : I} (hu : u ∈ ideleFiniteUnits) :
    ideleNorm u = ∏ w : InfinitePlace K, ‖(u : A).1 w‖ ^ w.mult := by
  have hloc (v : V) : ‖(u : A).2 v‖ = 1 :=
    Valued.toNormedField.norm_eq_one_iff.mpr ((mem_ideleFiniteUnits u).mp hu v)
  rw [ideleNorm_apply, AdeleRing.norm_apply_of_isUnit u.isUnit]
  simp only [hloc, finprod_one, mul_one]

/-- The last nontrivial arrow in (A.2.3.23): Take the class of the finite ideal. -/
public noncomputable def ideleIdealClass : I →* P :=
  (ClassGroup.mk K).comp ((finiteIdeleIdeal K).comp ideleFinitePart)

public theorem ideleIdealClass_apply (g : I) :
    ideleIdealClass g = ClassGroup.mk K (finiteIdeleIdeal K (ideleFinitePart g)) := by
  unfold ideleIdealClass
  rfl

private theorem finiteIdeal_diagonal (a : Kˣ) :
    finiteIdeleIdeal K (ideleFinitePart (IdeleGroup.unitEmbedding (𝓞 K) K a)) =
      toPrincipalIdeal (𝓞 K) K a := by
  apply Units.ext
  change (finiteIdeleIdeal K (FiniteAdeleRing.unitEmbedding (𝓞 K) K a) :
    FractionalIdeal (𝓞 K)⁰ K) = _
  rw [finiteIdeleIdeal_unitEmbedding, coe_toPrincipalIdeal]

private theorem idealClass_eq_one_iff {j : (FractionalIdeal (nonZeroDivisors (𝓞 K)) K)ˣ} :
    ClassGroup.mk K j = 1 ↔ ∃ a : Kˣ, toPrincipalIdeal (𝓞 K) K a = j := by
  rw [← (ClassGroup.equiv K).injective.eq_iff, ClassGroup.equiv_mk, map_one]
  simp only [FractionalIdeal.canonicalEquiv_self, QuotientGroup.mk'_apply,
    QuotientGroup.eq_one_iff, MonoidHom.mem_range]
  rfl

public theorem ideleIdealClass_diagonal (a : Kˣ) :
    ideleIdealClass (IdeleGroup.unitEmbedding (𝓞 K) K a) = 1 :=
  idealClass_eq_one_iff.mpr ⟨a, (finiteIdeal_diagonal a).symm⟩

/-- The kernel in (A.2.3.23): A principal idele times one with integral finite units. -/
public theorem ideleIdealClass_eq_one_iff (g : I) : ideleIdealClass g = 1 ↔
    ∃ (a : Kˣ) (u : I), u ∈ ideleFiniteUnits ∧
      g = IdeleGroup.unitEmbedding (𝓞 K) K a * u := by
  constructor
  · intro hg
    obtain ⟨a, ha⟩ := idealClass_eq_one_iff.mp hg
    let d := IdeleGroup.unitEmbedding (𝓞 K) K a
    refine ⟨a, d⁻¹ * g, ?_, (mul_inv_cancel_left d g).symm⟩
    change ((finiteIdeleIdeal K).comp ideleFinitePart) (d⁻¹ * g) = 1
    rw [map_mul, map_inv, MonoidHom.comp_apply, MonoidHom.comp_apply]
    rw [finiteIdeal_diagonal]
    change toPrincipalIdeal (𝓞 K) K a = finiteIdeleIdeal K (ideleFinitePart g) at ha
    rw [ha, inv_mul_cancel]
  · rintro ⟨a, u, hu, rfl⟩
    have h : ideleIdealClass u = 1 := by
      change ((finiteIdeleIdeal K).comp ideleFinitePart) u = 1 at hu
      change ClassGroup.mk K (((finiteIdeleIdeal K).comp ideleFinitePart) u) = 1
      rw [hu, map_one]
    rw [map_mul, ideleIdealClass_diagonal, h, one_mul]

public theorem ideleIdealClass_surjective : Function.Surjective (ideleIdealClass (K := K)) := by
  intro c
  refine ClassGroup.induction K ?_ c
  intro j
  obtain ⟨f, rfl⟩ := finiteIdeleIdeal_surjective K j
  obtain ⟨g, rfl⟩ := ideleFinitePart_surjective f
  exact ⟨g, ideleIdealClass_apply g⟩

/-- The right-hand map factors through the quotient by principal ideles. -/
public noncomputable def ideleClassIdealClass : C →* P :=
  QuotientGroup.lift (IdeleGroup.principalSubgroup (𝓞 K) K) ideleIdealClass (by
    rintro _ ⟨a, rfl⟩
    exact ideleIdealClass_diagonal a)

public theorem ideleClassIdealClass_mk (g : I) :
    ideleClassIdealClass (QuotientGroup.mk g) = ideleIdealClass g := by
  unfold ideleClassIdealClass
  rfl

public theorem ideleClassIdealClass_surjective :
    Function.Surjective (ideleClassIdealClass (K := K)) := by
  intro c
  obtain ⟨g, hg⟩ := ideleIdealClass_surjective c
  exact ⟨QuotientGroup.mk g, hg⟩

/-- The kernel in (A.2.3.24): The second factor can also be taken to have norm one. -/
public theorem ideleIdealClass_normOne_eq_one_iff (g : ideleNormOne (K := K)) :
    ideleIdealClass (g : I) = 1 ↔ ∃ (a : Kˣ) (u : ideleNormOne (K := K)),
      (u : I) ∈ ideleFiniteUnits ∧ (g : I) = IdeleGroup.unitEmbedding (𝓞 K) K a * (u : I) := by
  constructor
  · intro hg
    obtain ⟨a, u, hu, hgu⟩ := (ideleIdealClass_eq_one_iff (g : I)).mp hg
    have hn := (mem_ideleNormOne (g : I)).mp g.property
    rw [hgu, map_mul, ideleNorm_apply (IdeleGroup.unitEmbedding (𝓞 K) K a)] at hn
    change ‖algebraMap K A (a : K)‖ * ideleNorm u = 1 at hn
    rw [AdeleRing.norm_algebraMap_eq_one_of_ne_zero a.ne_zero, one_mul] at hn
    exact ⟨a, ⟨u, (mem_ideleNormOne u).mpr hn⟩, hu, hgu⟩
  · rintro ⟨a, u, hu, hgu⟩
    exact (ideleIdealClass_eq_one_iff (g : I)).mpr ⟨a, u, hu, hgu⟩

/-- Every ideal class has a norm-one idelic lift: Correct only the Archimedean part. -/
public theorem ideleIdealClass_normOne_surjective :
    Function.Surjective (fun g : ideleNormOne (K := K) ↦ ideleIdealClass (g : I)) := by
  intro c
  obtain ⟨g, hg⟩ := ideleIdealClass_surjective c
  obtain ⟨v⟩ := (inferInstance : Nonempty (InfinitePlace K))
  let s := ideleLogSection v (ideleLogNorm g)
  have hs : ideleFinitePart s = 1 := by
    apply Units.ext
    apply DFunLike.ext
    intro w
    change (s : A).2 w = 1
    exact ideleLogSection_finite v (ideleLogNorm g) w
  refine ⟨⟨s⁻¹ * g, ?_⟩, ?_⟩
  · apply (mem_ideleNormOne _).mpr
    rw [map_mul, map_inv]
    change (ideleNorm (ideleLogSection v (ideleLogNorm g)))⁻¹ * ideleNorm g = 1
    rw [ideleNorm_ideleLogSection, ideleLogNorm_apply,
      Real.exp_log (ideleClassNorm_mk g ▸ ideleClassNorm_pos (QuotientGroup.mk g))]
    exact inv_mul_cancel₀ (ideleClassNorm_mk g ▸ (ideleClassNorm_pos (QuotientGroup.mk g)).ne')
  · change ClassGroup.mk K (finiteIdeleIdeal K (ideleFinitePart (s⁻¹ * g))) = c
    rw [map_mul, map_inv, hs, inv_one, one_mul]
    rwa [ideleIdealClass_apply] at hg

public theorem ideleClassIdealClass_normOne_surjective :
    Function.Surjective (fun c : ideleClassNormOne (K := K) ↦ ideleClassIdealClass (c : C)) := by
  intro c
  obtain ⟨g, hg⟩ := ideleIdealClass_normOne_surjective c
  refine ⟨⟨QuotientGroup.mk (g : I), (mem_ideleClassNormOne _).mpr ?_⟩, ?_⟩
  · rw [ideleClassNorm_mk]
    exact (mem_ideleNormOne _).mp g.property
  · change ideleClassIdealClass (QuotientGroup.mk (g : I)) = c
    rw [ideleClassIdealClass_mk]
    exact hg

/-- On norm-one idele classes the kernel consists of classes of norm-one ideles
with integral finite units. -/
public theorem ideleClassIdealClass_normOne_eq_one_iff (c : ideleClassNormOne (K := K)) :
    ideleClassIdealClass (c : C) = 1 ↔ ∃ u : ideleNormOne (K := K),
      (u : I) ∈ ideleFiniteUnits ∧ QuotientGroup.mk (u : I) = (c : C) := by
  constructor
  · intro hc
    obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective (c : C)
    have hn : g ∈ ideleNormOne := by
      apply (mem_ideleNormOne g).mpr
      rw [← ideleClassNorm_mk, hg]
      exact (mem_ideleClassNormOne (c : C)).mp c.property
    have hclass : ideleIdealClass g = 1 := by
      rw [← ideleClassIdealClass_mk, hg, hc]
    obtain ⟨a, u, hu, hgu⟩ := (ideleIdealClass_normOne_eq_one_iff ⟨g, hn⟩).mp hclass
    refine ⟨u, hu, ?_⟩
    change g = _ at hgu
    have hdiag : (QuotientGroup.mk (IdeleGroup.unitEmbedding (𝓞 K) K a) : C) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr ⟨a, rfl⟩
    rw [← hg, hgu, QuotientGroup.mk_mul, hdiag]
    exact (one_mul (QuotientGroup.mk (u : I) : C)).symm
  · rintro ⟨u, hu, h⟩
    rw [← h, ideleClassIdealClass_mk, ideleIdealClass_eq_one_iff]
    exact ⟨1, u, hu, by simp⟩

end Masullo
