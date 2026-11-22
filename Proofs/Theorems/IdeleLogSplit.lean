module

public import Theorems.IdeleLogSection
public import Mathlib.Topology.Algebra.Group.Units

import Lemmas.ContinuousNormSplit

/-!
# Product splittings of ideles and idele classes by log norm

In Lemma A.2.2.9, (A.2.2.12), PDF p. 547, the section multiplies the
norm-one factor to reconstruct an idele. The word "homomorphism" in the
conclusion requires the section to be homomorphic, as supplied for the
single-place section by Lemma A.2.2.6 and assumed in §A.3.3.1, p. 561.
The descended section gives the same product on classes, and the
quotient map acts on the norm-one coordinate only. This is the
splitting used in §A.3.3.1, not its Radon measure decomposition.
-/

open NumberField

namespace Masullo

variable {K : Type*} [Field K] [NumberField K]

local notation "I" => IdeleGroup (𝓞 K) K
local notation "C" => IdeleClassGroup (𝓞 K) K
local notation "L" => Multiplicative ℝ

/-- The logarithm of the positive norm on actual idele classes. -/
public noncomputable def ideleClassLogNorm : C →ₜ* L :=
  logPositiveHom (G := C) ideleClassNorm ideleClassNorm_pos continuous_ideleClassNorm

public theorem ideleClassLogNorm_apply (g : C) :
    (ideleClassLogNorm g).toAdd = Real.log (ideleClassNorm g) := by
  unfold ideleClassLogNorm
  rfl

/-- The logarithm of the positive norm on actual ideles. -/
public noncomputable def ideleLogNorm : I →ₜ* L :=
  logPositiveHom ideleNorm (fun g ↦ ideleClassNorm_mk g ▸ ideleClassNorm_pos (QuotientGroup.mk g))
    continuous_ideleNorm

public theorem ideleLogNorm_apply (g : I) :
    (ideleLogNorm g).toAdd = Real.log (ideleNorm g) := by
  unfold ideleLogNorm
  rfl

public theorem ideleClassLogNorm_mk (g : I) :
    ideleClassLogNorm (QuotientGroup.mk g) = ideleLogNorm g := by
  apply Multiplicative.toAdd.injective
  rw [ideleClassLogNorm_apply, ideleLogNorm_apply, ideleClassNorm_mk]

public noncomputable def ideleNormOne : Subgroup I := ideleLogNorm.toMonoidHom.ker

public noncomputable def ideleClassNormOne : Subgroup C := ideleClassLogNorm.toMonoidHom.ker

public theorem mem_ideleNormOne (g : I) : g ∈ ideleNormOne ↔ ideleNorm g = 1 :=
  mem_ker_logPositiveHom ideleNorm _ _ g

public theorem mem_ideleClassNormOne (g : C) : g ∈ ideleClassNormOne ↔ ideleClassNorm g = 1 :=
  mem_ker_logPositiveHom ideleClassNorm _ _ g

/-- Lemma A.2.2.9 in log coordinates, for any continuous homomorphic section. -/
public noncomputable def ideleLogSplit (s : L →ₜ* I) (hs : ∀ x, ideleLogNorm (s x) = x) :
    (L × ideleNormOne (K := K)) ≃ₜ* I :=
  continuousMulEquivOfSection (G := I) ideleLogNorm s hs (fun x g ↦ mul_comm (s x) g)

public theorem ideleLogSplit_apply (s : L →ₜ* I) (hs : ∀ x, ideleLogNorm (s x) = x)
    (p : L × ideleNormOne (K := K)) : ideleLogSplit s hs p = s p.1 * p.2 := by
  unfold ideleLogSplit
  rfl

public theorem ideleLogSplit_symm (s : L →ₜ* I) (hs : ∀ x, ideleLogNorm (s x) = x) (g : I) :
    (ideleLogSplit s hs).symm g = (ideleLogNorm g, ⟨(s (ideleLogNorm g))⁻¹ * g, by
      change ideleLogNorm ((s (ideleLogNorm g))⁻¹ * g) = 1
      rw [map_mul, map_inv, hs, inv_mul_cancel]⟩) := by
  unfold ideleLogSplit
  rfl

/-- The log-norm splitting on the quotient by principal ideles. -/
public noncomputable def ideleClassLogSplit (s : L →ₜ* C)
    (hs : ∀ x, ideleClassLogNorm (s x) = x) : (L × ideleClassNormOne (K := K)) ≃ₜ* C :=
  continuousMulEquivOfSection (G := C) ideleClassLogNorm s hs (fun x g ↦ mul_comm (s x) g)

public theorem ideleClassLogSplit_apply (s : L →ₜ* C) (hs : ∀ x, ideleClassLogNorm (s x) = x)
    (p : L × ideleClassNormOne (K := K)) : ideleClassLogSplit s hs p = s p.1 * p.2 := by
  unfold ideleClassLogSplit
  rfl

public theorem ideleClassLogSplit_symm (s : L →ₜ* C) (hs : ∀ x, ideleClassLogNorm (s x) = x)
    (g : C) : (ideleClassLogSplit s hs).symm g =
      (ideleClassLogNorm g, ⟨(s (ideleClassLogNorm g))⁻¹ * g, by
        change ideleClassLogNorm ((s (ideleClassLogNorm g))⁻¹ * g) = 1
        rw [map_mul, map_inv, hs, inv_mul_cancel]⟩) := by
  unfold ideleClassLogSplit
  rfl

/-- The single-place section from (A.2.2.10) satisfies the splitting hypothesis. -/
public theorem ideleLogNorm_section (v : InfinitePlace K) (x : L) :
    ideleLogNorm (ideleLogSection v x) = x := by
  apply Multiplicative.toAdd.injective
  rw [ideleLogNorm_apply, ideleNorm_ideleLogSection, Real.log_exp]

public theorem ideleClassLogNorm_section (v : InfinitePlace K) (x : L) :
    ideleClassLogNorm (ideleClassLogSection v x) = x := by
  rw [ideleClassLogSection_apply, ideleClassLogNorm_mk, ideleLogNorm_section]

/-- On the split groups the quotient to idele classes preserves the log coordinate
and sends the norm-one idele to its norm-one class. -/
public theorem ideleClassLogSplit_mk (v : InfinitePlace K) (p : L × ideleNormOne (K := K)) :
    ideleClassLogSplit (ideleClassLogSection v) (ideleClassLogNorm_section v)
        (p.1, ⟨QuotientGroup.mk (p.2 : I), by
          change ideleClassLogNorm (QuotientGroup.mk (p.2 : I)) = 1
          rw [ideleClassLogNorm_mk]
          exact p.2.property⟩) =
      QuotientGroup.mk (ideleLogSplit (ideleLogSection v) (ideleLogNorm_section v) p) := by
  rw [ideleClassLogSplit_apply, ideleLogSplit_apply, ideleClassLogSection_apply,
    QuotientGroup.mk_mul]

end Masullo
