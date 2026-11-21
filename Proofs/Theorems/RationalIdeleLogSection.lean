module

public import Lemmas.RationalIdeleReal
public import Mathlib.Topology.Algebra.Group.Units
public import Mathlib.Topology.Algebra.ContinuousMonoidHom

import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# The canonical log-norm section over the rationals

In log coordinates the section (A.2.2.4), p. 546, sends `x` to the idele
with real coordinate `exp x` and every finite coordinate one. On idele
classes this gives the norm-one product, the analogue of the idele-level
splitting (A.2.2.12), p. 547. Neither the identification of the norm-one
factor with the finite integral units nor the Haar normalization is part
of this result.
-/

open NumberField IsDedekindDomain

namespace Masullo

private noncomputable def realCompletionEquiv : Rat.infinitePlace.Completion ≃+* ℝ :=
  InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace

private theorem continuous_realCompletionEquiv_symm : Continuous realCompletionEquiv.symm := by
  let e : Rat.infinitePlace.Completion ≃ᵢ ℝ := ⟨realCompletionEquiv.toEquiv,
    InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal Rat.isReal_infinitePlace⟩
  exact e.symm.isometry.continuous

private noncomputable def logSectionValue : Multiplicative ℝ →* AdeleRing (𝓞 ℚ) ℚ :=
  (AdeleRing.ofCompletion (𝓞 ℚ) ℚ Rat.infinitePlace).comp
    (realCompletionEquiv.symm.toMonoidHom.comp Real.expMonoidHom)

private theorem continuous_logSectionValue : Continuous logSectionValue := by
  let := Classical.decEq (InfinitePlace ℚ)
  have hr : Continuous (fun x : Multiplicative ℝ ↦ realCompletionEquiv.symm (Real.exp x.toAdd)) :=
    continuous_realCompletionEquiv_symm.comp Real.continuous_exp
  change Continuous (fun x : Multiplicative ℝ ↦ (Pi.mulSingle Rat.infinitePlace
    (realCompletionEquiv.symm (Real.exp x.toAdd)),
    (1 : IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)))
  exact ((continuous_mulSingle Rat.infinitePlace).comp hr).prodMk continuous_const

/-- The section `x ↦ (exp x, 1, …)` as a continuous homomorphism into the rational ideles. -/
public noncomputable def rationalIdeleLogSection :
    Multiplicative ℝ →ₜ* IdeleGroup (𝓞 ℚ) ℚ where
  toMonoidHom := logSectionValue.toHomUnits
  continuous_toFun := Units.continuous_iff.mpr
    ⟨continuous_logSectionValue, continuous_logSectionValue.comp continuous_inv⟩

public theorem rationalIdeleReal_logSection (x : Multiplicative ℝ) :
    rationalIdeleReal (rationalIdeleLogSection x) = Real.exp x.toAdd := by
  let := Classical.decEq (InfinitePlace ℚ)
  unfold rationalIdeleReal rationalIdeleLogSection logSectionValue
  change realCompletionEquiv (Pi.mulSingle Rat.infinitePlace
    (realCompletionEquiv.symm (Real.exp x.toAdd)) Rat.infinitePlace) = _
  rw [Pi.mulSingle_eq_same, RingEquiv.apply_symm_apply]

public theorem rationalIdeleLogSection_finite (x : Multiplicative ℝ)
    (v : HeightOneSpectrum (𝓞 ℚ)) :
    (rationalIdeleLogSection x : AdeleRing (𝓞 ℚ) ℚ).2 v = 1 := by
  unfold rationalIdeleLogSection logSectionValue
  rfl

public theorem ideleNorm_logSection (x : Multiplicative ℝ) :
    ideleNorm (rationalIdeleLogSection x) = Real.exp x.toAdd := by
  rw [ideleNorm_eq_abs_rationalIdeleReal, rationalIdeleReal_logSection,
    abs_of_pos (Real.exp_pos _)]
  intro v
  rw [rationalIdeleLogSection_finite, map_one]

/-- The induced section to the log norm on rational idele classes. -/
public noncomputable def rationalIdeleClassLogSection :
    Multiplicative ℝ →ₜ* IdeleClassGroup (𝓞 ℚ) ℚ where
  toMonoidHom := (QuotientGroup.mk' _).comp rationalIdeleLogSection.toMonoidHom
  continuous_toFun := QuotientGroup.continuous_mk.comp (map_continuous rationalIdeleLogSection)

public theorem rationalIdeleClassLogSection_apply (x : Multiplicative ℝ) :
    rationalIdeleClassLogSection x = QuotientGroup.mk (rationalIdeleLogSection x) := by
  unfold rationalIdeleClassLogSection
  rfl

/-- The logarithm of the positive idelic norm, in multiplicative notation. -/
public noncomputable def rationalIdeleClassLogNorm :
    IdeleClassGroup (𝓞 ℚ) ℚ →ₜ* Multiplicative ℝ where
  toFun g := Multiplicative.ofAdd (Real.log (ideleClassNorm g))
  map_one' := by rw [map_one, Real.log_one]; rfl
  map_mul' g h := by
    change Multiplicative.ofAdd (Real.log (ideleClassNorm (g * h))) =
      Multiplicative.ofAdd (Real.log (ideleClassNorm g) + Real.log (ideleClassNorm h))
    rw [map_mul, Real.log_mul (ideleClassNorm_pos g).ne' (ideleClassNorm_pos h).ne']
  continuous_toFun := continuous_iff_continuousAt.mpr fun g ↦
    (Real.continuousAt_log (ideleClassNorm_pos g).ne').comp continuous_ideleClassNorm.continuousAt

public theorem rationalIdeleClassLogNorm_apply (g : IdeleClassGroup (𝓞 ℚ) ℚ) :
    (rationalIdeleClassLogNorm g).toAdd = Real.log (ideleClassNorm g) := by
  unfold rationalIdeleClassLogNorm
  rfl

@[simp]
public theorem rationalIdeleClassLogNorm_section (x : Multiplicative ℝ) :
    rationalIdeleClassLogNorm (rationalIdeleClassLogSection x) = x := by
  change Multiplicative.ofAdd (Real.log (ideleClassNorm (QuotientGroup.mk
    (rationalIdeleLogSection x)))) = x
  rw [ideleClassNorm_mk, ideleNorm_logSection, Real.log_exp]
  rfl

/-- The subgroup of rational idele classes of norm one. -/
public noncomputable def rationalIdeleClassNormOne : Subgroup (IdeleClassGroup (𝓞 ℚ) ℚ) :=
  rationalIdeleClassLogNorm.toMonoidHom.ker

public theorem mem_rationalIdeleClassNormOne (g : IdeleClassGroup (𝓞 ℚ) ℚ) :
    g ∈ rationalIdeleClassNormOne ↔ ideleClassNorm g = 1 := by
  change Real.log (ideleClassNorm g) = 0 ↔ _
  constructor
  · intro h
    rw [← Real.exp_log (ideleClassNorm_pos g), h, Real.exp_zero]
  · intro h
    rw [h, Real.log_one]

private noncomputable def normOneComponent (g : IdeleClassGroup (𝓞 ℚ) ℚ) :
    rationalIdeleClassNormOne :=
  ⟨(rationalIdeleClassLogSection (rationalIdeleClassLogNorm g))⁻¹ * g, by
    change rationalIdeleClassLogNorm (_⁻¹ * g) = 1
    rw [map_mul, map_inv, rationalIdeleClassLogNorm_section, inv_mul_cancel]⟩

private theorem continuous_normOneComponent : Continuous normOneComponent := by
  have hs := (map_continuous rationalIdeleClassLogSection).comp
    (map_continuous rationalIdeleClassLogNorm)
  exact (hs.inv.mul continuous_id).subtype_mk (fun g ↦ (normOneComponent g).property)

/-- Split rational idele classes into log norm and a norm-one class. The forward
map is `(x, k) ↦ s(x) * k`, with `s` the canonical section on classes. -/
public noncomputable def rationalIdeleClassLogSplit :
    (Multiplicative ℝ × rationalIdeleClassNormOne) ≃ₜ* IdeleClassGroup (𝓞 ℚ) ℚ where
  toFun p := rationalIdeleClassLogSection p.1 * p.2
  invFun g := ⟨rationalIdeleClassLogNorm g, normOneComponent g⟩
  map_mul' p q := by
    change rationalIdeleClassLogSection (p.1 * q.1) * ((p.2 : IdeleClassGroup (𝓞 ℚ) ℚ) * q.2) = _
    rw [map_mul]
    exact mul_mul_mul_comm (rationalIdeleClassLogSection p.1) (rationalIdeleClassLogSection q.1)
      (p.2 : IdeleClassGroup (𝓞 ℚ) ℚ) q.2
  left_inv p := by
    have hk : rationalIdeleClassLogNorm (p.2 : IdeleClassGroup (𝓞 ℚ) ℚ) = 1 := p.2.property
    have h : rationalIdeleClassLogNorm (rationalIdeleClassLogSection p.1 * p.2) = p.1 := by
      rw [map_mul, rationalIdeleClassLogNorm_section, hk, mul_one]
    refine Prod.ext h (Subtype.ext ?_)
    change (rationalIdeleClassLogSection (rationalIdeleClassLogNorm
      (rationalIdeleClassLogSection p.1 * p.2)))⁻¹ * (rationalIdeleClassLogSection p.1 * p.2) = _
    rw [h, inv_mul_cancel_left]
  right_inv g := mul_inv_cancel_left _ _
  continuous_toFun := ((map_continuous rationalIdeleClassLogSection).comp continuous_fst).mul
    (continuous_subtype_val.comp continuous_snd)
  continuous_invFun := (map_continuous rationalIdeleClassLogNorm).prodMk continuous_normOneComponent

public theorem rationalIdeleClassLogSplit_apply (p : Multiplicative ℝ × rationalIdeleClassNormOne) :
    rationalIdeleClassLogSplit p = rationalIdeleClassLogSection p.1 * p.2 := by
  unfold rationalIdeleClassLogSplit
  rfl

/-- The first coordinate of the product is exactly the logarithm of the class norm. -/
public theorem rationalIdeleClassLogSplit_symm_fst (g : IdeleClassGroup (𝓞 ℚ) ℚ) :
    (rationalIdeleClassLogSplit.symm g).1 = rationalIdeleClassLogNorm g := by
  unfold rationalIdeleClassLogSplit
  rfl

end Masullo
