module

public import Lemmas.RationalIdeleUnitWindow
public import Mathlib.MeasureTheory.Group.FundamentalDomain

/-!
# A fundamental domain for principal rational ideles

Over `ℚ`, the positive-real, finite-unit window gives the representatives
of the class group description (A.2.2.3), p. 546. This is the radial
extension of the rational norm-one window in (A.2.3.14), p. 549. Here
we equip the window with the subspace topology. No measure is chosen.
-/

open NumberField MeasureTheory

namespace Masullo

private abbrev Classes := IdeleClassGroup (𝓞 ℚ) ℚ
private noncomputable abbrev Principal := IdeleGroup.principalSubgroup (𝓞 ℚ) ℚ

private noncomputable def windowClass (a : rationalIdeleUnitWindow) : Classes :=
  QuotientGroup.mk a.val

private theorem windowClass_bijective : Function.Bijective windowClass := by
  constructor
  · intro a b hab
    apply Subtype.ext
    apply div_eq_one.mp
    apply eq_one_of_mem_rationalIdeleUnitWindow_of_principal _
      (QuotientGroup.eq_iff_div_mem.mp hab)
    rw [div_eq_mul_inv]
    exact mul_mem_rationalIdeleUnitWindow a.property (inv_mem_rationalIdeleUnitWindow b.property)
  · intro c
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective c
    obtain ⟨r, hreal, hfin⟩ := exists_rational_principal_mul_norm_section a
    have hpos : 0 < ideleNorm a := ideleClassNorm_mk a ▸ ideleClassNorm_pos (QuotientGroup.mk a)
    have hwindow := mem_rationalIdeleUnitWindow_of_finiteValuation_eq_one (hreal.symm ▸ hpos) hfin
    refine ⟨⟨_, hwindow⟩, ?_⟩
    change QuotientGroup.mk (IdeleGroup.unitEmbedding (𝓞 ℚ) ℚ r * a) = QuotientGroup.mk a
    apply QuotientGroup.eq_iff_div_mem.mpr
    rw [mul_div_cancel_right]
    exact ⟨r, rfl⟩

/-- Each rational idele class has a unique representative with positive real
coordinate and finite coordinates that are integral units. The quotient map
on this open window is a homeomorphism. -/
public noncomputable def rationalIdeleUnitWindowHomeomorph :
    rationalIdeleUnitWindow ≃ₜ IdeleClassGroup (𝓞 ℚ) ℚ :=
  (Equiv.ofBijective windowClass windowClass_bijective).toHomeomorphOfContinuousOpen
    (QuotientGroup.continuous_mk.comp continuous_subtype_val)
    (QuotientGroup.isOpenMap_coe.comp isOpen_rationalIdeleUnitWindow.isOpenMap_subtype_val)

@[simp] public theorem rationalIdeleUnitWindowHomeomorph_apply (a : rationalIdeleUnitWindow) :
    rationalIdeleUnitWindowHomeomorph a = QuotientGroup.mk a.val := by rfl

-- Keep the Borel instances explicit rather than choosing project-wide instances.
set_option linter.concreteInstances false in
/-- The open window is a measurable fundamental domain for right translation
by the principal rational ideles. This holds for any Borel measure upstairs;
it does not choose or normalize a measure on the quotient. -/
public theorem rationalIdeleUnitWindow_isFundamentalDomain
    [MeasurableSpace (IdeleGroup (𝓞 ℚ) ℚ)] [BorelSpace (IdeleGroup (𝓞 ℚ) ℚ)]
    (μ : Measure (IdeleGroup (𝓞 ℚ) ℚ)) :
    IsFundamentalDomain (IdeleGroup.principalSubgroup (𝓞 ℚ) ℚ).op rationalIdeleUnitWindow μ := by
  apply IsFundamentalDomain.mk' isOpen_rationalIdeleUnitWindow.measurableSet.nullMeasurableSet
  intro a
  obtain ⟨b, hb⟩ := windowClass_bijective.surjective (QuotientGroup.mk a)
  have hab : a⁻¹ * b.val ∈ Principal := QuotientGroup.eq.mp hb.symm
  let g : Principal.op := ⟨MulOpposite.op (a⁻¹ * b.val), hab⟩
  refine ⟨g, ?_, ?_⟩
  · change a * (a⁻¹ * b.val) ∈ rationalIdeleUnitWindow
    simpa only [mul_inv_cancel_left] using b.property
  · intro h hh
    change a * (h.val.unop) ∈ rationalIdeleUnitWindow at hh
    have heq : windowClass ⟨a * h.val.unop, hh⟩ = windowClass b := by
      rw [hb]
      apply QuotientGroup.eq.mpr
      rw [mul_inv_rev, mul_assoc, inv_mul_cancel, mul_one]
      exact Principal.inv_mem h.property
    have hval := congrArg Subtype.val (windowClass_bijective.injective heq)
    apply Subtype.ext
    apply MulOpposite.unop_injective
    change h.val.unop = a⁻¹ * b.val
    exact (eq_inv_mul_iff_mul_eq).mpr hval

end Masullo
