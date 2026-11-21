module

public import Theorems.RationalIdeleLogSection
import Theorems.RationalIdeleFundamentalDomain
import Mathlib.NumberTheory.Padics.HeightOneSpectrum
import Mathlib.NumberTheory.Padics.ProperSpace

/-!
# Finite-unit representatives of norm-one rational idele classes

The rational case of the compactness assertion in Theorem A.1.4.3(1),
pp. 542–543, uses the finite integral units appearing in (A.2.2.3), p. 546.
-/

open NumberField IsDedekindDomain HeightOneSpectrum
open scoped RestrictedProduct

namespace Masullo

/-- The product of the integral unit groups at the finite places of `ℚ`. -/
public abbrev RationalFiniteUnits := (v : HeightOneSpectrum (𝓞 ℚ)) → (v.adicCompletionIntegers ℚ)ˣ

/-- Each integral unit group is compact, so their product is compact. -/
public theorem compactSpace_rationalFiniteUnits : CompactSpace RationalFiniteUnits := by
  let (v : HeightOneSpectrum (𝓞 ℚ)) : CompactSpace (v.adicCompletionIntegers ℚ) :=
    (Rat.HeightOneSpectrum.adicCompletionIntegers.padicIntEquiv v).toHomeomorph.symm.compactSpace
  infer_instance

private noncomputable def integralStage :
    ((v : HeightOneSpectrum (𝓞 ℚ)) → v.adicCompletionIntegers ℚ) ≃ₜ
      (Πʳ v : HeightOneSpectrum (𝓞 ℚ), [v.adicCompletion ℚ, v.adicCompletionIntegers ℚ]_[⊤]) :=
  RestrictedProduct.homeoTop

private noncomputable def finiteValue (u : RationalFiniteUnits) : FiniteAdeleRing (𝓞 ℚ) ℚ :=
  RestrictedProduct.inclusion _ _ (le_top : Filter.cofinite ≤ ⊤) (integralStage (fun v ↦ (u v).val))

private theorem continuous_finiteValue : Continuous finiteValue :=
  (RestrictedProduct.continuous_inclusion (le_top : Filter.cofinite ≤ ⊤)).comp
    (integralStage.continuous.comp (continuous_pi fun v ↦ Units.continuous_val.comp
      (continuous_apply v)))

/-- Insert the local units into the rational ideles with infinite coordinate one. -/
private noncomputable def finiteUnitIdele (u : RationalFiniteUnits) : IdeleGroup (𝓞 ℚ) ℚ where
  val := (1, finiteValue u)
  inv := (1, finiteValue u⁻¹)
  val_inv := by
    refine Prod.ext (mul_one 1) (FiniteAdeleRing.ext ℚ fun v ↦ ?_)
    exact congrArg Subtype.val (u v).val_inv
  inv_val := by
    refine Prod.ext (mul_one 1) (FiniteAdeleRing.ext ℚ fun v ↦ ?_)
    exact congrArg Subtype.val (u v).inv_val

private theorem continuous_finiteUnitIdele : Continuous finiteUnitIdele :=
  Units.continuous_iff.mpr ⟨continuous_const.prodMk continuous_finiteValue,
    continuous_const.prodMk (continuous_finiteValue.comp continuous_inv)⟩

private theorem rationalIdeleReal_finiteUnitIdele (u : RationalFiniteUnits) :
    rationalIdeleReal (finiteUnitIdele u) = 1 := by
  unfold rationalIdeleReal
  exact map_one _

/-- The class of `(1, u)` in the norm-one subgroup. -/
public noncomputable def rationalFiniteUnitClass (u : RationalFiniteUnits) : rationalIdeleClassNormOne :=
  ⟨QuotientGroup.mk (finiteUnitIdele u), (mem_rationalIdeleClassNormOne _).mpr (by
    rw [ideleClassNorm_mk, ideleNorm_eq_abs_rationalIdeleReal, rationalIdeleReal_finiteUnitIdele,
      abs_one]
    intro v
    exact adicCompletionIntegers.isUnit_iff_valued_eq_one.mp (u v).isUnit)⟩

public theorem continuous_rationalFiniteUnitClass : Continuous rationalFiniteUnitClass :=
  (QuotientGroup.continuous_mk.comp continuous_finiteUnitIdele).subtype_mk
    (fun u ↦ (rationalFiniteUnitClass u).property)

private theorem finiteUnitIdele_mul (u w : RationalFiniteUnits) :
    finiteUnitIdele (u * w) = finiteUnitIdele u * finiteUnitIdele w := by
  apply Units.ext
  exact Prod.ext (one_mul 1).symm (FiniteAdeleRing.ext ℚ fun _ ↦ rfl)

private theorem finiteUnitIdele_injective : Function.Injective finiteUnitIdele := by
  intro u w h
  funext v
  apply Units.ext
  apply Subtype.ext
  exact congrArg (fun a : IdeleGroup (𝓞 ℚ) ℚ ↦ (a : AdeleRing (𝓞 ℚ) ℚ).2 v) h

private theorem finiteUnitIdele_mem_window (u : RationalFiniteUnits) :
    finiteUnitIdele u ∈ rationalIdeleUnitWindow := by
  apply mem_rationalIdeleUnitWindow_of_finiteValuation_eq_one
  · rw [rationalIdeleReal_finiteUnitIdele]
    exact zero_lt_one
  · intro v
    exact adicCompletionIntegers.isUnit_iff_valued_eq_one.mp (u v).isUnit

public theorem rationalFiniteUnitClass_mul (u w : RationalFiniteUnits) :
    rationalFiniteUnitClass (u * w) = rationalFiniteUnitClass u * rationalFiniteUnitClass w := by
  apply Subtype.ext
  change QuotientGroup.mk' _ (finiteUnitIdele (u * w)) =
    QuotientGroup.mk' _ (finiteUnitIdele u) * QuotientGroup.mk' _ (finiteUnitIdele w)
  rw [finiteUnitIdele_mul, map_mul]

public theorem rationalFiniteUnitClass_injective : Function.Injective rationalFiniteUnitClass := by
  intro u w h
  let a : rationalIdeleUnitWindow := ⟨finiteUnitIdele u, finiteUnitIdele_mem_window u⟩
  let b : rationalIdeleUnitWindow := ⟨finiteUnitIdele w, finiteUnitIdele_mem_window w⟩
  have hab : rationalIdeleUnitWindowHomeomorph a = rationalIdeleUnitWindowHomeomorph b := by
    rw [rationalIdeleUnitWindowHomeomorph_apply, rationalIdeleUnitWindowHomeomorph_apply]
    exact congrArg Subtype.val h
  exact finiteUnitIdele_injective (congrArg Subtype.val
    (rationalIdeleUnitWindowHomeomorph.injective hab))

public theorem rationalFiniteUnitClass_surjective : Function.Surjective rationalFiniteUnitClass := by
  classical
  rintro ⟨g, hg⟩
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective g
  have hnorm : ideleNorm a = 1 := (ideleClassNorm_mk a).symm.trans
    ((mem_rationalIdeleClassNormOne _).mp hg)
  obtain ⟨r, hreal, hfin⟩ := exists_rational_principal_mul_norm_section a
  let b := IdeleGroup.unitEmbedding (𝓞 ℚ) ℚ r * a
  have hlocal (v : HeightOneSpectrum (𝓞 ℚ)) :
      IsUnit (⟨(b : AdeleRing (𝓞 ℚ) ℚ).2 v, (hfin v).le⟩ : v.adicCompletionIntegers ℚ) :=
    adicCompletionIntegers.isUnit_iff_valued_eq_one.mpr (hfin v)
  choose u hu using hlocal
  have hrep : finiteUnitIdele u = b := by
    apply Units.ext
    refine Prod.ext (funext fun v ↦ ?_) (FiniteAdeleRing.ext ℚ fun v ↦ congrArg Subtype.val (hu v))
    have hv : v = Rat.infinitePlace := Subsingleton.elim _ _
    subst v
    let e := InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace
    apply e.injective
    change e 1 = rationalIdeleReal b
    rw [map_one]
    exact (hreal.trans hnorm).symm
  refine ⟨u, Subtype.ext ?_⟩
  change QuotientGroup.mk (finiteUnitIdele u) = QuotientGroup.mk a
  rw [hrep, QuotientGroup.eq_iff_div_mem]
  change b / a ∈ (IdeleGroup.unitEmbedding (𝓞 ℚ) ℚ).range
  exact ⟨r, (mul_div_cancel_right _ _).symm⟩

end Masullo
