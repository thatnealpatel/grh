module

public import Theorems.RationalRealThetaQuotient
public import Mathlib.Topology.Algebra.Group.Quotient
import Lemmas.SchwartzWeightedDilation
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! # Translation of real S-local theta functions for ℚ

The full local group is `ℝˣ` modulo the image of `ℤˣ`. Its norm-one
subgroup is trivial. In this case the full local isotype is the intrinsic
Schwartz theta quotient. Translation is continuous in the group and the
quotient variable together, with no modular weight in the action.
-/

open scoped SchwartzMap

namespace Masullo

noncomputable section

local notation "V" => 𝓢(ℝ, ℂ)

/-- The image of the rational S-units for `S = {∞}` in the real idele group. -/
@[expose] public def rationalRealSUnitImage : Subgroup ℝˣ :=
  (Units.map (Int.castRingHom ℝ).toMonoidHom).range

/-- The full local group `J_{ℚ,{∞}}`, with its quotient group topology. -/
public abbrev RationalRealLocalIdeleGroup := ℝˣ ⧸ rationalRealSUnitImage

local notation "J" => RationalRealLocalIdeleGroup
local notation "Q" => RationalRealThetaQuotient

/-- The class of a real idele in `J_{ℚ,{∞}}`. -/
@[expose] public def rationalRealLocalIdele : ℝˣ →* J :=
  QuotientGroup.mk' rationalRealSUnitImage

private def realUnitAbs : ℝˣ →* ℝ where
  toFun u := |(u : ℝ)|
  map_one' := abs_one
  map_mul' a b := abs_mul (a : ℝ) (b : ℝ)

private theorem rationalRealSUnitImage_le_ker : rationalRealSUnitImage ≤ realUnitAbs.ker := by
  rintro u ⟨e, rfl⟩
  change |((Units.map (Int.castRingHom ℝ).toMonoidHom e : ℝˣ) : ℝ)| = 1
  obtain rfl | rfl := Int.units_eq_one_or e <;> simp

/-- The local idelic norm, the absolute value of any representative. -/
public def rationalRealLocalIdeleNorm : J →* ℝ :=
  QuotientGroup.lift _ realUnitAbs rationalRealSUnitImage_le_ker

local notation "N" => rationalRealLocalIdeleNorm

@[simp] public theorem rationalRealLocalIdeleNorm_mk (u : ℝˣ) :
    N (rationalRealLocalIdele u) = |(u : ℝ)| := by
  unfold rationalRealLocalIdeleNorm rationalRealLocalIdele
  rfl

public theorem rationalRealLocalIdeleNorm_pos (g : J) : 0 < N g := by
  obtain ⟨u, rfl⟩ := QuotientGroup.mk'_surjective rationalRealSUnitImage g
  exact abs_pos.mpr (Units.ne_zero u)

public theorem continuous_rationalRealLocalIdeleNorm : Continuous N :=
  (QuotientGroup.isQuotientMap_mk rationalRealSUnitImage).continuous_iff.2
    Units.continuous_val.abs

/-- The norm-one subgroup of `J_{ℚ,{∞}}` is trivial. In particular the only
norm-one character has the full local theta space as its isotype. -/
@[simp] public theorem rationalRealLocalIdeleNorm_eq_one (g : J) : N g = 1 ↔ g = 1 := by
  obtain ⟨u, rfl⟩ := QuotientGroup.mk'_surjective rationalRealSUnitImage g
  change N (rationalRealLocalIdele u) = 1 ↔ rationalRealLocalIdele u = 1
  rw [rationalRealLocalIdeleNorm_mk]
  change |(u : ℝ)| = 1 ↔ QuotientGroup.mk u = (1 : J)
  rw [QuotientGroup.eq_one_iff]
  refine ⟨fun h ↦ ?_, fun hu ↦ rationalRealSUnitImage_le_ker hu⟩
  rcases abs_choice (u : ℝ) with he | he
  · have hu : u = 1 := Units.ext (he.symm.trans h)
    rw [hu]
    exact rationalRealSUnitImage.one_mem
  · have hu : u = -1 := Units.ext (show (u : ℝ) = -(1 : ℝ) by linarith)
    exact ⟨-1, by simpa using hu.symm⟩

private theorem localNorm_inv (g : J) : N g⁻¹ = (N g)⁻¹ :=
  eq_inv_of_mul_eq_one_left (by rw [← map_mul, inv_mul_cancel, map_one])

private def logDilation (s : ℝ) : V →L[ℂ] V :=
  (Real.exp s : ℂ) • schwartzWeightedInverseDilation s

private theorem logDilation_apply (s : ℝ) (f : V) (x : ℝ) :
    logDilation s f x = f (Real.exp (-s) * x) := by
  rw [logDilation, smul_apply, smul_apply, schwartzWeightedInverseDilation_apply,
    RCLike.real_smul_eq_coe_smul (K := ℂ), smul_smul]
  change (Complex.ofReal (Real.exp s) * Complex.ofReal (Real.exp (-s))) • _ = _
  rw [← Complex.ofReal_mul, ← Real.exp_add, add_neg_cancel, Real.exp_zero, Complex.ofReal_one,
    one_smul]

private theorem continuous_logDilation : Continuous (fun z : ℝ × V ↦ logDilation z.1 z.2) :=
  (Complex.continuous_ofReal.comp (Real.continuous_exp.comp continuous_fst)).smul
    continuous_schwartzWeightedInverseDilation

private def translateEven (g : J) : rationalRealEvenSchwartz →L[ℂ] rationalRealEvenSchwartz :=
  ((logDilation (Real.log (N g))).comp rationalRealEvenSchwartz.subtypeL).codRestrict _ <| by
    intro f
    apply (mem_rationalRealEvenSchwartz _).2
    intro x
    change logDilation _ f.1 (-x) = logDilation _ f.1 x
    rw [logDilation_apply, logDilation_apply, mul_neg]
    exact (mem_rationalRealEvenSchwartz _).1 f.2 _

/-- Left translation is a continuous complex linear operator on the
original quotient. It is transported through its even Schwartz model. -/
public def rationalRealThetaTranslate (g : J) : Q →L[ℂ] Q :=
  rationalRealThetaEquiv.symm.toContinuousLinearMap.comp
    ((translateEven g).comp rationalRealThetaEquiv.toContinuousLinearMap)

private theorem equiv_translate_apply (g : J) (q : Q) (x : ℝ) :
    (rationalRealThetaEquiv (rationalRealThetaTranslate g q)).1 x =
      (rationalRealThetaEquiv q).1 ((N g)⁻¹ * x) := by
  change (rationalRealThetaEquiv (rationalRealThetaEquiv.symm (translateEven g
    (rationalRealThetaEquiv q)))).1 x = _
  rw [ContinuousLinearEquiv.apply_symm_apply]
  change logDilation (Real.log (N g)) (rationalRealThetaEquiv q).1 x = _
  rw [logDilation_apply, Real.exp_neg, Real.exp_log (rationalRealLocalIdeleNorm_pos g)]

/-- The unital action of the full S-local group on the theta quotient. -/
public instance rationalRealThetaMulAction : MulAction J Q where
  smul g q := rationalRealThetaTranslate g q
  one_smul q := by
    change rationalRealThetaTranslate 1 q = q
    apply rationalRealThetaEquiv.injective
    apply Subtype.ext
    ext x
    rw [equiv_translate_apply, map_one, inv_one, one_mul]
  mul_smul g h q := by
    change rationalRealThetaTranslate (g * h) q =
      rationalRealThetaTranslate g (rationalRealThetaTranslate h q)
    apply rationalRealThetaEquiv.injective
    apply Subtype.ext
    ext x
    simp only [equiv_translate_apply, map_mul, mul_inv, mul_assoc, mul_left_comm]

@[simp] public theorem rationalRealTheta_smul_eq_translate (g : J) (q : Q) :
    g • q = rationalRealThetaTranslate g q := rfl

/-- Translation is jointly continuous for the local group and Schwartz
quotient topologies, not just pointwise on the theta values. -/
public theorem continuous_rationalRealThetaTranslate :
    Continuous (fun z : J × Q ↦ rationalRealThetaTranslate z.1 z.2) := by
  apply rationalRealThetaEquiv.symm.continuous.comp
  apply Continuous.subtype_mk
  exact continuous_logDilation.comp
    ((continuous_rationalRealLocalIdeleNorm.log (fun g ↦
      (rationalRealLocalIdeleNorm_pos g).ne')).comp continuous_fst |>.prodMk
      (continuous_subtype_val.comp (rationalRealThetaEquiv.continuous.comp continuous_snd)))

/-- Joint continuity for the full group action on the original quotient. -/
public instance rationalRealThetaContinuousSMul : ContinuousSMul J Q :=
  ⟨continuous_rationalRealThetaTranslate⟩

private theorem even_abs (f : rationalRealEvenSchwartz) (x : ℝ) : f.1 |x| = f.1 x := by
  rcases abs_choice x with hx | hx
  · rw [hx]
  · rw [hx]
    exact (mem_rationalRealEvenSchwartz _).1 f.2 x

/-- Evaluate a local theta class at a local idele class. The norm selects
the positive representative; evenness makes the choice immaterial. -/
public def rationalRealThetaValue (q : Q) (x : J) : ℂ :=
  (rationalRealThetaEquiv q).1 (N x)

@[simp] public theorem rationalRealThetaValue_mkQ (f : V) (x : ℝˣ) :
    rationalRealThetaValue (rationalRealTheta.ker.mkQ f) (rationalRealLocalIdele x) =
      rationalRealTheta f x := by
  rw [rationalRealThetaValue, rationalRealLocalIdeleNorm_mk, even_abs,
    rationalRealThetaEquiv_mkQ_apply_unit]

/-- The action translates theta values by the inverse group argument. -/
public theorem rationalRealThetaValue_smul (g : J) (q : Q) (x : J) :
    rationalRealThetaValue (g • q) x = rationalRealThetaValue q (g⁻¹ * x) := by
  simp only [rationalRealTheta_smul_eq_translate, rationalRealThetaValue, equiv_translate_apply,
    map_mul N g⁻¹ x, localNorm_inv]

/-- For actual Schwartz representatives and real ideles, translation gives
the original two-term theta sum at the inverse-translated idele. -/
public theorem rationalRealThetaValue_smul_mkQ (u x : ℝˣ) (f : V) :
    rationalRealThetaValue (rationalRealLocalIdele u • rationalRealTheta.ker.mkQ f)
        (rationalRealLocalIdele x) = rationalRealTheta f (u⁻¹ * x) := by
  rw [rationalRealThetaValue_smul, ← map_inv, ← map_mul, rationalRealThetaValue_mkQ]

end
end Masullo
