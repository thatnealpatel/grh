module

public import Props.IdeleClassStripTrace
public import Theorems.RationalIdeleRadialExplicitFormula

import Lemmas.RationalIdeleWindowMeasure
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.Tactic.Ring

/-! # Radial Mellin pairings on rational idele classes -/

open NumberField MeasureTheory Set TopologicalSpace
open NumberField.Units.dirichletUnitTheorem (w₀)

namespace Masullo

/-- The residue scalar in the quotient Haar normalization is one over `ℚ`. -/
public theorem dedekindZeta_residue_rat : dedekindZeta_residue ℚ = 1 := by
  have hdeg := Module.finrank_self ℚ
  have hr := InfinitePlace.nrRealPlaces_eq_one_of_finrank_eq_one hdeg
  have hc := InfinitePlace.nrComplexPlaces_eq_zero_of_finrank_eq_one hdeg
  have ht : Units.torsionOrder ℚ = 2 := Units.torsionOrder_eq_two_of_odd_finrank (by simp)
  have hreg : Units.regulator ℚ = 1 := by
    classical
    rw [Units.regulator_eq_det']
    let : IsEmpty {w : InfinitePlace ℚ // w ≠ w₀} :=
      ⟨fun w ↦ w.property (Subsingleton.elim _ _)⟩
    simp only [Matrix.det_isEmpty, abs_one]
  simp [dedekindZeta_residue_def, hr, hc, ht, hreg, Rat.classNumber_eq, Rat.numberField_discr]

local notation "C" => RationalIdeleClasses
local notation "C₁" => ideleClassNormOne (K := ℚ)
local notation "Ω" => HeckeCharacter (𝓞 ℚ) ℚ
local notation "logNorm" => (fun c : C ↦ Real.log (ideleClassNorm c))
local notation "τ" => ideleClassLogSplit (ideleClassLogSection (w₀ : InfinitePlace ℚ))
  (ideleClassLogNorm_section w₀)

private theorem logNorm_split (p : Multiplicative ℝ × C₁) : logNorm (τ p) = p.1.toAdd := by
  change Real.log (ideleClassNorm (τ p)) = _
  rw [ideleClassLogSplit_apply, map_mul, (mem_ideleClassNormOne _).mp p.2.property, mul_one,
    ideleClassNorm_logSection, Real.log_exp]

private theorem continuous_logNorm : Continuous logNorm := by
  simpa only [Function.comp_def, ideleClassLogNorm_apply] using
    continuous_toAdd.comp (map_continuous (ideleClassLogNorm (K := ℚ)))

noncomputable section

local instance : MeasurableSpace C := borel _
local instance : BorelSpace C := ⟨rfl⟩
local instance : MeasurableSpace C₁ := borel _
local instance : BorelSpace C₁ := ⟨rfl⟩
local instance : CompactSpace C₁ := compactHausdorff_ideleClassNormOne.1
local instance : T2Space C₁ := compactHausdorff_ideleClassNormOne.2
local notation "η" => Measure.haarMeasure (⊤ : PositiveCompacts C₁)

-- After removing the residue scalar, the compact factor has total mass one.
-- The split pushforward is Haar and its unit log strip fixes its normalization.
private theorem splitHaar_eq_rationalIdeleClassHaar : (logVolume.prod η).map τ =
    rationalIdeleClassHaar := by
  let : IsProbabilityMeasure η := ⟨by simpa only [PositiveCompacts.coe_top] using
    (Measure.haarMeasure_self (K₀ := (⊤ : PositiveCompacts C₁)))⟩
  let := isHaarMeasure_logVolume_prod η
  let := ContinuousMulEquiv.isHaarMeasure_map (logVolume.prod η) τ
  have hτ : Measurable (⇑τ) := (map_continuous τ).measurable
  have hmap : ((logVolume.prod η).map τ).map logNorm = volume := by
    rw [Measure.map_map continuous_logNorm.measurable hτ]
    have hcomp : logNorm ∘ τ = Multiplicative.toAdd ∘ Prod.fst := funext logNorm_split
    rw [hcomp, ← Measure.map_map measurable_toAdd measurable_fst,
      (measurePreserving_fst (μ := logVolume) (ν := η)).map_eq, map_toAdd_logVolume]
  apply eq_rationalIdeleClassHaar_of_normStrip
  have hstrip : {c : C | ideleClassNorm c ∈ Icc 1 (Real.exp 1)} = logNorm ⁻¹' Icc 0 1 := by
    ext c
    change (1 ≤ ideleClassNorm c ∧ ideleClassNorm c ≤ Real.exp 1) ↔
      (0 ≤ Real.log (ideleClassNorm c) ∧ Real.log (ideleClassNorm c) ≤ 1)
    rw [Real.le_log_iff_exp_le (ideleClassNorm_pos c), Real.exp_zero,
      Real.log_le_iff_le_exp (ideleClassNorm_pos c)]
  rw [hstrip, ← Measure.map_apply continuous_logNorm.measurable measurableSet_Icc,
    hmap, Real.volume_Icc, sub_zero, ENNReal.ofReal_one]

private theorem rational_ideleClassMellin_eq_integral (φ : C → ℂ) (χ : Ω) :
    ideleClassMellin φ χ = ∫ c : C, φ c * χ c ∂rationalIdeleClassHaar := by
  unfold ideleClassMellin
  rw [dedekindZeta_residue_rat, ENNReal.ofReal_one, one_smul]
  exact congrArg (fun μ : Measure C ↦ ∫ c : C, φ c * χ c ∂μ)
    splitHaar_eq_rationalIdeleClassHaar

private theorem normPower_eq_logExp (s : ℂ) (c : C) :
    ideleClassNormPower s c = Complex.exp (s * (logNorm c : ℂ)) := by
  change ideleClassNormPower s c = Complex.exp (s * (Real.log (ideleClassNorm c) : ℂ))
  rw [ideleClassNormPower_apply, Complex.cpow_def_of_ne_zero
    (Complex.ofReal_ne_zero.mpr (ideleClassNorm_pos c).ne'),
    ← Complex.ofReal_log (ideleClassNorm_pos c).le, mul_comm]

private theorem hasCompactSupport_radial {F : ℝ → ℂ} (hc : HasCompactSupport F) :
    HasCompactSupport (F ∘ logNorm) := by
  have hcompact := ((hc.image continuous_ofAdd).prod (isCompact_univ (X := C₁))).image
    (map_continuous τ)
  apply hcompact.of_isClosed_subset isClosed_closure
  intro c hc'
  have hm := tsupport_comp_subset_preimage F continuous_logNorm hc'
  refine ⟨(ContinuousMulEquiv.symm τ) c, ⟨⟨logNorm c, hm, ?_⟩, mem_univ _⟩,
    ContinuousMulEquiv.apply_symm_apply τ c⟩
  apply Multiplicative.toAdd.injective
  simpa only [ContinuousMulEquiv.apply_symm_apply, toAdd_ofAdd] using
    logNorm_split ((ContinuousMulEquiv.symm τ) c)

/-- The rational radial test paired with the norm power at `s - 1/2` gives
exactly the radial Mellin value at `s`, without a volume factor. -/
public theorem rational_ideleClassMellin_normPower {F : ℝ → ℂ}
    (hF : Continuous F) (hc : HasCompactSupport F) (s : ℂ) :
    ideleClassMellin (fun c : C ↦ F (logNorm c)) (ideleClassNormPower (s - 1 / 2)) =
      (letI : MeasurableSpace C := borel C
       letI : BorelSpace C := ⟨rfl⟩
       rationalIdeleRadialMellin F s) := by
  change _ = rationalIdeleRadialMellin F s
  rw [rational_ideleClassMellin_eq_integral,
    (rationalIdeleRadialMellin_eq_compactLogMellin hF hc s).2]
  simp only [normPower_eq_logExp]
  let g (t : ℝ) := F t * Complex.exp ((s - 1 / 2) * (t : ℂ))
  have hg : Continuous g := hF.mul (Complex.continuous_exp.comp
    (continuous_const.mul Complex.continuous_ofReal))
  change (∫ c : C, g (logNorm c) ∂rationalIdeleClassHaar) = _
  rw [integral_rationalIdeleClass_logNorm (hg.integrable_of_hasCompactSupport hc.mul_right)]
  unfold compactLogMellin
  apply integral_congr_ae (Filter.Eventually.of_forall fun t ↦ ?_)
  dsimp only [g]
  rw [mul_comm (Complex.exp (-(t : ℂ) / 2)), mul_assoc, ← Complex.exp_add]
  congr 2
  ring

/-- A character nontrivial on the norm-one classes has zero pairing with a
continuous compactly supported log-norm profile. -/
public theorem rational_ideleClassMellin_eq_zero_of_nontrivial {F : ℝ → ℂ}
    (hF : Continuous F) (hc : HasCompactSupport F) (χ : Ω)
    (hχ : ∃ k : C₁, χ (k : C) ≠ 1) : ideleClassMellin (fun c : C ↦ F (logNorm c)) χ = 0 := by
  obtain ⟨k, hk⟩ := hχ
  let f (c : C) := F (logNorm c) * χ c
  let := isHaarMeasure_rationalIdeleClassHaar
  have hi : Integrable f rationalIdeleClassHaar :=
    ((hF.comp continuous_logNorm).mul χ.continuous).integrable_of_hasCompactSupport
      (hasCompactSupport_radial hc).mul_right
  have htranslate (c : C) : f ((k : C) * c) = χ (k : C) * f c := by
    have hnorm := (mem_ideleClassNormOne _).mp k.property
    change F (Real.log (ideleClassNorm ((k : C) * c))) * χ ((k : C) * c) =
      χ (k : C) * (F (Real.log (ideleClassNorm c)) * χ c)
    rw [map_mul, hnorm, one_mul, map_mul, mul_left_comm]
  have heq : χ (k : C) * (∫ c, f c ∂rationalIdeleClassHaar) =
      ∫ c, f c ∂rationalIdeleClassHaar := by
    rw [← smul_eq_mul, ← hi.integral_smul]
    simp_rw [smul_eq_mul, ← htranslate]
    exact integral_mul_left_eq_self f (k : C)
  rw [rational_ideleClassMellin_eq_integral]
  exact (mul_eq_zero.mp (by rw [sub_mul, heq, one_mul, sub_self] :
    (χ (k : C) - 1) * (∫ c, f c ∂rationalIdeleClassHaar) = 0)).resolve_left (sub_ne_zero.mpr hk)

end

end Masullo
