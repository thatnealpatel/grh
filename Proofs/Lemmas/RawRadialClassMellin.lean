module

public import Props.IdeleClassStripTrace
public import Lemmas.CompactLogMellin
import Mathlib.MeasureTheory.Integral.Prod

/-! # Raw Mellin pairings for radial idele-class functions -/

open NumberField MeasureTheory Set TopologicalSpace
open NumberField.Units.dirichletUnitTheorem (w₀)

namespace Masullo

variable {K : Type*} [Field K] [NumberField K]

local notation "C" => IdeleClassGroup (𝓞 K) K
local notation "C₁" => ideleClassNormOne (K := K)
local notation "τ" => ideleClassLogSplit (ideleClassLogSection (w₀ : InfinitePlace K))
  (ideleClassLogNorm_section w₀)
local notation "logNorm" => (fun c : C ↦ Real.log (ideleClassNorm c))

private theorem logNorm_split (p : Multiplicative ℝ × C₁) : logNorm (τ p) = p.1.toAdd := by
  change Real.log (ideleClassNorm (τ p)) = _
  rw [ideleClassLogSplit_apply, map_mul, (mem_ideleClassNormOne _).mp p.2.property, mul_one,
    ideleClassNorm_logSection, Real.log_exp]

private theorem continuous_logNorm : Continuous logNorm := by
  simpa only [Function.comp_def, ideleClassLogNorm_apply] using
    continuous_toAdd.comp (map_continuous (ideleClassLogNorm (K := K)))

noncomputable section

local instance : MeasurableSpace C := borel _
local instance : BorelSpace C := ⟨rfl⟩
local instance : MeasurableSpace C₁ := borel _
local instance : BorelSpace C₁ := ⟨rfl⟩
local instance : CompactSpace C₁ := compactHausdorff_ideleClassNormOne.1
local instance : T2Space C₁ := compactHausdorff_ideleClassNormOne.2
local notation "η" => Measure.haarMeasure (⊤ : PositiveCompacts C₁)
local notation "m" => (ENNReal.ofReal (dedekindZeta_residue K) • η)

private theorem logVolume_sFinite : SFinite logVolume := by
  have h := congrArg (Measure.map (Multiplicative.ofAdd : ℝ → Multiplicative ℝ))
    map_toAdd_logVolume
  rw [Measure.map_map measurable_ofAdd measurable_toAdd, show
    Multiplicative.ofAdd ∘ Multiplicative.toAdd = (id : Multiplicative ℝ → Multiplicative ℝ)
    from rfl, Measure.map_id] at h
  rw [h]
  infer_instance

private theorem normPower_eq (s : ℂ) (c : C) :
    ideleClassNormPower s c = Complex.exp (s * (logNorm c : ℂ)) := by
  change ideleClassNormPower s c = Complex.exp (s * (Real.log (ideleClassNorm c) : ℂ))
  rw [ideleClassNormPower_apply, Complex.cpow_def_of_ne_zero
    (Complex.ofReal_ne_zero.mpr (ideleClassNorm_pos c).ne'),
    ← Complex.ofReal_log (ideleClassNorm_pos c).le, mul_comm]

/-- The raw quotient Haar mass scales the radial norm-power pairing. Both
integrals are totalized; continuity alone is not a convergence assertion. -/
public theorem ideleClassMellin_radial_normPower {F : ℝ → ℂ} (hf : Continuous F) (s : ℂ) :
    ideleClassMellin (fun c : C ↦ F (logNorm c)) (ideleClassNormPower s) =
      (dedekindZeta_residue K : ℂ) * compactLogMellin F s := by
  let f (t : ℝ) := F t * Complex.exp (s * (t : ℂ))
  have hfc : Continuous f :=
    hf.mul (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal))
  have ht : Measurable (⇑τ) := (map_continuous τ).measurable
  have hm : η univ = 1 := by simpa only [PositiveCompacts.coe_top] using
    (Measure.haarMeasure_self (K₀ := (⊤ : PositiveCompacts C₁)))
  have hm' : (m).real univ = dedekindZeta_residue K := by
    simp [Measure.real, hm, ENNReal.toReal_ofReal (dedekindZeta_residue_pos K).le]
  let : SFinite logVolume := logVolume_sFinite
  unfold ideleClassMellin
  simp only [normPower_eq]
  change (∫ c : C, f (logNorm c) ∂((logVolume.prod m).map τ)) = _
  have hmeas : Continuous (fun c : C ↦ f (logNorm c)) := hfc.comp continuous_logNorm
  rw [integral_map (μ := logVolume.prod m) ht.aemeasurable hmeas.aestronglyMeasurable]
  simp only [logNorm_split]
  rw [integral_fun_fst (fun u : Multiplicative ℝ ↦ f u.toAdd), hm',
    ← integral_map measurable_toAdd.aemeasurable hfc.aestronglyMeasurable, map_toAdd_logVolume]
  rfl

/-- Translation on norm-one classes kills a radial pairing with a character
nontrivial on that subgroup. -/
public theorem ideleClassMellin_radial_eq_zero {F : ℝ → ℂ} (hf : Continuous F)
    (χ : HeckeCharacter (𝓞 K) K) (hχ : ∃ k : C₁, χ (k : C) ≠ 1) :
    ideleClassMellin (fun c : C ↦ F (logNorm c)) χ = 0 := by
  obtain ⟨k, hk⟩ := hχ
  let t (y : C₁) := χ (y : C)
  have htr (y : C₁) : t (k * y) = χ (k : C) * t y := map_mul χ _ _
  have heq : χ (k : C) * (∫ y, t y ∂m) = ∫ y, t y ∂m := by
    rw [← integral_const_mul]
    simp_rw [← htr]
    exact integral_mul_left_eq_self t k
  have hz : (∫ y, t y ∂m) = 0 := (mul_eq_zero.mp (by rw [sub_mul, heq, one_mul, sub_self] :
    (χ (k : C) - 1) * (∫ y, t y ∂m) = 0)).resolve_left (sub_ne_zero.mpr hk)
  let g (u : Multiplicative ℝ) := F u.toAdd * χ (ideleClassLogSection (w₀ : InfinitePlace K) u)
  have hfct : Continuous (fun c : C ↦ F (logNorm c) * χ c) :=
    (hf.comp continuous_logNorm).mul χ.continuous
  let : SFinite logVolume := logVolume_sFinite
  unfold ideleClassMellin
  rw [integral_map (μ := logVolume.prod m) (map_continuous τ).measurable.aemeasurable
    hfct.aestronglyMeasurable]
  simp only [logNorm_split]
  simp only [ideleClassLogSplit_apply, map_mul, ← mul_assoc]
  change (∫ p : Multiplicative ℝ × C₁, g p.1 * t p.2 ∂logVolume.prod m) = 0
  rw [integral_prod_mul, hz, mul_zero]

end

end Masullo
