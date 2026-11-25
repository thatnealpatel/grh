module

public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Function.LpSeminorm.Prod
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The short-cell crossing kernel

Source: `8058479e:.godel/bob/short-cell-weil-list.md:39–53` (unchanged at
`b6b5fe8`); the Hilbert–Schmidt identity and symmetric crossing bound enter
the sum of squared crossing norms in (4). The variable `Y` is `exp D`.
This is the continuous smeared kernel on the two halves of the window,
not an operator-norm estimate for the replacement of discrete prime shifts.

Owning check session: `01a20efe-657a-74fc-9a09-f6e32d4cc146`.
-/

open Set MeasureTheory
open scoped ENNReal

namespace ShortCellCrossing

public section

/-- The left half of the window. -/
@[expose] noncomputable def leftHalf (D : ℝ) : Set ℝ := Icc 0 (D / 2)

/-- The right half of the window. Its common endpoint with the left half is null. -/
@[expose] noncomputable def rightHalf (D : ℝ) : Set ℝ := Icc (D / 2) D

/-- The left/right rectangle carries product Lebesgue measure. -/
@[expose] noncomputable def crossMeasure (D : ℝ) : Measure (ℝ × ℝ) :=
  (volume.restrict (leftHalf D)).prod (volume.restrict (rightHalf D))

/-- The actual complex forward kernel, cut off on the allowed differences.
Real scalar multiplication here is multiplication by the real exponential in `ℂ`. -/
@[expose] noncomputable def kernel (D L : ℝ) (m : ℝ → ℂ) (x y : ℝ) : ℂ :=
  (Icc (Real.log L) D).indicator (fun t ↦ Real.exp (t / 2) • m (Real.exp t)) (y - x)

/-- The log-weighted square density on the original variable interval. -/
@[expose] noncomputable def weightedSquare (D : ℝ) (m : ℝ → ℂ) (v : ℝ) : ℝ :=
  Real.log (Real.exp D / v) * ‖m v‖ ^ 2

private noncomputable def shear : (ℝ × ℝ) ≃ᵐ (ℝ × ℝ) where
  toFun p := (p.1, p.1 + p.2)
  invFun p := (p.1, p.2 - p.1)
  left_inv p := Prod.ext rfl (by dsimp; ring)
  right_inv p := Prod.ext rfl (by dsimp; ring)
  measurable_toFun := by
    change Measurable (fun p : ℝ × ℝ ↦ (p.1, p.1 + p.2))
    fun_prop
  measurable_invFun := by
    change Measurable (fun p : ℝ × ℝ ↦ (p.1, p.2 - p.1))
    fun_prop

private theorem aestronglyMeasurable_difference {E : Type*} [TopologicalSpace E] [Zero E]
    {a D : ℝ} {g : ℝ → E}
    (hg : AEStronglyMeasurable g (volume.restrict (Icc a D))) :
    AEStronglyMeasurable (fun p : ℝ × ℝ ↦ (Icc a D).indicator g (p.2 - p.1))
      ((volume : Measure ℝ).prod volume) := by
  have hq : QuasiMeasurePreserving (fun p : ℝ × ℝ ↦ p.2 - p.1)
      ((volume : Measure ℝ).prod volume) volume :=
    Measure.quasiMeasurePreserving_snd.comp
      (measurePreserving_prod_sub volume volume).quasiMeasurePreserving
  exact ((aestronglyMeasurable_indicator_iff measurableSet_Icc).2 hg).comp_quasiMeasurePreserving hq

private theorem fiber_eq {a D t : ℝ} (ha : D / 2 ≤ a) (ht : t ∈ Icc a D) :
    {x | (x, x + t) ∈ leftHalf D ×ˢ rightHalf D} = Icc 0 (D - t) := by
  ext x
  obtain ⟨ht₁, ht₂⟩ := ht
  change (0 ≤ x ∧ x ≤ D / 2) ∧ (D / 2 ≤ x + t ∧ x + t ≤ D) ↔
    0 ≤ x ∧ x ≤ D - t
  constructor
  · rintro ⟨⟨hx, _⟩, ⟨_, hxt⟩⟩
    exact ⟨hx, by linarith⟩
  · rintro ⟨hx, hxt⟩
    exact ⟨⟨hx, by linarith⟩, ⟨by linarith, by linarith⟩⟩

/-- Compute the difference marginal on the band by Tonelli after a unit shear. -/
private theorem lintegral_difference {a D : ℝ} {g : ℝ → ℝ}
    (ha : D / 2 ≤ a) (hg : AEStronglyMeasurable g (volume.restrict (Icc a D))) :
    (∫⁻ p : ℝ × ℝ, ENNReal.ofReal ((Icc a D).indicator g (p.2 - p.1)) ∂crossMeasure D) =
      ∫⁻ t in Icc a D, ENNReal.ofReal ((D - t) * g t) := by
  let μ := (volume : Measure ℝ).prod (volume : Measure ℝ)
  let A := leftHalf D ×ˢ rightHalf D
  have hA : MeasurableSet A := measurableSet_Icc.prod measurableSet_Icc
  let q := fun p : ℝ × ℝ ↦ ENNReal.ofReal ((Icc a D).indicator g (p.2 - p.1))
  let F := A.indicator q
  have hF : AEMeasurable F μ :=
    (aestronglyMeasurable_difference hg).aemeasurable.ennreal_ofReal.indicator hA
  have hS : MeasurePreserving shear μ μ := measurePreserving_prod_add volume volume
  have hsection (t : ℝ) :
      (∫⁻ x : ℝ, F (shear (x, t))) =
        (Icc a D).indicator (fun t ↦ ENNReal.ofReal ((D - t) * g t)) t := by
    by_cases ht : t ∈ Icc a D
    · rw [indicator_of_mem ht]
      have heq (x : ℝ) : F (shear (x, t)) =
          (Icc 0 (D - t)).indicator (fun _ ↦ ENNReal.ofReal (g t)) x := by
        have hmem : (x, x + t) ∈ A ↔ x ∈ Icc 0 (D - t) := by
          change x ∈ {x | (x, x + t) ∈ leftHalf D ×ˢ rightHalf D} ↔ _
          rw [fiber_eq ha ht]
        change A.indicator q (x, x + t) = _
        by_cases hx : x ∈ Icc 0 (D - t)
        · rw [indicator_of_mem (hmem.mpr hx), indicator_of_mem hx]
          have hsub : x + t - x = t := by ring
          simp only [q, hsub, indicator_of_mem ht]
        · rw [indicator_of_notMem (mt hmem.mp hx), indicator_of_notMem hx]
      calc
        (∫⁻ x : ℝ, F (shear (x, t))) =
            ∫⁻ x in Icc (0 : ℝ) (D - t), ENNReal.ofReal (g t) := by
          simp_rw [heq]; exact lintegral_indicator measurableSet_Icc _
        _ = _ := by
          rw [lintegral_const, Measure.restrict_apply_univ, Real.volume_Icc, sub_zero, mul_comm,
            ← ENNReal.ofReal_mul (sub_nonneg.mpr ht.2)]
    · rw [indicator_of_notMem ht]
      have heq (x : ℝ) : F (shear (x, t)) = 0 := by
        have hsub : x + t - x = t := by ring
        change A.indicator q (x, x + t) = 0
        by_cases hx : (x, x + t) ∈ A
        · rw [indicator_of_mem hx]
          change ENNReal.ofReal ((Icc a D).indicator g (x + t - x)) = 0
          rw [hsub, indicator_of_notMem ht, ENNReal.ofReal_zero]
        · exact indicator_of_notMem hx _
      simp_rw [heq, lintegral_zero]
  calc
    (∫⁻ p : ℝ × ℝ, q p ∂crossMeasure D) = ∫⁻ p, F p ∂μ := by
      rw [crossMeasure, Measure.prod_restrict, lintegral_indicator hA]
    _ = ∫⁻ p, F (shear p) ∂μ := (hS.lintegral_comp_emb shear.measurableEmbedding F).symm
    _ = ∫⁻ t : ℝ, ∫⁻ x : ℝ, F (shear (x, t)) :=
      lintegral_prod_symm _ (hF.comp_quasiMeasurePreserving hS.quasiMeasurePreserving)
    _ = _ := by simp_rw [hsection]; exact lintegral_indicator measurableSet_Icc _

private theorem integrableOn_exp_iff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {L D : ℝ} (hL : 0 < L) (g : ℝ → E) :
    IntegrableOn g (Icc L (Real.exp D)) ↔
      IntegrableOn (fun t ↦ Real.exp t • g (Real.exp t)) (Icc (Real.log L) D) := by
  simpa only [Real.image_exp_Icc, Real.exp_log hL, abs_of_pos (Real.exp_pos _)] using
    integrableOn_image_iff_integrableOn_abs_deriv_smul (s := Icc (Real.log L) D) measurableSet_Icc
      (fun t _ ↦ (Real.hasDerivAt_exp t).hasDerivWithinAt) Real.exp_injective.injOn g

private theorem norm_kernel_sq (D L : ℝ) (m : ℝ → ℂ) (x y : ℝ) :
    ‖kernel D L m x y‖ ^ 2 =
      (Icc (Real.log L) D).indicator (fun t ↦ Real.exp t * ‖m (Real.exp t)‖ ^ 2) (y - x) := by
  by_cases ht : y - x ∈ Icc (Real.log L) D
  · simp only [kernel, indicator_of_mem ht, norm_smul, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _), mul_pow, pow_two (Real.exp _), ← Real.exp_add]
    rw [show (y - x) / 2 + (y - x) / 2 = y - x by ring]
  · simp [kernel, ht]

private theorem integrable_weightedSquare {D L : ℝ} {m : ℝ → ℂ} (hL : 0 < L)
    (hm : IntegrableOn (fun v ↦ ‖m v‖ ^ 2) (Icc L (Real.exp D))) :
    IntegrableOn (weightedSquare D m) (Icc L (Real.exp D)) := by
  have hlog : AEStronglyMeasurable (fun v ↦ Real.log (Real.exp D / v))
      (volume.restrict (Icc L (Real.exp D))) :=
    (Real.measurable_log.comp (measurable_const.div measurable_id)).aestronglyMeasurable
  refine hm.bdd_mul (c := D - Real.log L) hlog ?_
  filter_upwards [ae_restrict_mem (μ := (volume : Measure ℝ))
    (measurableSet_Icc (a := L) (b := Real.exp D))] with v hv
  have hv₀ := hL.trans_le hv.1
  have hupper : Real.log v ≤ D := by simpa using Real.log_le_log hv₀ hv.2
  have hlower := Real.log_le_log hL hv.1
  rw [Real.norm_eq_abs, Real.log_div (Real.exp_ne_zero _) hv₀.ne', Real.log_exp,
    abs_of_nonneg (sub_nonneg.mpr hupper)]
  exact sub_le_sub_left hlower D

private theorem weighted_exp (D : ℝ) (m : ℝ → ℂ) (t : ℝ) :
    Real.exp t • weightedSquare D m (Real.exp t) =
      (D - t) * (Real.exp t * ‖m (Real.exp t)‖ ^ 2) := by
  rw [weightedSquare, Real.log_div (Real.exp_ne_zero _) (Real.exp_ne_zero _),
    Real.log_exp, Real.log_exp, smul_eq_mul]
  ring

private theorem sq_integral_product {D L : ℝ} {m : ℝ → ℂ}
    (hL : 0 < L) (hhalf : D / 2 ≤ Real.log L)
    (hm : IntegrableOn (fun v ↦ ‖m v‖ ^ 2) (Icc L (Real.exp D))) :
    Integrable (fun p : ℝ × ℝ ↦ ‖kernel D L m p.1 p.2‖ ^ 2) (crossMeasure D) ∧
    (∫ p : ℝ × ℝ, ‖kernel D L m p.1 p.2‖ ^ 2 ∂crossMeasure D) =
      ∫ v in Icc L (Real.exp D), weightedSquare D m v := by
  let g := fun t : ℝ ↦ Real.exp t * ‖m (Real.exp t)‖ ^ 2
  have hg : IntegrableOn g (Icc (Real.log L) D) :=
    (integrableOn_exp_iff hL _).mp hm
  have hw := integrable_weightedSquare hL hm
  have hgw : IntegrableOn (fun t ↦ (D - t) * g t) (Icc (Real.log L) D) := by
    simpa only [weighted_exp] using (integrableOn_exp_iff hL _).mp hw
  have hgw₀ : 0 ≤ᵐ[volume.restrict (Icc (Real.log L) D)] (fun t ↦ (D - t) * g t) := by
    filter_upwards [ae_restrict_mem (μ := (volume : Measure ℝ))
      (measurableSet_Icc (a := Real.log L) (b := D))] with t ht
    exact mul_nonneg (sub_nonneg.mpr ht.2) (by dsimp [g]; positivity)
  have hKsm : AEStronglyMeasurable (fun p : ℝ × ℝ ↦ ‖kernel D L m p.1 p.2‖ ^ 2)
      (crossMeasure D) := by
    simp_rw [norm_kernel_sq]
    rw [crossMeasure, Measure.prod_restrict]
    exact (aestronglyMeasurable_difference hg.aestronglyMeasurable).restrict
  have hlin : (∫⁻ p : ℝ × ℝ, ENNReal.ofReal (‖kernel D L m p.1 p.2‖ ^ 2) ∂crossMeasure D) =
      ∫⁻ t in Icc (Real.log L) D, ENNReal.ofReal ((D - t) * g t) := by
    simp_rw [norm_kernel_sq]
    exact lintegral_difference hhalf hg.aestronglyMeasurable
  have hK₀ : 0 ≤ᵐ[crossMeasure D] (fun p : ℝ × ℝ ↦ ‖kernel D L m p.1 p.2‖ ^ 2) :=
    ae_of_all _ fun _ ↦ sq_nonneg _
  refine ⟨(lintegral_ofReal_ne_top_iff_integrable hKsm hK₀).1 ?_, ?_⟩
  · rw [hlin]
    exact (lintegral_ofReal_ne_top_iff_integrable hgw.aestronglyMeasurable hgw₀).2 hgw
  · rw [integral_eq_lintegral_of_nonneg_ae hK₀ hKsm, hlin,
      ← integral_eq_lintegral_of_nonneg_ae hgw₀ hgw.aestronglyMeasurable]
    symm
    simpa only [Real.image_exp_Icc, Real.exp_log hL, abs_of_pos (Real.exp_pos _), weighted_exp] using
      integral_image_eq_integral_abs_deriv_smul (s := Icc (Real.log L) D) measurableSet_Icc
        (fun t _ ↦ (Real.hasDerivAt_exp t).hasDerivWithinAt) Real.exp_injective.injOn
        (weightedSquare D m)

/-- Exact Hilbert–Schmidt square. Only the squared norm of `m` needs to be
measurable here. The closed interval is allowed to degenerate when `L = exp D`. -/
theorem integral_sq_kernel {D L : ℝ} {m : ℝ → ℂ}
    (_hD : 0 < D) (hL : 0 < L) (_hLY : L ≤ Real.exp D) (hhalf : D / 2 ≤ Real.log L)
    (hm : IntegrableOn (fun v ↦ ‖m v‖ ^ 2) (Icc L (Real.exp D))) :
    Integrable (fun p : ℝ × ℝ ↦ ‖kernel D L m p.1 p.2‖ ^ 2) (crossMeasure D) ∧
    (∫ x in leftHalf D, ∫ y in rightHalf D, ‖kernel D L m x y‖ ^ 2) =
      ∫ v in Icc L (Real.exp D), weightedSquare D m v := by
  obtain ⟨hi, h⟩ := sq_integral_product hL hhalf hm
  exact ⟨hi, (integral_prod _ hi).symm.trans h⟩

/-- The forward pairing integrand, with the input at the left endpoint conjugated. -/
@[expose] noncomputable def pairingIntegrand (D L : ℝ) (m f : ℝ → ℂ) (p : ℝ × ℝ) : ℂ :=
  kernel D L m p.1 p.2 * (star (f p.1) * f p.2)

/-- The forward pairing plus its adjoint, as a real quadratic form. -/
@[expose] noncomputable def symmetricForm (D L : ℝ) (m f : ℝ → ℂ) : ℝ :=
  2 * (∫ x in leftHalf D, ∫ y in rightHalf D, pairingIntegrand D L m f (x, y)).re

private theorem aestronglyMeasurable_kernel {D L : ℝ} {m : ℝ → ℂ} (hL : 0 < L)
    (hm : MemLp m 2 (volume.restrict (Icc L (Real.exp D)))) :
    AEStronglyMeasurable (fun p : ℝ × ℝ ↦ kernel D L m p.1 p.2) (crossMeasure D) := by
  have hi := (integrableOn_exp_iff hL m).mp (hm.integrable (by norm_num))
  have hsm : AEStronglyMeasurable (fun t ↦ Real.exp (t / 2) • m (Real.exp t))
      (volume.restrict (Icc (Real.log L) D)) := by
    have hfactor : Continuous (fun t : ℝ ↦ Real.exp (t / 2) * (Real.exp t)⁻¹) :=
      (Real.continuous_exp.comp (continuous_id.div_const 2)).mul
        (Real.continuous_exp.inv₀ fun t ↦ Real.exp_ne_zero t)
    convert hfactor.aestronglyMeasurable.smul hi.aestronglyMeasurable using 1
    funext t
    change _ = (Real.exp (t / 2) * (Real.exp t)⁻¹) • (Real.exp t • m (Real.exp t))
    rw [mul_smul, inv_smul_smul₀ (Real.exp_ne_zero t)]
  rw [crossMeasure, Measure.prod_restrict]
  exact (aestronglyMeasurable_difference hsm).restrict

private theorem integral_halves {D : ℝ} (hD : 0 < D) {g : ℝ → ℝ}
    (hg : IntegrableOn g (Icc 0 D)) :
    (∫ x in leftHalf D, g x) + (∫ y in rightHalf D, g y) = ∫ x in Icc 0 D, g x := by
  have hd₀ : 0 ≤ D / 2 := by linarith
  have hd₁ : D / 2 ≤ D := by linarith
  have hd : Disjoint (Icc 0 (D / 2)) (Ioc (D / 2) D) :=
    Set.disjoint_left.2 fun _ hx hy ↦ (not_lt_of_ge hx.2) hy.1
  rw [leftHalf, rightHalf, integral_Icc_eq_integral_Ioc (x := D / 2),
    ← setIntegral_union hd measurableSet_Ioc
      (hg.mono_set (Icc_subset_Icc le_rfl hd₁))
      (hg.mono_set (Ioc_subset_Icc_self.trans (Icc_subset_Icc hd₀ le_rfl))),
    Icc_union_Ioc_eq_Icc hd₀ hd₁]

/-- A unit window input has absolute symmetric crossing form at most the
Hilbert–Schmidt norm, not twice that norm. The source's cellwise constant
coefficient is measurable; its almost-everywhere measurability is stated here
separately from integrability of its squared norm. -/
theorem abs_symmetricForm_le {D L : ℝ} {m f : ℝ → ℂ}
    (hD : 0 < D) (hL : 0 < L) (_hLY : L ≤ Real.exp D) (hhalf : D / 2 ≤ Real.log L)
    (hm_meas : AEStronglyMeasurable m (volume.restrict (Icc L (Real.exp D))))
    (hm : IntegrableOn (fun v ↦ ‖m v‖ ^ 2) (Icc L (Real.exp D)))
    (hf : MemLp f 2 (volume.restrict (Icc 0 D)))
    (hunit : (∫ x in Icc 0 D, ‖f x‖ ^ 2) = 1) :
    Integrable (pairingIntegrand D L m f) (crossMeasure D) ∧
    |symmetricForm D L m f| ≤ Real.sqrt (∫ v in Icc L (Real.exp D), weightedSquare D m v) := by
  let μ := (volume : Measure ℝ).restrict (leftHalf D)
  let ν := (volume : Measure ℝ).restrict (rightHalf D)
  have : IsFiniteMeasure μ := by dsimp [μ, leftHalf]; infer_instance
  have : IsFiniteMeasure ν := by dsimp [ν, rightHalf]; infer_instance
  have hleft : MemLp f 2 μ :=
    hf.mono_measure (Measure.restrict_mono (Icc_subset_Icc le_rfl (by linarith)) le_rfl)
  have hright : MemLp f 2 ν :=
    hf.mono_measure (Measure.restrict_mono (Icc_subset_Icc (by linarith) le_rfl) le_rfl)
  have hl := hleft.integrable_norm_pow (by decide : (2 : ℕ) ≠ 0)
  have hr := hright.integrable_norm_pow (by decide : (2 : ℕ) ≠ 0)
  let K := fun p : ℝ × ℝ ↦ kernel D L m p.1 p.2
  let P := fun p : ℝ × ℝ ↦ star (f p.1) * f p.2
  obtain ⟨hK_sq, hK_integral⟩ := sq_integral_product hL hhalf hm
  have hK : MemLp K 2 (crossMeasure D) :=
    (memLp_two_iff_integrable_sq_norm (aestronglyMeasurable_kernel hL
      ((memLp_two_iff_integrable_sq_norm hm_meas).2 hm))).2 hK_sq
  have hP : MemLp P 2 (crossMeasure D) := by
    have hfst := (hleft.star.comp_fst ν).aestronglyMeasurable
    have hsnd := (hright.comp_snd μ).aestronglyMeasurable
    apply (memLp_two_iff_integrable_sq_norm (hfst.mul hsnd)).2
    simpa only [Pi.mul_apply, Pi.star_apply, norm_mul, norm_star, mul_pow] using hl.mul_prod hr
  have hp_integrable : Integrable (pairingIntegrand D L m f) (crossMeasure D) :=
    memLp_one_iff_integrable.1 (hK.fun_mul hP)
  refine ⟨hp_integrable, ?_⟩
  have hcs := integral_mul_norm_le_Lp_mul_Lq Real.HolderConjugate.two_two
    (show MemLp K (ENNReal.ofReal 2) (crossMeasure D) from by simpa using hK)
    (show MemLp P (ENNReal.ofReal 2) (crossMeasure D) from by simpa using hP)
  rw [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow] at hcs
  simp only [Real.rpow_two] at hcs
  let a := ∫ x in leftHalf D, ‖f x‖ ^ 2
  let b := ∫ y in rightHalf D, ‖f y‖ ^ 2
  have hP_integral : (∫ p : ℝ × ℝ, ‖P p‖ ^ 2 ∂crossMeasure D) = a * b := by
    simp only [P, norm_mul, norm_star, mul_pow]
    exact integral_prod_mul (μ := μ) (ν := ν) (fun x ↦ ‖f x‖ ^ 2) (fun y ↦ ‖f y‖ ^ 2)
  rw [hK_integral, hP_integral] at hcs
  have ha : 0 ≤ a := integral_nonneg fun _ ↦ sq_nonneg _
  have hb : 0 ≤ b := integral_nonneg fun _ ↦ sq_nonneg _
  have hab : a + b = 1 := (integral_halves hD (hf.integrable_norm_pow (by decide))).trans hunit
  have hyoung : 2 * √a * √b ≤ 1 := by
    nlinarith only [sq_nonneg (√a - √b), Real.sq_sqrt ha, Real.sq_sqrt hb, hab]
  let M := √(∫ v in Icc L (Real.exp D), weightedSquare D m v)
  have hpair : ‖∫ p, pairingIntegrand D L m f p ∂crossMeasure D‖ ≤ M * (√a * √b) := by
    refine (norm_integral_le_integral_norm _).trans ?_
    simpa only [pairingIntegrand, norm_mul, Real.sqrt_mul ha, M, K, P] using hcs
  rw [symmetricForm, ← integral_prod _ hp_integrable, abs_mul,
    abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  calc
    2 * |(∫ p, pairingIntegrand D L m f p ∂crossMeasure D).re| ≤ 2 * (M * (√a * √b)) :=
      mul_le_mul_of_nonneg_left ((Complex.abs_re_le_norm _).trans hpair) (by norm_num)
    _ = M * (2 * √a * √b) := by ring
    _ ≤ M := mul_le_of_le_one_right (Real.sqrt_nonneg _) hyoung

private theorem integrable_weighted_shift {k f : ℝ → ℂ} (hk : Integrable k)
    (hf : MemLp f 2 volume) :
    Integrable (fun p : ℝ × ℝ ↦ k p.1 * (star (f p.2) * f (p.1 + p.2)))
      ((volume : Measure ℝ).prod volume) := by
  let μ := (volume : Measure ℝ).prod (volume : Measure ℝ)
  have hS : MeasurePreserving shear μ μ := measurePreserving_prod_add volume volume
  have hk₁ : AEStronglyMeasurable (fun p : ℝ × ℝ ↦ k p.1) μ :=
    hk.aestronglyMeasurable.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_fst
  have hf₂ : AEStronglyMeasurable (fun p : ℝ × ℝ ↦ f p.2) μ :=
    hf.aestronglyMeasurable.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd
  have hfshift : AEStronglyMeasurable (fun p : ℝ × ℝ ↦ f (p.1 + p.2)) μ :=
    hf₂.comp_measurePreserving hS
  have ha := hk.norm.mul_prod (hf.integrable_norm_pow (by decide : (2 : ℕ) ≠ 0))
  have hb := (hS.integrable_comp_emb shear.measurableEmbedding).2 ha
  -- Use the average of the two squared norms as an absolute majorant.
  refine ((ha.add hb).div_const 2).mono (hk₁.mul (hf₂.star.mul hfshift)) ?_
  refine ae_of_all _ fun p ↦ ?_
  change ‖k p.1 * (star (f p.2) * f (p.1 + p.2))‖ ≤
    ‖(‖k p.1‖ * ‖f p.2‖ ^ 2 + ‖k p.1‖ * ‖f (p.1 + p.2)‖ ^ 2) / 2‖
  rw [norm_mul, norm_mul, norm_star, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  nlinarith only [mul_nonneg (norm_nonneg (k p.1))
    (sq_nonneg (‖f p.2‖ - ‖f (p.1 + p.2)‖))]

/-- The continuous crossing form is the forward shift correlation plus its
adjoint. The input is zero-extended from `[0,D]`; no unit-norm condition is needed.
An integrable complex cell coefficient suffices, in particular a bounded
measurable coefficient on the finite interval. Both the rectangle pairing
and the weighted correlation on the original variable interval are integrable.

Source: `8058479edd84:.godel/bob/short-cell-weil-list.md:41–47`, used at line 53
(scan pin `082a89e67352a18e3f534bc75a2d45807b145771`). This is only the
continuous geometric identity, not the discrete-to-continuous replacement.
Owning check session: `01a2102d-ae00-70d1-a793-4b136b9edf79`. -/
theorem symmetricForm_eq_shiftCorrelation {D L : ℝ} {m f : ℝ → ℂ}
    (_hD : 0 < D) (hL : 0 < L) (hhalf : D / 2 ≤ Real.log L) (_hupper : Real.log L ≤ D)
    (hm : IntegrableOn m (Icc L (Real.exp D)))
    (hf : MemLp f 2 (volume.restrict (Icc 0 D)))
    (hzero : ∀ x ∉ Icc 0 D, f x = 0) :
    Integrable (pairingIntegrand D L m f) (crossMeasure D) ∧
    IntegrableOn (fun v ↦ (m v / (√v : ℂ)) *
      (∫ x : ℝ, star (f x) * f (x + Real.log v))) (Icc L (Real.exp D)) ∧
    symmetricForm D L m f = 2 * (∫ v in Icc L (Real.exp D),
      (m v / (√v : ℂ)) * (∫ x : ℝ, star (f x) * f (x + Real.log v))).re := by
  let w := fun v : ℝ ↦ m v / (√v : ℂ)
  let c := fun t : ℝ ↦ ∫ x : ℝ, star (f x) * f (x + t)
  let g := fun v : ℝ ↦ w v * c (Real.log v)
  let J := Icc (Real.log L) D
  let K := fun t : ℝ ↦ Real.exp (t / 2) • m (Real.exp t)
  let k := J.indicator K
  have hw : IntegrableOn w (Icc L (Real.exp D)) := by
    have hmeas : Measurable (fun v : ℝ ↦ ((√v : ℝ) : ℂ)⁻¹) :=
      (Complex.continuous_ofReal.comp Real.continuous_sqrt).measurable.inv
    refine (hm.bdd_mul (c := (√L)⁻¹) hmeas.aestronglyMeasurable ?_).congr ?_
    · filter_upwards [ae_restrict_mem (μ := (volume : Measure ℝ))
        (measurableSet_Icc (a := L) (b := Real.exp D))] with v hv
      rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
      exact (inv_le_inv₀ (Real.sqrt_pos_of_pos (hL.trans_le hv.1))
        (Real.sqrt_pos_of_pos hL)).2 (Real.sqrt_le_sqrt hv.1)
    · exact ae_of_all _ fun v ↦ by simp only [w, div_eq_mul_inv, mul_comm]
  -- Under `v = exp t`, the density `dv / √v` becomes `exp (t / 2) dt`.
  have hJ (t : ℝ) : Real.exp t • w (Real.exp t) = K t := by
    simp only [w, K, RCLike.real_smul_eq_coe_mul, ← Real.exp_half]
    have he : Complex.ofReal (Real.exp t) = Complex.ofReal (Real.exp (t / 2)) ^ 2 := by
      rw [← Complex.ofReal_pow, pow_two, ← Real.exp_add, add_halves]
    have hn : Complex.ofReal (Real.exp (t / 2)) ≠ 0 :=
      Complex.ofReal_ne_zero.2 (Real.exp_ne_zero _)
    change Complex.ofReal (Real.exp t) * (m (Real.exp t) / Complex.ofReal (Real.exp (t / 2))) =
      Complex.ofReal (Real.exp (t / 2)) * m (Real.exp t)
    rw [he]
    field_simp [hn]
  have hk : Integrable k := (integrable_indicator_iff measurableSet_Icc).2 (by
    simpa only [hJ] using (integrableOn_exp_iff hL w).1 hw)
  have hfvol : MemLp f 2 volume := by
    have heq : (Icc 0 D).indicator f = f := by
      funext x
      by_cases hx : x ∈ Icc 0 D
      · exact indicator_of_mem hx f
      · rw [indicator_of_notMem hx, hzero x hx]
    simpa only [heq] using (memLp_indicator_iff_restrict measurableSet_Icc.nullMeasurableSet).2 hf
  let μ := (volume : Measure ℝ).prod (volume : Measure ℝ)
  let A := leftHalf D ×ˢ rightHalf D
  let F := A.indicator (pairingIntegrand D L m f)
  let G := fun p : ℝ × ℝ ↦ k p.1 * (star (f p.2) * f (p.1 + p.2))
  have hA : MeasurableSet A := measurableSet_Icc.prod measurableSet_Icc
  have hS : MeasurePreserving shear μ μ := measurePreserving_prod_add volume volume
  have hG : Integrable G μ := integrable_weighted_shift hk hfvol
  -- The rectangular indicator becomes redundant on the band: if both input
  -- values can be nonzero, their difference forces them into opposite halves.
  have hFG : F ∘ shear = G ∘ Prod.swap := by
    funext p
    obtain ⟨x, t⟩ := p
    change A.indicator (pairingIntegrand D L m f) (x, x + t) =
      k t * (star (f x) * f (t + x))
    rw [add_comm t x]
    by_cases hp : (x, x + t) ∈ A
    · rw [indicator_of_mem hp]
      have hsub : x + t - x = t := by ring
      simp only [pairingIntegrand, kernel, hsub, k, J, K]
    rw [indicator_of_notMem hp]
    by_cases ht : t ∈ J
    · by_cases hx : x ∈ Icc 0 D
      · have hy : x + t ∉ Icc 0 D := by
          intro hy
          apply hp
          change x ∈ {x | (x, x + t) ∈ leftHalf D ×ˢ rightHalf D}
          rw [fiber_eq hhalf ht]
          exact ⟨hx.1, by linarith only [hy.2]⟩
        rw [hzero _ hy, mul_zero, mul_zero]
      · rw [hzero _ hx, star_zero, zero_mul, mul_zero]
    · simp only [k, indicator_of_notMem ht, zero_mul]
  have hF : Integrable F μ := (hS.integrable_comp_emb shear.measurableEmbedding).1 (by
    rw [hFG]
    exact hG.swap)
  have hPair : Integrable (pairingIntegrand D L m f) (crossMeasure D) := by
    rw [crossMeasure, Measure.prod_restrict]
    exact (integrable_indicator_iff hA).1 hF
  have hinner (t : ℝ) : (∫ x : ℝ, G (t, x)) = J.indicator (fun t ↦ K t * c t) t := by
    change (∫ x : ℝ, k t * (star (f x) * f (t + x))) = _
    simp_rw [add_comm t, integral_const_mul]
    by_cases ht : t ∈ J
    · simp only [k, indicator_of_mem ht, c]
    · simp only [k, indicator_of_notMem ht, zero_mul]
  have hlog : IntegrableOn (fun t ↦ K t * c t) J :=
    (integrable_indicator_iff measurableSet_Icc).1 (by
      simpa only [hinner] using hG.integral_prod_left)
  have hchange (t : ℝ) : Real.exp t • g (Real.exp t) = K t * c t := by
    dsimp only [g]
    rw [Real.log_exp, ← smul_mul_assoc, hJ]
  have hg : IntegrableOn g (Icc L (Real.exp D)) :=
    (integrableOn_exp_iff hL g).2 (by simpa only [hchange] using hlog)
  have hsubst : (∫ v in Icc L (Real.exp D), g v) = ∫ t in J, K t * c t := by
    simpa only [J, Real.image_exp_Icc, Real.exp_log hL, abs_of_pos (Real.exp_pos _), hchange] using
      integral_image_eq_integral_abs_deriv_smul (s := J) measurableSet_Icc
        (fun t _ ↦ (Real.hasDerivAt_exp t).hasDerivWithinAt) Real.exp_injective.injOn g
  have heq : (∫ p, pairingIntegrand D L m f p ∂crossMeasure D) = ∫ v in Icc L (Real.exp D), g v :=
    calc
      (∫ p, pairingIntegrand D L m f p ∂crossMeasure D) = ∫ p, F p ∂μ := by
        rw [crossMeasure, Measure.prod_restrict, ← integral_indicator hA]
      _ = ∫ p, F (shear p) ∂μ := (hS.integral_comp shear.measurableEmbedding F).symm
      _ = ∫ p, G p ∂μ := by
        change (∫ p, (F ∘ shear) p ∂μ) = _
        rw [hFG]
        exact integral_prod_swap G
      _ = ∫ t : ℝ, ∫ x : ℝ, G (t, x) := integral_prod G hG
      _ = ∫ t in J, K t * c t := by simp_rw [hinner]; exact integral_indicator measurableSet_Icc
      _ = _ := hsubst.symm
  refine ⟨hPair, hg, ?_⟩
  rw [symmetricForm, ← integral_prod _ hPair]
  change 2 * (∫ p, pairingIntegrand D L m f p ∂crossMeasure D).re =
    2 * (∫ v in Icc L (Real.exp D), g v).re
  rw [heq]

end

end ShortCellCrossing
