module

public import Theorems.DirichletThreeRectangleResidues
import Theorems.DirichletThreeResidueSummability
import Theorems.DirichletContourReflection
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.Normed.Group.InfiniteSum

/-!
# Conductor-three completed residue exhaustion

The exact Mathlib completion of the odd primitive quadratic character modulo
three is used, without a conductor power. This is a local full-order residue
exhaustion, not an identification with the normalized idelic completion or a
zero-location theorem. Its correspondence to the counterclockwise contour
(Fig. 3 and (B.3.2.3), PDF pp. 605–606) and to (B.4.2.2) (PDF p. 614) is
provisional. Owning check session: `01a20525-b261-79ef-94fa-7a6b64536cd6`.
-/

open Complex Filter MeasureTheory Set
open scoped ContDiff Topology

namespace Masullo

local notation "χ₃" => padicRamifiedThreeCharacter
local notation "C₃" => DirichletCharacter.completedLFunction χ₃
local notation "Z₃" => {z : ℂ // C₃ z = 0}
local notation "W" => fun (g : ℝ → ℂ) (z : ℂ) ↦
  (analyticOrderNatAt C₃ z : ℂ) * compactLogMellin g z
local notation "F" => fun (g : ℝ → ℂ) (s : ℂ) ↦ compactLogMellin g s * logDeriv C₃ s

/-- Both vertical lines are absolutely integrable in the upward coordinate. -/
private theorem three_vertical_integrable {g : ℝ → ℂ} (hg : ContDiff ℝ ∞ g)
    (hcg : HasCompactSupport g) :
    let V (σ t : ℝ) := F g ((σ : ℂ) + (t : ℂ) * I)
    Integrable (V (3 / 2)) ∧ Integrable (V (-1 / 2)) := by
  constructor
  · let k := fun x : ℝ ↦ exp (-x) * g (-x)
    have hExp : ContDiff ℝ ∞ (fun x : ℝ ↦ exp (-x)) :=
      Complex.contDiff_exp.comp Complex.ofRealCLM.contDiff.neg
    have hk : ContDiff ℝ ∞ k := hExp.mul (hg.comp contDiff_neg)
    have hck : HasCompactSupport k := (hcg.comp_homeomorph (Homeomorph.neg ℝ)).mul_left
    have hv := integrable_compactLogMellin_completedDirichlet_reflected χ₃ hk hck
      (a := 3 / 2) (by norm_num)
    have htest (s : ℂ) : compactLogMellin k (1 - s) = compactLogMellin g s :=
      (compactLogMellin_reflect g (1 - s)).symm.trans
        (congrArg (compactLogMellin g) (by ring))
    simpa only [htest] using hv
  · have hv := (completedDirichlet_reflect_left_integral
      padicRamifiedThreeCharacter_isPrimitive (by norm_num) (a := 3 / 2) (by norm_num) hg hcg).1
    dsimp only at hv
    simpa only [show (1 - (3 / 2 : ℝ)) = -1 / 2 by norm_num] using hv

/-- The finite rectangles eventually contain each finite subset of the full zero divisor. -/
private theorem three_rectangle_subtypes_cofinal {T : ℕ → ℝ} (hT : Tendsto T atTop atTop) :
    Tendsto (fun n ↦ (padicRamifiedThree_rectangleZeros (T n)).subtype (fun z ↦ C₃ z = 0))
      atTop (atTop : Filter (Finset Z₃)) := by
  classical
  simp only [atTop_finset_eq_iInf, tendsto_iInf, tendsto_principal]
  intro z
  have hleft : 0 < (z : ℂ).re := lt_of_not_ge fun hz ↦
    padicRamifiedThree_completed_ne_zero_of_re_nonpos hz z.property
  have hright : (z : ℂ).re < 1 := lt_of_not_ge fun hz ↦
    padicRamifiedThree_completed_ne_zero_of_one_le_re hz z.property
  filter_upwards [hT.eventually (eventually_gt_atTop |(z : ℂ).im|)] with n hn
  exact Finset.singleton_subset_iff.mpr <| Finset.mem_subtype.mpr <|
    mem_padicRamifiedThree_rectangleZeros.mpr
      ⟨mem_reProdIm.mpr ⟨⟨by linarith, by linarith⟩, abs_lt.mp hn⟩, z.property⟩

/-- For any heights tending to infinity the finite full-order sums converge to
the unrestricted sum over the completed zeros. -/
public theorem tendsto_padicRamifiedThree_completed_rectangle_zero_sum
    {T : ℕ → ℝ} (hT : Tendsto T atTop atTop) {g : ℝ → ℂ}
    (hg : ContDiff ℝ ∞ g) (hcg : HasCompactSupport g) :
    Tendsto (fun n ↦ ∑ z ∈ padicRamifiedThree_rectangleZeros (T n), W g z)
      atTop (𝓝 (∑' z : Z₃, W g (z : ℂ))) := by
  classical
  have hs : Summable (fun z : Z₃ ↦ W g (z : ℂ)) :=
    (summable_norm_padicRamifiedThree_completed_zero_test hg hcg).of_norm_bounded
      (fun _ ↦ le_rfl)
  have hlim : Tendsto (fun s : Finset Z₃ ↦ ∑ z ∈ s, W g (z : ℂ))
      atTop (𝓝 (∑' z : Z₃, W g (z : ℂ))) := hs.hasSum
  have hc := hlim.comp (three_rectangle_subtypes_cofinal hT)
  refine hc.congr' (Eventually.of_forall fun n ↦ ?_)
  exact Finset.sum_subtype_of_mem (W g) (fun z hz ↦
    (mem_padicRamifiedThree_rectangleZeros.mp hz).2)

/-- One sequence of heights works for every smooth compact log profile. The
full-order sum is absolutely convergent and equals the right-minus-left upward
vertical contour integrals, divided by `2πi`. The factors `I` in the numerator
are the vertical Jacobians; there are no pole terms for this completion. -/
public theorem padicRamifiedThree_completed_residue_exhaustion :
    ∃ T : ℕ → ℝ,
      (∀ n : ℕ, T n ∈ Ioo ((n : ℝ) + 1) ((n : ℝ) + 2)) ∧
      ∀ (g : ℝ → ℂ), ContDiff ℝ ∞ g → HasCompactSupport g →
        let V (σ t : ℝ) := F g ((σ : ℂ) + (t : ℂ) * I)
        Summable (fun z : Z₃ ↦ ‖W g (z : ℂ)‖) ∧
        Tendsto (fun n ↦ ∑ z ∈ padicRamifiedThree_rectangleZeros (T n), W g z)
          atTop (𝓝 (∑' z : Z₃, W g (z : ℂ))) ∧
        Integrable (V (3 / 2)) ∧ Integrable (V (-1 / 2)) ∧
        (∑' z : Z₃, W g (z : ℂ)) =
          (I * (∫ t, V (3 / 2) t) - I * (∫ t, V (-1 / 2) t)) / (2 * Real.pi * I) := by
  obtain ⟨T, hT, hrect⟩ := padicRamifiedThree_completed_rectangleResidues_at_good_heights
  have hTlim : Tendsto T atTop atTop :=
    tendsto_atTop_mono (f := fun n : ℕ ↦ (n : ℝ))
      (fun n ↦ by linarith [(hT n).1]) tendsto_natCast_atTop_atTop
  refine ⟨T, hT, fun g hg hcg ↦ ?_⟩
  obtain ⟨hres, htop, hbot⟩ := hrect g hg hcg
  obtain ⟨hR, hL⟩ := three_vertical_integrable hg hcg
  have hsum := summable_norm_padicRamifiedThree_completed_zero_test hg hcg
  have hsumlim := tendsto_padicRamifiedThree_completed_rectangle_zero_sum hTlim hg hcg
  refine ⟨hsum, hsumlim, hR, hL, ?_⟩
  let V (σ t : ℝ) := F g ((σ : ℂ) + (t : ℂ) * I)
  have hneg := tendsto_neg_atTop_atBot.comp hTlim
  have hr := intervalIntegral_tendsto_integral hR hneg hTlim
  have hl := intervalIntegral_tendsto_integral hL hneg hTlim
  have hcontour : Tendsto (fun n ↦ rectangleIntegral (-1 / 2) (3 / 2) (-T n) (T n) (F g))
      atTop (𝓝 (I * (∫ t, V (3 / 2) t) - I * (∫ t, V (-1 / 2) t))) := by
    simpa only [rectangleIntegral, V, ofReal_neg, neg_mul, sub_eq_add_neg, zero_add, sub_self,
      neg_zero, add_zero, Function.comp_def] using
      ((hbot.sub htop).add (hr.const_mul I)).sub (hl.const_mul I)
  have hreslim := ((hsumlim.const_mul (2 * (Real.pi : ℂ) * I))).congr' (Eventually.of_forall
    fun n ↦ (hres n).symm)
  have h := tendsto_nhds_unique hreslim hcontour
  exact (eq_div_iff (show (2 * (Real.pi : ℂ) * I) ≠ 0 by simp [Real.pi_ne_zero])).2
    ((mul_comm _ _).trans h)

end Masullo
