module

public import Lemmas.CompactLogMellinPolynomial
public import Lemmas.CompactLogMellinSmoothing
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-! # Adjoint operations on positive-log densities -/

open Filter Function MeasureTheory Set
open scoped ContDiff Topology

namespace Masullo

/-- The formal adjoint `P(-∂)` of the real log differential operator `P(∂)`. -/
@[expose] public noncomputable def logPolynomialAdjoint (P : Polynomial ℝ) (ρ : ℝ → ℝ)
    (x : ℝ) : ℝ := ∑ n ∈ P.support, P.coeff n * ((-1 : ℝ) ^ n * iteratedDeriv n ρ x)

private theorem iteratedDeriv_pos_smooth {ρ : ℝ → ℝ} (hρ : ContDiffOn ℝ ∞ ρ (Ioi 0))
    (n : ℕ) : ContDiffOn ℝ ∞ (iteratedDeriv n ρ) (Ioi 0) := by
  induction n with
  | zero => simpa using hρ
  | succ n ih => rw [iteratedDeriv_succ]; exact ih.deriv_of_isOpen isOpen_Ioi (by simp)

private theorem iteratedDeriv_support_subset (g : ℝ → ℝ) (n : ℕ) :
    tsupport (iteratedDeriv n g) ⊆ tsupport g := by
  induction n with
  | zero => simp
  | succ n ih => rw [iteratedDeriv_succ]; exact tsupport_deriv_subset.trans ih

private theorem integrable_pos_density_mul {ρ g : ℝ → ℝ} {a b : ℝ}
    (hρ : ContinuousOn ρ (Ioi 0)) (hg : Continuous g) (ha : 0 < a)
    (hs : tsupport g ⊆ Icc a b) : Integrable (fun x ↦ ρ x * g x) := by
  have hc := (hρ.mono (show Icc a b ⊆ Ioi (0 : ℝ) from fun _ hx ↦ ha.trans_le hx.1)).mul
    hg.continuousOn
  refine ((integrable_indicator_iff measurableSet_Icc).mpr
    (hc.integrableOn_compact isCompact_Icc)).congr (Eventually.of_forall fun x ↦ ?_)
  by_cases hx : x ∈ Icc a b
  · simp [hx]
  · simp [hx, image_eq_zero_of_notMem_tsupport (fun h ↦ hx (hs h))]

private theorem integral_density_iteratedDeriv (n : ℕ) {ρ g : ℝ → ℝ} {a b : ℝ}
    (hρ : ContDiffOn ℝ ∞ ρ (Ioi 0)) (hg : ContDiff ℝ ∞ g) (ha : 0 < a)
    (hs : tsupport g ⊆ Icc a b) :
    (∫ x, ρ x * iteratedDeriv n g x) = (-1 : ℝ) ^ n * ∫ x, iteratedDeriv n ρ x * g x := by
  induction n generalizing ρ with
  | zero => simp
  | succ n ih =>
    have hν : ContDiffOn ℝ ∞ (deriv ρ) (Ioi 0) := hρ.deriv_of_isOpen isOpen_Ioi (by simp)
    have hGn := hg.continuous_iteratedDeriv n (by simp)
    have hGn' := hg.continuous_iteratedDeriv (n + 1) (by simp)
    rw [iteratedDeriv_succ] at hGn' ⊢
    have hsG := (iteratedDeriv_support_subset g n).trans hs
    have hsG' : tsupport (deriv (iteratedDeriv n g)) ⊆ Icc a b := tsupport_deriv_subset.trans hsG
    have hzero (x : ℝ) (hx : x ∉ Icc a b) : (ρ * iteratedDeriv n g) x = 0 :=
      mul_eq_zero_of_right _ (image_eq_zero_of_notMem_tsupport fun h ↦ hx (hsG h))
    have hb : Tendsto (ρ * iteratedDeriv n g) atBot (𝓝 0) :=
      tendsto_const_nhds.congr' ((eventually_lt_atBot a).mono fun _ hx ↦
        (hzero _ (by simp [hx.not_ge])).symm)
    have ht : Tendsto (ρ * iteratedDeriv n g) atTop (𝓝 0) :=
      tendsto_const_nhds.congr' ((eventually_gt_atTop b).mono fun _ hx ↦
        (hzero _ (by simp [hx.not_ge])).symm)
    have hdg := hg.differentiable_iteratedDeriv n (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top n))
    have hbyparts := MeasureTheory.integral_mul_deriv_eq_deriv_mul
      (fun x hx ↦ ((hρ.differentiableOn (by simp) x (ha.trans_le (hsG hx).1)).differentiableAt
        (isOpen_Ioi.mem_nhds (ha.trans_le (hsG hx).1))).hasDerivAt)
      (fun x _ ↦ (hdg x).hasDerivAt)
      (integrable_pos_density_mul hρ.continuousOn hGn' ha hsG')
      (integrable_pos_density_mul hν.continuousOn hGn ha hsG) hb ht
    rw [hbyparts, sub_self, zero_sub, ih hν, ← iteratedDeriv_succ', iteratedDeriv_succ, pow_succ']
    ring

/-- Positive-log densities may be singular at zero; the formal adjoint is
continuous at all strictly positive arguments. -/
public theorem logPolynomialAdjoint_continuousOn (P : Polynomial ℝ) {ρ : ℝ → ℝ}
    (hρ : ContDiffOn ℝ ∞ ρ (Ioi 0)) : ContinuousOn (logPolynomialAdjoint P ρ) (Ioi 0) := by
  exact continuousOn_finsetSum _ fun n _ ↦ continuousOn_const.mul
    (continuousOn_const.mul (iteratedDeriv_pos_smooth hρ n).continuousOn)

/-- Transfer the polynomial from a compact positive-log test to the density. -/
public theorem integral_logPolynomialDeriv_adjoint (P : Polynomial ℝ)
    {ρ g : ℝ → ℝ} {a b : ℝ} (hρ : ContDiffOn ℝ ∞ ρ (Ioi 0)) (hg : ContDiff ℝ ∞ g)
    (ha : 0 < a) (hs : tsupport g ⊆ Icc a b) :
    Integrable (fun x ↦ ρ x * logPolynomialDeriv P g x) ∧
      (∫ x, ρ x * logPolynomialDeriv P g x) = ∫ x, logPolynomialAdjoint P ρ x * g x := by
  have hL (n : ℕ) : Integrable (fun x ↦ P.coeff n * (ρ x * iteratedDeriv n g x)) :=
    (integrable_pos_density_mul hρ.continuousOn (hg.continuous_iteratedDeriv n (by simp)) ha
      ((iteratedDeriv_support_subset g n).trans hs)).const_mul _
  have hR (n : ℕ) : Integrable (fun x ↦ P.coeff n * ((-1 : ℝ) ^ n * (iteratedDeriv n ρ x * g x))) :=
    ((integrable_pos_density_mul (iteratedDeriv_pos_smooth hρ n).continuousOn
      hg.continuous ha hs).const_mul _).const_mul _
  have hLeq (x : ℝ) : ρ x * logPolynomialDeriv P g x =
      ∑ n ∈ P.support, P.coeff n * (ρ x * iteratedDeriv n g x) := by
    rw [logPolynomialDeriv, Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ ↦ by ring
  have hReq (x : ℝ) : logPolynomialAdjoint P ρ x * g x =
      ∑ n ∈ P.support, P.coeff n * ((-1 : ℝ) ^ n * (iteratedDeriv n ρ x * g x)) := by
    simp only [logPolynomialAdjoint, Finset.sum_mul, mul_assoc]
  simp_rw [hLeq, hReq]
  refine ⟨integrable_finsetSum _ (fun n _ ↦ hL n), ?_⟩
  rw [integral_finsetSum _ (fun n _ ↦ hL n), integral_finsetSum _ (fun n _ ↦ hR n)]
  apply Finset.sum_congr rfl
  intro n _
  simp only [integral_const_mul, integral_density_iteratedDeriv n hρ hg ha hs]

private theorem integrable_on_carrying_rectangle {μ : Measure ℝ} [IsFiniteMeasure μ]
    {F : ℝ × ℝ → ℝ} {a c D : ℝ} (hμ : ∀ᵐ u ∂μ, u ∈ Icc 0 D)
    (hF : ContinuousOn F (Icc a c ×ˢ Icc 0 D))
    (hzero : ∀ x u, u ∈ Icc 0 D → x ∉ Icc a c → F (x, u) = 0) :
    Integrable F (volume.prod μ) := by
  have hc : IsCompact (Icc a c ×ˢ Icc 0 D) := isCompact_Icc.prod isCompact_Icc
  refine ((integrable_indicator_iff hc.measurableSet).mpr (hF.integrableOn_compact hc)).congr ?_
  filter_upwards [Measure.quasiMeasurePreserving_snd.ae hμ] with p hp
  by_cases hx : p.1 ∈ Icc a c
  · exact indicator_of_mem (show p ∈ Icc a c ×ˢ Icc 0 D from ⟨hx, hp⟩) _
  · rw [indicator_of_notMem (fun h : p ∈ Icc a c ×ˢ Icc 0 D ↦ hx h.1), ← Prod.mk.eta (p := p)]
    exact (hzero _ _ hp hx).symm

/-- Move a rightward translation average on the test to a leftward
translation average on the density, with an integrable pairing on the seed side. -/
public theorem integral_logTranslateAverage_adjoint {μ : Measure ℝ} [IsFiniteMeasure μ]
    {D a b : ℝ} (hμ : μ (Icc 0 D)ᶜ = 0) {φ ρ : ℝ → ℝ}
    (hρ : ContinuousOn ρ (Ioi 0)) (hφ : Continuous φ) (ha : 0 < a)
    (hs : tsupport φ ⊆ Icc a b) :
    Integrable (fun x ↦ (∫ u, ρ (x + u) ∂μ) * φ x) ∧
      (∫ x, ρ x * logTranslateAverage μ φ x) = ∫ x, (∫ u, ρ (x + u) ∂μ) * φ x := by
  have hD : ∀ᵐ u ∂μ, u ∈ Icc 0 D := ae_iff.mpr hμ
  let F (x u : ℝ) := ρ x * φ (x - u)
  let G (x u : ℝ) := ρ (x + u) * φ x
  have hFi : Integrable (uncurry F) (volume.prod μ) := by
    apply integrable_on_carrying_rectangle (a := a) (c := b + D) hD
    · have hp : MapsTo Prod.fst (Icc a (b + D) ×ˢ Icc 0 D) (Ioi (0 : ℝ)) :=
        fun _ h ↦ ha.trans_le h.1.1
      exact (hρ.comp continuous_fst.continuousOn hp).mul
        ((hφ.comp (continuous_fst.sub continuous_snd)).continuousOn)
    · intro x u hu hx
      apply mul_eq_zero_of_right
      apply image_eq_zero_of_notMem_tsupport
      intro h
      have hh := hs h
      exact hx ⟨by linarith [hu.1, hh.1], by linarith [hu.2, hh.2]⟩
  have hGi : Integrable (uncurry G) (volume.prod μ) := by
    apply integrable_on_carrying_rectangle (a := a) (c := b) hD
    · refine (hρ.comp (continuous_fst.add continuous_snd).continuousOn ?_).mul
        ((hφ.comp continuous_fst).continuousOn)
      rintro ⟨x, u⟩ ⟨hx, hu⟩
      exact add_pos_of_pos_of_nonneg (ha.trans_le hx.1) hu.1
    · intro x u _ hx
      exact mul_eq_zero_of_right _ (image_eq_zero_of_notMem_tsupport fun h ↦ hx (hs h))
  have hFx (x : ℝ) : (∫ u, F x u ∂μ) = ρ x * logTranslateAverage μ φ x := integral_const_mul _ _
  have hGx (x : ℝ) : (∫ u, G x u ∂μ) = (∫ u, ρ (x + u) ∂μ) * φ x := integral_mul_const _ _
  have hshift (u : ℝ) : (∫ x, F x u) = ∫ x, G x u := by
    rw [← integral_add_right_eq_self (fun x ↦ F x u) u]
    simp only [F, G, add_sub_cancel_right]
  refine ⟨hGi.integral_prod_left.congr (Eventually.of_forall hGx), ?_⟩
  calc
    _ = ∫ x, ∫ u, F x u ∂μ := integral_congr_ae (Eventually.of_forall fun x ↦ (hFx x).symm)
    _ = ∫ u, (∫ x, F x u) ∂μ := integral_integral_swap hFi
    _ = ∫ u, (∫ x, G x u) ∂μ := integral_congr_ae (Eventually.of_forall hshift)
    _ = ∫ x, ∫ u, G x u ∂μ := (integral_integral_swap hGi).symm
    _ = _ := integral_congr_ae (Eventually.of_forall hGx)

end Masullo
