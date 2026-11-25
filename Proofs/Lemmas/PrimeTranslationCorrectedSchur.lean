module

public import Lemmas.PrimeTranslationProfileApproximation

/-! # Corrected Schur bound for finite prime translations

Sources: `309f4808a753:.godel/conjectures/closed/unsigned-edge-rh-row-bound.md`,
lines 85–102, and `5f22f5a60aef:.godel/bob/unsigned-edge-rh.md`, lines 36–52.
Owning check session: `01a2102d-ae00-70d1-a793-4b136b9edf79`.

Scope: transfer the three separate window rows to the absolute correlation bound
with coefficient `exp (D / 2) + D + C1`, where `C1 = max 0 (C0 + c * Ct)` suffices
independently of `D`. The arithmetic estimates supplying the rows under RH are not
proved or assumed to follow from RH here. The all-real error profile in the source
can be used to form `r`; the translated input is its zero extension from `[0,D]`.
-/

open MeasureTheory
open Real (exp log sqrt)
open scoped ArithmeticFunction.vonMangoldt

namespace Masullo

/-- The sum of the two endpoint profiles, zero off `[0,D]`. -/
@[expose] public noncomputable def primeTranslationEndpointWeight (D x : ℝ) : ℝ :=
  primeTranslationProfile D x + primeTranslationReflectedProfile D x

/-- The corrected weight is `w + (r + c) / exp (D / 2)` on `[0,D]`, with both
correction terms and the endpoint weight zero-extended off the window. -/
@[expose] public noncomputable def primeTranslationCorrectedWeight (D c : ℝ)
    (r : ℝ → ℝ) (x : ℝ) : ℝ :=
  primeTranslationEndpointWeight D x +
    ((Set.Icc 0 D).indicator r x + c * (Set.Icc 0 D).indicator (fun _ ↦ 1) x) / exp (D / 2)

private theorem endpointWeight_on {D x : ℝ} (hx : x ∈ Set.Icc 0 D) :
    primeTranslationEndpointWeight D x = exp (-x / 2) + exp (-(D - x) / 2) := by
  have hy : D - x ∈ Set.Icc 0 D := ⟨sub_nonneg.mpr hx.2, sub_le_self _ hx.1⟩
  simp only [primeTranslationEndpointWeight, primeTranslationReflectedProfile,
    primeTranslationProfile, Set.indicator_of_mem hx, Set.indicator_of_mem hy]

private theorem correctedWeight_on {D c x : ℝ} {r : ℝ → ℝ} (hx : x ∈ Set.Icc 0 D) :
    primeTranslationCorrectedWeight D c r x =
      primeTranslationEndpointWeight D x + (r x + c) / exp (D / 2) := by
  simp only [primeTranslationCorrectedWeight, Set.indicator_of_mem hx, mul_one]

private theorem correctedWeight_off {D c x : ℝ} {r : ℝ → ℝ} (hx : x ∉ Set.Icc 0 D) :
    primeTranslationCorrectedWeight D c r x = 0 := by
  have hy : D - x ∉ Set.Icc 0 D := fun h ↦ hx ⟨by linarith [h.2], sub_nonneg.mp h.1⟩
  simp only [primeTranslationCorrectedWeight, primeTranslationEndpointWeight,
    primeTranslationReflectedProfile, primeTranslationProfile, Set.indicator_of_notMem hx,
    Set.indicator_of_notMem hy, mul_zero, add_zero, zero_div]

private theorem correctedWeight_measurable (D c : ℝ) {r : ℝ → ℝ} (hr : Measurable r) :
    Measurable (primeTranslationCorrectedWeight D c r) := by
  have hf : Measurable (primeTranslationProfile D) :=
    (by fun_prop : Measurable (fun x : ℝ ↦ exp (-x / 2))).indicator measurableSet_Icc
  have hg : Measurable (primeTranslationReflectedProfile D) :=
    hf.comp (by fun_prop : Measurable (fun x : ℝ ↦ D - x))
  have h₁ : Measurable ((Set.Icc 0 D).indicator (fun _ ↦ (1 : ℝ))) :=
    measurable_const.indicator measurableSet_Icc
  exact (hf.add hg).add
    (((hr.indicator measurableSet_Icc).add (measurable_const.mul h₁)).div_const _)

private theorem apply_correctedWeight (D c : ℝ) (r : ℝ → ℝ) (x : ℝ) :
    primeTranslationApply D (primeTranslationCorrectedWeight D c r) x =
      primeTranslationApply D (primeTranslationEndpointWeight D) x +
        (primeTranslationApply D ((Set.Icc 0 D).indicator r) x +
          c * primeTranslationApply D ((Set.Icc 0 D).indicator (fun _ ↦ 1)) x) / exp (D / 2) := by
  unfold primeTranslationApply
  rw [Finset.mul_sum, ← Finset.sum_add_distrib, Finset.sum_div, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun n _ ↦ ?_
  unfold primeTranslationCorrectedWeight
  ring

/-- The three concrete rows at a point in the window imply the corrected row there. -/
public theorem primeTranslationCorrectedRow {D C0 c Ct C1 x : ℝ} {r : ℝ → ℝ}
    (hD : 0 ≤ D) (hc : 0 ≤ c) (hC1 : max 0 (C0 + c * Ct) ≤ C1)
    (hx : x ∈ Set.Icc 0 D) (hr : 0 ≤ r x)
    (hwrow : primeTranslationApply D (primeTranslationEndpointWeight D) x ≤
      (exp (D / 2) + D + C0) * primeTranslationEndpointWeight D x + r x)
    (hrrow : primeTranslationApply D ((Set.Icc 0 D).indicator r) x ≤ c * exp (D / 2))
    (h1row : primeTranslationApply D ((Set.Icc 0 D).indicator (fun _ ↦ 1)) x ≤
      Ct * exp (D / 2) * primeTranslationEndpointWeight D x) :
    primeTranslationApply D (primeTranslationCorrectedWeight D c r) x ≤
      (exp (D / 2) + D + C1) * primeTranslationCorrectedWeight D c r x := by
  let E := exp (D / 2)
  let w := primeTranslationEndpointWeight D x
  have hE : 0 < E := Real.exp_pos _
  have hw : 0 ≤ w := by
    dsimp only [w]
    rw [endpointWeight_on hx]
    positivity
  have hcoef : E + D + C0 + c * Ct ≤ E + D + C1 := by
    linarith [(le_max_right 0 (C0 + c * Ct)).trans hC1]
  have hM : E ≤ E + D + C1 := by
    linarith [(le_max_left 0 (C0 + c * Ct)).trans hC1]
  rw [apply_correctedWeight]
  calc
    _ ≤ ((E + D + C0) * w + r x) + (c * E + c * (Ct * E * w)) / E :=
      add_le_add hwrow (div_le_div_of_nonneg_right
        (add_le_add hrrow (mul_le_mul_of_nonneg_left h1row hc)) hE.le)
    _ = (E + D + C0 + c * Ct) * w + (r x + c) := by field_simp [hE.ne']; ring
    _ ≤ (E + D + C1) * w + (E + D + C1) * ((r x + c) / E) := by
      refine add_le_add (mul_le_mul_of_nonneg_right hcoef hw) ?_
      calc
        r x + c = E * ((r x + c) / E) := (mul_div_cancel₀ _ hE.ne').symm
        _ ≤ _ := mul_le_mul_of_nonneg_right hM (div_nonneg (add_nonneg hr hc) hE.le)
    _ = _ := by rw [correctedWeight_on hx, mul_add]

/-- The corrected Schur estimate for every complex `L²` input supported almost
everywhere on `[0,D]`. Both translated directions have weight `Λ n / sqrt n`;
`Nat.lt_ceil` gives the strict upper cutoff `n < exp D`. -/
public theorem primeTranslationCorrectedSchur {D C0 c Ct C1 R : ℝ} {r : ℝ → ℝ}
    (hD : 0 ≤ D) (hc : 0 ≤ c) (hC1 : max 0 (C0 + c * Ct) ≤ C1)
    (hr : Measurable r) (hrnonneg : ∀ x ∈ Set.Icc 0 D, 0 ≤ r x)
    (hrbound : ∀ x ∈ Set.Icc 0 D, r x ≤ R)
    (hwrow : ∀ x ∈ Set.Icc 0 D, primeTranslationApply D (primeTranslationEndpointWeight D) x ≤
      (exp (D / 2) + D + C0) * primeTranslationEndpointWeight D x + r x)
    (hrrow : ∀ x ∈ Set.Icc 0 D,
      primeTranslationApply D ((Set.Icc 0 D).indicator r) x ≤ c * exp (D / 2))
    (h1row : ∀ x ∈ Set.Icc 0 D,
      primeTranslationApply D ((Set.Icc 0 D).indicator (fun _ ↦ 1)) x ≤
        Ct * exp (D / 2) * primeTranslationEndpointWeight D x)
    {u : ℝ → ℂ} (hu : MemLp u 2 volume)
    (huzero : ∀ᵐ x ∂volume, x ∉ Set.Icc 0 D → u x = 0) :
    2 * (∑ n ∈ Finset.Ico 1 ⌈exp D⌉₊, Λ n / sqrt n *
      ∫ x : ℝ, ‖u x‖ * ‖u (x + log n)‖) ≤
      (exp (D / 2) + D + C1) * ∫ x : ℝ, ‖u x‖ ^ 2 := by
  let E := exp (D / 2)
  have hE : 0 < E := Real.exp_pos _
  have hrow : ∀ᵐ x ∂volume.restrict (Set.Icc 0 D),
      primeTranslationApply D (primeTranslationCorrectedWeight D c r) x ≤
        (E + D + C1) * primeTranslationCorrectedWeight D c r x :=
    (ae_restrict_iff' measurableSet_Icc).2 <| ae_of_all _ fun x hx ↦
      primeTranslationCorrectedRow hD hc hC1 hx (hrnonneg x hx)
        (hwrow x hx) (hrrow x hx) (h1row x hx)
  refine finiteShiftSchur (b := exp (-D / 2)) (B := 2 + (R + c) / E) _
    (fun n : ℕ ↦ log n) (fun n ↦ Λ n / sqrt n)
    (fun _ _ ↦ div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _))
    measurableSet_Icc (correctedWeight_measurable D c hr) (fun _ ↦ correctedWeight_off)
    (Real.exp_pos _) ?_ ?_ hrow hu huzero
  · intro x hx
    rw [correctedWeight_on hx, endpointWeight_on hx]
    have hleft : exp (-D / 2) ≤ exp (-x / 2) := Real.exp_le_exp.mpr (by linarith [hx.2])
    exact (hleft.trans (le_add_of_nonneg_right (Real.exp_pos _).le)).trans
      (le_add_of_nonneg_right (div_nonneg (add_nonneg (hrnonneg x hx) hc) hE.le))
  · intro x hx
    rw [correctedWeight_on hx, endpointWeight_on hx]
    have ha : exp (-x / 2) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith [hx.1])
    have hb : exp (-(D - x) / 2) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith [hx.2])
    have hrc : (r x + c) / E ≤ (R + c) / E :=
      div_le_div_of_nonneg_right (add_le_add_left (hrbound x hx) c) hE.le
    change exp (-x / 2) + exp (-(D - x) / 2) + (r x + c) / E ≤ 2 + (R + c) / E
    linarith

end Masullo
