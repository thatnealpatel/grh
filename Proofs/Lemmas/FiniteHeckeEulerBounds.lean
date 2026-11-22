module

public import Lemmas.FiniteHeckeMajorant
public import Mathlib.Analysis.Calculus.LogDerivUniformlyOn
import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.Ring

/-! Bounds for finite Euler factors on closed right half-planes. -/

open Complex Filter IsDedekindDomain NumberField

namespace Masullo

variable {K : Type*} [Field K] [NumberField K]
local notation "Places" => HeightOneSpectrum (𝓞 K)

/-- The monomial subtracted in the finite Euler denominator. -/
@[expose] public noncomputable def finiteHeckeMonomial (z : Places → ℂ) (v : Places) (s : ℂ) : ℂ :=
  z v * exp (-s * (Real.log (finitePlaceNorm v) : ℂ))

/-- The finite Euler factor, equal to one at an omitted place (`z v = 0`). -/
@[expose] public noncomputable def finiteHeckeEulerFactor (z : Places → ℂ) (v : Places) (s : ℂ) : ℂ :=
  (1 - finiteHeckeMonomial z v s)⁻¹

private theorem log_pos_finitePlaceNorm (v : Places) : 0 < Real.log (finitePlaceNorm v) :=
  Real.log_pos ((by norm_num : (1 : ℝ) < 2).trans_le (two_le_finitePlaceNorm v))

private theorem norm_finiteHeckeMonomial_le {z : Places → ℂ} {v : Places} {a : ℝ} {s : ℂ}
    (hz : ‖z v‖ ≤ 1) (hs : a ≤ s.re) :
    ‖finiteHeckeMonomial z v s‖ ≤ Real.exp (-a * Real.log (finitePlaceNorm v)) := by
  rw [finiteHeckeMonomial, norm_mul, Complex.norm_exp]
  simp only [mul_re, neg_re, neg_im, ofReal_re, ofReal_im, mul_zero, sub_zero]
  simpa only [one_mul] using mul_le_mul hz (Real.exp_le_exp.mpr (by
    exact mul_le_mul_of_nonneg_right (neg_le_neg hs) (log_pos_finitePlaceNorm v).le))
    (Real.exp_nonneg _) zero_le_one

public theorem norm_finiteHeckeMonomial_lt_one {z : Places → ℂ} {v : Places} {s : ℂ}
    (hz : ‖z v‖ ≤ 1) (hs : 0 < s.re) : ‖finiteHeckeMonomial z v s‖ < 1 :=
  (norm_finiteHeckeMonomial_le hz le_rfl).trans_lt
    (Real.exp_lt_one_iff.mpr (mul_neg_of_neg_of_pos (neg_neg_of_pos hs) (log_pos_finitePlaceNorm v)))

public theorem finiteHecke_denom_ne_zero {z : Places → ℂ} {v : Places} {s : ℂ}
    (hz : ‖z v‖ ≤ 1) (hs : 0 < s.re) : 1 - finiteHeckeMonomial z v s ≠ 0 := by
  intro h
  simpa [(sub_eq_zero.mp h).symm] using norm_finiteHeckeMonomial_lt_one hz hs

public theorem hasDerivAt_finiteHeckeMonomial (z : Places → ℂ) (v : Places) (s : ℂ) :
    HasDerivAt (finiteHeckeMonomial z v)
      (-(Real.log (finitePlaceNorm v) : ℂ) * finiteHeckeMonomial z v s) s := by
  let l : ℂ := Real.log (finitePlaceNorm v)
  have h := (((hasDerivAt_id s).neg.mul_const l).cexp).const_mul (z v)
  change HasDerivAt (fun t ↦ z v * exp (-t * l)) (-l * (z v * exp (-s * l))) s
  convert h using 1
  · funext t
    simp [Pi.neg_apply, mul_comm t l]
  · simp only [Pi.neg_apply, id_eq, neg_mul, one_mul]
    ring

private noncomputable def eulerPerturbation (z : Places → ℂ) (v : Places) (s : ℂ) : ℂ :=
  finiteHeckeMonomial z v s / (1 - finiteHeckeMonomial z v s)

private theorem eulerFactor_eq_one_add {z : Places → ℂ} {v : Places} {s : ℂ}
    (hz : ‖z v‖ ≤ 1) (hs : 0 < s.re) :
    finiteHeckeEulerFactor z v s = 1 + eulerPerturbation z v s := by
  unfold finiteHeckeEulerFactor eulerPerturbation
  field_simp [finiteHecke_denom_ne_zero hz hs]
  ring

private theorem summable_eulerBound {a : ℝ} (ha : 1 < a) :
    Summable (fun v : Places ↦ 2 * Real.exp (-a * Real.log (finitePlaceNorm v))) := by
  have h := (summable_finitePlace_log_powers (K := K) ha).comp_injective
    (show Function.Injective (fun v : Places ↦ (v, (0 : ℕ))) from fun _ _ h ↦ congrArg Prod.fst h)
  refine (h.mul_left (2 / Real.log 2)).of_nonneg_of_le (fun _ ↦ by positivity) fun v ↦ ?_
  have hq := two_le_finitePlaceNorm v
  have hq0 : 0 < finitePlaceNorm v := (by norm_num : (0 : ℝ) < 2).trans_le hq
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hll := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hq
  let q := finitePlaceNorm v
  change 2 * Real.exp (-a * Real.log q) ≤ (2 / Real.log 2) *
    (Real.log q / q ^ (a * ((0 : ℕ) + 1 : ℝ)))
  simp only [Nat.cast_zero, zero_add, mul_one]
  rw [Real.rpow_def_of_pos (show 0 < q from hq0), div_eq_mul_inv (Real.log q), ← Real.exp_neg,
    mul_comm (Real.log q) a, ← neg_mul, ← mul_assoc]
  apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
  calc
    (2 : ℝ) = (2 / Real.log 2) * Real.log 2 := (div_mul_cancel₀ _ hlog.ne').symm
    _ ≤ _ := mul_le_mul_of_nonneg_left hll (by positivity)

private theorem norm_eulerPerturbation_le {a : ℝ} (ha : 1 ≤ a) {z : Places → ℂ}
    {v : Places} {s : ℂ} (hz : ‖z v‖ ≤ 1) (hs : a ≤ s.re) :
    ‖eulerPerturbation z v s‖ ≤ 2 * Real.exp (-a * Real.log (finitePlaceNorm v)) := by
  let q := finitePlaceNorm v
  have hw := norm_finiteHeckeMonomial_le hz hs
  have hhalf : Real.exp (-a * Real.log q) ≤ 1 / 2 := by
    rw [one_div, ← Real.exp_log (by norm_num : (0 : ℝ) < 2), ← Real.exp_neg]
    apply Real.exp_le_exp.mpr
    have hll := Real.log_le_log (by norm_num : (0 : ℝ) < 2) (two_le_finitePlaceNorm v)
    calc
      -a * Real.log q ≤ -(1 : ℝ) * Real.log q := mul_le_mul_of_nonneg_right (neg_le_neg ha) (log_pos_finitePlaceNorm v).le
      _ ≤ -Real.log 2 := by linarith
  have hb := norm_sub_norm_le (1 : ℂ) (finiteHeckeMonomial z v s)
  rw [norm_one] at hb
  have hden : 1 / 2 ≤ ‖1 - finiteHeckeMonomial z v s‖ := by linarith [hw.trans hhalf]
  have hd0 : 0 < ‖1 - finiteHeckeMonomial z v s‖ := by linarith
  rw [eulerPerturbation, norm_div, div_le_iff₀ hd0]
  refine hw.trans ?_
  calc
    Real.exp (-a * Real.log q) = (2 * Real.exp (-a * Real.log q)) * (1 / 2) := by ring
    _ ≤ _ := by gcongr

private theorem differentiableAt_eulerPerturbation {z : Places → ℂ} {v : Places} {s : ℂ}
    (hz : ‖z v‖ ≤ 1) (hs : 0 < s.re) : DifferentiableAt ℂ (eulerPerturbation z v) s := by
  have h := (hasDerivAt_finiteHeckeMonomial z v s).differentiableAt
  exact h.div ((differentiableAt_const (1 : ℂ)).sub h) (finiteHecke_denom_ne_zero hz hs)

/-- The all-place product converges uniformly on compact subsets of `Re s > 1`. -/
public theorem finiteHeckeEulerFactor_hasProdLocallyUniformlyOn {z : Places → ℂ}
    (hz : ∀ v, ‖z v‖ ≤ 1) :
    HasProdLocallyUniformlyOn (finiteHeckeEulerFactor z)
      (fun s ↦ ∏' v, finiteHeckeEulerFactor z v s) {s : ℂ | 1 < s.re} := by
  apply hasProdLocallyUniformlyOn_of_forall_compact (isOpen_lt continuous_const continuous_re)
  intro S hS hc
  rcases S.eq_empty_or_nonempty with h | h
  · rw [h, hasProdUniformlyOn_iff_tendstoUniformlyOn]
    exact tendstoUniformlyOn_empty
  obtain ⟨s₀, hs₀, hmin⟩ := hc.exists_isMinOn h continuous_re.continuousOn
  have ha : 1 < s₀.re := hS hs₀
  have hpos (s) (hs : s ∈ S) : 0 < s.re := zero_lt_one.trans (hS hs)
  have hp := (summable_eulerBound (K := K) ha).hasProdUniformlyOn_one_add
    (f := eulerPerturbation z) hc
    (.of_forall fun v s hs ↦ norm_eulerPerturbation_le ha.le (hz v) (hmin hs))
    (fun v s hs ↦ (differentiableAt_eulerPerturbation (hz v) (hpos s hs)).continuousAt.continuousWithinAt)
  have hprod (F : Finset Places) : S.EqOn (fun s ↦ ∏ v ∈ F, (1 + eulerPerturbation z v s))
      (fun s ↦ ∏ v ∈ F, finiteHeckeEulerFactor z v s) := by
    intro s hs
    simp only [eulerFactor_eq_one_add (hz _) (hpos s hs)]
  refine (hp.congr (.of_forall hprod)).congr_right ?_
  intro s hs
  simp only [eulerFactor_eq_one_add (hz _) (hpos s hs)]

public theorem finiteHeckeEulerProduct_ne_zero {z : Places → ℂ} (hz : ∀ v, ‖z v‖ ≤ 1)
    {s : ℂ} (hs : 1 < s.re) : (∏' v, finiteHeckeEulerFactor z v s) ≠ 0 := by
  simp only [eulerFactor_eq_one_add (hz _) (zero_lt_one.trans hs)]
  refine tprod_one_add_ne_zero_of_summable (fun v ↦ ?_) ?_
  · rw [← eulerFactor_eq_one_add (hz v) (zero_lt_one.trans hs)]
    exact inv_ne_zero (finiteHecke_denom_ne_zero (hz v) (zero_lt_one.trans hs))
  · exact (summable_eulerBound (K := K) hs).of_nonneg_of_le (fun _ ↦ norm_nonneg _)
      fun v ↦ norm_eulerPerturbation_le hs.le (hz v) le_rfl

end Masullo
