module

public import Lemmas.FinitePickSpanTail
public import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.Analysis.PSeries
import Mathlib.MeasureTheory.Function.L2Space

/-! # Truncating prime correlations on a finite Pick span

Source: `bdd74f2a:.godel/adhoc/prime-translation-norm.md`, §4.
Consumer: `85842a8f:.godel/alice/prime-conductor-window.md`, “The same estimate
for whole right-hand blocks”.
Owning check session: `01a20e74-7a96-7653-9648-0eb1c4d5d43d`.

Scope: the autocorrelation bounds and the absolutely convergent prime-term
replacement for the whole zero-extended finite exponential span. There is no
asymptotic prime estimate or archimedean term.
-/

open MeasureTheory Set
open scoped ArithmeticFunction

namespace Masullo

/-- The squared Lebesgue `L²` norm of a complex-valued function on the real line. -/
@[expose] public noncomputable def pickL2Sq (h : ℝ → ℂ) : ℝ := ∫ x, ‖h x‖ ^ 2

/-- The autocorrelation of a complex-valued test on the real line. -/
@[expose] public noncomputable def pickAutocorrelation (h : ℝ → ℂ) (t : ℝ) : ℂ :=
  ∫ x, (starRingEnd ℂ) (h x) * h (x + t)

private noncomputable def shiftedPair (f g : ℝ → ℂ) (t : ℝ) : ℂ :=
  ∫ x, (starRingEnd ℂ) (f x) * g (x + t)

/-- The loss factor coming from the nodes of the whole span. -/
@[expose] public noncomputable def pickSpanProduct (S : Finset ℝ) (η : ℝ) : ℝ :=
  ∏ m ∈ S, (m + η) / (m - η)

private theorem pickL2Sq_nonneg (h : ℝ → ℂ) : 0 ≤ pickL2Sq h :=
  integral_nonneg fun _ ↦ sq_nonneg _

private theorem pickSpanProduct_nonneg {S : Finset ℝ} {η : ℝ} (hη : 0 ≤ η)
    (hS : ∀ m ∈ S, η < m) : 0 ≤ pickSpanProduct S η :=
  Finset.prod_nonneg fun m hm ↦ div_nonneg (add_nonneg (hη.trans (hS m hm).le) hη)
    (sub_nonneg.mpr (hS m hm).le)

private theorem memLp_finitePickSpan (S : Finset ℝ) (c : ℝ → ℂ)
    (hS : ∀ m ∈ S, 0 < m) : MemLp (finitePickSpan S c) 2 volume := by
  have hcont : Continuous (fun x : ℝ ↦ ∑ i ∈ S, c i * (Real.exp (-i * x) : ℂ)) :=
    continuous_finsetSum S fun i _ ↦ continuous_const.mul <|
      Complex.continuous_ofReal.comp (Real.continuous_exp.comp (continuous_const.mul continuous_id))
  have hm : StronglyMeasurable (finitePickSpan S c) :=
    hcont.stronglyMeasurable.indicator measurableSet_Ici
  exact (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mpr
    (integrable_finitePickSpan_sq S c hS)

private theorem memLp_translate {g : ℝ → ℂ} (hg : MemLp g 2 volume) (t : ℝ) :
    MemLp (fun x ↦ g (x + t)) 2 volume :=
  hg.comp_measurePreserving (measurePreserving_add_right volume t)

private theorem integrable_shiftedPair {f g : ℝ → ℂ} (hf : MemLp f 2 volume)
    (hg : MemLp g 2 volume) (t : ℝ) :
    Integrable (fun x ↦ (starRingEnd ℂ) (f x) * g (x + t)) :=
  hf.star.integrable_mul (memLp_translate hg t)

private theorem norm_shiftedPair_le {f g : ℝ → ℂ} (hf : MemLp f 2 volume)
    (hg : MemLp g 2 volume) (t : ℝ) :
    ‖shiftedPair f g t‖ ≤ Real.sqrt (pickL2Sq f) * Real.sqrt (pickL2Sq g) := by
  have hp : ENNReal.ofReal (2 : ℝ) = 2 := ENNReal.ofReal_ofNat 2
  have hf' : MemLp f (ENNReal.ofReal (2 : ℝ)) volume := hp ▸ hf
  have hg' : MemLp (fun x ↦ g (x + t)) (ENNReal.ofReal (2 : ℝ)) volume :=
    hp ▸ memLp_translate hg t
  have h := integral_mul_norm_le_Lp_mul_Lq Real.HolderConjugate.two_two hf' hg'
  calc
    _ ≤ ∫ x, ‖(starRingEnd ℂ) (f x) * g (x + t)‖ := norm_integral_le_integral_norm _
    _ = ∫ x, ‖f x‖ * ‖g (x + t)‖ := by simp only [norm_mul, Complex.norm_conj]
    _ ≤ _ := by
      simpa only [Real.rpow_two, ← Real.sqrt_eq_rpow, pickL2Sq,
        integral_add_right_eq_self (fun x ↦ ‖g x‖ ^ 2) t] using h

private theorem sqrt_pickL2Sq_tail_le (S : Finset ℝ) (c : ℝ → ℂ) {η t : ℝ}
    (hη : 0 < η) (hS : ∀ m ∈ S, η < m) (ht : 0 ≤ t) :
    Real.sqrt (pickL2Sq ((Ici t).indicator (finitePickSpan S c))) ≤
      (pickSpanProduct S η * Real.exp (-η * t)) * Real.sqrt (pickL2Sq (finitePickSpan S c)) := by
  let P := pickSpanProduct S η
  let E := pickL2Sq (finitePickSpan S c)
  let q := Real.exp (-η * t) * P
  have hq : 0 ≤ q := mul_nonneg (Real.exp_pos _).le (pickSpanProduct_nonneg hη.le hS)
  have hm : 0 ≤ min 1 q := le_min zero_le_one hq
  have hsq : pickL2Sq ((Ici t).indicator (finitePickSpan S c)) ≤ (min 1 q) ^ 2 * E :=
    finitePickSpan_tail_sq_le S c hη hS ht
  calc
    _ ≤ Real.sqrt ((min 1 q) ^ 2 * E) := Real.sqrt_le_sqrt hsq
    _ = min 1 q * Real.sqrt E := by rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hm]
    _ ≤ q * Real.sqrt E := mul_le_mul_of_nonneg_right (min_le_right _ _) (Real.sqrt_nonneg _)
    _ = _ := by
      change (Real.exp (-η * t) * P) * Real.sqrt E = (P * Real.exp (-η * t)) * Real.sqrt E
      rw [mul_comm (Real.exp (-η * t)) P]

private theorem finitePickSpan_eq_zero_of_neg (S : Finset ℝ) (c : ℝ → ℂ) {x : ℝ}
    (hx : x < 0) : finitePickSpan S c x = 0 := by
  simp [finitePickSpan, hx.not_ge]

/-- At a nonnegative shift (in particular `log n` for `n ≥ 2`), only the shifted
half-line tail can pair with the zero-extended span. -/
public theorem finitePickSpan_autocorrelation_tail_le (S : Finset ℝ) (c : ℝ → ℂ) {η t : ℝ}
    (hη : 0 < η) (hS : ∀ m ∈ S, η < m) (ht : 0 ≤ t) :
    ‖pickAutocorrelation (finitePickSpan S c) t‖ ≤
      pickL2Sq (finitePickSpan S c) * pickSpanProduct S η * Real.exp (-η * t) := by
  let h := finitePickSpan S c
  let w := (Ici t).indicator h
  have hh : MemLp h 2 volume := memLp_finitePickSpan S c fun m hm ↦ hη.trans (hS m hm)
  have hw : MemLp w 2 volume := hh.indicator measurableSet_Ici.nullMeasurableSet
  have heq : pickAutocorrelation h t = shiftedPair h w t := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun x ↦ ?_)
    change (starRingEnd ℂ) (h x) * h (x + t) = (starRingEnd ℂ) (h x) * w (x + t)
    by_cases hx : 0 ≤ x
    · rw [show w (x + t) = h (x + t) from indicator_of_mem (by simpa using hx) _]
    · simp [h, finitePickSpan_eq_zero_of_neg S c (lt_of_not_ge hx)]
  calc
    _ = ‖shiftedPair h w t‖ := congrArg norm heq
    _ ≤ Real.sqrt (pickL2Sq h) * Real.sqrt (pickL2Sq w) := norm_shiftedPair_le hh hw t
    _ ≤ Real.sqrt (pickL2Sq h) *
        ((pickSpanProduct S η * Real.exp (-η * t)) * Real.sqrt (pickL2Sq h)) :=
      mul_le_mul_of_nonneg_left (sqrt_pickL2Sq_tail_le S c hη hS ht) (Real.sqrt_nonneg _)
    _ = Real.sqrt (pickL2Sq h) ^ 2 * pickSpanProduct S η * Real.exp (-η * t) := by ring
    _ = _ := by rw [Real.sq_sqrt (pickL2Sq_nonneg h)]

private theorem shiftedPair_autocorrelation_sub {h v : ℝ → ℂ} (hh : MemLp h 2 volume)
    (hv : MemLp v 2 volume) (t : ℝ) :
    pickAutocorrelation h t - pickAutocorrelation v t =
      shiftedPair (h - v) h t + shiftedPair v (h - v) t := by
  have hw := hh.sub hv
  unfold pickAutocorrelation shiftedPair
  rw [← integral_sub (integrable_shiftedPair hh hh t) (integrable_shiftedPair hv hv t),
    ← integral_add (integrable_shiftedPair hw hh t) (integrable_shiftedPair hv hw t)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x ↦ ?_)
  simp only [Pi.sub_apply, map_sub]
  ring

/-- Replacing both factors by the restriction to `[0,d]` costs at most
`2 P exp(-η d) ‖h‖₂²`, uniformly in the shift. -/
public theorem finitePickSpan_autocorrelation_truncate_le (S : Finset ℝ) (c : ℝ → ℂ)
    {η d : ℝ} (hη : 0 < η) (hS : ∀ m ∈ S, η < m) (hd : 0 ≤ d) (t : ℝ) :
    ‖pickAutocorrelation (finitePickSpan S c) t -
      pickAutocorrelation ((Icc 0 d).indicator (finitePickSpan S c)) t‖ ≤
      2 * pickL2Sq (finitePickSpan S c) * (pickSpanProduct S η * Real.exp (-η * d)) := by
  let h := finitePickSpan S c
  let v := (Icc 0 d).indicator h
  let w := (Ici d).indicator h
  let E := pickL2Sq h
  let F := pickSpanProduct S η * Real.exp (-η * d)
  have hh : MemLp h 2 volume := memLp_finitePickSpan S c fun m hm ↦ hη.trans (hS m hm)
  have hv : MemLp v 2 volume := hh.indicator measurableSet_Icc.nullMeasurableSet
  have hw : MemLp w 2 volume := hh.indicator measurableSet_Ici.nullMeasurableSet
  have hv_le : pickL2Sq v ≤ E := by
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ ↦ sq_nonneg _)
      ((memLp_two_iff_integrable_sq_norm hh.aestronglyMeasurable).1 hh) ?_
    refine Filter.Eventually.of_forall fun x ↦ ?_
    by_cases hx : x ∈ Icc 0 d <;> simp [v, hx]
  have hw_le : pickL2Sq (h - v) ≤ pickL2Sq w := by
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ ↦ sq_nonneg _)
      ((memLp_two_iff_integrable_sq_norm hw.aestronglyMeasurable).1 hw) ?_
    refine Filter.Eventually.of_forall fun x ↦ ?_
    by_cases hx : x ∈ Icc 0 d
    · simp [v, hx]
    · by_cases hx' : x < 0
      · simp [v, hx, h, finitePickSpan_eq_zero_of_neg S c hx']
      · have hxd : x ∈ Ici d := by
          exact le_of_lt (lt_of_not_ge (fun hxd ↦ hx ⟨le_of_not_gt hx', hxd⟩))
        simp [v, w, hx, hxd]
  have hv' := Real.sqrt_le_sqrt hv_le
  have hw' : Real.sqrt (pickL2Sq (h - v)) ≤ F * Real.sqrt E :=
    (Real.sqrt_le_sqrt hw_le).trans (sqrt_pickL2Sq_tail_le S c hη hS hd)
  change ‖pickAutocorrelation h t - pickAutocorrelation v t‖ ≤ 2 * E * F
  rw [shiftedPair_autocorrelation_sub hh hv t]
  calc
    _ ≤ ‖shiftedPair (h - v) h t‖ + ‖shiftedPair v (h - v) t‖ := norm_add_le _ _
    _ ≤ Real.sqrt (pickL2Sq (h - v)) * Real.sqrt E +
        Real.sqrt (pickL2Sq v) * Real.sqrt (pickL2Sq (h - v)) :=
      add_le_add (norm_shiftedPair_le (hh.sub hv) hh t) (norm_shiftedPair_le hv (hh.sub hv) t)
    _ ≤ (F * Real.sqrt E) * Real.sqrt E + Real.sqrt E * (F * Real.sqrt E) :=
      add_le_add (mul_le_mul_of_nonneg_right hw' (Real.sqrt_nonneg _))
        (mul_le_mul hv' hw' (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
    _ = 2 * Real.sqrt E ^ 2 * F := by ring
    _ = _ := by
      have he : 0 ≤ E := pickL2Sq_nonneg h
      rw [Real.sq_sqrt he]

private noncomputable def pickMangoldtRootWeight (n : ℕ) : ℝ := Λ n / Real.sqrt (n : ℝ)

/-- The `n`th complex prime term, with zero terms at `0` and `1`. -/
@[expose] public noncomputable def pickPrimeTerm (χ : ℕ → ℂ) (h : ℝ → ℂ) (n : ℕ) : ℂ :=
  if 2 ≤ n then χ n * ((Λ n / Real.sqrt (n : ℝ) : ℝ) : ℂ) *
    pickAutocorrelation h (Real.log (n : ℝ)) else 0

/-- The summable majorant `Λ(n)n^(-5/2)` indexed by `n ≥ 2`. -/
@[expose] public noncomputable def pickMangoldtTailWeight (n : ℕ) : ℝ :=
  if 2 ≤ n then Λ n * (n : ℝ) ^ (-(5 / 2) : ℝ) else 0

private theorem pickMangoldtRootWeight_nonneg (n : ℕ) : 0 ≤ pickMangoldtRootWeight n :=
  div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _)

private theorem pickMangoldtTailWeight_nonneg (n : ℕ) : 0 ≤ pickMangoldtTailWeight n := by
  unfold pickMangoldtTailWeight
  split
  · exact mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.rpow_nonneg (by positivity) _)
  · exact le_rfl

public theorem summable_pickMangoldtTailWeight : Summable pickMangoldtTailWeight := by
  have hp := Real.summable_nat_rpow.mpr (show (-(3 / 2) : ℝ) < -1 by norm_num)
  refine Summable.of_nonneg_of_le pickMangoldtTailWeight_nonneg (fun n ↦ ?_) hp
  by_cases hn : 2 ≤ n
  · have hn' : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
    rw [pickMangoldtTailWeight, ite_eq_left hn]
    calc
      _ ≤ (n : ℝ) * (n : ℝ) ^ (-(5 / 2) : ℝ) :=
        mul_le_mul_of_nonneg_right
          (ArithmeticFunction.vonMangoldt_le_log.trans (Real.log_le_self hn'.le))
          (Real.rpow_nonneg hn'.le _)
      _ = (n : ℝ) ^ (1 + -(5 / 2) : ℝ) := by rw [Real.rpow_add hn', Real.rpow_one]
      _ = _ := by norm_num
  · rw [pickMangoldtTailWeight, ite_eq_right hn]
    exact Real.rpow_nonneg (by positivity) _

private theorem pickPrimeCoefficient_mul_norm_le {χ : ℕ → ℂ} {n : ℕ}
    (hχ : ‖χ n‖ ≤ 1) (z : ℂ) :
    ‖χ n * (pickMangoldtRootWeight n : ℂ) * z‖ ≤ pickMangoldtRootWeight n * ‖z‖ := by
  rw [norm_mul, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (pickMangoldtRootWeight_nonneg n)]
  exact mul_le_mul_of_nonneg_right
    (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hχ (pickMangoldtRootWeight_nonneg n))
    (norm_nonneg _)

private theorem pickPrimeWeight_decay {P η d : ℝ} (hP : 0 ≤ P) (hη : 2 < η)
    {n : ℕ} (hn : 2 ≤ n) (hdn : d ≤ Real.log (n : ℝ)) :
    pickMangoldtRootWeight n * (P * Real.exp (-η * Real.log (n : ℝ))) ≤
      (P * Real.exp (-(η - 2) * d)) * pickMangoldtTailWeight n := by
  have hn' : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have htwo : Real.exp (-(2 : ℝ) * Real.log (n : ℝ)) = (n : ℝ) ^ (-2 : ℝ) := by
    rw [Real.rpow_def_of_pos hn', mul_comm]
  have hweight : pickMangoldtRootWeight n * Real.exp (-(2 : ℝ) * Real.log (n : ℝ)) =
      pickMangoldtTailWeight n := by
    rw [pickMangoldtRootWeight, pickMangoldtTailWeight, ite_eq_left hn, htwo, Real.sqrt_eq_rpow,
      div_eq_mul_inv, ← Real.rpow_neg hn'.le, mul_assoc, ← Real.rpow_add hn']
    norm_num
  have hsplit : -η * Real.log (n : ℝ) =
      -(η - 2) * Real.log (n : ℝ) + -2 * Real.log (n : ℝ) := by ring
  have hdec : Real.exp (-(η - 2) * Real.log (n : ℝ)) ≤ Real.exp (-(η - 2) * d) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left hdn (by linarith))
  calc
    _ = (P * Real.exp (-(η - 2) * Real.log (n : ℝ))) * pickMangoldtTailWeight n := by
      rw [hsplit, Real.exp_add, ← hweight]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hdec hP)
      (pickMangoldtTailWeight_nonneg n)

/-- Absolute convergence and the prime-term truncation estimate on the whole
finite Pick span. `Ico 2 ⌈exp d⌉₊` retains exactly `2 ≤ n < exp d`, so equality
at the cutoff is assigned to the omitted terms. -/
public theorem finitePickSpan_prime_truncation_le (S : Finset ℝ) (c : ℝ → ℂ) (χ : ℕ → ℂ)
    {η d : ℝ} (hη : 2 < η) (hS : ∀ m ∈ S, η < m) (hd : 0 ≤ d)
    (hχ : ∀ n : ℕ, 2 ≤ n → ‖χ n‖ ≤ 1) :
    let h := finitePickSpan S c
    let v := (Icc 0 d).indicator h
    let E := pickL2Sq h
    let P := pickSpanProduct S η
    let F := P * Real.exp (-η * d)
    let s := Finset.Ico 2 ⌈Real.exp d⌉₊
    Summable (fun n ↦ ‖pickPrimeTerm χ h n‖) ∧
      |2 * (∑' n, pickPrimeTerm χ h n).re - 2 * (∑ n ∈ s, pickPrimeTerm χ v n).re| ≤
        2 * E * (2 * F * (∑ n ∈ s, Λ n / Real.sqrt (n : ℝ)) +
          P * Real.exp (-(η - 2) * d) * ∑' n, pickMangoldtTailWeight n) := by
  dsimp only
  let h := finitePickSpan S c
  let v := (Icc 0 d).indicator h
  let E := pickL2Sq h
  let P := pickSpanProduct S η
  let F := P * Real.exp (-η * d)
  let K := P * Real.exp (-(η - 2) * d)
  let s := Finset.Ico 2 ⌈Real.exp d⌉₊
  let a := pickPrimeTerm χ h
  let b (n : ℕ) := if n ∈ s then pickPrimeTerm χ v n else 0
  let m (n : ℕ) := if n ∈ s then 2 * F * pickMangoldtRootWeight n else 0
  let q := pickMangoldtTailWeight
  have hη' : 0 < η := by linarith
  have hE : 0 ≤ E := pickL2Sq_nonneg h
  have hP : 0 ≤ P := pickSpanProduct_nonneg hη'.le hS
  have hK : 0 ≤ K := mul_nonneg hP (Real.exp_pos _).le
  have hmem (n : ℕ) : n ∈ s ↔ 2 ≤ n ∧ (n : ℝ) < Real.exp d :=
    Finset.mem_Ico.trans (and_congr_right fun _ ↦ Nat.lt_ceil)
  have hle (n : ℕ) : ‖a n - b n‖ ≤ E * (m n + K * q n) := by
    by_cases hsn : n ∈ s
    · have hn := ((hmem n).1 hsn).1
      calc
        _ = ‖χ n * (pickMangoldtRootWeight n : ℂ) *
            (pickAutocorrelation h (Real.log (n : ℝ)) -
              pickAutocorrelation v (Real.log (n : ℝ)))‖ := by
          simp only [a, b, ite_eq_left hsn, pickPrimeTerm, ite_eq_left hn, pickMangoldtRootWeight, mul_sub]
        _ ≤ pickMangoldtRootWeight n * ‖pickAutocorrelation h (Real.log (n : ℝ)) -
            pickAutocorrelation v (Real.log (n : ℝ))‖ := pickPrimeCoefficient_mul_norm_le (hχ n hn) _
        _ ≤ pickMangoldtRootWeight n * (2 * E * F) :=
          mul_le_mul_of_nonneg_left
            (finitePickSpan_autocorrelation_truncate_le S c hη' hS hd _) (pickMangoldtRootWeight_nonneg n)
        _ = E * m n := by simp only [m, ite_eq_left hsn]; ring
        _ ≤ _ := mul_le_mul_of_nonneg_left
          (le_add_of_nonneg_right (mul_nonneg hK (pickMangoldtTailWeight_nonneg n))) hE
    · by_cases hn : 2 ≤ n
      · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
        have hdn : d ≤ Real.log (n : ℝ) := (Real.le_log_iff_exp_le (by linarith)).2 <|
          le_of_not_gt fun hh ↦ hsn ((hmem n).2 ⟨hn, hh⟩)
        calc
          _ = ‖χ n * (pickMangoldtRootWeight n : ℂ) *
              pickAutocorrelation h (Real.log (n : ℝ))‖ := by
            simp only [a, b, ite_eq_right hsn, sub_zero, pickPrimeTerm, ite_eq_left hn, pickMangoldtRootWeight]
          _ ≤ pickMangoldtRootWeight n * ‖pickAutocorrelation h (Real.log (n : ℝ))‖ :=
            pickPrimeCoefficient_mul_norm_le (hχ n hn) _
          _ ≤ pickMangoldtRootWeight n * (E * P * Real.exp (-η * Real.log (n : ℝ))) :=
            mul_le_mul_of_nonneg_left
              (finitePickSpan_autocorrelation_tail_le S c hη' hS (Real.log_nonneg hn1))
              (pickMangoldtRootWeight_nonneg n)
          _ = E * (pickMangoldtRootWeight n * (P * Real.exp (-η * Real.log (n : ℝ)))) := by ring
          _ ≤ E * (K * q n) := mul_le_mul_of_nonneg_left (pickPrimeWeight_decay hP hη hn hdn) hE
          _ = _ := by simp only [m, ite_eq_right hsn, zero_add]
      · simp only [a, b, m, q, pickPrimeTerm, pickMangoldtTailWeight, ite_eq_right hsn, ite_eq_right hn,
          sub_zero, norm_zero, mul_zero, add_zero, le_refl]
  have hm0 (n : ℕ) (hn : n ∉ s) : m n = 0 := ite_eq_right hn
  have hb0 (n : ℕ) (hn : n ∉ s) : b n = 0 := ite_eq_right hn
  have hm : Summable m := summable_of_ne_finset_zero hm0
  have hb : Summable b := summable_of_ne_finset_zero hb0
  have hq : Summable q := summable_pickMangoldtTailWeight
  have hg : Summable (fun n ↦ m n + K * q n) := hm.add (hq.mul_left K)
  have hg' := hg.mul_left E
  have herr : Summable (fun n ↦ ‖a n - b n‖) :=
    Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) hle hg'
  have hab : Summable (fun n ↦ a n - b n) := herr.of_norm_bounded (fun _ ↦ le_rfl)
  have ha : Summable a := by simpa only [sub_add_cancel] using hab.add hb
  have hbsum : (∑' n, b n) = ∑ n ∈ s, pickPrimeTerm χ v n := by
    rw [tsum_eq_sum hb0]
    exact Finset.sum_congr rfl fun n hn ↦ ite_eq_left hn
  have hmsum : (∑' n, m n) = 2 * F * ∑ n ∈ s, pickMangoldtRootWeight n := by
    rw [tsum_eq_sum hm0, Finset.mul_sum]
    exact Finset.sum_congr rfl fun n hn ↦ ite_eq_left hn
  have hnorm : ‖(∑' n, a n) - ∑ n ∈ s, pickPrimeTerm χ v n‖ ≤
      E * (2 * F * (∑ n ∈ s, pickMangoldtRootWeight n) + K * ∑' n, q n) := by
    rw [← hbsum, ← ha.tsum_sub hb]
    calc
      _ ≤ ∑' n, ‖a n - b n‖ := norm_tsum_le_tsum_norm herr
      _ ≤ ∑' n, E * (m n + K * q n) := herr.tsum_le_tsum hle hg'
      _ = _ := by rw [hg.tsum_mul_left, hm.tsum_add (hq.mul_left K), hmsum, hq.tsum_mul_left]
  refine ⟨ha.norm, ?_⟩
  change |2 * (∑' n, a n).re - 2 * (∑ n ∈ s, pickPrimeTerm χ v n).re| ≤
    2 * E * (2 * F * (∑ n ∈ s, pickMangoldtRootWeight n) + K * ∑' n, q n)
  rw [← mul_sub, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), mul_assoc, ← Complex.sub_re]
  exact mul_le_mul_of_nonneg_left ((Complex.abs_re_le_norm _).trans hnorm) (by norm_num)

end Masullo
