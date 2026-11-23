module

public import Lemmas.DetectorCoefficientDisk
public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.IteratedDeriv.Analytic
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Analytic cubic log remainder for the detector

Source: `78091476:.godel/bob/balanced-height-reconstruction.md:23–44`, especially
lines 25–30 and 34–40. Scope: the detector modules at `011d4c8f`.
Owning check session: `01a209f7-85a2-71df-a0cc-7987e51e67d1`.

On the activity ray `z ↦ z y`, the formal log coefficients of the actual
complex independence polynomial sum to the analytic branch normalized at zero.
For `θ = L B₀ < 1`, the disk `‖z‖ < 1/θ` contains the unit disk, and the tail
at `z = 1` after degrees 1–3 is bounded by `4 A L θ³ / (1 - θ)`, where `A`
is the full weight mass. This is uniform in the activities satisfying the
detector's weight and degree bounds. The first three formal log coefficients
also have the ordered conflict-sum form from the source. No saddle or contour
estimate is asserted.
-/

open scoped BigOperators Topology
open DetectorCoefficientDisk (complexIndependencePolynomial)
open SeparationQuadraticCost (independentSets startDistance)

namespace DetectorLogRemainder

private theorem eval_zero (starts : Finset ℕ) (R : ℝ) (y : ℕ → ℂ) :
    (complexIndependencePolynomial starts R y).eval 0 = 1 := by
  classical
  rw [← Polynomial.coeff_zero_eq_eval_zero, complexIndependencePolynomial,
    Polynomial.finsetSum_coeff, Finset.sum_eq_single_of_mem ∅ (by simp [independentSets])]
  · simp
  · intro I _ hI
    have hc : I.card ≠ 0 := by simpa using hI
    simp [Polynomial.coeff_monomial, hc]

-- The normalized Taylor coefficients, regarded as an ordinary formal power series.
private noncomputable def taylor (f : ℂ → ℂ) : PowerSeries ℂ :=
  PowerSeries.mk fun n ↦ iteratedDeriv n f 0 / (n.factorial : ℂ)

private theorem taylor_mul {f g : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0) :
    taylor (f * g) = taylor f * taylor g := by
  ext n
  simp only [taylor, PowerSeries.coeff_mk, PowerSeries.coeff_mul]
  rw [iteratedDeriv_mul hf.contDiffAt hg.contDiffAt,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun i k ↦ iteratedDeriv i f 0 / (i.factorial : ℂ) *
        (iteratedDeriv k g 0 / (k.factorial : ℂ))), Finset.sum_div]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  have hi' : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  have hfac : (n.choose i : ℂ) * (i.factorial : ℂ) * ((n - i).factorial : ℂ) = n.factorial := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hi'
  have hn : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
  have hi₀ : (i.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr i.factorial_ne_zero
  have hni : ((n - i).factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (n - i).factorial_ne_zero
  field_simp
  linear_combination (iteratedDeriv i f 0 * iteratedDeriv (n - i) g 0) * hfac

private theorem taylor_poly (p : Polynomial ℂ) : taylor p.eval = (p : PowerSeries ℂ) := by
  have hd (n : ℕ) (q : Polynomial ℂ) :
      iteratedDeriv n q.eval = ((⇑Polynomial.derivative)^[n] q).eval := by
    induction n generalizing q with
    | zero => rfl
    | succ n ih =>
      rw [iteratedDeriv_succ', Function.iterate_succ_apply, ← ih q.derivative]
      exact congrArg (iteratedDeriv n) (funext fun z ↦ (q.hasDerivAt z).deriv)
  ext n
  rw [taylor, PowerSeries.coeff_mk, Polynomial.coeff_coe, hd]
  change ((⇑Polynomial.derivative)^[n] p).eval 0 / (n.factorial : ℂ) = p.coeff n
  rw [← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_iterate_derivative]
  simp [nsmul_eq_mul, Nat.descFactorial_self, Nat.factorial_ne_zero]

private theorem taylor_deriv (f : ℂ → ℂ) :
    taylor (deriv f) = PowerSeries.derivative (taylor f) := by
  ext n
  simp only [taylor, PowerSeries.coeff_derivative, PowerSeries.coeff_mk, iteratedDeriv_succ',
    Nat.factorial_succ, Nat.cast_mul, Nat.cast_succ]
  have hn : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
  have hs : (n : ℂ) + 1 ≠ 0 := by exact_mod_cast n.succ_ne_zero
  field_simp

open PowerSeries in
private theorem derivative_logOf_mul (P : PowerSeries ℂ) (hP : constantCoeff P = 1) :
    derivative (logOf P) * P = derivative P := by
  have hs : HasSubst (P - 1) := HasSubst.of_constantCoeff_zero' (by simp [hP])
  have h := congrArg (fun f : PowerSeries ℂ ↦ f.subst (P - 1))
    (derivative_log_mul_one_add_X (A := ℂ))
  rw [subst_mul hs, subst_add hs, subst_X hs] at h
  simp only [← coe_substAlgHom hs, map_one, add_sub_cancel] at h
  rw [logOf_eq, derivative_subst hs, map_sub, Derivation.map_one_eq_zero, sub_zero,
    mul_comm _ (derivative P), mul_assoc, ← coe_substAlgHom hs, h, mul_one]

-- Match the series to the principal log only locally, at the point where `p(0) = 1`.
-- The derivative product and constant term identify the ordinary formal series.
private theorem taylor_clog_poly (p : Polynomial ℂ) (hp : p.eval 0 = 1) :
    taylor (Complex.log ∘ p.eval) = PowerSeries.logOf (p : PowerSeries ℂ) := by
  let f := Complex.log ∘ p.eval
  have h₀ : PowerSeries.constantCoeff (p : PowerSeries ℂ) = 1 := by
    rwa [Polynomial.constantCoeff_coe, Polynomial.coeff_zero_eq_eval_zero]
  have hslit : p.eval 0 ∈ Complex.slitPlane := hp ▸ Complex.one_mem_slitPlane
  have hpa : AnalyticAt ℂ p.eval 0 := p.differentiable.analyticAt _
  have hf : AnalyticAt ℂ f 0 := AnalyticAt.comp (f := p.eval) (x := 0) (analyticAt_clog hslit) hpa
  have he : deriv f * p.eval =ᶠ[𝓝 0] p.derivative.eval := by
    have hc : ContinuousAt p.eval (0 : ℂ) := p.differentiable.continuous.continuousAt
    filter_upwards [hc.preimage_mem_nhds (Complex.isOpen_slitPlane.mem_nhds hslit)] with z hz
    have hz' : p.eval z ∈ Complex.slitPlane := hz
    have hd := ((Complex.hasDerivAt_log hz').comp z (p.hasDerivAt z)).deriv
    change deriv f z * p.eval z = p.derivative.eval z
    rw [show deriv f z = _ from hd]
    rw [mul_comm, ← mul_assoc, mul_inv_cancel₀ (Complex.slitPlane_ne_zero hz'), one_mul]
  have hprod : taylor (deriv f * p.eval) = taylor p.derivative.eval := by
    ext n
    simp only [taylor, PowerSeries.coeff_mk, he.iteratedDeriv_eq n]
  rw [taylor_mul hf.deriv hpa, taylor_deriv, taylor_poly, taylor_poly,
    ← PowerSeries.derivative_coe] at hprod
  have hu : IsUnit (p : PowerSeries ℂ) := PowerSeries.isUnit_iff_constantCoeff.mpr (by simp [h₀])
  let _ : HasUniqueDiv ℂ := .of_module_rat ℂ
  apply PowerSeries.derivative.ext
  · exact hu.mul_right_cancel (hprod.trans (derivative_logOf_mul _ h₀).symm)
  · rw [PowerSeries.constantCoeff_logOf h₀]
    simp [taylor, hp, ← PowerSeries.coeff_zero_eq_constantCoeff_apply]

private theorem ofScalars_logOf_hasFPowerSeriesAt (p : Polynomial ℂ) (hp : p.eval 0 = 1) :
    HasFPowerSeriesAt (Complex.log ∘ p.eval)
      (FormalMultilinearSeries.ofScalars ℂ
        fun n ↦ PowerSeries.coeff n (PowerSeries.logOf (p : PowerSeries ℂ))) 0 := by
  have hslit : p.eval 0 ∈ Complex.slitPlane := hp ▸ Complex.one_mem_slitPlane
  have ha := AnalyticAt.comp (f := p.eval) (x := 0) (analyticAt_clog hslit)
    (p.differentiable.analyticAt (0 : ℂ))
  have he (n : ℕ) := congrArg (PowerSeries.coeff n : PowerSeries ℂ → ℂ) (taylor_clog_poly p hp)
  simp only [taylor, PowerSeries.coeff_mk] at he
  simpa only [← he] using ha.hasFPowerSeriesAt

-- A coefficient bound at positive degrees gives a radius bound even at the boundary:
-- the weighted norms are bounded there, without claiming convergence there.
private theorem le_radius_of_majorant {c : ℕ → ℂ} {M θ : ℝ} (hθ : 0 < θ) (hM : 0 ≤ M)
    (hc₀ : c 0 = 0) (hc : ∀ n, ‖c (n + 1)‖ ≤ M * θ ^ n) :
    ENNReal.ofReal (1 / θ) ≤ (FormalMultilinearSeries.ofScalars ℂ c).radius := by
  let r : NNReal := ⟨1 / θ, by positivity⟩
  rw [show ENNReal.ofReal (1 / θ) = (r : ENNReal) from
    ENNReal.ofReal_eq_coe_nnreal (one_div_nonneg.mpr hθ.le)]
  apply FormalMultilinearSeries.le_radius_of_bound _ (M / θ)
  intro n
  rw [FormalMultilinearSeries.ofScalars_norm]
  cases n with
  | zero => simpa [hc₀] using div_nonneg hM hθ.le
  | succ n =>
    calc
      _ ≤ (M * θ ^ n) * (1 / θ) ^ (n + 1) :=
        mul_le_mul_of_nonneg_right (hc n) (by positivity)
      _ = M / θ := by
        rw [pow_succ (1 / θ), ← mul_assoc, mul_assoc M, ← mul_pow, mul_one_div_cancel hθ.ne']
        simp only [one_pow, mul_one]
        exact (div_eq_mul_one_div _ _).symm

-- The local identity `exp (log (p z)) = p z` continues over the whole disk.
private theorem exp_ofScalarsSum_logOf_eqOn (p : Polynomial ℂ) (hp : p.eval 0 = 1) {r : ℝ}
    (hr : 0 < r)
    (hF : HasFPowerSeriesOnBall
      (FormalMultilinearSeries.ofScalarsSum
        (fun n ↦ PowerSeries.coeff n (PowerSeries.logOf (p : PowerSeries ℂ))))
      (FormalMultilinearSeries.ofScalars ℂ
        (fun n ↦ PowerSeries.coeff n (PowerSeries.logOf (p : PowerSeries ℂ))))
      0 (ENNReal.ofReal r)) :
    Set.EqOn (Complex.exp ∘ FormalMultilinearSeries.ofScalarsSum
        (fun n ↦ PowerSeries.coeff n (PowerSeries.logOf (p : PowerSeries ℂ))))
      p.eval (Metric.ball 0 r) := by
  let q := FormalMultilinearSeries.ofScalars ℂ
    (fun n ↦ PowerSeries.coeff n (PowerSeries.logOf (p : PowerSeries ℂ)))
  have hlocal : Complex.log ∘ p.eval =ᶠ[𝓝 0] q.sum := by
    obtain ⟨s, hs⟩ := ofScalars_logOf_hasFPowerSeriesAt p hp
    filter_upwards [Metric.eball_mem_nhds (x := (0 : ℂ)) hs.r_pos] with z hz
    simpa only [zero_add] using hs.sum hz
  have he : Complex.exp ∘ q.sum =ᶠ[𝓝 0] p.eval := by
    have hslit : p.eval 0 ∈ Complex.slitPlane := hp ▸ Complex.one_mem_slitPlane
    have hc : ContinuousAt p.eval (0 : ℂ) := p.differentiable.continuous.continuousAt
    filter_upwards [hlocal, hc.preimage_mem_nhds (Complex.isOpen_slitPlane.mem_nhds hslit)]
      with z hz hs
    change Complex.log (p.eval z) = q.sum z at hz
    change Complex.exp (q.sum z) = p.eval z
    exact hz ▸ Complex.exp_log (Complex.slitPlane_ne_zero hs)
  have ha : AnalyticOnNhd ℂ (Complex.exp ∘ q.sum) (Metric.ball 0 r) := by
    intro z hz
    exact AnalyticAt.comp (f := q.sum) (x := z) analyticAt_cexp
      (hF.analyticAt_of_mem (by rwa [Metric.eball_ofReal]))
  exact ha.eqOn_of_preconnected_of_eventuallyEq (fun z _ ↦ p.differentiable.analyticAt z)
    (convex_ball (0 : ℂ) r).isPreconnected (Metric.mem_ball_self hr) he

private theorem norm_cubic_tail_le {c : ℕ → ℂ} {M θ : ℝ} (hθ₀ : 0 ≤ θ) (hθ : θ < 1)
    (hc₀ : c 0 = 0) (hs : Summable c) (hc : ∀ n, ‖c (n + 1)‖ ≤ M * θ ^ n) :
    ‖(∑' n, c n) - (c 1 + c 2 + c 3)‖ ≤ M * θ ^ 3 / (1 - θ) := by
  have hsplit := hs.sum_add_tsum_nat_add 4
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_one, hc₀, zero_add] at hsplit
  rw [← hsplit, add_sub_cancel_left]
  have ht := ((summable_nat_add_iff 4).2 hs).hasSum
  refine ht.norm_le_of_bounded (by
    simpa only [div_eq_mul_inv] using (hasSum_geometric_of_lt_one hθ₀ hθ).mul_left (M * θ ^ 3)) ?_
  intro n
  calc
    ‖c (n + 4)‖ ≤ M * θ ^ (n + 3) := hc (n + 3)
    _ = (M * θ ^ 3) * θ ^ n := by rw [add_comm n, pow_add, mul_assoc]

/-- The normalized analytic log of the actual scaled detector on the disk
`‖z‖ < 1/(L B₀)`, with its uniform cubic remainder at `z = 1`.
The `HasFPowerSeriesOnBall` clause asserts convergence to this branch for the
actual formal log coefficients, not just the existence of some logarithm. -/
public theorem complex_analytic_log_cubic_remainder
    (starts : Finset ℕ) {R : ℝ} (hR : 0 ≤ R) (y : ℕ → ℂ) (w : ℕ → ℝ) (Δ : ℕ)
    {wStar B₀ L : ℝ}
    (hdeg : ∀ p ∈ starts, ((starts.erase p).filter (fun q ↦ startDistance p q ≤ R)).card ≤ Δ)
    (hy : ∀ p ∈ starts, ‖y p‖ ≤ L * w p) (hw : ∀ p ∈ starts, w p ≤ wStar)
    (hL : 0 < L) (hB₀ : 0 < B₀) (hscale : 8 * ((Δ : ℝ) + 1) * wStar ≤ B₀)
    (hθ : L * B₀ < 1) :
    let P := complexIndependencePolynomial starts R y
    let θ := L * B₀
    let A := ∑ p ∈ starts, w p
    let c (n : ℕ) := PowerSeries.coeff n (PowerSeries.logOf (P : PowerSeries ℂ))
    let F := FormalMultilinearSeries.ofScalarsSum c
    HasFPowerSeriesOnBall F (FormalMultilinearSeries.ofScalars ℂ c) 0 (ENNReal.ofReal (1 / θ)) ∧
      F 0 = 0 ∧
      Set.EqOn (Complex.exp ∘ F) P.eval (Metric.ball 0 (1 / θ)) ∧
      1 < 1 / θ ∧
      ‖F 1 - (c 1 + c 2 + c 3)‖ ≤ 4 * A * L * θ ^ 3 / (1 - θ) := by
  dsimp only
  let P := complexIndependencePolynomial starts R y
  let θ := L * B₀
  let M := 4 * (∑ p ∈ starts, w p) * L
  let c (n : ℕ) := PowerSeries.coeff n (PowerSeries.logOf (P : PowerSeries ℂ))
  let q := FormalMultilinearSeries.ofScalars ℂ c
  have hp : P.eval 0 = 1 := eval_zero starts R y
  have hp₀ : PowerSeries.constantCoeff (P : PowerSeries ℂ) = 1 := by
    rwa [Polynomial.constantCoeff_coe, Polynomial.coeff_zero_eq_eval_zero]
  have hc₀ : c 0 = 0 := by
    change PowerSeries.coeff 0 (PowerSeries.logOf (P : PowerSeries ℂ)) = 0
    rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.constantCoeff_logOf hp₀]
  have hθ₀ : 0 < θ := mul_pos hL hB₀
  have hM : 0 ≤ M := by
    have hA : 0 ≤ ∑ p ∈ starts, w p := Finset.sum_nonneg fun p hp ↦
      nonneg_of_mul_nonneg_right ((norm_nonneg _).trans (hy p hp)) hL
    dsimp [M]
    positivity
  have hc (n : ℕ) : ‖c (n + 1)‖ ≤ M * θ ^ n := by
    have hb := DetectorCoefficientDisk.norm_logCoeff_le starts hR y w Δ hdeg hy hw hL hB₀ hscale
      (n + 1) (by omega)
    change ‖c (n + 1)‖ ≤ M * θ ^ (n + 1 - 1) / (↑(n + 1) : ℝ) at hb
    rw [Nat.add_sub_cancel] at hb
    exact hb.trans (div_le_self (by positivity) (by simp))
  have hr : ENNReal.ofReal (1 / θ) ≤ q.radius := le_radius_of_majorant hθ₀ hM hc₀ hc
  have hr₀ : 0 < ENNReal.ofReal (1 / θ) := ENNReal.ofReal_pos.mpr (one_div_pos.mpr hθ₀)
  have hF := (q.hasFPowerSeriesOnBall (hr₀.trans_le hr)).mono hr₀ hr
  have h1 : 1 < 1 / θ := (lt_div_iff₀ hθ₀).2 (by simpa using hθ)
  have h1' : (1 : ℂ) ∈ Metric.eball 0 (ENNReal.ofReal (1 / θ)) := by
    simpa [Metric.eball_ofReal, Metric.mem_ball, dist_zero_right] using h1
  have hs : HasSum c (q.sum 1) := by
    simpa [FormalMultilinearSeries.ofScalars_apply_eq, zero_add, q] using hF.hasSum h1'
  refine ⟨hF, ?_, exp_ofScalarsSum_logOf_eqOn P hp (one_div_pos.mpr hθ₀) hF, h1, ?_⟩
  · change FormalMultilinearSeries.ofScalarsSum c 0 = 0
    rw [FormalMultilinearSeries.ofScalarsSum_zero, hc₀, zero_smul]
  · change ‖q.sum 1 - (c 1 + c 2 + c 3)‖ ≤ M * θ ^ 3 / (1 - θ)
    rw [← hs.tsum_eq]
    exact norm_cubic_tail_le hθ₀.le hθ hc₀ hs.summable hc

open PowerSeries in
private theorem logOf_first_three (p : Polynomial ℂ) (hp : p.eval 0 = 1) :
    let c := fun n ↦ coeff n (logOf (p : PowerSeries ℂ))
    c 1 = p.coeff 1 ∧
      c 2 = p.coeff 2 - p.coeff 1 ^ 2 / 2 ∧
      c 3 = p.coeff 3 - p.coeff 1 * p.coeff 2 + p.coeff 1 ^ 3 / 3 := by
  let P : PowerSeries ℂ := p
  let c := fun n ↦ coeff n (logOf P)
  have hp₀ : constantCoeff P = 1 := by
    change constantCoeff (p : PowerSeries ℂ) = 1
    rwa [Polynomial.constantCoeff_coe, Polynomial.coeff_zero_eq_eval_zero]
  have ha₀ : p.coeff 0 = 1 := (Polynomial.coeff_zero_eq_eval_zero p).trans hp
  have h (n : ℕ) :
      (∑ i ∈ Finset.range (n + 1), c (i + 1) * ((i : ℂ) + 1) * p.coeff (n - i)) =
        p.coeff (n + 1) * ((n : ℂ) + 1) := by
    have hh := congrArg (coeff n : PowerSeries ℂ → ℂ) (derivative_logOf_mul P hp₀)
    rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun i j ↦ coeff i (derivative (logOf P)) * coeff j P)] at hh
    simpa only [coeff_derivative, Polynomial.coeff_coe, P, c] using hh
  have h1 : c 1 = p.coeff 1 := by
    simpa [ha₀] using h 0
  have h2 : c 2 = p.coeff 2 - p.coeff 1 ^ 2 / 2 := by
    have h' := h 1
    norm_num [Finset.sum_range_succ, ha₀, h1] at h'
    linear_combination h' / 2
  have h3 : c 3 = p.coeff 3 - p.coeff 1 * p.coeff 2 + p.coeff 1 ^ 3 / 3 := by
    have h' := h 2
    norm_num [Finset.sum_range_succ, ha₀, h1, h2] at h'
    linear_combination h' / 3
  exact ⟨h1, h2, h3⟩

/-- The actual terms subtracted in the cubic remainder, explicitly in terms of
the degree-one, degree-two and degree-three independence coefficients. -/
public theorem complex_log_first_three (starts : Finset ℕ) (R : ℝ) (y : ℕ → ℂ) :
    let P := complexIndependencePolynomial starts R y
    let c (n : ℕ) := PowerSeries.coeff n (PowerSeries.logOf (P : PowerSeries ℂ))
    c 1 = P.coeff 1 ∧
      c 2 = P.coeff 2 - P.coeff 1 ^ 2 / 2 ∧
      c 3 = P.coeff 3 - P.coeff 1 * P.coeff 2 + P.coeff 1 ^ 3 / 3 :=
  logOf_first_three _ (eval_zero starts R y)

private noncomputable def far (s : Finset ℕ) (R : ℝ) (i : ℕ) : Finset ℕ := by
  classical
  exact s.filter (fun j ↦ R < startDistance i j)

private theorem mem_far {s : Finset ℕ} {R : ℝ} {i j : ℕ} :
    j ∈ far s R i ↔ j ∈ s ∧ R < startDistance i j := by
  classical
  exact Finset.mem_filter

private theorem notMem_far_self {s : Finset ℕ} {R : ℝ} (hR : 0 ≤ R) (i : ℕ) :
    i ∉ far s R i := by
  simp [mem_far, startDistance, not_lt.mpr hR]

private theorem distance_comm (i j : ℕ) : startDistance i j = startDistance j i :=
  abs_sub_comm _ _

private theorem coeff_eq_sum (s : Finset ℕ) (R : ℝ) (y : ℕ → ℂ) (n : ℕ) :
    (complexIndependencePolynomial s R y).coeff n =
      ∑ I ∈ (independentSets s R).filter (fun I ↦ I.card = n), ∏ p ∈ I, y p := by
  rw [complexIndependencePolynomial, Polynomial.finsetSum_coeff, Finset.sum_filter]
  simp only [Polynomial.coeff_monomial, Finsupp.single_apply]

-- Mark one of the `n+1` vertices in an independent set, then omit it.
private theorem marked_coeff (s : Finset ℕ) {R : ℝ} (hR : 0 ≤ R) (y : ℕ → ℂ) (n : ℕ) :
    ((n : ℂ) + 1) * (complexIndependencePolynomial s R y).coeff (n + 1) =
      ∑ i ∈ s, y i * (complexIndependencePolynomial (far s R i) R y).coeff n := by
  classical
  let S (t : Finset ℕ) (m : ℕ) := (independentSets t R).filter (fun I ↦ I.card = m)
  have hS {t I : Finset ℕ} {m : ℕ} : I ∈ S t m ↔
      (I ⊆ t ∧ ∀ i ∈ I, ∀ j ∈ I, i ≠ j → R < startDistance i j) ∧ I.card = m := by
    simp [S, independentSets]
  simp only [coeff_eq_sum]
  change ((n : ℂ) + 1) * (∑ I ∈ S s (n + 1), ∏ p ∈ I, y p) =
    ∑ i ∈ s, y i * (∑ J ∈ S (far s R i) n, ∏ p ∈ J, y p)
  calc
    _ = ∑ I ∈ S s (n + 1), ∑ _i ∈ I, ∏ p ∈ I, y p := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro I hI
      rw [Finset.sum_const, (hS.mp hI).2, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
    _ = ∑ i ∈ s, ∑ I ∈ (S s (n + 1)).filter (fun I ↦ i ∈ I), ∏ p ∈ I, y p := by
      simp_rw [Finset.sum_filter]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro I hI
      rw [← Finset.sum_filter]
      congr 1
      ext j
      exact ⟨fun hj ↦ Finset.mem_filter.mpr ⟨(hS.mp hI).1.1 hj, hj⟩,
        fun hj ↦ (Finset.mem_filter.mp hj).2⟩
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mul_sum]
      symm
      refine Finset.sum_nbij' (insert i) (fun I ↦ I.erase i) ?_ ?_ ?_ ?_ ?_
      · intro J hJ
        obtain ⟨⟨hsub, hsep⟩, hcard⟩ := hS.mp hJ
        have hf (j : ℕ) (hj : j ∈ J) : j ∈ s ∧ R < startDistance i j :=
          mem_far.mp (hsub hj)
        have hni : i ∉ J := fun h ↦ notMem_far_self hR i (hsub h)
        refine Finset.mem_filter.mpr ⟨hS.mpr ⟨⟨?_, ?_⟩, ?_⟩, Finset.mem_insert_self ..⟩
        · intro j hj
          rcases Finset.mem_insert.mp hj with rfl | hj
          · exact hi
          · exact (hf j hj).1
        · intro j hj k hk hjk
          rcases Finset.mem_insert.mp hj with hji | hjJ
          · subst j
            exact (hf k ((Finset.mem_insert.mp hk).resolve_left hjk.symm)).2
          · rcases Finset.mem_insert.mp hk with hki | hkJ
            · subst k
              rw [distance_comm]
              exact (hf j hjJ).2
            · exact hsep j hjJ k hkJ hjk
        · rw [Finset.card_insert_of_notMem hni, hcard]
      · intro I hI
        obtain ⟨hI, hiI⟩ := Finset.mem_filter.mp hI
        obtain ⟨⟨hsub, hsep⟩, hcard⟩ := hS.mp hI
        refine hS.mpr ⟨⟨?_, fun j hj k hk ↦ hsep j (Finset.mem_of_mem_erase hj) k
          (Finset.mem_of_mem_erase hk)⟩,
          by rw [Finset.card_erase_of_mem hiI, hcard, Nat.add_sub_cancel]⟩
        intro j hj
        obtain ⟨hne, hj⟩ := Finset.mem_erase.mp hj
        exact mem_far.mpr ⟨hsub hj, hsep i hiI j hj hne.symm⟩
      · intro J hJ
        have hni : i ∉ J := fun hiJ ↦ notMem_far_self hR i ((hS.mp hJ).1.1 hiJ)
        exact Finset.erase_insert hni
      · intro I hI
        exact Finset.insert_erase (Finset.mem_filter.mp hI).2
      · intro J hJ
        have hni : i ∉ J := fun hiJ ↦ notMem_far_self hR i ((hS.mp hJ).1.1 hiJ)
        exact (Finset.prod_insert hni).symm

private theorem coeff_one (s : Finset ℕ) {R : ℝ} (hR : 0 ≤ R) (y : ℕ → ℂ) :
    (complexIndependencePolynomial s R y).coeff 1 = ∑ i ∈ s, y i := by
  simpa [Polynomial.coeff_zero_eq_eval_zero, eval_zero] using marked_coeff s hR y 0

private theorem twice_coeff_two (s : Finset ℕ) {R : ℝ} (hR : 0 ≤ R) (y : ℕ → ℂ) :
    2 * (complexIndependencePolynomial s R y).coeff 2 =
      ∑ i ∈ s, ∑ j ∈ far s R i, y i * y j := by
  have h := marked_coeff s hR y 1
  norm_num [coeff_one _ hR, Finset.mul_sum] at h
  exact h

private theorem six_coeff_three (s : Finset ℕ) {R : ℝ} (hR : 0 ≤ R) (y : ℕ → ℂ) :
    6 * (complexIndependencePolynomial s R y).coeff 3 =
      ∑ i ∈ s, ∑ j ∈ far s R i, ∑ k ∈ far (far s R i) R j, y i * y j * y k := by
  calc
    _ = 2 * ∑ i ∈ s, y i * (complexIndependencePolynomial (far s R i) R y).coeff 2 := by
      rw [← marked_coeff s hR y 2]
      ring
    _ = _ := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [← mul_assoc, mul_comm (2 : ℂ) (y i), mul_assoc, twice_coeff_two _ hR]
      simp only [Finset.mul_sum, ← mul_assoc]

/-- The first three log coefficients in ordered conflict form. The conflict
indicator includes `i = j` (since `0 ≤ R`) and equality at the distance cutoff. -/
public theorem complex_log_first_three_eq_conflict_sums (starts : Finset ℕ) {R : ℝ}
    (hR : 0 ≤ R) (y : ℕ → ℂ) :
    let P := complexIndependencePolynomial starts R y
    let c (n : ℕ) := PowerSeries.coeff n (PowerSeries.logOf (P : PowerSeries ℂ))
    let H (i j : ℕ) := if startDistance i j ≤ R then (1 : ℂ) else 0
    c 1 = (∑ i ∈ starts, y i) ∧
      c 2 = -(∑ i ∈ starts, ∑ j ∈ starts, y i * y j * H i j) / 2 ∧
      c 3 = (∑ i ∈ starts, ∑ j ∈ starts, ∑ k ∈ starts,
        y i * y j * y k *
          (H i j * H i k + H i j * H j k + H i k * H j k - H i j * H i k * H j k)) / 6 := by
  classical
  let P := complexIndependencePolynomial starts R y
  let H (i j : ℕ) := if startDistance i j ≤ R then (1 : ℂ) else 0
  let U (i j : ℕ) := if R < startDistance i j then (1 : ℂ) else 0
  let T (f : ℕ → ℕ → ℕ → ℂ) :=
    ∑ i ∈ starts, ∑ j ∈ starts, ∑ k ∈ starts, y i * y j * y k * f i j k
  have hcompl (i j : ℕ) : H i j = 1 - U i j := by
    by_cases h : R < startDistance i j
    · simp [H, U, h, not_le.mpr h]
    · simp [H, U, h, le_of_not_gt h]
  have hadd (f g : ℕ → ℕ → ℕ → ℂ) :
      T (fun i j k ↦ f i j k + g i j k) = T f + T g := by
    simp only [T, mul_add, Finset.sum_add_distrib]
  have hsub (f g : ℕ → ℕ → ℕ → ℂ) :
      T (fun i j k ↦ f i j k - g i j k) = T f - T g := by
    simp only [T, mul_sub, Finset.sum_sub_distrib]
  have hswap₂ (f : ℕ → ℕ → ℕ → ℂ) : T (fun i j k ↦ f i k j) = T f := by
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ ↦ Finset.sum_congr rfl fun k _ ↦ ?_
    ring
  have hswap₁ (f : ℕ → ℕ → ℕ → ℂ) : T (fun i j k ↦ f j i k) = T f := by
    dsimp only [T]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦
      Finset.sum_congr rfl fun k _ ↦ ?_
    ring
  have hA : P.coeff 1 = ∑ i ∈ starts, y i := coeff_one starts hR y
  have h₂ : 2 * P.coeff 2 = ∑ i ∈ starts, ∑ j ∈ starts, y i * y j * U i j := by
    rw [twice_coeff_two starts hR]
    simp only [far, Finset.sum_filter, U, mul_ite, mul_one, mul_zero]
  refine ⟨(complex_log_first_three starts R y).1.trans hA, ?_, ?_⟩
  · have hcoeff : PowerSeries.coeff 2 (PowerSeries.logOf (P : PowerSeries ℂ)) =
        P.coeff 2 - P.coeff 1 ^ 2 / 2 := (complex_log_first_three starts R y).2.1
    have hsum : (∑ i ∈ starts, ∑ j ∈ starts, y i * y j * H i j) =
        P.coeff 1 ^ 2 - 2 * P.coeff 2 := by
      rw [hA, pow_two, h₂, Finset.sum_mul]
      simp only [hcompl, Finset.mul_sum, Finset.sum_sub_distrib, mul_sub, mul_one]
    change PowerSeries.coeff 2 (PowerSeries.logOf (P : PowerSeries ℂ)) =
      -(∑ i ∈ starts, ∑ j ∈ starts, y i * y j * H i j) / 2
    rw [hcoeff, hsum]
    ring
  have hij : T (fun i j _ ↦ U i j) = (2 * P.coeff 2) * P.coeff 1 := by
    rw [h₂, hA, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    ring
  have hik : T (fun i _ k ↦ U i k) = (2 * P.coeff 2) * P.coeff 1 := by
    rw [← hij]
    exact hswap₂ (fun i j _ ↦ U i j)
  have hjk : T (fun _ j k ↦ U j k) = (2 * P.coeff 2) * P.coeff 1 := by
    rw [← hik]
    exact hswap₁ (fun i _ k ↦ U i k)
  have hconst : T (fun _ _ _ ↦ 2) = 2 * P.coeff 1 ^ 3 := by
    rw [hA, pow_succ, pow_two]
    simp only [T, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦
      Finset.sum_congr rfl fun k _ ↦ ?_
    ring
  have htriple : T (fun i j k ↦ U i j * U i k * U j k) = 6 * P.coeff 3 := by
    rw [six_coeff_three starts hR]
    simp only [T, far, Finset.sum_filter]
    refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
    by_cases hij' : R < startDistance i j
    · simp only [U, hij', ite_true, one_mul]
      refine Finset.sum_congr rfl fun k _ ↦ ?_
      by_cases hik' : R < startDistance i k <;>
        by_cases hjk' : R < startDistance j k <;> simp [hik', hjk']
    · simp [U, hij']
  have hk (i j k : ℕ) :
      H i j * H i k + H i j * H j k + H i k * H j k - H i j * H i k * H j k =
        U i j * U i k * U j k - U i j - U i k - U j k + 2 := by
    simp only [hcompl]; ring
  change PowerSeries.coeff 3 (PowerSeries.logOf (P : PowerSeries ℂ)) =
    T (fun i j k ↦ H i j * H i k + H i j * H j k + H i k * H j k - H i j * H i k * H j k) / 6
  have hc : PowerSeries.coeff 3 (PowerSeries.logOf (P : PowerSeries ℂ)) =
      P.coeff 3 - P.coeff 1 * P.coeff 2 + P.coeff 1 ^ 3 / 3 :=
    (complex_log_first_three starts R y).2.2
  rw [hc]
  simp only [hk]
  rw [hadd, hsub, hsub, hsub, htriple, hij, hik, hjk, hconst]
  ring

end DetectorLogRemainder
