module

public import Lemmas.PrimeWindowPoleCorrection
import Lemmas.PrimeTranslationEndpointAsymptotic
import Lemmas.PrimeTranslationRayleigh
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Tactic

/-! # Corrected prime-window Rayleigh limit

Source: `bdd74f2a:.godel/adhoc/prime-translation-norm.md`, §3 (scan pin
`fa7259d`, checked at base `fad1c055`).
Owning check session: `01a20eab-a304-7e57-9eec-1f7fc75e3637`.

Scope: the leading real Rayleigh supremum of the untwisted strict-cutoff
prime translations minus the actual two-pole operator, on the full complex
`L²` window modeled by zero extensions. No positivity of the pole operator
or assertion about the remaining Weil form is used.
-/

open Filter MeasureTheory
open Real (exp log sqrt)
open scoped ArithmeticFunction.vonMangoldt ComplexConjugate InnerProductSpace Topology

namespace Masullo

local notation "𝓗" => Lp ℂ 2 (volume : Measure ℝ)
local notation "wSet" => Set.Icc (0 : ℝ)
local notation "cut" D:max => Finset.Ico 1 ⌈exp D⌉₊
local notation "weight" n:max => (Λ n / sqrt (n : ℝ))
local notation "f₀" => primeTranslationProfile
local notation "g₀" => primeTranslationReflectedProfile

private noncomputable def restrictWindow (D : ℝ) (u : 𝓗) : 𝓗 :=
  ((Lp.memLp u).indicator measurableSet_Icc.nullMeasurableSet).toLp ((wSet D).indicator u)

private theorem restrictWindow_ae (D : ℝ) (u : 𝓗) :
    restrictWindow D u =ᵐ[volume] (wSet D).indicator u :=
  MemLp.coeFn_toLp _

private theorem supported_restrictWindow (D : ℝ) (u : 𝓗) :
    PrimeWindowSupported D (restrictWindow D u) := by
  filter_upwards [restrictWindow_ae D u] with x hx h
  rw [hx, Set.indicator_of_notMem h]

private theorem inner_restrictWindow {D : ℝ} {v : 𝓗} (hv : PrimeWindowSupported D v) (u : 𝓗) :
    ⟪v, restrictWindow D u⟫_ℂ = ⟪v, u⟫_ℂ := by
  simp only [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [restrictWindow_ae D u, hv] with x hx hvx
  rw [RCLike.inner_apply, RCLike.inner_apply, hx]
  by_cases h : x ∈ wSet D
  · rw [Set.indicator_of_mem h]
  · simp [hvx h]

private noncomputable def shiftPair (n : ℕ) (u : 𝓗) : 𝓗 :=
  primeWindowTranslate (log n) u + primeWindowTranslate (-log n) u

private noncomputable def fullSum (D : ℝ) (u : 𝓗) : 𝓗 :=
  ∑ n ∈ cut D, (↑(weight n) : ℂ) • shiftPair n u

/-- The untwisted sum of both translates at each `log n`, weighted by `Λ n / √n`
for `1 ≤ n < exp D`, with output cut to `[0,D]`. Its window-space inputs are
represented by their full-line zero extensions. -/
public noncomputable def primeWindowOperator (D : ℝ) (u : 𝓗) : 𝓗 :=
  restrictWindow D (fullSum D u)

private theorem shiftPair_ae (n : ℕ) (u : 𝓗) :
    shiftPair n u =ᵐ[volume] fun x ↦ u (x + log n) + u (x - log n) := by
  filter_upwards [Lp.coeFn_add (primeWindowTranslate (log n) u) (primeWindowTranslate (-log n) u),
    primeWindowTranslate_ae (log n) u, primeWindowTranslate_ae (-log n) u] with x hx hp hm
  exact hx.trans (by simp only [Pi.add_apply, hp, hm, sub_eq_add_neg])

private theorem fullSum_ae (D : ℝ) (u : 𝓗) :
    fullSum D u =ᵐ[volume] primeTranslationComplexApply D u := by
  unfold fullSum primeTranslationComplexApply
  refine (Lp.coeFn_finsetSum _ _).trans ?_
  have h (n : ℕ) : (⇑((↑(weight n) : ℂ) • shiftPair n u)) =ᵐ[volume]
      fun x ↦ (↑(weight n) : ℂ) * (u (x + log n) + u (x - log n)) := by
    filter_upwards [Lp.coeFn_smul (↑(weight n) : ℂ) (shiftPair n u), shiftPair_ae n u] with x hs hx
    rw [hs, Pi.smul_apply, smul_eq_mul, hx]
  filter_upwards [eventuallyEq_sum (s := cut D) (fun n _ ↦ h n)] with x hx
  simpa only [Finset.sum_apply] using hx

/-- The `L²` action agrees with the strict-cutoff representative sum, zero extended
on the output. This needs no choice of a pointwise supported input representative. -/
public theorem primeWindowOperator_ae (D : ℝ) (u : 𝓗) :
    primeWindowOperator D u =ᵐ[volume] (wSet D).indicator (primeTranslationComplexApply D u) := by
  filter_upwards [restrictWindow_ae D (fullSum D u), fullSum_ae D u] with x hx hs
  change restrictWindow D (fullSum D u) x = _
  rw [hx]
  by_cases h : x ∈ wSet D <;> simp [h, hs]

private theorem inner_operator {D : ℝ} {v : 𝓗} (hv : PrimeWindowSupported D v) (u : 𝓗) :
    ⟪v, primeWindowOperator D u⟫_ℂ =
      ∑ n ∈ cut D, (↑(weight n) : ℂ) *
        (⟪v, primeWindowTranslate (log n) u⟫_ℂ + ⟪v, primeWindowTranslate (-log n) u⟫_ℂ) := by
  rw [primeWindowOperator, inner_restrictWindow hv]
  simp only [fullSum, shiftPair, inner_sum, inner_smul_right, inner_add_right]

private theorem operator_symmetric {D : ℝ} {u v : 𝓗}
    (hu : PrimeWindowSupported D u) (hv : PrimeWindowSupported D v) :
    ⟪v, primeWindowOperator D u⟫_ℂ = ⟪primeWindowOperator D v, u⟫_ℂ := by
  rw [← inner_conj_symm (primeWindowOperator D v) u, inner_operator hv, inner_operator hu, map_sum]
  refine Finset.sum_congr rfl fun n _ ↦ ?_
  simp only [map_mul, Complex.conj_ofReal, map_add, inner_conj_symm]
  rw [primeWindowTranslate_adjoint (log n) v u, primeWindowTranslate_adjoint (-log n) v u,
    neg_neg, add_comm]

private theorem support_smul {D : ℝ} {u : 𝓗} (hu : PrimeWindowSupported D u) (a : ℂ) :
    PrimeWindowSupported D (a • u) := by
  filter_upwards [hu, Lp.coeFn_smul a u] with x hu hx h
  simp [hx, hu h]

private theorem support_add {D : ℝ} {u v : 𝓗}
    (hu : PrimeWindowSupported D u) (hv : PrimeWindowSupported D v) :
    PrimeWindowSupported D (u + v) := by
  filter_upwards [hu, hv, Lp.coeFn_add u v] with x hu hv hx h
  rw [hx, Pi.add_apply, hu h, hv h, add_zero]

private theorem support_sub {D : ℝ} {u v : 𝓗}
    (hu : PrimeWindowSupported D u) (hv : PrimeWindowSupported D v) :
    PrimeWindowSupported D (u - v) := by
  filter_upwards [hu, hv, Lp.coeFn_sub u v] with x hu hv hx h
  rw [hx, Pi.sub_apply, hu h, hv h, sub_zero]

private theorem norm_sq_integral (u : 𝓗) : ‖u‖ ^ 2 = ∫ x, ‖u x‖ ^ 2 := by
  have hi : Integrable (fun x ↦ ⟪u x, u x⟫_ℂ) := L2.integrable_inner u u
  have h (z : ℂ) : RCLike.re ⟪z, z⟫_ℂ = ‖z‖ ^ 2 := by
    rw [inner_self_eq_norm_sq_to_K, ← RCLike.ofReal_pow, RCLike.ofReal_re]
  have hu : RCLike.re ⟪u, u⟫_ℂ = ‖u‖ ^ 2 := by
    rw [inner_self_eq_norm_sq_to_K, ← RCLike.ofReal_pow, RCLike.ofReal_re]
  rw [← hu, L2.inner_def, ← integral_re hi]
  simp only [h]

private theorem norm_window {D : ℝ} {u : 𝓗} (hu : PrimeWindowSupported D u)
    {r : ℝ → ℂ} (hr : u =ᵐ[volume.restrict (wSet D)] r) :
    ‖u‖ = primeTranslationWindowL2Norm D r := by
  have h : (fun x ↦ ‖u x‖ ^ 2) =ᵐ[volume.restrict (wSet D)] (fun x ↦ ‖r x‖ ^ 2) :=
    hr.mono fun x hx ↦ congrArg (fun z : ℂ ↦ ‖z‖ ^ 2) hx
  have hs : ∀ᵐ x ∂volume, x ∉ wSet D → ‖u x‖ ^ 2 = 0 :=
    hu.mono fun x hx h ↦ by simp [hx h]
  rw [primeTranslationWindowL2Norm, ← integral_congr_ae h,
    setIntegral_eq_integral_of_ae_compl_eq_zero hs, ← norm_sq_integral, Real.sqrt_sq (norm_nonneg _)]

private theorem norm_window_on {D : ℝ} {u : 𝓗} (hu : PrimeWindowSupported D u)
    {r : ℝ → ℂ} (hr : ∀ᵐ x ∂volume, x ∈ wSet D → u x = r x) :
    ‖u‖ = primeTranslationWindowL2Norm D r :=
  norm_window hu ((ae_restrict_iff' measurableSet_Icc).mpr hr)

private theorem reflect_mem_iff (D x : ℝ) : D - x ∈ wSet D ↔ x ∈ wSet D := by
  simp only [Set.mem_Icc, sub_nonneg, sub_le_self_iff, and_comm]

private theorem profile_memLp (D : ℝ) (a : ℝ → ℝ) (ha : Continuous a)
    (h : ∀ x ∈ wSet D, a x ≤ 0) :
    MemLp ((wSet D).indicator (fun x ↦ (exp (a x) : ℂ))) 2 volume := by
  rw [memLp_indicator_iff_restrict measurableSet_Icc.nullMeasurableSet]
  have : IsFiniteMeasure ((volume : Measure ℝ).restrict (wSet D)) :=
    isFiniteMeasure_restrict.mpr (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
  refine MemLp.of_bound (by fun_prop) 1 ?_
  filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
  rw [Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
  exact Real.exp_le_one_iff.mpr (h x hx)

private theorem left_memLp (D : ℝ) : MemLp (fun x ↦ (f₀ D x : ℂ)) 2 volume := by
  convert profile_memLp D (fun x ↦ -x / 2) (by fun_prop) (fun x hx ↦ by linarith [hx.1]) using 1
  funext x
  by_cases hx : x ∈ wSet D <;> simp [primeTranslationProfile, hx]

private theorem right_memLp (D : ℝ) : MemLp (fun x ↦ (g₀ D x : ℂ)) 2 volume := by
  convert profile_memLp D (fun x ↦ -(D - x) / 2) (by fun_prop)
    (fun x hx ↦ by linarith [hx.2]) using 1
  funext x
  unfold primeTranslationReflectedProfile primeTranslationProfile
  by_cases hx : x ∈ wSet D
  · rw [Set.indicator_of_mem hx, Set.indicator_of_mem ((reflect_mem_iff D x).mpr hx)]
  · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem (fun h ↦ hx ((reflect_mem_iff D x).mp h)),
      Complex.ofReal_zero]

private noncomputable def left (D : ℝ) : 𝓗 := (left_memLp D).toLp _
private noncomputable def right (D : ℝ) : 𝓗 := (right_memLp D).toLp _

private theorem left_ae (D : ℝ) : left D =ᵐ[volume] fun x ↦ (f₀ D x : ℂ) :=
  (left_memLp D).coeFn_toLp

private theorem right_ae (D : ℝ) : right D =ᵐ[volume] fun x ↦ (g₀ D x : ℂ) :=
  (right_memLp D).coeFn_toLp

private theorem support_left (D : ℝ) : PrimeWindowSupported D (left D) := by
  filter_upwards [left_ae D] with x hx hxD
  simp [hx, primeTranslationProfile, hxD]

private theorem support_right (D : ℝ) : PrimeWindowSupported D (right D) := by
  filter_upwards [right_ae D] with x hx hxD
  rw [hx, primeTranslationReflectedProfile, primeTranslationProfile,
    Set.indicator_of_notMem (fun h ↦ hxD ((reflect_mem_iff D x).mp h)), Complex.ofReal_zero]

private theorem inner_profile (D : ℝ) {v : 𝓗} (hv : PrimeWindowSupported D v) (u : 𝓗)
    {r : ℝ → ℝ} (hr : v =ᵐ[volume] fun x ↦ (r x : ℂ)) :
    ⟪v, u⟫_ℂ = ∫ x in wSet D, (r x : ℂ) * u x := by
  rw [L2.inner_def, ← setIntegral_eq_integral_of_ae_compl_eq_zero
    (hv.mono fun x hx h ↦ by simp [hx h])]
  apply integral_congr_ae
  filter_upwards [ae_restrict_of_ae hr] with x hx
  rw [RCLike.inner_apply, hx, Complex.conj_ofReal, mul_comm]

private theorem pole_eq (D : ℝ) (u : 𝓗) :
    primeWindowPoleOperator D u = (exp (D / 2) : ℂ) •
      (⟪right D, u⟫_ℂ • left D + ⟪left D, u⟫_ℂ • right D) := by
  let a := ⟪right D, u⟫_ℂ
  let b := ⟪left D, u⟫_ℂ
  let E : ℂ := exp (D / 2)
  have ha : a = _ := inner_profile D (support_right D) u (right_ae D)
  have hb : b = _ := inner_profile D (support_left D) u (left_ae D)
  apply Lp.ext
  change primeWindowPoleOperator D u =ᵐ[volume] ⇑(E • (a • left D + b • right D))
  filter_upwards [primeWindowPoleOperator_ae D u, Lp.coeFn_smul E (a • left D + b • right D),
    Lp.coeFn_add (a • left D) (b • right D), Lp.coeFn_smul a (left D),
    Lp.coeFn_smul b (right D), left_ae D, right_ae D] with x hR hE hab ha' hb' hf hg
  simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul] at hE hab ha' hb'
  rw [hR, hE, hab, ha', hb', hf, hg, ha, hb, primeTranslationPoleApply]
  dsimp only [E]
  ring

private theorem pole_symmetric (D : ℝ) (u v : 𝓗) :
    ⟪v, primeWindowPoleOperator D u⟫_ℂ = ⟪primeWindowPoleOperator D v, u⟫_ℂ := by
  rw [pole_eq D u, pole_eq D v]
  simp only [inner_smul_right, inner_smul_left, inner_add_right, inner_add_left, Complex.conj_ofReal,
    inner_conj_symm]
  ring

private noncomputable def residual (D : ℝ) (u : 𝓗) : 𝓗 :=
  primeWindowOperator D u - primeWindowPoleOperator D u

private theorem residual_symmetric {D : ℝ} {u v : 𝓗}
    (hu : PrimeWindowSupported D u) (hv : PrimeWindowSupported D v) :
    ⟪v, residual D u⟫_ℂ = ⟪residual D v, u⟫_ℂ := by
  rw [residual, residual, inner_sub_right, inner_sub_left, operator_symmetric hu hv, pole_symmetric]

private theorem supported_residual (D : ℝ) (u : 𝓗) : PrimeWindowSupported D (residual D u) := by
  refine support_sub (supported_restrictWindow _ _) ?_
  rw [pole_eq]
  exact support_smul (support_add (support_smul (support_left D) _) (support_smul (support_right D) _)) _

private theorem sum_ae_congr (D : ℝ) {u v : ℝ → ℂ} (h : u =ᵐ[volume] v) :
    primeTranslationComplexApply D u =ᵐ[volume] primeTranslationComplexApply D v := by
  unfold primeTranslationComplexApply
  have ht (n : ℕ) :
      (fun x ↦ (↑(weight n) : ℂ) * (u (x + log n) + u (x - log n))) =ᵐ[volume]
      (fun x ↦ (↑(weight n) : ℂ) * (v (x + log n) + v (x - log n))) := by
    have shift (t : ℝ) := (measurePreserving_add_right volume t).quasiMeasurePreserving.ae_eq_comp h
    filter_upwards [shift (log n), shift (-log n)] with x hp hm
    change u (x + log n) = v (x + log n) at hp
    change u (x - log n) = v (x - log n) at hm
    rw [hp, hm]
  filter_upwards [eventuallyEq_sum (s := cut D) (fun n _ ↦ ht n)] with x hx
  simpa only [Finset.sum_apply] using hx

private theorem poleApply_ae_congr (D : ℝ) {u v : ℝ → ℂ} (h : u =ᵐ[volume] v) (x : ℝ) :
    primeTranslationPoleApply D u x = primeTranslationPoleApply D v x := by
  unfold primeTranslationPoleApply
  have integral_eq (r : ℝ → ℝ) :
      (∫ z in wSet D, (r z : ℂ) * u z) = ∫ z in wSet D, (r z : ℂ) * v z :=
    integral_congr_ae ((ae_restrict_of_ae h).mono fun z hz ↦ congrArg ((r z : ℂ) * ·) hz)
  rw [integral_eq, integral_eq]

private theorem residual_on {D : ℝ} {u : 𝓗} {v : ℝ → ℂ} (h : u =ᵐ[volume] v) :
    ∀ᵐ x ∂volume, x ∈ wSet D → residual D u x =
      primeTranslationComplexApply D v x - primeTranslationPoleApply D v x := by
  filter_upwards [Lp.coeFn_sub (primeWindowOperator D u) (primeWindowPoleOperator D u),
    primeWindowOperator_ae D u, primeWindowPoleOperator_ae D u, sum_ae_congr D h]
    with x hA hT hR ht hx
  change (primeWindowOperator D u - primeWindowPoleOperator D u) x = _
  rw [hA, Pi.sub_apply, hT, Set.indicator_of_mem hx, ht, hR, poleApply_ae_congr D h]

private noncomputable def endpointSpan (D : ℝ) : Submodule ℂ 𝓗 :=
  Submodule.span ℂ {left D, right D}

private instance (D : ℝ) : FiniteDimensional ℂ (endpointSpan D) :=
  FiniteDimensional.span_of_finite _ (Set.toFinite _)

private theorem combo_ae (D : ℝ) (a b : ℂ) :
    a • left D + b • right D =ᵐ[volume] fun x ↦ a * (f₀ D x : ℂ) + b * (g₀ D x : ℂ) := by
  filter_upwards [Lp.coeFn_add (a • left D) (b • right D), Lp.coeFn_smul a (left D),
    Lp.coeFn_smul b (right D), left_ae D, right_ae D] with x h hx hy hf hg
  simp only [h, hx, hy, hf, hg, Pi.add_apply, Pi.smul_apply, smul_eq_mul]

private theorem support_combo (D : ℝ) (a b : ℂ) :
    PrimeWindowSupported D (a • left D + b • right D) :=
  support_add (support_smul (support_left D) a) (support_smul (support_right D) b)

private theorem support_span {D : ℝ} {v : 𝓗} (hv : v ∈ endpointSpan D) : PrimeWindowSupported D v := by
  obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.mp hv
  exact support_combo D a b

private theorem residual_span {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ D : ℝ in atTop, ∀ v ∈ endpointSpan D, ‖residual D v‖ ≤ ε * exp (D / 2) * ‖v‖ := by
  filter_upwards [primeTranslationSpanCancellation hε] with D hD
  intro v hv
  obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.mp hv
  have h := combo_ae D a b
  rw [norm_window_on (supported_residual D _) (residual_on h),
    norm_window (support_combo D a b) (ae_restrict_of_ae h)]
  exact hD a b

private theorem re_le_norm (z : ℂ) : z.re ≤ ‖z‖ :=
  (le_abs_self _).trans (Complex.abs_re_le_norm z)

private theorem norm_shift_inner_le (t : ℝ) (u : 𝓗) :
    ‖⟪u, primeWindowTranslate t u⟫_ℂ‖ ≤ ∫ x, ‖u x‖ * ‖u (x + t)‖ := by
  rw [L2.inner_def]
  refine (norm_integral_le_integral_norm _).trans_eq (integral_congr_ae ?_)
  filter_upwards [primeWindowTranslate_ae t u] with x hx
  rw [RCLike.inner_apply, hx, norm_mul, Complex.norm_conj, mul_comm]

private theorem operator_upper {η : ℝ} (hη : 0 < η) :
    ∀ᶠ D : ℝ in atTop, ∀ u : 𝓗, PrimeWindowSupported D u →
      (⟪u, primeWindowOperator D u⟫_ℂ).re ≤ (1 + η) * exp (D / 2) * ‖u‖ ^ 2 := by
  filter_upwards [primeTranslationEndpointAsymptotic hη] with D hD
  intro u hu
  have hback (t : ℝ) : ‖⟪u, primeWindowTranslate (-t) u⟫_ℂ‖ =
      ‖⟪u, primeWindowTranslate t u⟫_ℂ‖ := by
    rw [primeWindowTranslate_adjoint (-t) u u, neg_neg, norm_inner_symm]
  refine (re_le_norm _).trans ?_
  rw [inner_operator hu, norm_sq_integral]
  refine (norm_sum_le _ _).trans ?_
  refine le_trans ?_ (hD (Lp.memLp u) hu)
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun n _ ↦ ?_
  have hn : 0 ≤ weight n := div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _)
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hn]
  calc
    _ ≤ weight n * (‖⟪u, primeWindowTranslate (log n) u⟫_ℂ‖ +
          ‖⟪u, primeWindowTranslate (-log n) u⟫_ℂ‖) :=
      mul_le_mul_of_nonneg_left (norm_add_le _ _) hn
    _ ≤ weight n * ((∫ x, ‖u x‖ * ‖u (x + log n)‖) + ∫ x, ‖u x‖ * ‖u (x + log n)‖) := by
      rw [hback]
      exact mul_le_mul_of_nonneg_left (add_le_add (norm_shift_inner_le _ _) (norm_shift_inner_le _ _)) hn
    _ = _ := by ring

private theorem residual_quadratic (D : ℝ) (u : 𝓗) :
    (⟪u, residual D u⟫_ℂ).re =
      (⟪u, primeWindowOperator D u⟫_ℂ).re - primeWindowPoleQuadratic D u := by
  rw [residual, inner_sub_right, Complex.sub_re, primeWindowPoleQuadratic]

-- Compress to the orthogonal complement of the endpoint span. The two
-- residual pairings each contain the error-controlled vector `(T - R) p`.
private theorem corrected_upper {η : ℝ} (hη : 0 < η) :
    ∀ᶠ D : ℝ in atTop, ∀ u : 𝓗, PrimeWindowSupported D u → ‖u‖ = 1 →
      (⟪u, primeWindowOperator D u⟫_ℂ).re - primeWindowPoleQuadratic D u ≤
        (1 + 3 * η) * exp (D / 2) := by
  filter_upwards [operator_upper hη, residual_span hη] with D hT hA
  intro u hu hu₁
  let S := endpointSpan D
  let p := S.starProjection u
  let q := u - p
  have hpS : p ∈ S := Submodule.starProjection_apply_mem S u
  have hp := support_span hpS
  have hq := support_sub hu hp
  have hpn : ‖p‖ ≤ 1 := hu₁ ▸ S.norm_starProjection_apply_le u
  have hqn : ‖q‖ ≤ 1 := by
    rw [show q = Sᗮ.starProjection u from (Submodule.starProjection_orthogonal_val u).symm, ← hu₁]
    exact Sᗮ.norm_starProjection_apply_le u
  have hsum : p + q = u := by dsimp [q]; abel
  have horth (v : 𝓗) (hv : v ∈ S) : ⟪v, q⟫_ℂ = 0 :=
    inner_eq_zero_symm.mp (Submodule.starProjection_inner_eq_zero u v hv)
  have hRq : primeWindowPoleOperator D q = 0 := by
    rw [pole_eq, horth (right D) (Submodule.subset_span (by simp)),
      horth (left D) (Submodule.subset_span (by simp))]
    simp
  have hAq : residual D q = primeWindowOperator D q := by rw [residual, hRq, sub_zero]
  have hexpand : ⟪u, residual D u⟫_ℂ = ⟪q, primeWindowOperator D q⟫_ℂ +
      ⟪u, residual D p⟫_ℂ + ⟪residual D p, q⟫_ℂ := by
    calc
      _ = ⟪residual D u, p⟫_ℂ + ⟪residual D u, q⟫_ℂ := by
        rw [residual_symmetric hu hu, ← inner_add_right, hsum]
      _ = ⟪u, residual D p⟫_ℂ + ⟪p, residual D q⟫_ℂ + ⟪q, residual D q⟫_ℂ := by
        rw [← residual_symmetric hp hu, ← residual_symmetric hq hu, add_assoc,
          ← inner_add_left, hsum]
      _ = _ := by rw [residual_symmetric hq hp, hAq]; ring
  have hnorm : ‖residual D p‖ ≤ η * exp (D / 2) :=
    (hA p hpS).trans (mul_le_of_le_one_right (by positivity) hpn)
  have h₁ : (⟪u, residual D p⟫_ℂ).re ≤ η * exp (D / 2) := by
    refine (re_le_norm _).trans ((norm_inner_le_norm u _).trans ?_)
    simpa only [hu₁, one_mul] using hnorm
  have h₂ : (⟪residual D p, q⟫_ℂ).re ≤ η * exp (D / 2) :=
    (re_le_norm _).trans ((norm_inner_le_norm _ q).trans
      ((mul_le_of_le_one_right (norm_nonneg _) hqn).trans hnorm))
  have h₃ : (⟪q, primeWindowOperator D q⟫_ℂ).re ≤ (1 + η) * exp (D / 2) :=
    (hT q hq).trans (mul_le_of_le_one_right (by positivity)
      ((sq_le_sq₀ (norm_nonneg q) zero_le_one).mpr hqn |>.trans_eq (one_pow _)))
  rw [← residual_quadratic, hexpand, Complex.add_re, Complex.add_re]
  linarith only [h₁, h₂, h₃]

private theorem sum_primePowers (D : ℝ) (F : ℕ → ℂ) :
    let p : ↥((cut D).filter Nat.Prime) → ℕ := Subtype.val
    (∑ ik ∈ primeWindowPowers D p, (↑(weight (p ik.1 ^ ik.2)) : ℂ) * F (p ik.1 ^ ik.2)) =
      ∑ n ∈ cut D, (↑(weight n) : ℂ) * F n := by
  classical
  dsimp only
  let ι := ↥((cut D).filter Nat.Prime)
  let p : ι → ℕ := Subtype.val
  have hp (i : ι) : (p i).Prime := (Finset.mem_filter.mp i.property).2
  have hcut {n : ℕ} (hn : 0 < n) : log (n : ℝ) < D ↔ n < ⌈exp D⌉₊ :=
    (Real.log_lt_iff_lt_exp (by exact_mod_cast hn)).trans Nat.lt_ceil.symm
  calc
    _ = ∑ n ∈ (cut D).filter IsPrimePow, (↑(weight n) : ℂ) * F n := by
      refine Finset.sum_bij (fun ik _ ↦ p ik.1 ^ ik.2) ?_ ?_ ?_ ?_
      · rintro ⟨i, k⟩ hik
        obtain ⟨hk, hD⟩ := (mem_primeWindowPowers hp i k).mp hik
        have hn := pow_pos (hp i).pos k
        exact Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨hn, (hcut hn).mp hD⟩,
          (isPrimePow_nat_iff _).mpr ⟨p i, k, hp i, hk, rfl⟩⟩
      · rintro ⟨i, k⟩ hik ⟨j, l⟩ hjl he
        have hk := ((mem_primeWindowPowers hp i k).mp hik).1
        have hl := ((mem_primeWindowPowers hp j l).mp hjl).1
        obtain ⟨a, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
        obtain ⟨b, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : l ≠ 0)
        obtain ⟨hij, hab⟩ := (hp i).pow_inj (hp j) he
        exact Prod.ext (Subtype.ext hij) (congrArg Nat.succ hab)
      · intro n hn
        obtain ⟨hn, hn'⟩ := Finset.mem_filter.mp hn
        obtain ⟨r, k, hr, hk, rfl⟩ := (isPrimePow_nat_iff n).mp hn'
        have hlt := (Finset.mem_Ico.mp hn).2
        let i : ι := ⟨r, Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr
          ⟨hr.pos, (Nat.le_self_pow hk.ne' r).trans_lt hlt⟩, hr⟩⟩
        exact ⟨(i, k), (mem_primeWindowPowers hp i k).mpr
          ⟨hk, (hcut (pow_pos hr.pos k)).mpr hlt⟩, rfl⟩
      · intro ik _
        simp only [p, Nat.cast_pow]
    _ = _ := by
      refine Finset.sum_subset (Finset.filter_subset _ _) fun n hn hn' ↦ ?_
      have hz : Λ n = 0 := ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr
        (fun h ↦ hn' (Finset.mem_filter.mpr ⟨hn, h⟩))
      simp [hz]

/-- For a supported test, the operator pairing is the negative of the
existing signed form with untwisted coefficients on all active primes. -/
public theorem primeWindowOperator_inner_eq_neg_signedForm (D : ℝ) (u : 𝓗)
    (hu : PrimeWindowSupported D u) :
    ⟪u, primeWindowOperator D u⟫_ℂ = -primeWindowSignedForm D
      (fun i : ↥((Finset.Ico 1 ⌈exp D⌉₊).filter Nat.Prime) ↦ (i : ℕ)) (fun _ ↦ 1) u := by
  rw [inner_operator hu, primeWindowSignedForm, neg_neg]
  simp only [primeWindowShiftForm, primeWindowPowerWeight, one_pow, map_one, one_mul]
  simpa only [Nat.cast_pow] using (sum_primePowers D fun n ↦
    ⟪u, primeWindowTranslate (log n) u⟫_ℂ + ⟪u, primeWindowTranslate (-log n) u⟫_ℂ).symm

-- Use the escaping modulation of the admissible endpoint-weight test, not
-- the endpoint-weight test itself, to obtain a corrected lower bound.
private theorem corrected_lower_test {D : ℝ} (hD : 0 < D) (u : 𝓗)
    (hu : PrimeWindowSupported D u) (hu₁ : ‖u‖ = 1) {ε : ℝ} (hε : 0 < ε) :
    ∃ v : 𝓗, PrimeWindowSupported D v ∧ ‖v‖ = 1 ∧
      (⟪u, primeWindowOperator D u⟫_ℂ).re - ε ≤
        (⟪v, primeWindowOperator D v⟫_ℂ).re - primeWindowPoleQuadratic D v := by
  let p : ↥((cut D).filter Nat.Prime) → ℕ := Subtype.val
  obtain ⟨v, hv, hv₁, h⟩ := exists_primeWindowPoleCorrected_test D hD p
    (fun i ↦ (Finset.mem_filter.mp i.property).2) Subtype.val_injective (fun _ ↦ 1)
    (fun _ ↦ norm_one) u hu hu₁ ε hε
  refine ⟨v, hv, hv₁, ?_⟩
  simpa only [primeWindowOperator_inner_eq_neg_signedForm D u hu,
    primeWindowOperator_inner_eq_neg_signedForm D v hv, Complex.neg_re] using h

private noncomputable def endpointWeight (D x : ℝ) : ℝ := f₀ D x + g₀ D x
private noncomputable def weightVector (D : ℝ) : 𝓗 := left D + right D

private theorem weightVector_ae (D : ℝ) : weightVector D =ᵐ[volume] fun x ↦ (endpointWeight D x : ℂ) := by
  simpa only [one_smul, one_mul, endpointWeight, weightVector, Complex.ofReal_add] using combo_ae D 1 1

private theorem support_weightVector (D : ℝ) : PrimeWindowSupported D (weightVector D) :=
  support_add (support_left D) (support_right D)

private theorem norm_weightVector_pos {D : ℝ} (hD : 0 < D) : 0 < ‖weightVector D‖ := by
  refine norm_pos_iff.mpr fun h ↦ ?_
  have h0 : weightVector D =ᵐ[volume] (0 : ℝ → ℂ) := by
    rw [h]
    exact Lp.coeFn_zero ℂ 2 volume
  have hμ : (volume : Measure ℝ).restrict (wSet D) ≠ 0 := by
    intro hm
    have hvol := Measure.restrict_apply_self (μ := (volume : Measure ℝ)) (wSet D)
    rw [hm, Real.volume_Icc, sub_zero] at hvol
    exact (ENNReal.ofReal_pos.mpr hD).ne' (show (0 : ENNReal) = ENNReal.ofReal D from hvol).symm
  have hne : (ae ((volume : Measure ℝ).restrict (wSet D))).NeBot := ae_neBot.mpr hμ
  have hw : ∀ᵐ x ∂((volume : Measure ℝ).restrict (wSet D)),
      x ∈ wSet D ∧ (endpointWeight D x : ℂ) = 0 :=
    (ae_restrict_mem measurableSet_Icc).and (ae_restrict_of_ae ((weightVector_ae D).symm.trans h0))
  obtain ⟨x, hx, hx₀⟩ := @Filter.Eventually.exists _ _ _ hne hw
  have hpos : 0 < endpointWeight D x := by
    unfold endpointWeight primeTranslationReflectedProfile primeTranslationProfile
    rw [Set.indicator_of_mem hx, Set.indicator_of_mem ((reflect_mem_iff D x).mpr hx)]
    positivity
  exact hpos.ne' (Complex.ofReal_eq_zero.mp hx₀)

private theorem weightVector_sq (D : ℝ) :
    ‖weightVector D‖ ^ 2 = ∫ x in wSet D, endpointWeight D x ^ 2 := by
  rw [norm_window (support_weightVector D) (ae_restrict_of_ae (weightVector_ae D)),
    primeTranslationWindowL2Norm, Real.sq_sqrt (integral_nonneg fun _ ↦ sq_nonneg _)]
  simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs]

private theorem operator_weightVector (D : ℝ) :
    (⟪weightVector D, primeWindowOperator D (weightVector D)⟫_ℂ).re =
      ∫ x in wSet D, primeTranslationApply D (endpointWeight D) x * endpointWeight D x := by
  let w := weightVector D
  let r := endpointWeight D
  have hf : (∫ x, ⟪w x, primeWindowOperator D w x⟫_ℂ) =
      ∫ x in wSet D, (↑(primeTranslationApply D r x * r x) : ℂ) := by
    have hz : ∀ᵐ x ∂volume, x ∉ wSet D → ⟪w x, primeWindowOperator D w x⟫_ℂ = 0 :=
      (support_weightVector D).mono fun x hx h ↦ by rw [hx h, inner_zero_left]
    rw [← setIntegral_eq_integral_of_ae_compl_eq_zero hz]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Icc, ae_restrict_of_ae (weightVector_ae D),
      ae_restrict_of_ae (primeWindowOperator_ae D w),
      ae_restrict_of_ae (sum_ae_congr D (weightVector_ae D))] with x hx hw hT hsum
    rw [RCLike.inner_apply, hw, Complex.conj_ofReal, hT, Set.indicator_of_mem hx, hsum]
    simp only [r, primeTranslationComplexApply, primeTranslationApply, Complex.ofReal_mul,
      Complex.ofReal_sum, Complex.ofReal_add]
  rw [L2.inner_def, hf]
  exact congrArg Complex.re (integral_ofReal (𝕜 := ℂ) (f := fun x ↦ primeTranslationApply D r x * r x))

private theorem operator_quadratic_smul {D : ℝ} {u : 𝓗} (hu : PrimeWindowSupported D u) (a : ℝ) :
    (⟪(a : ℂ) • u, primeWindowOperator D ((a : ℂ) • u)⟫_ℂ).re =
      a ^ 2 * (⟪u, primeWindowOperator D u⟫_ℂ).re := by
  rw [inner_smul_left, operator_symmetric (support_smul hu _) hu, inner_smul_right,
    ← operator_symmetric hu hu, Complex.conj_ofReal, ← mul_assoc, ← pow_two, ← Complex.ofReal_pow,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

private noncomputable def unitWeight (D : ℝ) : 𝓗 := ((‖weightVector D‖⁻¹ : ℝ) : ℂ) • weightVector D

private theorem support_unitWeight (D : ℝ) : PrimeWindowSupported D (unitWeight D) :=
  support_smul (support_weightVector D) _

private theorem norm_unitWeight {D : ℝ} (hD : 0 < D) : ‖unitWeight D‖ = 1 := by
  rw [unitWeight, norm_smul, Complex.norm_real,
    Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _)), inv_mul_cancel₀ (norm_weightVector_pos hD).ne']

private theorem unitWeight_rayleigh : Tendsto (fun D : ℝ ↦
    exp (-(D / 2)) * (⟪unitWeight D, primeWindowOperator D (unitWeight D)⟫_ℂ).re) atTop (𝓝 1) := by
  refine primeTranslationRayleigh.congr fun D ↦ ?_
  change (∫ x in wSet D, primeTranslationApply D (endpointWeight D) x * endpointWeight D x) /
    (exp (D / 2) * ∫ x in wSet D, endpointWeight D x ^ 2) = _
  rw [← operator_weightVector, ← weightVector_sq, unitWeight,
    operator_quadratic_smul (support_weightVector D), Real.exp_neg, inv_pow, div_eq_mul_inv, mul_inv]
  ring

private def correctedValues (D : ℝ) : Set ℝ :=
  {r | ∃ u : 𝓗, PrimeWindowSupported D u ∧ ‖u‖ = 1 ∧
    r = (⟪u, primeWindowOperator D u⟫_ℂ).re - primeWindowPoleQuadratic D u}

/-- The whole-window real Rayleigh supremum of the strict-cutoff untwisted
prime operator minus the two-pole quadratic, divided by `exp (D / 2)`, tends
to one. The supremum is over all supported complex `L²` unit vectors. -/
public theorem primeWindowCorrectedRayleighLimit :
    Tendsto (fun D : ℝ ↦ exp (-(D / 2)) * sSup
      {r | ∃ u : 𝓗, PrimeWindowSupported D u ∧ ‖u‖ = 1 ∧
        r = (⟪u, primeWindowOperator D u⟫_ℂ).re - primeWindowPoleQuadratic D u}) atTop (𝓝 1) := by
  change Tendsto (fun D : ℝ ↦ exp (-(D / 2)) * sSup (correctedValues D)) atTop (𝓝 1)
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hη : 0 < ε / 8 := by positivity
  filter_upwards [corrected_upper hη, eventually_gt_atTop (0 : ℝ),
    Metric.tendsto_nhds.mp unitWeight_rayleigh (ε / 2) (half_pos hε)] with D hbound hD hw
  have hsup (y : ℝ) (hy : y ∈ correctedValues D) : y ≤ (1 + 3 * (ε / 8)) * exp (D / 2) := by
    obtain ⟨u, hu, hu₁, rfl⟩ := hy
    exact hbound u hu hu₁
  have hb : BddAbove (correctedValues D) := ⟨_, hsup⟩
  have hn : (correctedValues D).Nonempty :=
    ⟨_, unitWeight D, support_unitWeight D, norm_unitWeight hD, rfl⟩
  have hE : exp (-(D / 2)) * exp (D / 2) = 1 := by
    rw [Real.exp_neg, inv_mul_cancel₀ (Real.exp_pos _).ne']
  have hupp : exp (-(D / 2)) * sSup (correctedValues D) ≤ 1 + 3 * (ε / 8) := by
    calc
      _ ≤ exp (-(D / 2)) * ((1 + 3 * (ε / 8)) * exp (D / 2)) :=
        mul_le_mul_of_nonneg_left (csSup_le hn hsup) (Real.exp_pos _).le
      _ = _ := by rw [mul_left_comm, hE, mul_one]
  obtain ⟨v, hv, hv₁, htest⟩ := corrected_lower_test hD (unitWeight D) (support_unitWeight D)
    (norm_unitWeight hD) (ε := ε / 4 * exp (D / 2)) (by positivity)
  have hvle := le_csSup hb (show _ ∈ correctedValues D from ⟨v, hv, hv₁, rfl⟩)
  have hlo := mul_le_mul_of_nonneg_left (htest.trans hvle) (Real.exp_pos (-(D / 2))).le
  rw [mul_sub, mul_left_comm (exp (-(D / 2))) (ε / 4), hE, mul_one] at hlo
  simp only [Real.dist_eq, abs_lt] at hw ⊢
  exact ⟨by linarith only [hlo, hw.1, hε], by linarith only [hupp, hε]⟩

end Masullo
