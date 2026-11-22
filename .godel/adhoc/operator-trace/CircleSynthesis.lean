import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.PSeries

/-!
# Fourier coefficient bounds for periodized output profiles

Use a single period `[a,b]` with matching value and first derivative at its endpoints.
In a fixed-annulus application the real profiles vanish near both endpoints. The
estimates use the normalized Haar measure on the circle of length `b - a` and
require no information about how the profiles were produced.
-/

open Set MeasureTheory Complex
open scoped ContDiff Topology

namespace AdHoc

/-- Descend a continuous real-periodic function to the quotient circle. -/
def periodicProfile {T : ℝ} {f : ℝ → ℂ} (hf : Continuous f)
    (hp : Function.Periodic f T) : C(AddCircle T, ℂ) where
  toFun := hp.lift
  continuous_toFun := continuous_coinduced_dom.mpr hf

@[simp] theorem periodicProfile_apply {T : ℝ} {f : ℝ → ℂ} (hf : Continuous f)
    (hp : Function.Periodic f T) (x : ℝ) : periodicProfile hf hp (x : AddCircle T) = f x :=
  hp.lift_coe x

/-- Pointwise synthesis of a continuous periodic function with absolutely summable coefficients. -/
theorem hasSum_periodicProfile {T : ℝ} [Fact (0 < T)] {f : ℝ → ℂ} (hf : Continuous f)
    (hp : Function.Periodic f T)
    (hs : Summable fun n => ‖fourierCoeff (periodicProfile hf hp) n‖) (x : ℝ) :
    HasSum (fun n => fourierCoeff (periodicProfile hf hp) n * fourier n (x : AddCircle T))
      (f x) := by
  simpa only [periodicProfile_apply, smul_eq_mul] using
    has_pointwise_sum_fourier_series_of_summable hs.of_norm (x : AddCircle T)

variable {a b : ℝ}

private theorem norm_fourierCoeffOn_le (hab : a < b) {f : ℝ → ℂ} {M : ℝ}
    (hM : ∀ x ∈ Icc a b, ‖f x‖ ≤ M) (n : ℤ) : ‖fourierCoeffOn hab f n‖ ≤ M := by
  have hL : 0 < b - a := sub_pos.mpr hab
  rw [fourierCoeffOn_eq_integral, norm_smul, Real.norm_of_nonneg (by positivity)]
  calc
    _ ≤ (1 / (b - a)) * (M * (b - a)) := by
      gcongr
      rw [← abs_of_pos hL]
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro x hx
      rw [norm_smul, fourier_apply, Circle.norm_coe, one_mul]
      exact hM x (Ioc_subset_Icc_self (by simpa only [uIoc_of_le hab.le] using hx))
    _ = M := by field_simp

/-- One integration by parts, with the boundary term canceled by matching endpoint values. -/
theorem fourierCoeffOn_eq_mul_deriv_of_endpoints (hab : a < b) {f g : ℝ → ℂ}
    (hd : ∀ x ∈ Icc a b, HasDerivAt f (g x) x) (hg : ContinuousOn g (Icc a b))
    (he : f b = f a) {n : ℤ} (hn : n ≠ 0) :
    fourierCoeffOn hab f n = ((b - a : ℝ) : ℂ) / (2 * (Real.pi : ℂ) * I * n) * fourierCoeffOn hab g n := by
  rw [fourierCoeffOn_of_hasDerivAt hab hn (by simpa [uIcc_of_le hab.le] using hd)
    (ContinuousOn.intervalIntegrable (by simpa [uIcc_of_le hab.le] using hg))]
  simp only [he, sub_self, mul_zero, zero_sub, neg_mul, div_neg, one_div, Complex.ofReal_sub]
  ring

/-- Two integrations by parts give the inverse-square bound. The first derivative
must also match at the endpoints, so neither integration contributes a boundary term. -/
theorem norm_fourierCoeffOn_le_inv_sq (hab : a < b) {f g h : ℝ → ℂ}
    (hd : ∀ x ∈ Icc a b, HasDerivAt f (g x) x)
    (hg : ∀ x ∈ Icc a b, HasDerivAt g (h x) x) (hh : ContinuousOn h (Icc a b))
    (he : f b = f a) (hge : g b = g a) {M : ℝ} (hM : ∀ x ∈ Icc a b, ‖h x‖ ≤ M)
    {n : ℤ} (hn : n ≠ 0) :
    ‖fourierCoeffOn hab f n‖ ≤ ((b - a) / (2 * Real.pi)) ^ 2 * M / (n : ℝ) ^ 2 := by
  rw [fourierCoeffOn_eq_mul_deriv_of_endpoints hab hd
    (fun x hx => (hg x hx).continuousAt.continuousWithinAt) he hn,
    fourierCoeffOn_eq_mul_deriv_of_endpoints hab hg hh hge hn, ← mul_assoc, norm_mul]
  have hL : 0 < b - a := sub_pos.mpr hab
  calc
    _ ≤ _ * M := mul_le_mul_of_nonneg_left (norm_fourierCoeffOn_le hab hM n) (norm_nonneg _)
    _ = _ := by
      simp only [norm_mul, norm_div, Complex.norm_real, norm_I, mul_one, Complex.norm_intCast,
        Real.norm_eq_abs, abs_of_pos hL, abs_of_pos Real.pi_pos]
      norm_num only [Complex.norm_ofNat]
      rw [← pow_two, div_pow, mul_pow (2 * Real.pi), sq_abs, div_mul_eq_mul_div,
        div_pow, div_mul_eq_mul_div, div_div]

private theorem summable_of_inv_sq {u : ℤ → ℝ} (hu : ∀ n, 0 ≤ u n) {K : ℝ}
    (h : ∀ n : ℤ, n ≠ 0 → u n ≤ K / (n : ℝ) ^ 2) : Summable u := by
  have hsq := (Real.summable_one_div_int_pow (p := 2)).2 (by decide)
  have hzero : Summable (fun n : ℤ => if n = 0 then u 0 else 0) :=
    (hasSum_ite_eq 0 (u 0)).summable
  apply (hzero.add (hsq.mul_left K)).of_nonneg_of_le hu
  intro n
  by_cases hn : n = 0
  · subst n
    simp
  · simpa only [ite_eq_right hn, zero_add, mul_one_div] using h n hn

private theorem fourierCoeffOn_congr_right {c : ℝ} (h : b = c) (hab : a < b) (hac : a < c)
    (f : ℝ → ℂ) (n : ℤ) : fourierCoeffOn hab f n = fourierCoeffOn hac f n := by
  subst c
  rfl

/-- For a continuous real-periodic profile the interval and circle coefficients agree. -/
theorem fourierCoeff_periodicProfile_eq {T : ℝ} [hT : Fact (0 < T)] {f : ℝ → ℂ}
    (hf : Continuous f) (hp : Function.Periodic f T) (n : ℤ) :
    fourierCoeff (periodicProfile hf hp) n = fourierCoeffOn hT.out f n := by
  have h : (periodicProfile hf hp : AddCircle T → ℂ) = AddCircle.liftIoc T 0 f := by
    funext z
    let x := AddCircle.equivIoc T 0 z
    have hx : ((x : ℝ) : AddCircle T) = z := AddCircle.coe_equivIoc
    rw [← hx, periodicProfile_apply, AddCircle.liftIoc_coe_apply x.property]
  rw [h, fourierCoeff_liftIoc_eq]
  exact fourierCoeffOn_congr_right (zero_add T) _ _ f n

/-- A `C²` profile with matched endpoint values and first derivatives has absolutely
summable coefficients on that period. -/
theorem summable_norm_fourierCoeffOn_of_contDiff (hab : a < b) {f : ℝ → ℂ}
    (hf : ContDiff ℝ 2 f) (he : f b = f a) (hde : deriv f b = deriv f a) :
    Summable fun n => ‖fourierCoeffOn hab f n‖ := by
  have hfd : ContDiff ℝ 1 (deriv f) := hf.deriv'
  have hdd : Continuous (deriv (deriv f)) := hfd.continuous_deriv_one
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (s := Icc a b) hdd.continuousOn
  refine summable_of_inv_sq (fun _ => norm_nonneg _) (K := ((b - a) / (2 * Real.pi)) ^ 2 * M)
    fun n hn => ?_
  exact norm_fourierCoeffOn_le_inv_sq hab
    (fun x _ => (hf.differentiable (by decide) x).hasDerivAt)
    (fun x _ => (hfd.differentiable (by decide) x).hasDerivAt) hdd.continuousOn he hde hM hn

/-- A periodic `C²` profile has absolutely summable Fourier coefficients. -/
theorem summable_norm_fourierCoeff_periodicProfile {T : ℝ} [hT : Fact (0 < T)] {f : ℝ → ℂ}
    (hf : ContDiff ℝ 2 f) (hp : Function.Periodic f T) :
    Summable fun n => ‖fourierCoeff (periodicProfile hf.continuous hp) n‖ := by
  have hpd : Function.Periodic (deriv f) T := fun x => by
    rw [← deriv_comp_add_const f T x, show (fun y => f (y + T)) = f from funext hp]
  simp only [fourierCoeff_periodicProfile_eq]
  exact summable_norm_fourierCoeffOn_of_contDiff hT.out hf
    (by simpa only [zero_add] using hp 0) (by simpa only [zero_add] using hpd 0)

/-- The scalar coefficients of a periodic `C²` profile are summable in `ℂ`. -/
theorem summable_fourierCoeff_periodicProfile {T : ℝ} [Fact (0 < T)] {f : ℝ → ℂ}
    (hf : ContDiff ℝ 2 f) (hp : Function.Periodic f T) :
    Summable (fourierCoeff (periodicProfile hf.continuous hp)) :=
  (summable_norm_fourierCoeff_periodicProfile hf hp).of_norm

/-- A `C²` function supported strictly inside one period gives a continuous circle profile
with absolutely summable coefficients, agreeing with the original function on the cell. -/
theorem exists_circleProfile_of_support {T a u w : ℝ} [hT : Fact (0 < T)] {f : ℝ → ℂ}
    (hf : ContDiff ℝ 2 f) (hs : Function.support f ⊆ Icc u w) (ha : a < u) (hb : w < a + T) :
    ∃ F : C(AddCircle T, ℂ),
      EqOn (fun x : ℝ => F (x : AddCircle T)) f (Icc a (a + T)) ∧
      Summable (fourierCoeff F) := by
  have hzero {t : ℝ} (ht : t ∉ Icc u w) : f t = 0 :=
    Function.notMem_support.mp fun ht' => ht (hs ht')
  have hdzero {t : ℝ} (ht : t ∉ Icc u w) : deriv f t = 0 := by
    have he : f =ᶠ[𝓝 t] (fun _ => 0) :=
      Filter.eventually_of_mem (U := (Icc u w)ᶜ) (isClosed_Icc.isOpen_compl.mem_nhds ht)
        fun _ hx => hzero hx
    simpa using he.deriv_eq
  have hleft : a ∉ Icc u w := fun h => (not_le_of_gt ha) h.1
  have hright : a + T ∉ Icc u w := fun h => (not_le_of_gt hb) h.2
  have he : f a = f (a + T) := (hzero hleft).trans (hzero hright).symm
  let F : C(AddCircle T, ℂ) :=
    ⟨AddCircle.liftIoc T a f, AddCircle.liftIoc_continuous he hf.continuous.continuousOn⟩
  refine ⟨F, ?_, ?_⟩
  · intro x hx
    change AddCircle.liftIoc T a f (x : AddCircle T) = f x
    rcases eq_or_lt_of_le hx.1 with h | h
    · subst x
      rw [← AddCircle.coe_add_period T a,
        AddCircle.liftIoc_coe_apply ⟨lt_add_of_pos_right a hT.out, le_rfl⟩, he]
    · exact AddCircle.liftIoc_coe_apply ⟨h, hx.2⟩
  · change Summable (fourierCoeff (AddCircle.liftIoc T a f))
    have hcoeff : fourierCoeff (AddCircle.liftIoc T a f) =
        fourierCoeffOn (lt_add_of_pos_right a hT.out) f :=
      funext (fourierCoeff_liftIoc_eq f)
    rw [hcoeff]
    exact (summable_norm_fourierCoeffOn_of_contDiff (lt_add_of_pos_right a hT.out) hf he.symm
      ((hdzero hright).trans (hdzero hleft).symm)).of_norm

section CoefficientFunctionals

variable {T : ℝ} [Fact (0 < T)]

private theorem norm_fourierCoeff_le (f : C(AddCircle T, ℂ)) (n : ℤ) :
    ‖fourierCoeff f n‖ ≤ ‖f‖ := by
  rw [fourierCoeff]
  have h : ∀ z : AddCircle T, ‖fourier (-n) z • f z‖ ≤ ‖f‖ := by
    intro z
    rw [norm_smul, fourier_apply, Circle.norm_coe, one_mul]
    exact f.norm_coe_le_norm z
  simpa using norm_integral_le_of_norm_le_const (ae_of_all AddCircle.haarAddCircle h)

/-- Extracting one Fourier coefficient is a continuous linear functional on the circle profiles. -/
noncomputable def fourierCoeffCLM (n : ℤ) : C(AddCircle T, ℂ) →L[ℂ] ℂ :=
  ({ toFun f := fourierCoeff f n
     map_add' f g := by
       have hint (h : C(AddCircle T, ℂ)) : Integrable h AddCircle.haarAddCircle :=
         h.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace h)
       exact congrFun (fourierCoeff.add (hint f) (hint g)) n
     map_smul' c f := fourierCoeff.const_smul f c n } : C(AddCircle T, ℂ) →ₗ[ℂ] ℂ).mkContinuous
    1 (fun f => by
      change ‖fourierCoeff f n‖ ≤ 1 * ‖f‖
      rw [one_mul]
      exact norm_fourierCoeff_le f n)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The coefficient functional of the output of a bounded linear profile operator. -/
noncomputable def fourierCoeffFunctional (A : E →L[ℂ] C(AddCircle T, ℂ)) (n : ℤ) : E →L[ℂ] ℂ :=
  (fourierCoeffCLM n).comp A

@[simp] theorem fourierCoeffFunctional_apply (A : E →L[ℂ] C(AddCircle T, ℂ)) (n : ℤ) (v : E) :
    fourierCoeffFunctional A n v = fourierCoeff (A v) n := rfl

/-- The zero mode is controlled by the profile operator's sup-norm bound. -/
theorem norm_fourierCoeffFunctional_zero_le (A : E →L[ℂ] C(AddCircle T, ℂ)) :
    ‖fourierCoeffFunctional A 0‖ ≤ ‖A‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun v => ?_
  exact (norm_fourierCoeff_le (A v) 0).trans (A.le_opNorm v)

/-- Norm summability of the coefficient functionals gives synthesis for every input. -/
theorem hasSum_fourierCoeffFunctional (A : E →L[ℂ] C(AddCircle T, ℂ))
    (h : Summable fun n => ‖fourierCoeffFunctional A n‖) (v : E) (z : AddCircle T) :
    HasSum (fun n => fourierCoeffFunctional A n v * fourier n z) (A v z) := by
  have hv : Summable fun n => ‖fourierCoeff (A v) n‖ :=
    (h.mul_right ‖v‖).of_nonneg_of_le (fun _ => norm_nonneg _) fun n =>
      (fourierCoeffFunctional A n).le_opNorm v
  simpa only [fourierCoeffFunctional_apply, smul_eq_mul] using
    has_pointwise_sum_fourier_series_of_summable hv.of_norm z

end CoefficientFunctionals

section IntervalProfiles

private theorem add_period_eq_right : a + (b - a) = b := by ring

private theorem endpoints_eq_on_circle : (b : AddCircle (b - a)) = (a : AddCircle (b - a)) := by
  simpa only [add_period_eq_right] using AddCircle.coe_add_period (b - a) a

variable [hL : Fact (0 < b - a)]

/-- Periodize a profile specified on one interval. Only the values at the seam must match
for continuity; derivative matching is handled separately by the decay estimate. -/
noncomputable def intervalProfile {f : ℝ → ℂ} (hf : ContinuousOn f (Icc a b)) (he : f b = f a) :
    C(AddCircle (b - a), ℂ) where
  toFun := AddCircle.liftIoc (b - a) a f
  continuous_toFun := AddCircle.liftIoc_continuous
    (by simpa only [add_period_eq_right] using he.symm)
    (by simpa only [add_period_eq_right] using hf)

theorem intervalProfile_apply {f : ℝ → ℂ} (hf : ContinuousOn f (Icc a b)) (he : f b = f a)
    {x : ℝ} (hx : x ∈ Icc a b) : intervalProfile hf he (x : AddCircle (b - a)) = f x := by
  have happly (y : ℝ) (hy : y ∈ Ioc a b) :
      intervalProfile hf he (y : AddCircle (b - a)) = f y :=
    AddCircle.liftIoc_coe_apply (by simpa only [add_period_eq_right] using hy)
  rcases eq_or_lt_of_le hx.1 with h | h
  · subst x
    rw [← endpoints_eq_on_circle, happly b ⟨sub_pos.mp hL.out, le_rfl⟩, he]
  · exact happly x ⟨h, hx.2⟩

private theorem fourierCoeff_eq_fourierCoeffOn_of_eqOn {u : AddCircle (b - a) → ℂ} {f : ℝ → ℂ}
    (hf : EqOn (fun x : ℝ => u (x : AddCircle (b - a))) f (Icc a b)) (n : ℤ) :
    fourierCoeff u n = fourierCoeffOn (sub_pos.mp hL.out) f n := by
  have h : u = AddCircle.liftIoc (b - a) a f := by
    funext z
    let x := AddCircle.equivIoc (b - a) a z
    have hx : ((x : ℝ) : AddCircle (b - a)) = z := AddCircle.coe_equivIoc
    rw [← hx, AddCircle.liftIoc_coe_apply x.property]
    apply hf
    simpa only [add_period_eq_right] using Ioc_subset_Icc_self x.property
  rw [h, fourierCoeff_liftIoc_eq]
  exact fourierCoeffOn_congr_right (add_period_eq_right (a := a) (b := b)) _ _ f n

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- A linear family of continuous profiles with matching endpoints and a uniform zeroth-order
bound gives a bounded linear operator into the continuous functions on the circle. -/
noncomputable def intervalProfileCLM (F : E →ₗ[ℂ] (ℝ → ℂ))
    (hc : ∀ v, ContinuousOn (F v) (Icc a b)) (he : ∀ v, F v b = F v a) {M₀ : ℝ}
    (h₀ : ∀ v x, x ∈ Icc a b → ‖F v x‖ ≤ M₀ * ‖v‖) : E →L[ℂ] C(AddCircle (b - a), ℂ) :=
  ({ toFun v := intervalProfile (hc v) (he v)
     map_add' u v := by
       ext1 z
       exact congrFun (F.map_add u v) (AddCircle.equivIoc (b - a) a z)
     map_smul' c v := by
       ext1 z
       exact congrFun (F.map_smul c v) (AddCircle.equivIoc (b - a) a z) } :
    E →ₗ[ℂ] C(AddCircle (b - a), ℂ)).mkContinuous M₀ (fun v => by
      refine (ContinuousMap.norm_le_of_nonempty _).mpr fun z => ?_
      change ‖F v (AddCircle.equivIoc (b - a) a z)‖ ≤ M₀ * ‖v‖
      apply h₀
      simpa only [add_period_eq_right] using
        Ioc_subset_Icc_self (AddCircle.equivIoc (b - a) a z).property)

theorem intervalProfileCLM_apply (F : E →ₗ[ℂ] (ℝ → ℂ))
    (hc : ∀ v, ContinuousOn (F v) (Icc a b)) (he : ∀ v, F v b = F v a) {M₀ : ℝ}
    (h₀ : ∀ v x, x ∈ Icc a b → ‖F v x‖ ≤ M₀ * ‖v‖) (v : E) {x : ℝ} (hx : x ∈ Icc a b) :
    intervalProfileCLM F hc he h₀ v (x : AddCircle (b - a)) = F v x :=
  intervalProfile_apply (hc v) (he v) hx

/-- A common second-derivative bound for the output profiles on the input unit ball gives
inverse-square decay in **operator norm**. The functions `f v` are real-coordinate representatives
of `A v` on one period. Outside that interval they need not be periodic. -/
theorem norm_fourierCoeffFunctional_le_inv_sq (A : E →L[ℂ] C(AddCircle (b - a), ℂ))
    {f g h : E → ℝ → ℂ}
    (hf : ∀ v, EqOn (fun x : ℝ => A v (x : AddCircle (b - a))) (f v) (Icc a b))
    (hd : ∀ v, ‖v‖ ≤ 1 → ∀ x ∈ Icc a b, HasDerivAt (f v) (g v x) x)
    (hg : ∀ v, ‖v‖ ≤ 1 → ∀ x ∈ Icc a b, HasDerivAt (g v) (h v x) x)
    (hh : ∀ v, ‖v‖ ≤ 1 → ContinuousOn (h v) (Icc a b))
    (hge : ∀ v, ‖v‖ ≤ 1 → g v b = g v a)
    {M : ℝ} (hM : 0 ≤ M) (hbound : ∀ v, ‖v‖ ≤ 1 → ∀ x ∈ Icc a b, ‖h v x‖ ≤ M)
    {n : ℤ} (hn : n ≠ 0) :
    ‖fourierCoeffFunctional A n‖ ≤ ((b - a) / (2 * Real.pi)) ^ 2 * M / (n : ℝ) ^ 2 := by
  have hab := sub_pos.mp hL.out
  refine ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity) fun v hv => ?_
  have hv' : ‖v‖ ≤ 1 := hv.le
  have he : f v b = f v a := by
    calc
      f v b = A v (b : AddCircle (b - a)) := (hf v (right_mem_Icc.mpr hab.le)).symm
      _ = A v (a : AddCircle (b - a)) := congrArg (A v) endpoints_eq_on_circle
      _ = f v a := hf v (left_mem_Icc.mpr hab.le)
  rw [fourierCoeffFunctional_apply, fourierCoeff_eq_fourierCoeffOn_of_eqOn (hf v)]
  exact norm_fourierCoeffOn_le_inv_sq hab (hd v hv') (hg v hv') (hh v hv') he (hge v hv')
    (hbound v hv') hn

/-- The coefficient functionals are absolutely summable in operator norm, with the zero
mode handled separately from the inverse-square tail. -/
theorem summable_norm_fourierCoeffFunctional (A : E →L[ℂ] C(AddCircle (b - a), ℂ))
    {f g h : E → ℝ → ℂ}
    (hf : ∀ v, EqOn (fun x : ℝ => A v (x : AddCircle (b - a))) (f v) (Icc a b))
    (hd : ∀ v, ‖v‖ ≤ 1 → ∀ x ∈ Icc a b, HasDerivAt (f v) (g v x) x)
    (hg : ∀ v, ‖v‖ ≤ 1 → ∀ x ∈ Icc a b, HasDerivAt (g v) (h v x) x)
    (hh : ∀ v, ‖v‖ ≤ 1 → ContinuousOn (h v) (Icc a b))
    (hge : ∀ v, ‖v‖ ≤ 1 → g v b = g v a)
    {M : ℝ} (hM : 0 ≤ M) (hbound : ∀ v, ‖v‖ ≤ 1 → ∀ x ∈ Icc a b, ‖h v x‖ ≤ M) :
    Summable fun n => ‖fourierCoeffFunctional A n‖ :=
  summable_of_inv_sq (fun _ => norm_nonneg _) fun _ hn =>
    norm_fourierCoeffFunctional_le_inv_sq A hf hd hg hh hge hM hbound hn

end IntervalProfiles

end AdHoc
