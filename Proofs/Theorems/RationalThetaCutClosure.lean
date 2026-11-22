module

public import Lemmas.RationalThetaWeightedLog
public import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! # One-prime differences after a log-position cutoff

On the zero line the unramified real dilation is `b(y) ↦ b(p * y)`, with no
Mellin scalar. Its theta profile translates forward by `log p` before the
weight is applied. On a cutoff bounded below this sends the escaping term of
the finite forward telescope into the rapidly decaying end of the profile.
-/

open Filter MeasureTheory Set
open scoped FourierTransform SchwartzMap Topology

namespace Masullo

local notation "LogL2" => Lp ℂ 2 (volume : Measure ℝ)

/-- Multiplication by a measurable indicator on the log-line `L²` space.
This uses `MemLp.indicator` to work with classes, not a choice of pointwise
representative of a generator. -/
public noncomputable def rationalThetaLogCut {S : Set ℝ} (hS : MeasurableSet S)
    (u : LogL2) : LogL2 :=
  (MemLp.indicator hS.nullMeasurableSet (Lp.memLp u)).toLp (S.indicator u)

public theorem rationalThetaLogCut_ae {S : Set ℝ} (hS : MeasurableSet S) (u : LogL2) :
    ⇑(rationalThetaLogCut hS u) =ᵐ[volume] S.indicator u :=
  (MemLp.indicator hS.nullMeasurableSet (Lp.memLp u)).coeFn_toLp

/-- Rapid decay to the right, in the exact zero-line polynomially weighted
norm. The cutoff need not have finite measure. `U` denotes actual `L²`
classes with the indicated representatives. -/
public theorem tendsto_zeroLineWeightedLog_cut_translate {S : Set ℝ} {A d s : ℝ}
    (hs : 0 ≤ s) (hS : S ⊆ Ici A) (hd : 0 < d) (f : ℝ → ℂ)
    (hdecay : ∀ N : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ,
      ‖f x‖ ≤ C * Real.exp (-(N : ℝ) * |x|))
    (U : ℕ → LogL2)
    (hU : ∀ n, ⇑(U n) =ᵐ[volume] S.indicator (fun x ↦
      (symmetricStripWeightRoot 0 s x : ℂ) * f (x + (n : ℝ) * d))) :
    Tendsto U atTop (𝓝 0) := by
  obtain ⟨N, hN⟩ := exists_nat_gt (s + 1)
  have hNpos : (0 : ℝ) < N := by linarith
  obtain ⟨C, hC, hf⟩ := hdecay N
  let w := symmetricStripWeightRoot 0 s
  let g (x : ℝ) := Real.exp (-(N : ℝ) * |x|)
  have hg : Continuous g := by dsimp [g]; fun_prop
  have hw (x : ℝ) : 0 ≤ w x := (symmetricStripWeightRoot_pos ..).le
  have hg0 (x : ℝ) : 0 ≤ g x := (Real.exp_pos _).le
  have hmem : MemLp (fun x ↦ w x * g x) 2 volume := by
    apply (memLp_two_iff_integrable_sq_norm
      ((continuous_symmetricStripWeightRoot 0 s).mul hg).aestronglyMeasurable).2
    have hI := integrable_hardySobolevWeight_mul_norm_sq (α := 0) (β := 0)
      (C := 1) (N := (N : ℝ)) (Complex.continuous_ofReal.comp hg) hs
      (by simp; linarith) (fun x ↦ by
        change ‖(g x : ℂ)‖ ≤ 1 * g x
        rw [Complex.norm_real, Real.norm_of_nonneg (hg0 x), one_mul])
    convert hI using 1
    ext x
    simp only [Pi.mul_apply, Function.comp_apply, Complex.norm_real,
      Real.norm_of_nonneg (hg0 x), mul_zero, zero_mul, Real.exp_zero, max_self, mul_one]
    change ‖w x * g x‖ ^ 2 = _
    rw [Real.norm_of_nonneg (mul_nonneg (hw x) (hg0 x)), mul_pow,
      show w x ^ 2 = (1 + x ^ 2) ^ (s / 2) by
        simpa [w] using symmetricStripWeightRoot_sq 0 s x, mul_comm]
  let M := hmem.toLp _
  let r (n : ℕ) := (C * Real.exp ((N : ℝ) * (2 * |A|))) * Real.exp (-(N : ℝ) * ((n : ℝ) * d))
  have hr (n : ℕ) : 0 ≤ r n := by dsimp [r]; positivity
  have hbound (n : ℕ) : ‖U n‖ ≤ r n * ‖M‖ := by
    rw [← Real.norm_of_nonneg (hr n), ← norm_smul]
    apply Lp.norm_le_norm_of_ae_le
    filter_upwards [hU n, hmem.coeFn_toLp, Lp.coeFn_smul (r n) M] with x hx hM hsmul
    change M x = _ at hM
    rw [hx, hsmul, Pi.smul_apply, smul_eq_mul, hM,
      Real.norm_of_nonneg (mul_nonneg (hr n) (mul_nonneg (hw x) (hg0 x)))]
    by_cases hxS : x ∈ S
    · rw [indicator_of_mem hxS, norm_mul, Complex.norm_real, Real.norm_of_nonneg (hw x)]
      have hxA : A ≤ x := hS hxS
      have habs : |x| ≤ x + 2 * |A| := abs_le.mpr
        ⟨by linarith [neg_abs_le A], by linarith [abs_nonneg A]⟩
      have hexp : Real.exp (-(N : ℝ) * |x + (n : ℝ) * d|) ≤
          Real.exp ((N : ℝ) * (2 * |A|)) * Real.exp (-(N : ℝ) * ((n : ℝ) * d)) * g x := by
        rw [show g x = _ by rfl, ← Real.exp_add, ← Real.exp_add, Real.exp_le_exp]
        have h := (le_abs_self (x + (n : ℝ) * d))
        nlinarith [mul_le_mul_of_nonneg_left h hNpos.le,
          mul_le_mul_of_nonneg_left habs hNpos.le]
      calc
        _ ≤ w x * (C * Real.exp (-(N : ℝ) * |x + (n : ℝ) * d|)) :=
          mul_le_mul_of_nonneg_left (hf _) (hw x)
        _ ≤ w x * (C * (Real.exp ((N : ℝ) * (2 * |A|)) *
            Real.exp (-(N : ℝ) * ((n : ℝ) * d)) * g x)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hexp hC.le) (hw x)
        _ = r n * (w x * g x) := by dsimp [r]; ring
    · rw [indicator_of_notMem hxS, norm_zero]
      exact mul_nonneg (hr n) (mul_nonneg (hw x) (hg0 x))
  have hexp : Tendsto (fun n : ℕ ↦ Real.exp (-(N : ℝ) * ((n : ℝ) * d))) atTop (𝓝 0) := by
    apply Real.tendsto_exp_atBot.comp
    have h := ((tendsto_natCast_atTop_atTop (R := ℝ)).atTop_mul_const hd).atTop_mul_const hNpos
    simpa only [Function.comp_def, neg_mul, mul_comm _ (N : ℝ)] using
      tendsto_neg_atTop_atBot.comp h
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  refine squeeze_zero (fun _ ↦ norm_nonneg _) hbound ?_
  simpa [r] using ((tendsto_const_nhds.mul hexp).mul
    (tendsto_const_nhds (x := ‖M‖)))

/-- A finite forward sum realizes the approximation by a *single* difference,
not just by a member of the linear span of the difference range. -/
public theorem closure_range_sub_iterate_eq {E H : Type*} [AddCommGroup E]
    [AddCommGroup H] [TopologicalSpace H] [IsTopologicalAddGroup H]
    (D : E →+ E) (F : E →+ H) (h : ∀ b, Tendsto (fun n : ℕ ↦ F (D^[n] b)) atTop (𝓝 0)) :
    closure (range (fun b ↦ F (b - D b))) = closure (range F) := by
  refine Subset.antisymm (closure_mono ?_) (closure_minimal ?_ isClosed_closure)
  · rintro _ ⟨b, rfl⟩
    exact ⟨b - D b, rfl⟩
  · rintro _ ⟨b, rfl⟩
    apply mem_closure_of_tendsto (show Tendsto (fun n : ℕ ↦ F b - F (D^[n] b))
        atTop (𝓝 (F b)) by simpa using tendsto_const_nhds.sub (h b))
    refine Eventually.of_forall fun n ↦ ⟨∑ i ∈ Finset.range n, D^[i] b, ?_⟩
    dsimp only
    rw [map_sum, ← Finset.sum_sub_distrib]
    simp only [← Function.iterate_succ_apply']
    rw [Finset.sum_range_sub', Function.iterate_zero_apply, map_sub]

/-- The even real Schwartz generators with vanishing value and Fourier value at zero. -/
@[expose] public def rationalEvenThetaInputs : AddSubgroup 𝓢(ℝ, ℂ) where
  carrier := {b : 𝓢(ℝ, ℂ) | Function.Even (⇑b) ∧ b 0 = (0 : ℂ) ∧ (𝓕 b) 0 = (0 : ℂ)}
  zero_mem' := by simp [Function.Even]
  add_mem' := by
    rintro b c ⟨hb, h₀b, hFb⟩ ⟨hc, h₀c, hFc⟩
    exact ⟨fun x ↦ by simp [_root_.add_apply, hb x, hc x],
      by simp [_root_.add_apply, h₀b, h₀c], by simp [FourierAdd.fourier_add, hFb, hFc]⟩
  neg_mem' := by
    rintro b ⟨hb, h₀b, hFb⟩
    exact ⟨fun x ↦ by simp [_root_.neg_apply, hb x], by simp [_root_.neg_apply, h₀b],
      by simp [hFb]⟩

/-- Forward dilation preserves the admissible generators. The value at zero
is unchanged; the Fourier value at zero picks up the factor `q⁻¹`. -/
public noncomputable def rationalEvenThetaDilation {q : ℝ} (hq : 0 < q) :
    rationalEvenThetaInputs →+ rationalEvenThetaInputs where
  toFun b := ⟨dilateSchwartz b.val q hq.ne', by
    obtain ⟨he, h₀, hF⟩ := b.property
    exact ⟨fun x ↦ by simpa only [dilateSchwartz_apply, mul_neg] using he (q * x),
      by rw [dilateSchwartz_apply, mul_zero, h₀],
      by rw [fourier_dilateSchwartz _ hq, mul_zero, hF, smul_zero]⟩⟩
  map_zero' := by
    apply Subtype.ext
    ext x
    simp [dilateSchwartz_apply]
  map_add' b c := by
    apply Subtype.ext
    ext x
    simp only [dilateSchwartz_apply, _root_.add_apply, AddSubgroup.coe_add]

public theorem rationalEvenThetaDilation_apply {q : ℝ} (hq : 0 < q)
    (b : rationalEvenThetaInputs) (y : ℝ) :
    (rationalEvenThetaDilation hq b).val y = b.val (q * y) :=
  dilateSchwartz_apply b.val q hq.ne' y

private theorem theta_add (b c : 𝓢(ℝ, ℂ)) {t : ℝ} (ht : 0 < t) :
    rationalTheta (b + c) t = rationalTheta b t + rationalTheta c t := by
  unfold rationalTheta
  simp only [_root_.add_apply]
  exact ((summable_norm_schwartz_int_mul b ht.ne').of_norm.subtype _).tsum_add
    ((summable_norm_schwartz_int_mul c ht.ne').of_norm.subtype _)

private theorem theta_dilation (b : 𝓢(ℝ, ℂ)) {q : ℝ} (hq : 0 < q) (t : ℝ) :
    rationalTheta (dilateSchwartz b q hq.ne') t = rationalTheta b (q * t) := by
  simp only [rationalTheta, dilateSchwartz_apply, mul_assoc]

private abbrev toThetaInput (b : rationalEvenThetaInputs) : RationalThetaInput :=
  ⟨b.val, b.property.2⟩

private theorem cut_theta_ae {S : Set ℝ} (hS : MeasurableSet S) {s : ℝ} (hs : 0 ≤ s)
    (b : rationalEvenThetaInputs) :
    ⇑(rationalThetaLogCut hS (rationalThetaWeightedLog 0 hs le_rfl (toThetaInput b)))
      =ᵐ[volume] S.indicator (fun x ↦
        (symmetricStripWeightRoot 0 s x : ℂ) * rationalTheta b.val (Real.exp x)) := by
  refine (rationalThetaLogCut_ae hS _).trans (EventuallyEq.indicator ?_)
  simpa only [rationalThetaWeightedLog, Complex.ofReal_zero, zero_mul, Complex.exp_zero, one_mul]
    using (memLp_rationalTheta_weighted (toThetaInput b) 0 0 s hs le_rfl).coeFn_toLp

/-- The cut zero-line weighted generator map. -/
public noncomputable def rationalThetaWeightedLogCut {S : Set ℝ} (hS : MeasurableSet S)
    {s : ℝ} (hs : 0 ≤ s) : rationalEvenThetaInputs →+ LogL2 := by
  let F (b : rationalEvenThetaInputs) :=
    rationalThetaLogCut hS (rationalThetaWeightedLog 0 hs le_rfl (toThetaInput b))
  have hadd (b c : rationalEvenThetaInputs) : F (b + c) = F b + F c := by
    apply Lp.ext
    filter_upwards [cut_theta_ae hS hs (b + c), cut_theta_ae hS hs b, cut_theta_ae hS hs c,
      Lp.coeFn_add (F b) (F c)] with x hbc hb hc hsum
    rw [hbc, hsum, Pi.add_apply, hb, hc]
    by_cases hx : x ∈ S
    · simp only [indicator_of_mem hx, AddSubgroup.coe_add, theta_add _ _ (Real.exp_pos x), mul_add]
    · simp only [indicator_of_notMem hx, add_zero]
  exact { toFun := F, map_add' := hadd, map_zero' := by simpa using hadd 0 0 }

/-- The cut map uses exactly `rationalThetaWeightedLog` at `a = α = 0`. -/
public theorem rationalThetaWeightedLogCut_apply {S : Set ℝ} (hS : MeasurableSet S)
    {s : ℝ} (hs : 0 ≤ s) (b : rationalEvenThetaInputs) :
    rationalThetaWeightedLogCut hS hs b =
      rationalThetaLogCut hS (rationalThetaWeightedLog 0 hs le_rfl ⟨b.val, b.property.2⟩) := by
  rfl

/-- The cut generator is represented by the indicator times the weighted theta profile. -/
public theorem rationalThetaWeightedLogCut_ae {S : Set ℝ} (hS : MeasurableSet S)
    {s : ℝ} (hs : 0 ≤ s) (b : rationalEvenThetaInputs) :
    ⇑(rationalThetaWeightedLogCut hS hs b) =ᵐ[volume] S.indicator (fun x ↦
      (symmetricStripWeightRoot 0 s x : ℂ) * rationalTheta b.val (Real.exp x)) := by
  rw [rationalThetaWeightedLogCut_apply]
  exact cut_theta_ae hS hs b

private theorem theta_dilation_iterate {q : ℝ} (hq : 0 < q) (n : ℕ)
    (b : rationalEvenThetaInputs) (x : ℝ) :
    rationalTheta ((rationalEvenThetaDilation hq)^[n] b).val (Real.exp x) =
      rationalTheta b.val (Real.exp (x + (n : ℝ) * Real.log q)) := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    change rationalTheta (dilateSchwartz (((rationalEvenThetaDilation hq)^[n] b).val)
      q hq.ne') (Real.exp x) = _
    rw [theta_dilation _ hq, show q * Real.exp x = Real.exp (Real.log q + x) by
      rw [Real.exp_add, Real.exp_log hq], ih, Nat.cast_succ]
    congr 2
    ring

/-- At zero twist the generator difference is the forward theta difference,
with the weight at the original log point on both terms. -/
public theorem rationalThetaWeightedLogCut_sub_dilation_ae {S : Set ℝ} (hS : MeasurableSet S)
    {q s : ℝ} (hq : 0 < q) (hs : 0 ≤ s) (b : rationalEvenThetaInputs) :
    ⇑(rationalThetaWeightedLogCut hS hs (b - rationalEvenThetaDilation hq b)) =ᵐ[volume]
      S.indicator (fun x ↦ (symmetricStripWeightRoot 0 s x : ℂ) *
        (rationalTheta b.val (Real.exp x) - rationalTheta b.val (Real.exp (x + Real.log q)))) := by
  let F := rationalThetaWeightedLogCut hS hs
  let Db := rationalEvenThetaDilation hq b
  rw [map_sub]
  filter_upwards [Lp.coeFn_sub (F b) (F Db), rationalThetaWeightedLogCut_ae hS hs b,
    rationalThetaWeightedLogCut_ae hS hs Db] with x hsub hb hDb
  rw [hsub, Pi.sub_apply, hb, hDb]
  have hshift : rationalTheta Db.val (Real.exp x) =
      rationalTheta b.val (Real.exp (x + Real.log q)) := by
    simpa only [Db, Function.iterate_one, Nat.cast_one, one_mul] using
      theta_dilation_iterate hq 1 b x
  by_cases hx : x ∈ S
  · simp only [indicator_of_mem hx, hshift, mul_sub]
  · simp only [indicator_of_notMem hx, sub_zero]

/-- Cut one-prime differences are dense in precisely the cut theta-generator
closure, on every measurable set bounded below in log coordinates. The
statement allows any forward dilation factor `q > 1`. -/
public theorem rationalThetaWeightedLogCut_closure {S : Set ℝ} (hS : MeasurableSet S)
    {A q s : ℝ} (hA : S ⊆ Ici A) (hq : 1 < q) (hs : 0 ≤ s) :
    closure (range (fun b ↦ rationalThetaWeightedLogCut hS hs
      (b - rationalEvenThetaDilation (zero_lt_one.trans hq) b))) =
    closure (range (rationalThetaWeightedLogCut hS hs)) := by
  have hq₀ := zero_lt_one.trans hq
  apply closure_range_sub_iterate_eq
  intro b
  apply tendsto_zeroLineWeightedLog_cut_translate hs hA (Real.log_pos hq)
    (fun x ↦ rationalTheta b.val (Real.exp x))
  · intro N
    obtain ⟨C, hC, hb⟩ := rationalTheta_uniform_log_bound
      (Bornology.isVonNBounded_singleton (𝕜 := ℂ) b.val) N
    exact ⟨C, hC, hb b.val (mem_singleton _) b.property.2.1 b.property.2.2⟩
  · intro n
    exact (rationalThetaWeightedLogCut_ae hS hs _).trans (Eventually.of_forall fun _ ↦
      congrFun (indicator_congr fun x _ ↦ by rw [theta_dilation_iterate hq₀ n b x]) _)

/-- The real cutoff `[1/Λ, ∞)` pulls back to the log cutoff `[-log Λ, ∞)`. -/
public theorem exp_preimage_Ici_inv {Λ : ℝ} (hΛ : 0 < Λ) :
    Real.exp ⁻¹' Ici (Λ⁻¹) = Ici (-Real.log Λ) := by
  ext x
  change Λ⁻¹ ≤ Real.exp x ↔ -Real.log Λ ≤ x
  rw [← Real.log_le_iff_le_exp (inv_pos.mpr hΛ), Real.log_inv]

/-- The real cutoff `[1/Λ, Λ]` pulls back to `[-log Λ, log Λ]`. -/
public theorem exp_preimage_Icc_inv {Λ : ℝ} (hΛ : 0 < Λ) :
    Real.exp ⁻¹' Icc (Λ⁻¹) Λ = Icc (-Real.log Λ) (Real.log Λ) := by
  ext x
  change Λ⁻¹ ≤ Real.exp x ∧ Real.exp x ≤ Λ ↔ -Real.log Λ ≤ x ∧ x ≤ Real.log Λ
  rw [← Real.log_le_iff_le_exp (inv_pos.mpr hΛ), Real.log_inv, Real.le_log_iff_exp_le hΛ]

/-- One-prime closure equality for the real upper-ray cutoff `[1/Λ, ∞)`. -/
public theorem rationalThetaWeightedLogCut_closure_Ici {p : ℕ} (hp : p.Prime)
    {Λ s : ℝ} (hΛ : 0 < Λ) (hs : 0 ≤ s) :
    let hS := (measurableSet_Ici (a := Λ⁻¹)).preimage Real.continuous_exp.measurable
    closure (range (fun b ↦ rationalThetaWeightedLogCut hS hs
      (b - rationalEvenThetaDilation (q := (p : ℝ)) (by exact_mod_cast hp.pos) b))) =
    closure (range (rationalThetaWeightedLogCut hS hs)) := by
  dsimp only
  apply rationalThetaWeightedLogCut_closure (A := -Real.log Λ) _ _
    (show (1 : ℝ) < p by exact_mod_cast hp.one_lt) hs
  rw [exp_preimage_Ici_inv hΛ]

/-- One-prime closure equality for the real two-sided cutoff `[1/Λ, Λ]`. -/
public theorem rationalThetaWeightedLogCut_closure_Icc {p : ℕ} (hp : p.Prime)
    {Λ s : ℝ} (hΛ : 0 < Λ) (hs : 0 ≤ s) :
    let hS := (measurableSet_Icc (a := Λ⁻¹) (b := Λ)).preimage Real.continuous_exp.measurable
    closure (range (fun b ↦ rationalThetaWeightedLogCut hS hs
      (b - rationalEvenThetaDilation (q := (p : ℝ)) (by exact_mod_cast hp.pos) b))) =
    closure (range (rationalThetaWeightedLogCut hS hs)) := by
  dsimp only
  apply rationalThetaWeightedLogCut_closure (A := -Real.log Λ) _ _
    (show (1 : ℝ) < p by exact_mod_cast hp.one_lt) hs
  rw [exp_preimage_Icc_inv hΛ]
  exact Icc_subset_Ici_self

end Masullo
