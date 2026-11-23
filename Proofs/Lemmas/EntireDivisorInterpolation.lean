module

public import Lemmas.EntireDivisorDivision
import Lemmas.EntireFiniteFactors
import Mathlib.Analysis.Complex.LocallyUniformLimit

/-! # Global jets of an entire divisor

Prescribe arbitrary Taylor coefficients at the zeros of a nonzero entire function.
The proof uses one pole at a time: remove the pole using the entire generator, and
subtract entire multiples of the generator to make the resulting blocks locally
normally summable. No growth bounds are imposed on the interpolant.
-/

open Filter Set Metric
open scoped Topology NNReal ENNReal

namespace Masullo

/-- Taylor coefficients below the multiplicities at every zero of the generator. -/
@[expose] public noncomputable def entireDivisorJet {g : ℂ → ℂ} (f : ℂ → ℂ)
    (a : {z : ℂ // g z = 0}) (k : Fin (analyticOrderAt g a.val).toNat) : ℂ :=
  iteratedDeriv k f a.val / (k.val.factorial : ℂ)

/-- The kernel of the normalized jet map is the principal entire-function ideal. -/
public theorem entireDivisorJet_eq_zero_iff {f g : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f univ) (hg : AnalyticOnNhd ℂ g univ) (hg₀ : g ≠ 0) :
    entireDivisorJet (g := g) f = 0 ↔
      ∃ q : ℂ → ℂ, AnalyticOnNhd ℂ q univ ∧ f = g * q := by
  rw [entire_mul_iff_vanishing_jets hf hg hg₀]
  constructor
  · intro h z hz k hk
    have h₁ := congrFun (congrFun h ⟨z, hz⟩) ⟨k, hk⟩
    simpa [entireDivisorJet, div_eq_zero_iff, Nat.factorial_ne_zero] using h₁
  · intro h
    funext z k
    simp [entireDivisorJet, h z.val z.property k.val k.isLt]

private theorem order_eq_toNat {g : ℂ → ℂ} (hg : AnalyticOnNhd ℂ g univ) (hg₀ : g ≠ 0)
    (a : ℂ) : analyticOrderAt g a = ((analyticOrderAt g a).toNat : ℕ∞) :=
  (ENat.natCast_toNat <|
    (AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero a (fun z ↦ hg z trivial)).not.mpr hg₀).symm

private theorem iteratedDeriv_jetPolynomial (a : ℂ) {m : ℕ} (J : Fin m → ℂ) (k : Fin m) :
    iteratedDeriv k (fun z : ℂ ↦ ∑ i : Fin m, J i * (z - a) ^ i.val) a =
      J k * (k.val.factorial : ℂ) := by
  rw [iteratedDeriv_fun_sum (by intro; fun_prop)]
  have hpow (i : Fin m) :
      iteratedDeriv k (fun z : ℂ ↦ (z - a) ^ i.val) a =
        if k = i then (i.val.factorial : ℂ) else 0 := by
    have h := congrFun (iteratedDeriv_comp_sub_const k.val (fun z : ℂ ↦ z ^ i.val) a) a
    simpa only [sub_self, iteratedDeriv_fun_pow_zero, Fin.ext_iff, Nat.cast_ite,
      Nat.cast_zero] using h
  simp only [iteratedDeriv_const_mul_field, hpow, mul_ite, mul_zero]
  rw [Finset.sum_ite_eq_of_mem _ _ _ (Finset.mem_univ k)]

/-- A single principal part, after multiplication by the generator, gives an
entire block with exactly the requested jets at its own center. -/
private theorem exists_singleBlock {g : ℂ → ℂ} (hg : AnalyticOnNhd ℂ g univ) (hg₀ : g ≠ 0)
    (a : {z : ℂ // g z = 0}) (J : Fin (analyticOrderAt g a.val).toNat → ℂ) :
    ∃ B R : ℂ → ℂ, AnalyticOnNhd ℂ B univ ∧
      (∀ z ≠ a.val, AnalyticAt ℂ R z ∧ B z = g z * R z) ∧
      (∀ k, entireDivisorJet B a k = J k) ∧
      (∀ b ≠ a, ∀ k, entireDivisorJet B b k = 0) := by
  let m := (analyticOrderAt g a.val).toNat
  obtain ⟨h, hh, hna, hfac⟩ := entire_extract_finset_factors hg {a.val} (fun _ ↦ m)
    (by simpa [m] using order_eq_toNat hg hg₀ a.val)
  have hh₀ := hna a.val (Finset.mem_singleton_self _)
  simp only [Finset.prod_singleton] at hfac
  let Q (z : ℂ) := ∑ i : Fin m, J i * (z - a.val) ^ i.val
  have hQ (z : ℂ) : AnalyticAt ℂ Q z := by
    exact Finset.analyticAt_fun_sum _ fun _ _ ↦ by fun_prop
  let S (y : ℂ) := Q (a.val + y) / h (a.val + y)
  have hS : AnalyticAt ℂ S 0 := by
    have ha : AnalyticAt ℂ (fun y : ℂ ↦ a.val + y) 0 := by fun_prop
    exact (((hQ (a.val + 0)).div (hh _ trivial) (by simpa using hh₀)).comp ha)
  obtain ⟨E, hE, hrem⟩ := hS.exists_eventuallyEq_sum_add_pow_mul m
  let T (z : ℂ) := ∑ i ∈ Finset.range m,
    ((z - a.val) ^ i / (i.factorial : ℂ)) * iteratedDeriv i S 0
  have hT (z : ℂ) : AnalyticAt ℂ T z := by
    exact Finset.analyticAt_fun_sum _ fun _ _ ↦ by fun_prop
  let B (z : ℂ) := h z * T z
  let R (z : ℂ) := T z / (z - a.val) ^ m
  have hB (z : ℂ) : AnalyticAt ℂ B z := (hh z trivial).mul (hT z)
  have hR (z : ℂ) (hz : z ≠ a.val) : AnalyticAt ℂ R z ∧ B z = g z * R z := by
    have hn := pow_ne_zero m (sub_ne_zero.mpr hz)
    refine ⟨(hT z).div (by fun_prop) hn, ?_⟩
    dsimp [B, R]
    rw [hfac z]
    field_simp
  refine ⟨B, R, fun z _ ↦ hB z, hR, fun k ↦ ?_, fun b hba k ↦ ?_⟩
  · have hz : Tendsto (fun z : ℂ ↦ z - a.val) (𝓝 a.val) (𝓝 0) := by
      have hc : ContinuousAt (fun z : ℂ ↦ z - a.val) a.val := by fun_prop
      simpa [ContinuousAt] using hc
    have H : (fun z ↦ Q z - B z) =ᶠ[𝓝 a.val]
        fun z ↦ (z - a.val) ^ m • (h z * E (z - a.val)) := by
      filter_upwards [hz.eventually hrem, (hh a.val trivial).continuousAt.eventually_ne hh₀]
        with z he hn
      change S (z - a.val) = _ at he
      have he' : Q z / h z = T z + (z - a.val) ^ m * E (z - a.val) := by
        simpa [S, T, smul_eq_mul] using he
      rw [div_eq_iff hn] at he'
      simp only [B, smul_eq_mul]
      rw [he']
      ring
    have horder : (m : ℕ∞) ≤ analyticOrderAt (fun z ↦ Q z - B z) a.val := by
      apply (natCast_le_analyticOrderAt ((hQ _).fun_sub (hB _))).mpr
      refine ⟨_, (hh _ trivial).mul ?_, H⟩
      apply AnalyticAt.comp (f := fun z : ℂ ↦ z - a.val)
      · simpa using hE
      · fun_prop
    have hd := (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero
      ((hQ _).fun_sub (hB _))).mp horder k k.isLt
    rw [iteratedDeriv_fun_sub (hQ _).contDiffAt (hB _).contDiffAt, sub_eq_zero,
      iteratedDeriv_jetPolynomial] at hd
    rw [entireDivisorJet, ← hd, mul_div_cancel_right₀ _ (by exact_mod_cast k.val.factorial_ne_zero)]
  · have hab : b.val ≠ a.val := fun h ↦ hba (Subtype.ext h)
    have heq : B =ᶠ[𝓝 b.val] g * R := by
      filter_upwards [isOpen_ne.mem_nhds hab] with z hz using (hR z hz).2
    have hord : ((analyticOrderAt g b.val).toNat : ℕ∞) ≤ analyticOrderAt (g * R) b.val := by
      rw [← order_eq_toNat hg hg₀, analyticOrderAt_mul (hg _ trivial) (hR _ hab).1]
      exact le_self_add
    have hd := (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero
      ((hg _ trivial).mul (hR _ hab).1)).mp hord k k.isLt
    simp [entireDivisorJet, heq.iteratedDeriv_eq k.val, hd]

/-- Subtract a multiple of the generator to preserve every jet while making the
block small on a disk that stays away from its center. -/
private theorem exists_smallBlock {g B R : ℂ → ℂ} {a : ℂ}
    (hg : AnalyticOnNhd ℂ g univ) (hg₀ : g ≠ 0) (hB : AnalyticOnNhd ℂ B univ)
    (hR : ∀ z ≠ a, AnalyticAt ℂ R z ∧ B z = g z * R z) {ε : ℝ} (hε : 0 < ε) :
    ∃ F : ℂ → ℂ, AnalyticOnNhd ℂ F univ ∧
      (∀ b : {z : ℂ // g z = 0}, ∀ k, entireDivisorJet F b k = entireDivisorJet B b k) ∧
      (a ≠ 0 → ∀ z ∈ closedBall (0 : ℂ) (‖a‖ / 2), ‖F z‖ ≤ ε) := by
  by_cases ha : a = 0
  · exact ⟨B, hB, fun _ _ ↦ rfl, fun h ↦ (h ha).elim⟩
  have ha' : 0 < ‖a‖ := norm_pos_iff.mpr ha
  let r : ℝ≥0 := ⟨3 * ‖a‖ / 4, by positivity⟩
  let s : ℝ≥0 := ⟨2 * ‖a‖ / 3, by positivity⟩
  have hr : 0 < r := by change 0 < 3 * ‖a‖ / 4; positivity
  have hsr : (s : ℝ≥0∞) < (r : ℝ≥0∞) := by
    rw [ENNReal.coe_lt_coe]
    change 2 * ‖a‖ / 3 < 3 * ‖a‖ / 4
    linarith
  have hrR : DifferentiableOn ℂ R (closedBall 0 (r : ℝ)) := by
    intro z hz
    have hza : z ≠ a := by
      intro h
      rw [h, mem_closedBall, dist_zero_right] at hz
      change ‖a‖ ≤ 3 * ‖a‖ / 4 at hz
      linarith
    exact (hR z hza).1.differentiableAt.differentiableWithinAt
  let p := cauchyPowerSeries R 0 r
  have hp : TendstoUniformlyOn (fun n z ↦ p.partialSum n z) R atTop (ball 0 (s : ℝ)) := by
    simpa only [zero_add] using (hrR.hasFPowerSeriesOnBall hr).tendstoUniformlyOn hsr
  have hgc : Continuous g := continuous_iff_continuousAt.mpr fun z ↦ (hg z trivial).continuousAt
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : ℂ) (‖a‖ / 2)).exists_bound_of_continuousOn
    hgc.continuousOn
  let C := max 1 M
  have hC : 0 < C := zero_lt_one.trans_le (le_max_left _ _)
  obtain ⟨n, hn⟩ := ((Metric.tendstoUniformlyOn_iff.mp hp) (ε / C) (div_pos hε hC)).exists
  have hpent (z : ℂ) : AnalyticAt ℂ (p.partialSum n) z := by
    unfold FormalMultilinearSeries.partialSum
    apply Finset.analyticAt_fun_sum
    intro i _
    have H : (fun w : ℂ ↦ p i (fun _ ↦ w)) = fun w ↦ w ^ i • p i (fun _ ↦ 1) := by
      funext w
      simpa only [smul_eq_mul, mul_one, Finset.prod_const, Finset.card_fin] using
        (p i).map_smul_univ (fun _ ↦ w) (fun _ ↦ 1)
    rw [H]
    fun_prop
  let F (z : ℂ) := B z - g z * p.partialSum n z
  refine ⟨F, fun z _ ↦ (hB z trivial).sub ((hg z trivial).mul (hpent z)), ?_, ?_⟩
  · intro b k
    have hprod : AnalyticOnNhd ℂ (g * p.partialSum n) univ :=
      fun z _ ↦ (hg z trivial).mul (hpent z)
    have hz : iteratedDeriv k (g * p.partialSum n) b.val = 0 :=
      (entire_mul_iff_vanishing_jets hprod hg hg₀).mp ⟨_, fun z _ ↦ hpent z, rfl⟩
        b.val b.property k k.isLt
    change iteratedDeriv k (fun z ↦ B z - (g * p.partialSum n) z) b.val / _ = _
    rw [iteratedDeriv_fun_sub (hB b.val trivial).contDiffAt (hprod b.val trivial).contDiffAt,
      hz, sub_zero]
    rfl
  · intro _ z hz
    rw [mem_closedBall, dist_zero_right] at hz
    have hza : z ≠ a := by
      intro h
      rw [h] at hz
      linarith
    have hzs : z ∈ ball (0 : ℂ) (s : ℝ) := by
      rw [mem_ball, dist_zero_right]
      change ‖z‖ < 2 * ‖a‖ / 3
      linarith
    have hdiff : ‖R z - p.partialSum n z‖ ≤ ε / C := by
      have := hn z hzs
      rw [dist_eq_norm] at this
      exact this.le
    change ‖B z - g z * p.partialSum n z‖ ≤ ε
    rw [(hR z hza).2, ← mul_sub, norm_mul]
    calc
      _ ≤ C * (ε / C) := mul_le_mul ((hM z (by simpa only [mem_closedBall,
        dist_zero_right] using hz)).trans (le_max_right _ _)) hdiff (norm_nonneg _) hC.le
      _ = ε := by field_simp

private theorem finite_zeros_in_compact {g : ℂ → ℂ}
    (hg : AnalyticOnNhd ℂ g univ) (hg₀ : g ≠ 0) {K : Set ℂ} (hK : IsCompact K) :
    {a : {z : ℂ // g z = 0} | a.val ∈ K}.Finite := by
  obtain ⟨a, ha⟩ : ∃ a, g a ≠ 0 := by
    by_contra! h
    exact hg₀ (funext h)
  have hA : {z : ℂ | g z ≠ 0} ∈ Filter.codiscrete ℂ :=
    hg.preimage_zero_mem_codiscrete ha
  have hfin := hK.finite_sdiff_of_mem_codiscreteWithin
    ((Filter.codiscreteWithin_mono (subset_univ K)) hA)
  exact (hfin.preimage Subtype.val_injective.injOn).subset (fun b hb ↦ ⟨hb, by simp [b.property]⟩)

private theorem tendstoLocallyUniformlyOn_iteratedDeriv {ι : Type*} {p : Filter ι}
    {F : ι → ℂ → ℂ} {f : ℂ → ℂ}
    (hF : ∀ i, AnalyticOnNhd ℂ (F i) univ)
    (h : TendstoLocallyUniformlyOn F f p univ) (k : ℕ) :
    TendstoLocallyUniformlyOn (fun i ↦ iteratedDeriv k (F i)) (iteratedDeriv k f) p univ := by
  have hA (i : ι) (z : ℂ) (k : ℕ) : AnalyticAt ℂ (iteratedDeriv k (F i)) z := by
    induction k with
    | zero => simpa only [iteratedDeriv_zero] using hF i z trivial
    | succ k ih => simpa only [iteratedDeriv_succ] using ih.deriv
  induction k with
  | zero => simpa only [iteratedDeriv_zero] using h
  | succ k ih =>
    simpa only [iteratedDeriv_succ, Function.comp_def] using
      ih.deriv (.of_forall fun i z _ ↦ (hA i z k).differentiableAt.differentiableWithinAt)
        isOpen_univ

/-- Every array of normalized Taylor coefficients, indexed by all zeros and all
orders strictly below their multiplicities, comes from an entire function. -/
public theorem entireDivisorJet_surjective {g : ℂ → ℂ}
    (hg : AnalyticOnNhd ℂ g univ) (hg₀ : g ≠ 0) :
    Function.Surjective (fun f : {f : ℂ → ℂ // AnalyticOnNhd ℂ f univ} ↦
      entireDivisorJet (g := g) f.val) := by
  classical
  intro J
  let Z := {z : ℂ // g z = 0}
  have hZ (r : ℝ) : {a : Z | a.val ∈ closedBall (0 : ℂ) r}.Finite :=
    finite_zeros_in_compact hg hg₀ (isCompact_closedBall _ _)
  have hcount : Countable Z := by
    apply Set.countable_univ_iff.mp
    have hu : (univ : Set Z) = ⋃ n : ℕ, {a : Z | a.val ∈ closedBall (0 : ℂ) n} := by
      ext a
      simp only [mem_univ, mem_iUnion, mem_ofPred_eq, mem_closedBall, dist_zero_right, true_iff]
      exact exists_nat_ge ‖a.val‖
    rw [hu]
    exact Set.countable_iUnion fun n ↦ (hZ n).countable
  obtain ⟨e, he⟩ := exists_injective_nat Z
  let u (a : Z) : ℝ := (1 / 2) ^ e a
  have hu : Summable u :=
    (summable_geometric_of_lt_one (r := (1 / 2 : ℝ)) (by norm_num) (by norm_num)).comp_injective he
  have hb (a : Z) : ∃ F : ℂ → ℂ, AnalyticOnNhd ℂ F univ ∧
      (∀ k, entireDivisorJet F a k = J a k) ∧
      (∀ b ≠ a, ∀ k, entireDivisorJet F b k = 0) ∧
      (a.val ≠ 0 → ∀ z ∈ closedBall (0 : ℂ) (‖a.val‖ / 2), ‖F z‖ ≤ u a) := by
    obtain ⟨B, R, hB, hR, hBa, hBb⟩ := exists_singleBlock hg hg₀ a (J a)
    obtain ⟨F, hF, hFB, hsmall⟩ := exists_smallBlock hg hg₀ hB hR (ε := u a) (by
      dsimp [u]
      positivity)
    exact ⟨F, hF, fun k ↦ (hFB a k).trans (hBa k),
      fun b hb k ↦ (hFB b k).trans (hBb b hb k), hsmall⟩
  choose F hF hFa hFb hsmall using hb
  let f (z : ℂ) := ∑' a : Z, F a z
  let P (t : Finset Z) (z : ℂ) := ∑ a ∈ t, F a z
  have hP (t : Finset Z) : AnalyticOnNhd ℂ (P t) univ :=
    fun z hz ↦ Finset.analyticAt_fun_sum _ fun a _ ↦ hF a z hz
  -- The radii grow with the zeros, so on each compact only finitely many blocks
  -- can escape the summable bounds.
  have hlim : TendstoLocallyUniformlyOn P f atTop univ := by
    rw [tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_univ]
    intro K _ hK
    obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn (f := id) continuous_id.continuousOn
    apply tendstoUniformlyOn_tsum_of_cofinite_eventually hu
    have hevent : ∀ᶠ a : Z in cofinite, a.val ∉ closedBall (0 : ℂ) (max 0 (2 * M)) := by
      rw [eventually_cofinite]
      simpa only [not_not] using hZ (max 0 (2 * M))
    filter_upwards [hevent] with a ha z hz
    rw [mem_closedBall, dist_zero_right, not_le] at ha
    have ha₀ : a.val ≠ 0 := norm_pos_iff.mp ((le_max_left _ _).trans_lt ha)
    apply hsmall a ha₀ z
    rw [mem_closedBall, dist_zero_right]
    have hzM : ‖z‖ ≤ M := hM z hz
    linarith [((le_max_right 0 (2 * M)).trans_lt ha)]
  refine ⟨⟨f, ?_⟩, ?_⟩
  · exact (hlim.differentiableOn (.of_forall fun t ↦ (hP t).differentiableOn)
      isOpen_univ).analyticOnNhd isOpen_univ
  · funext a k
    -- Passing to the limit after differentiation preserves the full jet.
    have hD := (tendstoLocallyUniformlyOn_iteratedDeriv hP hlim k.val).tendsto_at
      (mem_univ a.val)
    have hEq : ∀ᶠ t : Finset Z in atTop, iteratedDeriv k (P t) a.val = J a k *
        (k.val.factorial : ℂ) := by
      have hft : (k.val.factorial : ℂ) ≠ 0 := by exact_mod_cast k.val.factorial_ne_zero
      filter_upwards [eventually_ge_atTop ({a} : Finset Z)] with t ht
      have ha : a ∈ t := Finset.singleton_subset_iff.mp ht
      have hterm (b : Z) : iteratedDeriv k (F b) a.val =
          if b = a then J a k * (k.val.factorial : ℂ) else 0 := by
        split_ifs with h
        · subst b
          exact (div_eq_iff hft).mp (hFa a k)
        · exact (div_eq_zero_iff.mp (hFb b a (Ne.symm h) k)).resolve_right hft
      change iteratedDeriv k (fun z ↦ ∑ b ∈ t, F b z) a.val = _
      rw [iteratedDeriv_fun_sum (fun b _ ↦ (hF b a.val trivial).contDiffAt)]
      simp only [hterm, Finset.sum_ite_eq', ha, ite_true]
    have hE := tendsto_nhds_unique_of_eventuallyEq hD tendsto_const_nhds hEq
    exact (div_eq_iff (by exact_mod_cast k.val.factorial_ne_zero)).mpr hE

end Masullo
