module

public import Mathlib.Analysis.SpecialFunctions.Log.Monotone
public import Mathlib.NumberTheory.LegendreSymbol.ZModChar
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Tactic

/-!
# Dirichlet tail bounds for χ₈

The inclusive sums `S` and `D` have limits with explicit errors at cutoff 32.
The prefix table for the character has absolute value at most one and vanishes
at 32. Summation by parts uses that zero to save a factor of two at this cutoff.
-/

open Filter Finset
open scoped Topology

namespace Chi8Tails

/-- Mathlib's integer-valued character χ₈ on natural numbers, cast to ℝ. -/
@[expose] public noncomputable def w (n : ℕ) : ℝ := (ZMod.χ₈ (n : ZMod 8) : ℝ)

/-- The harmonic-weighted character sum through `N`, inclusive. -/
@[expose] public noncomputable def S (N : ℕ) : ℝ := ∑ n ∈ Icc 1 N, w n / (n : ℝ)

/-- The negative logarithm-weighted character sum through `N`, inclusive. -/
@[expose] public noncomputable def D (N : ℕ) : ℝ := ∑ n ∈ Icc 1 N, -w n * (Real.log n / n)

-- The prefix after each residue in a block. The total of a full block is zero.
private def prefixInt (n : ℕ) : ℤ :=
  if n % 8 = 1 ∨ n % 8 = 2 then 1 else if n % 8 = 5 ∨ n % 8 = 6 then -1 else 0

private noncomputable def blockPrefix (n : ℕ) : ℝ := (prefixInt n : ℝ)

private theorem abs_prefix_le (n : ℕ) : |blockPrefix n| ≤ 1 := by
  simp only [blockPrefix, prefixInt]
  split_ifs <;> norm_num

private theorem prefix_32 : blockPrefix 32 = 0 := by norm_num [blockPrefix, prefixInt]

private theorem w_succ (n : ℕ) : w (n + 1) = blockPrefix (n + 1) - blockPrefix n := by
  have step : ∀ r : Fin 8, ZMod.χ₈ ((r.val + 1 : ℕ) : ZMod 8) =
      prefixInt (r.val + 1) - prefixInt r.val := by decide
  let r : Fin 8 := ⟨n % 8, Nat.mod_lt _ (by decide)⟩
  have hmod : (n + 1) % 8 = (r.val + 1) % 8 := by simp [r, Nat.mod_add_mod]
  have hχ : ZMod.χ₈ ((n + 1 : ℕ) : ZMod 8) = ZMod.χ₈ ((r.val + 1 : ℕ) : ZMod 8) := by
    rw [ZMod.χ₈_nat_mod_eight (n + 1), hmod, ← ZMod.χ₈_nat_mod_eight]
  have hp : prefixInt (n + 1) = prefixInt (r.val + 1) := by simp only [prefixInt, hmod]
  have hq : prefixInt n = prefixInt r.val := by simp [prefixInt, r]
  have h := hχ.trans (step r)
  rw [← hp, ← hq] at h
  unfold w blockPrefix
  exact_mod_cast h

private noncomputable def weighted (f : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ Icc 1 N, w n * f n

private theorem weighted_succ (f : ℕ → ℝ) (m : ℕ) :
    weighted f (m + 1) = weighted f m + w (m + 1) * f (m + 1) :=
  sum_Icc_succ_top (Nat.succ_le_succ (Nat.zero_le m)) _

-- Abel summation on (a, m], with the prefix re-anchored at a.
private theorem weighted_sub (f : ℕ → ℝ) {a m : ℕ} (ham : a ≤ m) :
    weighted f m - weighted f a = f m * (blockPrefix m - blockPrefix a) +
      ∑ i ∈ Ico a m, (f i - f (i + 1)) * (blockPrefix i - blockPrefix a) := by
  induction m, ham using Nat.le_induction with
  | base => simp
  | succ m hm ih =>
    calc
      _ = (weighted f m - weighted f a) + w (m + 1) * f (m + 1) := by
        rw [weighted_succ]
        ring
      _ = _ := by
        rw [ih, w_succ, sum_Ico_succ_top hm]
        ring

private theorem abs_weighted_sub_le (f : ℕ → ℝ) (hnonneg : ∀ n ≥ 32, 0 ≤ f n)
    (hanti : AntitoneOn f (Set.Ici 32)) {a m : ℕ} (ha : 32 ≤ a) (ham : a ≤ m) :
    |weighted f m - weighted f a| ≤ (1 + |blockPrefix a|) * f a := by
  let C := 1 + |blockPrefix a|
  have hterm (i : ℕ) {t : ℝ} (ht : 0 ≤ t) : |t * (blockPrefix i - blockPrefix a)| ≤ t * C := by
    rw [abs_mul, abs_of_nonneg ht]
    exact mul_le_mul_of_nonneg_left
      ((abs_sub _ _).trans (add_le_add (abs_prefix_le i) le_rfl)) ht
  have hdiff (i : ℕ) (hi : i ∈ Ico a m) : 0 ≤ f i - f (i + 1) := by
    have hi' : 32 ≤ i := ha.trans (mem_Ico.mp hi).1
    exact sub_nonneg.mpr (hanti hi' (hi'.trans (Nat.le_succ i)) (Nat.le_succ i))
  have htel : ∑ i ∈ Ico a m, (f i - f (i + 1)) = f a - f m := by
    simpa only [neg_sub_neg] using sum_Ico_sub (fun i => -f i) ham
  rw [weighted_sub f ham]
  calc
    |f m * (blockPrefix m - blockPrefix a) +
        ∑ i ∈ Ico a m, (f i - f (i + 1)) * (blockPrefix i - blockPrefix a)| ≤ _ := abs_add_le _ _
    _ ≤ f m * C + ∑ i ∈ Ico a m, (f i - f (i + 1)) * C :=
      add_le_add (hterm m (hnonneg m (ha.trans ham)))
        ((abs_sum_le_sum_abs _ _).trans (sum_le_sum fun i hi => hterm i (hdiff i hi)))
    _ = C * f a := by rw [← sum_mul, htel]; ring

private theorem abs_weighted_sub_32_le (f : ℕ → ℝ) (hnonneg : ∀ n ≥ 32, 0 ≤ f n)
    (hanti : AntitoneOn f (Set.Ici 32)) {M : ℕ} (hM : 32 ≤ M) :
    |weighted f M - weighted f 32| ≤ f 32 := by
  simpa only [prefix_32, abs_zero, add_zero, one_mul] using
    abs_weighted_sub_le f hnonneg hanti le_rfl hM

private theorem exists_tendsto_weighted (f : ℕ → ℝ) (hnonneg : ∀ n ≥ 32, 0 ≤ f n)
    (hanti : AntitoneOn f (Set.Ici 32)) (hf : Tendsto f atTop (𝓝 0)) :
    ∃ L : ℝ, Tendsto (weighted f) atTop (𝓝 L) ∧ |L - weighted f 32| ≤ f 32 := by
  have hc : CauchySeq (weighted f) := by
    rw [Metric.cauchySeq_iff']
    intro ε hε
    have ht : Tendsto (fun n => 2 * f n) atTop (𝓝 0) := by simpa using hf.const_mul 2
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp ht ε hε
    let a := max 32 N
    have ha : 32 ≤ a := le_max_left _ _
    refine ⟨a, fun m hm => ?_⟩
    rw [Real.dist_eq]
    calc
      _ ≤ (1 + |blockPrefix a|) * f a := abs_weighted_sub_le f hnonneg hanti ha hm
      _ ≤ 2 * f a := mul_le_mul_of_nonneg_right (by linarith [abs_prefix_le a]) (hnonneg a ha)
      _ ≤ dist (2 * f a) 0 := by rw [Real.dist_eq, sub_zero]; exact le_abs_self _
      _ < ε := hN a (le_max_right _ _)
  obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hc
  refine ⟨L, hL, le_of_tendsto ((hL.sub tendsto_const_nhds).abs) ?_⟩
  filter_upwards [eventually_ge_atTop (32 : ℕ)] with M hM
  exact abs_weighted_sub_32_le f hnonneg hanti hM

private noncomputable def invWeight (n : ℕ) : ℝ := 1 / (n : ℝ)
private noncomputable def logWeight (n : ℕ) : ℝ := Real.log n / n

private theorem S_eq_weighted : S = weighted invWeight := by
  funext N
  simp only [S, weighted, invWeight, mul_one_div]

private theorem D_eq_neg_weighted : D = fun N => -weighted logWeight N := by
  funext N
  simp only [D, weighted, logWeight, neg_mul, sum_neg_distrib]

private theorem invWeight_nonneg (n : ℕ) (_hn : 32 ≤ n) : 0 ≤ invWeight n := by
  unfold invWeight
  positivity

private theorem invWeight_antitone : AntitoneOn invWeight (Set.Ici 32) := by
  intro a ha b _hab hab
  have ha' : 32 ≤ a := ha
  exact one_div_le_one_div_of_le (by exact_mod_cast (show 0 < a by omega)) (by exact_mod_cast hab)

private theorem logWeight_nonneg (n : ℕ) (hn : 32 ≤ n) : 0 ≤ logWeight n := by
  have h : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  exact div_nonneg (Real.log_nonneg h) (Nat.cast_nonneg n)

private theorem logWeight_antitone : AntitoneOn logWeight (Set.Ici 32) := by
  have hexp (n : ℕ) (hn : n ∈ Set.Ici 32) : Real.exp 1 ≤ (n : ℝ) := by
    have hn' : (32 : ℝ) ≤ n := by exact_mod_cast (show 32 ≤ n from hn)
    exact Real.exp_one_lt_three.le.trans ((by norm_num : (3 : ℝ) ≤ 32).trans hn')
  intro a ha b hb hab
  exact Real.log_div_self_antitoneOn (hexp a ha) (hexp b hb) (by exact_mod_cast hab)

private theorem tendsto_invWeight : Tendsto invWeight atTop (𝓝 0) := by
  change Tendsto (fun n : ℕ => 1 / (n : ℝ)) atTop (𝓝 0)
  simpa only [Function.comp_def, one_div] using
    (tendsto_inv_atTop_zero : Tendsto (fun x : ℝ => x⁻¹) atTop (𝓝 0)).comp
      tendsto_natCast_atTop_atTop

private theorem tendsto_logWeight : Tendsto logWeight atTop (𝓝 0) := by
  change Tendsto (fun n : ℕ => Real.log n / n) atTop (𝓝 0)
  simpa only [Function.comp_def, pow_one, one_mul, add_zero] using
    (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))

/-- The finite tail of `S` after 32, in absolute value. -/
public theorem abs_S_sub_S32_le {M : ℕ} (hM : 32 ≤ M) : |S M - S 32| ≤ 1 / 32 := by
  simpa only [S_eq_weighted, invWeight, Nat.cast_ofNat] using
    abs_weighted_sub_32_le invWeight invWeight_nonneg invWeight_antitone hM

/-- The finite tail of `D` after 32, in absolute value. -/
public theorem abs_D_sub_D32_le {M : ℕ} (hM : 32 ≤ M) :
    |D M - D 32| ≤ Real.log (32 : ℝ) / 32 := by
  rw [D_eq_neg_weighted, neg_sub_neg, abs_sub_comm]
  simpa only [logWeight, Nat.cast_ofNat] using
    abs_weighted_sub_32_le logWeight logWeight_nonneg logWeight_antitone hM

/-- Convergence of `S` with the error bound at the inclusive cutoff 32. -/
public theorem exists_tendsto_S :
    ∃ L : ℝ, Tendsto S atTop (𝓝 L) ∧ |L - S 32| ≤ 1 / 32 := by
  simpa only [S_eq_weighted, invWeight, Nat.cast_ofNat] using
    exists_tendsto_weighted invWeight invWeight_nonneg invWeight_antitone tendsto_invWeight

/-- Convergence of `D` with the error bound at the inclusive cutoff 32. -/
public theorem exists_tendsto_D :
    ∃ L : ℝ, Tendsto D atTop (𝓝 L) ∧ |L - D 32| ≤ Real.log (32 : ℝ) / 32 := by
  obtain ⟨L, hL, hbound⟩ :=
    exists_tendsto_weighted logWeight logWeight_nonneg logWeight_antitone tendsto_logWeight
  refine ⟨-L, ?_, ?_⟩
  · rw [D_eq_neg_weighted]
    exact hL.neg
  · rw [D_eq_neg_weighted, neg_sub_neg, abs_sub_comm]
    simpa only [logWeight, Nat.cast_ofNat] using hbound

end Chi8Tails
