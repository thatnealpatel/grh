module

public import Lemmas.PrimeHybridMeanValue
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.NumberTheory.DirichletCharacter.Bounds
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

/-! # Peaks of the first-crossing prime polynomial

Source: `145f6475:.godel/alice/stopped-conductor-window.md`, lines 17–31.
Owning check session: `01a209ce-61c0-7258-9ef8-09cad8ad12db`.

This finite exceptional-character bound is the peak step in the length-stopped slice
supremum (lines 11–15), which is used in the masked Schur estimate (lines 33–47).
It includes the principal character and makes no asymptotic or Schur estimate.
-/

open MeasureTheory
open scoped BigOperators

namespace Masullo.StoppedCharacterPeak

open StoppedPrimeProductMoment

/-- The prime sum whose peaks are counted. -/
@[expose] public noncomputable def primeSum {q : ℕ} (S : Finset ℕ) (b : ℕ → ℝ)
    (χ : DirichletCharacter ℂ q) (u : ℝ) : ℂ :=
  ∑ p ∈ S, (b p : ℂ) * χ (p : ZMod q) *
    Complex.exp (Complex.I * (Real.log (p : ℝ) : ℂ) * (u : ℂ))

/-- The degree-`k` stopped polynomial with the first-crossing coefficients. -/
@[expose] public noncomputable def stoppedPolynomial {q : ℕ} (S : Finset ℕ) (U : ℝ)
    (b : ℕ → ℝ) (k : ℕ) (χ : DirichletCharacter ℂ q) (u : ℝ) : ℂ :=
  ∑ n ∈ stoppedProducts S U k, (coefficient S U b k n : ℂ) * χ (n : ZMod q) *
    Complex.exp (Complex.I * (Real.log (n : ℝ) : ℂ) * (u : ℂ))

/-- Only depths with a nonempty first-crossing product support are charged. -/
@[expose] public noncomputable def stoppedDepths (S : Finset ℕ) (U : ℝ) (J : ℕ) : Finset ℕ := by
  classical exact (Finset.range (J + 1)).filter (fun k ↦ (stoppedProducts S U k).Nonempty)

/-- All characters attaining at least `H` somewhere in the closed window `[-Y,Y]`. -/
@[expose] public noncomputable def peakCharacters {q : ℕ} (S : Finset ℕ) (b : ℕ → ℝ)
    (Y H : ℝ) : Finset (DirichletCharacter ℂ q) := by
  classical exact Finset.univ.filter (fun χ ↦ ∃ u : ℝ, |u| ≤ Y ∧ H ≤ ‖primeSum S b χ u‖)

/-- Under the stopping cutoff this finite set contains every nonempty stopped depth. -/
public theorem mem_stoppedDepths_iff {S : Finset ℕ} {U : ℝ} {J k : ℕ}
    (hprime : ∀ p ∈ S, p.Prime) (hJ : U ≤ (2 : ℝ) ^ J) :
    k ∈ stoppedDepths S U J ↔ (stoppedProducts S U k).Nonempty := by
  classical
  rw [stoppedDepths, Finset.mem_filter, Finset.mem_range]
  refine ⟨And.right, fun hk ↦ ⟨?_, hk⟩⟩
  obtain ⟨n, hn⟩ := hk
  obtain ⟨v, hv, _⟩ := Finset.mem_image.mp hn
  exact Nat.lt_succ_of_le (stopped_length_le hprime hJ hv)

-- Extend the positive-integer twist by zero to get an actual multiplicative map on ℕ.
private noncomputable def twist {q : ℕ} (χ : DirichletCharacter ℂ q) (u : ℝ) : ℕ →* ℂ where
  toFun n := if n = 0 then 0 else
    χ (n : ZMod q) * Complex.exp (Complex.I * (Real.log (n : ℝ) : ℂ) * (u : ℂ))
  map_one' := by simp
  map_mul' m n := by
    by_cases hm : m = 0
    · simp [hm]
    by_cases hn : n = 0
    · simp [hn]
    have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm
    have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
    simp only [ite_eq_right hm, ite_eq_right hn, ite_eq_right (Nat.mul_ne_zero hm hn), Nat.cast_mul,
      map_mul, Real.log_mul hm' hn', Complex.ofReal_add]
    rw [mul_add, add_mul, Complex.exp_add]
    ring

private theorem twist_apply {q n : ℕ} (χ : DirichletCharacter ℂ q) (u : ℝ) (hn : n ≠ 0) :
    twist χ u n = χ (n : ZMod q) *
      Complex.exp (Complex.I * (Real.log (n : ℝ) : ℂ) * (u : ℂ)) := by
  change (if n = 0 then _ else _) = _
  rw [ite_eq_right hn]

private theorem stopped_expansion {q J : ℕ} {S : Finset ℕ} {U X : ℝ} (hU : 1 < U)
    (hprime : ∀ p ∈ S, p.Prime) (hX : ∀ p ∈ S, (p : ℝ) ≤ X) (hJ : U ≤ (2 : ℝ) ^ J)
    (b : ℕ → ℝ) (χ : DirichletCharacter ℂ q) (u : ℝ) (hz : primeSum S b χ u ≠ 0) :
    (1 : ℂ) = ∑ k ∈ stoppedDepths S U J,
      (primeSum S b χ u)⁻¹ ^ k * stoppedPolynomial S U b k χ u := by
  classical
  have hsum : (∑ p ∈ S, (b p : ℂ) * twist χ u p) = primeSum S b χ u := by
    apply Finset.sum_congr rfl
    intro p hp
    rw [twist_apply χ u (hprime p hp).ne_zero, ← mul_assoc]
  have hpoly (k : ℕ) :
      (∑ n ∈ stoppedProducts S U k, (coefficient S U b k n : ℂ) * twist χ u n) =
        stoppedPolynomial S U b k χ u := by
    apply Finset.sum_congr rfl
    intro n hn
    have hn₀ : n ≠ 0 := by
      have h₁ := (stoppedProducts_window hU hprime hX hn).1
      exact fun he ↦ by rw [he, Nat.cast_zero] at h₁; linarith
    rw [twist_apply χ u hn₀, ← mul_assoc]
  have hexp := finite_normalized_leaf_expansion hU hprime b (twist χ u)
    (by rwa [hsum]) J hJ
  dsimp only at hexp
  rw [hsum] at hexp
  simp_rw [hpoly] at hexp
  refine hexp.trans (Finset.sum_subset (Finset.filter_subset _ _) ?_).symm
  intro k _ hk
  have he := Finset.not_nonempty_iff_eq_empty.mp (mt (mem_stoppedDepths_iff hprime hJ).mpr hk)
  simp [stoppedPolynomial, he]

private theorem phase_norm (x : ℝ) : ‖Complex.exp (Complex.I * (x : ℂ))‖ = 1 := by
  simp [Complex.norm_exp, Complex.mul_re]

private theorem phase_sub_le (x u v : ℝ) (hx : 0 ≤ x) :
    ‖Complex.exp (Complex.I * (x : ℂ) * (u : ℂ)) -
      Complex.exp (Complex.I * (x : ℂ) * (v : ℂ))‖ ≤ |u - v| * x := by
  have he : Complex.I * (x : ℂ) * (u : ℂ) =
      Complex.I * ((x * v : ℝ) : ℂ) + Complex.I * ((x * (u - v) : ℝ) : ℂ) := by
    push_cast
    ring
  rw [he, Complex.exp_add, mul_assoc, ← Complex.ofReal_mul, ← mul_sub_one,
    norm_mul, phase_norm, one_mul]
  simpa only [Real.norm_eq_abs, abs_mul, abs_of_nonneg hx, mul_comm x] using
    (Real.norm_exp_I_mul_ofReal_sub_one_le (x := x * (u - v)))

private theorem primeSum_sub_le {q : ℕ} {S : Finset ℕ} (hprime : ∀ p ∈ S, p.Prime)
    (b : ℕ → ℝ) (χ : DirichletCharacter ℂ q) (u v : ℝ) :
    ‖primeSum S b χ u - primeSum S b χ v‖ ≤
      |u - v| * ∑ p ∈ S, |b p| * Real.log (p : ℝ) := by
  unfold primeSum
  rw [← Finset.sum_sub_distrib, Finset.mul_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun p hp ↦ ?_))
  have hp₁ : (1 : ℝ) ≤ p := by exact_mod_cast (hprime p hp).one_lt.le
  have hlog := Real.log_nonneg hp₁
  rw [← mul_sub, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  calc
    _ ≤ (|b p| * 1) * (|u - v| * Real.log (p : ℝ)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left (χ.norm_le_one _) (abs_nonneg _))
        (phase_sub_le _ _ _ hlog) (norm_nonneg _) (by positivity)
    _ = _ := by ring

-- Persistence is for the original prime sum, not for a particular stopped degree.
private theorem persists {q : ℕ} {S : Finset ℕ} (hprime : ∀ p ∈ S, p.Prime)
    {b : ℕ → ℝ} {χ : DirichletCharacter ℂ q} {ρ ℓ H u v : ℝ}
    (hvar : ρ * (∑ p ∈ S, |b p| * Real.log (p : ℝ)) ≤ H - ℓ)
    (hpeak : H ≤ ‖primeSum S b χ u‖) (hv : |v - u| ≤ ρ) : ℓ ≤ ‖primeSum S b χ v‖ := by
  have hL : 0 ≤ ∑ p ∈ S, |b p| * Real.log (p : ℝ) :=
    Finset.sum_nonneg (fun p hp ↦ mul_nonneg (abs_nonneg _)
      (Real.log_nonneg (by exact_mod_cast (hprime p hp).one_lt.le)))
  have hd := (primeSum_sub_le hprime b χ v u).trans
    ((mul_le_mul_of_nonneg_right hv hL).trans hvar)
  have ht := (abs_sub_le_iff.mp ((abs_norm_sub_norm_le _ _).trans hd)).2
  linarith

-- Pointwise majorant from the normalized expansion. Cauchy–Schwarz costs only one
-- factor of the number of depths; we retain the paper's safe square in the bound.
private theorem one_le_stopped_energy {q J : ℕ} {S : Finset ℕ} {U X ℓ : ℝ} (hU : 1 < U)
    (hprime : ∀ p ∈ S, p.Prime) (hX : ∀ p ∈ S, (p : ℝ) ≤ X) (hJ : U ≤ (2 : ℝ) ^ J)
    (hℓ : 0 < ℓ) (b : ℕ → ℝ) (χ : DirichletCharacter ℂ q) (u : ℝ)
    (hlevel : ℓ ≤ ‖primeSum S b χ u‖) :
    1 ≤ ((stoppedDepths S U J).card : ℝ) ^ 2 *
      ∑ k ∈ stoppedDepths S U J, ‖stoppedPolynomial S U b k χ u‖ ^ 2 / ℓ ^ (2 * k) := by
  let K := stoppedDepths S U J
  let z := primeSum S b χ u
  let a (k : ℕ) := ‖stoppedPolynomial S U b k χ u‖ / ℓ ^ k
  have hz : z ≠ 0 := norm_pos_iff.mp (hℓ.trans_le hlevel)
  have hexp := stopped_expansion hU hprime hX hJ b χ u hz
  have hsum : 1 ≤ ∑ k ∈ K, a k := by
    calc
      (1 : ℝ) = ‖∑ k ∈ K, z⁻¹ ^ k * stoppedPolynomial S U b k χ u‖ := by
        rw [← hexp, norm_one]
      _ ≤ ∑ k ∈ K, ‖z⁻¹ ^ k * stoppedPolynomial S U b k χ u‖ := norm_sum_le _ _
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro k _
        rw [norm_mul, norm_pow, norm_inv, inv_pow, inv_mul_eq_div]
        exact div_le_div_of_nonneg_left (norm_nonneg _) (pow_pos hℓ _)
          (pow_le_pow_left₀ hℓ.le hlevel k)
  have hsquares : (∑ k ∈ K, a k ^ 2) =
      ∑ k ∈ K, ‖stoppedPolynomial S U b k χ u‖ ^ 2 / ℓ ^ (2 * k) := by
    apply Finset.sum_congr rfl
    intro k _
    simp only [a, div_pow, ← pow_mul, Nat.mul_comm k 2]
  have hcard : (K.card : ℝ) ≤ (K.card : ℝ) ^ 2 := by
    exact_mod_cast Nat.le_self_pow (by decide : 2 ≠ 0) K.card
  calc
    (1 : ℝ) = 1 ^ 2 := by norm_num
    _ ≤ (∑ k ∈ K, a k) ^ 2 := pow_le_pow_left₀ zero_le_one hsum _
    _ ≤ (K.card : ℝ) * ∑ k ∈ K, a k ^ 2 := sq_sum_le_card_mul_sum_sq
    _ ≤ (K.card : ℝ) ^ 2 * ∑ k ∈ K, a k ^ 2 :=
      mul_le_mul_of_nonneg_right hcard (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _)
    _ = _ := by rw [hsquares]

private theorem continuous_stoppedPolynomial {q : ℕ} (S : Finset ℕ) (U : ℝ) (b : ℕ → ℝ)
    (k : ℕ) (χ : DirichletCharacter ℂ q) : Continuous (stoppedPolynomial S U b k χ) := by
  unfold stoppedPolynomial
  exact continuous_finsetSum _ (fun _ _ ↦ by fun_prop)

-- Use the entire persistence interval, even if the degree detecting the peak changes.
private theorem peak_le_stopped_integral {q J : ℕ} {S : Finset ℕ} {U X : ℝ} (hU : 1 < U)
    (hprime : ∀ p ∈ S, p.Prime) (hX : ∀ p ∈ S, (p : ℝ) ≤ X) (hJ : U ≤ (2 : ℝ) ^ J)
    {Y ρ T ℓ H u : ℝ} (hρ : 0 < ρ) (hwindow : Y + ρ ≤ T) (hℓ : 0 < ℓ)
    {b : ℕ → ℝ} {χ : DirichletCharacter ℂ q}
    (hvar : ρ * (∑ p ∈ S, |b p| * Real.log (p : ℝ)) ≤ H - ℓ)
    (hu : |u| ≤ Y) (hpeak : H ≤ ‖primeSum S b χ u‖) :
    2 * ρ ≤ ((stoppedDepths S U J).card : ℝ) ^ 2 *
      ∑ k ∈ stoppedDepths S U J, (∫ v in -T..T, ‖stoppedPolynomial S U b k χ v‖ ^ 2) /
        ℓ ^ (2 * k) := by
  let K := stoppedDepths S U J
  let f (k : ℕ) (v : ℝ) := ‖stoppedPolynomial S U b k χ v‖ ^ 2 / ℓ ^ (2 * k)
  let g (v : ℝ) := (K.card : ℝ) ^ 2 * ∑ k ∈ K, f k v
  have hf (k : ℕ) : Continuous (f k) :=
    ((continuous_stoppedPolynomial S U b k χ).norm.pow 2).div_const _
  have hg : Continuous g := continuous_const.mul (continuous_finsetSum _ (fun k _ ↦ hf k))
  have hgnonneg (v : ℝ) : 0 ≤ g v := by dsimp [g, f]; positivity
  obtain ⟨hu₁, hu₂⟩ := abs_le.mp hu
  have hleft : -T ≤ u - ρ := by linarith
  have hright : u + ρ ≤ T := by linarith
  have hord : u - ρ ≤ u + ρ := by linarith
  have hmajor (v : ℝ) (hv : v ∈ Set.Icc (u - ρ) (u + ρ)) : 1 ≤ g v := by
    have hv' : |v - u| ≤ ρ := by
      obtain ⟨h₁, h₂⟩ := hv
      exact abs_le.mpr ⟨by linarith, by linarith⟩
    exact one_le_stopped_energy hU hprime hX hJ hℓ b χ v (persists hprime hvar hpeak hv')
  calc
    _ = ∫ v in (u - ρ)..(u + ρ), (1 : ℝ) := by simp [intervalIntegral.integral_const]; ring
    _ ≤ ∫ v in (u - ρ)..(u + ρ), g v :=
      intervalIntegral.integral_mono_on hord (continuous_const.intervalIntegrable _ _)
        (hg.intervalIntegrable _ _) hmajor
    _ ≤ ∫ v in -T..T, g v := intervalIntegral.integral_mono_interval hleft hord hright
      (Filter.Eventually.of_forall hgnonneg) (hg.intervalIntegrable _ _)
    _ = _ := by
      dsimp only [g]
      rw [intervalIntegral.integral_const_mul,
        intervalIntegral.integral_finsetSum (fun k _ ↦ (hf k).intervalIntegrable (-T) T)]
      simp only [f, K, intervalIntegral.integral_div]

/-- A finite bound on the fraction of all characters modulo the prime `q` with a prime-sum
peak of height at least `H` at some `|u| ≤ Y`. The two-sided persistence interval has radius
`ρ`; only nonempty stopped depths contribute to the finite sum. -/
public theorem peak_fraction_le {q N J : ℕ} (hq : q.Prime) (hN : 1 ≤ N)
    {S : Finset ℕ} {U X : ℝ} (hU : 1 < U) (hprime : ∀ p ∈ S, p.Prime)
    (hX : ∀ p ∈ S, (p : ℝ) ≤ X) (hNX : U * X ≤ (N : ℝ) + 1) (hJ : U ≤ (2 : ℝ) ^ J)
    (b : ℕ → ℝ) {Y ρ T ℓ H : ℝ} (hY : 0 ≤ Y) (hρ : 0 < ρ) (hwindow : Y + ρ ≤ T)
    (hℓ : 0 < ℓ) (_hℓH : ℓ < H)
    (hvar : ρ * (∑ p ∈ S, |b p| * Real.log (p : ℝ)) ≤ H - ℓ) :
    let K := stoppedDepths S U J
    ((peakCharacters (q := q) S b Y H).card : ℝ) / ((q : ℝ) - 1) ≤
      (K.card : ℝ) ^ 2 / (2 * ρ) * (2 * T + 4 * ((N : ℝ) / q) * (1 + Real.log (N : ℝ))) *
        ∑ k ∈ K, ((k.factorial : ℝ) / Real.sqrt U) * (∑ p ∈ S, Real.sqrt (p : ℝ) * b p ^ 2) ^ k /
          ℓ ^ (2 * k) := by
  classical
  intro K
  let A := peakCharacters (q := q) S b Y H
  let M (χ : DirichletCharacter ℂ q) (k : ℕ) := ∫ v in -T..T, ‖stoppedPolynomial S U b k χ v‖ ^ 2
  let F (χ : DirichletCharacter ℂ q) := ∑ k ∈ K, M χ k / ℓ ^ (2 * k)
  let C := 2 * T + 4 * ((N : ℝ) / q) * (1 + Real.log (N : ℝ))
  let E (k : ℕ) := ((k.factorial : ℝ) / Real.sqrt U) * (∑ p ∈ S, Real.sqrt (p : ℝ) * b p ^ 2) ^ k
  have hT : 0 < T := by linarith
  have hqden : 0 < (q : ℝ) - 1 := sub_pos.mpr (by exact_mod_cast hq.one_lt)
  have hF (χ : DirichletCharacter ℂ q) : 0 ≤ F χ := by
    refine Finset.sum_nonneg (fun k _ ↦ div_nonneg ?_ (by positivity))
    exact intervalIntegral.integral_nonneg (by linarith) (fun _ _ ↦ sq_nonneg _)
  have hpeak (χ : DirichletCharacter ℂ q) (hχ : χ ∈ A) :
      1 ≤ (K.card : ℝ) ^ 2 / (2 * ρ) * F χ := by
    obtain ⟨u, hu, hHu⟩ := (Finset.mem_filter.mp hχ).2
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by positivity)).mpr
    simpa only [one_mul] using peak_le_stopped_integral hU hprime hX hJ hρ hwindow hℓ hvar hu hHu
  have hcount : (A.card : ℝ) ≤ (K.card : ℝ) ^ 2 / (2 * ρ) * ∑ χ, F χ := by
    calc
      _ = ∑ χ ∈ A, (1 : ℝ) := by simp
      _ ≤ ∑ χ ∈ A, (K.card : ℝ) ^ 2 / (2 * ρ) * F χ := Finset.sum_le_sum hpeak
      _ ≤ ∑ χ, (K.card : ℝ) ^ 2 / (2 * ρ) * F χ :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ A)
          (fun χ _ _ ↦ mul_nonneg (by positivity) (hF χ))
      _ = _ := Finset.mul_sum .. |>.symm
  have hmean (k : ℕ) : ((q : ℝ) - 1)⁻¹ * (∑ χ, M χ k) ≤ C * E k :=
    PrimeHybridMeanValue.stopped_mean_value_le hq hN hT hU hprime hX hNX b k
  calc
    (A.card : ℝ) / ((q : ℝ) - 1) ≤
        ((K.card : ℝ) ^ 2 / (2 * ρ) * ∑ χ, F χ) / ((q : ℝ) - 1) :=
      div_le_div_of_nonneg_right hcount hqden.le
    _ = (K.card : ℝ) ^ 2 / (2 * ρ) *
        ∑ k ∈ K, (((q : ℝ) - 1)⁻¹ * (∑ χ, M χ k)) / ℓ ^ (2 * k) := by
      rw [div_eq_mul_inv, mul_assoc, mul_comm (∑ χ, F χ), Finset.mul_sum]
      congr 1
      simp only [F, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k _
      simp only [← mul_div_assoc, ← Finset.sum_div]
    _ ≤ (K.card : ℝ) ^ 2 / (2 * ρ) * ∑ k ∈ K, (C * E k) / ℓ ^ (2 * k) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun k _ ↦
        div_le_div_of_nonneg_right (hmean k) (by positivity))) (by positivity)
    _ = _ := by
      change _ = (K.card : ℝ) ^ 2 / (2 * ρ) * C * ∑ k ∈ K, E k / ℓ ^ (2 * k)
      simp only [mul_div_assoc, ← Finset.mul_sum, ← mul_assoc]

end Masullo.StoppedCharacterPeak
