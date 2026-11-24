module

public import Lemmas.PrimePairShellMoment
public import Lemmas.ProductLaurentMoment
import all Lemmas.PrimePairShellMoment
import all Lemmas.PrimeTupleRedrawSpacing
import all Lemmas.LaurentCircleMoment
import Lemmas.SignedBlockIntervalMoment
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Exact continuous shell moment of a signed prime cube

Source: `dcc11ec5:.godel/bob/signed-gap-cube-screen.md:52–66` (selection pin
`059232cff7d3894d8545eb11ffccf9cd2fec1646`, obligation unchanged at `e96c4611`).
Use: the continuous weighted moment in the proof of (2), before the independent-phase
moment bound and Markov's inequality price the flagged heights.
Owning check session: `01a20c71-faab-7613-8747-63acf6b0d98e`.

The finite keys are the distinct, coalesced valuation vectors of surviving labels.
Only the balanced signs and the distinct prime coordinates enter the transfer;
coefficients may be arbitrary complex numbers. This is an exact continuous identity
with Haar probability, not a bound for the product-circle moment or a mesh estimate.
-/

open MeasureTheory
open scoped BigOperators ComplexConjugate

namespace Masullo.PrimeCubeShellMoment

open LaurentCircleMoment (uniformCircle)
open PrimePairShellMoment (shellKernel shellKernel_transform integrable_shellKernel_phase)
open ProductLaurentMoment (monomial phaseFactor supportSize)
open SignedBlockIntervalMoment (phase)

variable {ι : Type*} [Fintype ι]

/-- The angular prime flow in the product of unit circles. -/
@[expose] public noncomputable def primeFlow (p : ι → ℕ) (u : ℝ) (i : ι) : Circle :=
  Circle.exp (u * Real.log (p i))

private def bit (s x : Fin 3) : ℕ := if x = s then 1 else 0

private def signed (x : Fin 3) : ℤ := (bit 1 x : ℤ) - bit 2 x

private noncomputable def character (k : ι → ℤ) (z : ι → Circle) : ℂ :=
  ((∏ i, z i ^ k i : Circle) : ℂ)

private theorem character_eq_prod (k : ι → ℤ) (z : ι → Circle) :
    character k z = ∏ i, (↑(z i ^ k i) : ℂ) :=
  map_prod Circle.coeHom (fun i ↦ z i ^ k i) Finset.univ

private theorem phaseFactor_eq (s : Fin 3) (z : Circle) :
    phaseFactor s z = (↑(z ^ signed s) : ℂ) := by
  fin_cases s <;> norm_num [phaseFactor, signed, bit]
  exact (Circle.coe_inv_eq_conj z).symm

private theorem character_sub (k l : ι → ℤ) (z : ι → Circle) :
    character (k - l) z = character k z * conj (character l z) := by
  simp only [character, Pi.sub_apply, zpow_sub, Finset.prod_mul_distrib, Finset.prod_inv_distrib,
    Circle.coe_mul, Circle.coe_inv_eq_conj]

private theorem continuous_character (k : ι → ℤ) : Continuous (character k) := by
  have hc : Continuous (fun z : ι → Circle ↦ (∏ i, z i ^ k i : Circle)) :=
    continuous_finsetProd _ fun i _ ↦ (continuous_apply i).zpow (k i)
  exact continuous_subtype_val.comp hc

private theorem zpow_sum_finset {α : Type*} (s : Finset α) (f : α → ℤ) (z : Circle) :
    z ^ (∑ j ∈ s, f j) = ∏ j ∈ s, z ^ f j := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih => simp [hj, zpow_add, ih]

private theorem character_tuple {m : ℕ} (a : Fin m → ι → Fin 3) (z : ι → Circle) :
    character (fun i ↦ ∑ j, signed (a j i)) z = ∏ j, monomial (a j) z := by
  unfold character
  simp_rw [zpow_sum_finset]
  rw [Finset.prod_comm]
  change Circle.coeHom (∏ j, ∏ i, z i ^ signed (a j i)) = _
  simp_rw [map_prod]
  simp only [monomial, phaseFactor_eq]
  rfl

private noncomputable def frequency (p : ι → ℕ) (k : ι → ℤ) : ℝ :=
  ∑ i, (k i : ℝ) * Real.log (p i)

private theorem character_primeFlow (p : ι → ℕ) (k : ι → ℤ) (u : ℝ) :
    character k (primeFlow p u) = phase (u * frequency p k) := by
  have h (s : Finset ι) (f : ι → ℝ) : Circle.exp (∑ i ∈ s, f i) = ∏ i ∈ s, Circle.exp (f i) := by
    classical
    induction s using Finset.induction_on with
    | empty => simp
    | insert i s hi ih => simp [hi, Circle.exp_add, ih]
  have harg : (∑ i, (k i : ℝ) * (u * Real.log (p i))) =
      ∑ i, u * ((k i : ℝ) * Real.log (p i)) :=
    Finset.sum_congr rfl fun i _ ↦ by ring
  simp only [character, primeFlow, frequency, ← Circle.exp_intCast_mul, ← h,
    Circle.coe_exp, phase, Finset.mul_sum, harg]

private theorem integral_circle_zpow (k : ℤ) :
    (∫ z : Circle, (↑(z ^ k) : ℂ) ∂uniformCircle) = if k = 0 then 1 else 0 := by
  split_ifs with hk
  · simp [hk]
  let r := Circle.exp (Real.pi / (k : ℝ))
  have hr : (↑(r ^ k) : ℂ) = -1 := by
    have hkR : (k : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hk
    have harg : (k : ℝ) * (Real.pi / (k : ℝ)) = Real.pi := by field_simp
    change (↑(Circle.exp (Real.pi / (k : ℝ)) ^ k) : ℂ) = -1
    rw [← Circle.exp_intCast_mul, harg, Circle.coe_exp, Complex.exp_pi_mul_I]
  have hinv := integral_mul_left_eq_self (μ := uniformCircle)
    (fun z : Circle ↦ (↑(z ^ k) : ℂ)) r
  simp only [mul_zpow, Circle.coe_mul, hr, neg_one_mul, integral_neg] at hinv
  exact neg_eq_self.mp hinv

private theorem integral_character (k : ι → ℤ) :
    (∫ z, character k z ∂Measure.pi (fun _ : ι ↦ uniformCircle)) =
      if ∀ i, k i = 0 then 1 else 0 := by
  classical
  simp_rw [character_eq_prod]
  rw [integral_fintype_prod_eq_prod (fun i (z : Circle) ↦ (↑(z ^ k i) : ℂ))]
  simp_rw [integral_circle_zpow]
  split_ifs with h
  · simp [h]
  · obtain ⟨i, hi⟩ := not_forall.mp h
    exact Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hi)

private abbrev tuples (S : Finset (ι → Fin 3)) (m : ℕ) :=
  Fintype.piFinset (fun _ : Fin m ↦ S)

private abbrev TuplePair (ι : Type*) (m : ℕ) :=
  (Fin m → ι → Fin 3) × (Fin m → ι → Fin 3)

private def momentExp {m : ℕ} (ab : TuplePair ι m) (i : ι) : ℤ :=
  (∑ j, signed (ab.1 j i)) - ∑ j, signed (ab.2 j i)

private def momentCoeff {m : ℕ} (c : (ι → Fin 3) → ℂ) (ab : TuplePair ι m) : ℂ :=
  (∏ j, c (ab.1 j)) * conj (∏ j, c (ab.2 j))

private theorem moment_expansion (S : Finset (ι → Fin 3)) (c : (ι → Fin 3) → ℂ)
    (m : ℕ) (z : ι → Circle) :
    (↑(‖∑ v ∈ S, c v * monomial v z‖ ^ (2 * m)) : ℂ) =
      ∑ ab ∈ (tuples S m ×ˢ tuples S m), momentCoeff c ab * character (momentExp ab) z := by
  have hpow : (∑ v ∈ S, c v * monomial v z) ^ m =
      ∑ a ∈ tuples S m, (∏ j, c (a j)) * character (fun i ↦ ∑ j, signed (a j i)) z := by
    rw [← Fin.prod_const m (∑ v ∈ S, c v * monomial v z), Finset.prod_univ_sum]
    exact Finset.sum_congr rfl fun a _ ↦ by rw [character_tuple, Finset.prod_mul_distrib]
  rw [Nat.mul_comm 2 m, pow_mul, ← norm_pow, Complex.ofReal_pow, ← Complex.mul_conj',
    hpow, map_sum, Finset.sum_mul_sum, Finset.sum_product]
  refine Finset.sum_congr rfl fun a _ ↦ Finset.sum_congr rfl fun b _ ↦ ?_
  rw [show momentExp (a, b) = (fun i ↦ ∑ j, signed (a j i)) - (fun i ↦ ∑ j, signed (b j i)) by rfl,
    character_sub, map_mul, momentCoeff]
  ring

private def signCount (s : Fin 3) (v : ι → Fin 3) : ℕ := ∑ i, bit s (v i)

private theorem signCount_eq_card (s : Fin 3) (v : ι → Fin 3) :
    signCount s v = (Finset.univ.filter fun i ↦ v i = s).card := by
  simp only [signCount, bit, Finset.card_filter]

private theorem signCount_add (v : ι → Fin 3) :
    signCount 1 v + signCount 2 v = supportSize v := by
  simp only [signCount, supportSize, Finset.card_filter, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  generalize v i = x
  fin_cases x <;> decide

-- Conjugation interchanges the numerator and denominator counts of the second tuple.
private def heightPowers {m : ℕ} (s r : Fin 3) (ab : TuplePair ι m) (i : ι) : ℕ :=
  (∑ j, bit s (ab.1 j i)) + ∑ j, bit r (ab.2 j i)

omit [Fintype ι] in
private theorem momentExp_eq_counts {m : ℕ} (ab : TuplePair ι m) (i : ι) :
    momentExp ab i = (heightPowers 1 2 ab i : ℤ) - heightPowers 2 1 ab i := by
  simp only [momentExp, signed, heightPowers, Nat.cast_add, Nat.cast_sum, Finset.sum_sub_distrib]
  abel

private theorem sum_heightPowers {m R : ℕ} (s r : Fin 3) (ab : TuplePair ι m)
    (h : ∀ j, signCount s (ab.1 j) + signCount r (ab.2 j) = R) :
    (∑ i, heightPowers s r ab i) = m * R := by
  calc
    _ = ∑ j, (signCount s (ab.1 j) + signCount r (ab.2 j)) := by
      simp only [heightPowers, signCount, Finset.sum_add_distrib]
      rw [Finset.sum_comm (f := fun i j ↦ bit s (ab.1 j i)),
        Finset.sum_comm (f := fun i j ↦ bit r (ab.2 j i))]
    _ = _ := by simp [h]

private def height (p N : ι → ℕ) : ℕ := ∏ i, p i ^ N i

private theorem height_pos {p : ι → ℕ} (hp : ∀ i, 0 < p i) (N : ι → ℕ) :
    0 < height p N := Finset.prod_pos fun i _ ↦ pow_pos (hp i) _

private theorem height_le {p : ι → ℕ} {X : ℝ} (hpX : ∀ i, (p i : ℝ) ≤ X) (N : ι → ℕ) :
    (height p N : ℝ) ≤ X ^ (∑ i, N i) := by
  rw [height, Nat.cast_prod, ← Finset.prod_pow_eq_pow_sum]
  simp only [Nat.cast_pow]
  exact Finset.prod_le_prod₀ (fun i _ ↦ pow_nonneg (Nat.cast_nonneg (p i)) _)
    (fun i _ ↦ pow_le_pow_left₀ (Nat.cast_nonneg (p i)) (hpX i) _)

private theorem log_height {p : ι → ℕ} (hp : ∀ i, 0 < p i) (N : ι → ℕ) :
    Real.log (height p N) = ∑ i, (N i : ℝ) * Real.log (p i) := by
  rw [height, Nat.cast_prod, Real.log_prod]
  · simp only [Nat.cast_pow, Real.log_pow]
  · exact fun i _ ↦ Nat.cast_ne_zero.mpr (pow_pos (hp i) _).ne'

private theorem factorization_height {p : ι → ℕ} (hp : ∀ i, (p i).Prime)
    (hinj : Function.Injective p) (N : ι → ℕ) (i : ι) :
    (height p N).factorization (p i) = N i := by
  classical
  rw [height, Nat.factorization_prod (fun j _ ↦ pow_ne_zero _ (hp j).ne_zero),
    Finsupp.finsetSum_apply, Finset.sum_eq_single i]
  · simp [Nat.factorization_pow, (hp i).factorization]
  · intro j _ hji
    simp [Nat.factorization_pow, (hp j).factorization,
      Finsupp.single_eq_of_ne (fun h ↦ hji (hinj h).symm : p i ≠ p j)]
  · simp

private theorem height_eq_iff {p : ι → ℕ} (hp : ∀ i, (p i).Prime)
    (hinj : Function.Injective p) (N D : ι → ℕ) :
    height p N = height p D ↔ ∀ i, N i = D i := by
  constructor
  · intro h i
    rw [← factorization_height hp hinj N i, ← factorization_height hp hinj D i, h]
  · intro h
    rw [funext h]

private theorem frequency_eq_log_div {m : ℕ} {p : ι → ℕ} (hp : ∀ i, 0 < p i)
    (ab : TuplePair ι m) :
    frequency p (momentExp ab) =
      Real.log ((height p (heightPowers 1 2 ab) : ℝ) / height p (heightPowers 2 1 ab)) := by
  rw [Real.log_div (Nat.cast_ne_zero.mpr (height_pos hp _).ne')
    (Nat.cast_ne_zero.mpr (height_pos hp _).ne'), log_height hp, log_height hp, frequency,
    ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ ↦ by rw [momentExp_eq_counts, Int.cast_sub, sub_mul]; norm_cast

-- The worst spacing is the ratio of adjacent integers, at the larger integer.
private theorem inv_max_le_abs_log_div {A B : ℕ} (hA : 0 < A) (hB : 0 < B) (hne : A ≠ B) :
    (max (A : ℝ) B)⁻¹ ≤ |Real.log ((A : ℝ) / B)| := by
  have hAR : (0 : ℝ) < A := Nat.cast_pos.mpr hA
  have hBR : (0 : ℝ) < B := Nat.cast_pos.mpr hB
  rcases lt_or_gt_of_ne hne with h | h
  · rw [max_eq_right (Nat.cast_le.mpr h.le)]
    calc
      _ ≤ Real.log ((B : ℝ) / A) := PrimeTupleRedrawSpacing.inv_le_log_div_of_lt hA h
      _ = -Real.log ((A : ℝ) / B) := by
        rw [Real.log_div hBR.ne' hAR.ne', Real.log_div hAR.ne' hBR.ne', neg_sub]
      _ ≤ _ := neg_le_abs _
  · rw [max_eq_left (Nat.cast_le.mpr h.le)]
    exact (PrimeTupleRedrawSpacing.inv_le_log_div_of_lt hB h).trans (le_abs_self _)

private theorem integral_shell_character_eq {p : ι → ℕ} {X t : ℝ} {m R : ℕ}
    (hp : ∀ i, (p i).Prime) (hinj : Function.Injective p) (hpX : ∀ i, (p i : ℝ) ≤ X)
    (hX : 1 ≤ X) (ht : X ^ (m * R) < t) (ab : TuplePair ι m)
    (hN : (∑ i, heightPowers 1 2 ab i) = m * R)
    (hD : (∑ i, heightPowers 2 1 ab i) = m * R) :
    (∫ u, (shellKernel t (9 * t / 8) u : ℂ) * character (momentExp ab) (primeFlow p u)) =
      (↑(2 * Real.pi * t) : ℂ) *
        ∫ z, character (momentExp ab) z ∂Measure.pi (fun _ : ι ↦ uniformCircle) := by
  classical
  have hpos : 0 < X ^ (m * R) := pow_pos (zero_lt_one.trans_le hX) _
  have ht₀ : 0 < t := hpos.trans ht
  simp_rw [character_primeFlow]
  rw [shellKernel_transform ht₀, integral_character]
  by_cases hz : ∀ i, momentExp ab i = 0
  · have hf : frequency p (momentExp ab) = 0 := by simp [frequency, hz]
    simp [hf, hz, phase]
  let N := heightPowers 1 2 ab
  let D := heightPowers 2 1 ab
  let A := height p N
  let B := height p D
  have hne : A ≠ B := by
    intro heq
    have h := (height_eq_iff hp hinj N D).mp heq
    exact hz fun i ↦ by
      rw [momentExp_eq_counts]
      exact sub_eq_zero.mpr (congrArg (fun n : ℕ ↦ (n : ℤ)) (h i))
  have hp₀ i : 0 < p i := (hp i).pos
  have hAX : (A : ℝ) ≤ X ^ (m * R) := by simpa only [A, N, hN] using height_le hpX N
  have hBX : (B : ℝ) ≤ X ^ (m * R) := by simpa only [B, D, hD] using height_le hpX D
  have hsep : (X ^ (m * R))⁻¹ ≤ |frequency p (momentExp ab)| := by
    rw [frequency_eq_log_div hp₀]
    exact (inv_anti₀ (lt_max_of_lt_left (Nat.cast_pos.mpr (height_pos hp₀ N)))
      (max_le hAX hBX)).trans (inv_max_le_abs_log_div (height_pos hp₀ N) (height_pos hp₀ D) hne)
  have hband : 1 < t * |frequency p (momentExp ab)| := by
    apply (div_lt_iff₀' ht₀).mp
    rw [one_div]
    exact (inv_strictAnti₀ hpos ht).trans_le hsep
  have hcut : max (1 - t * |frequency p (momentExp ab)|) 0 = 0 :=
    max_eq_right (sub_nonpos.mpr hband.le)
  simp [hcut, hz]

/-- The normalized product-circle moment is exactly the continuous shell moment
up to the kernel mass `2πt`. Each key has `R` nonzero coordinates, equally split
between `+1` (key entry `1`) and `-1` (key entry `2`). The strict cutoff uses the
angular, not cyclic, convention for the prime flow. -/
public theorem integral_shellKernel_mul_moment_eq {p : ι → ℕ} {X t : ℝ} {m R : ℕ}
    (hp : ∀ i, (p i).Prime) (hinj : Function.Injective p) (hpX : ∀ i, (p i : ℝ) ≤ X)
    (hX : 1 ≤ X) (_hm : 1 ≤ m) (ht : X ^ (m * R) < t)
    (S : Finset (ι → Fin 3)) (c : (ι → Fin 3) → ℂ)
    (hsize : ∀ v ∈ S, supportSize v = R)
    (hbalance : ∀ v ∈ S,
      (Finset.univ.filter fun i ↦ v i = 1).card = (Finset.univ.filter fun i ↦ v i = 2).card) :
    (∫ u, shellKernel t (9 * t / 8) u * ‖∑ v ∈ S, c v * monomial v (primeFlow p u)‖ ^ (2 * m)) =
      (2 * Real.pi * t) *
        ∫ z : ι → Circle, ‖∑ v ∈ S, c v * monomial v z‖ ^ (2 * m)
          ∂Measure.pi (fun _ : ι ↦ uniformCircle) := by
  classical
  let T := tuples S m ×ˢ tuples S m
  let μ := Measure.pi (fun _ : ι ↦ uniformCircle)
  let L (ab : TuplePair ι m) (u : ℝ) := momentCoeff c ab *
    ((shellKernel t (9 * t / 8) u : ℂ) * character (momentExp ab) (primeFlow p u))
  let H (ab : TuplePair ι m) (z : ι → Circle) := momentCoeff c ab * character (momentExp ab) z
  have ht₀ : 0 < t := (pow_pos (zero_lt_one.trans_le hX) _).trans ht
  have hL (ab : TuplePair ι m) : Integrable (L ab) := by
    simp only [L, character_primeFlow]
    exact (integrable_shellKernel_phase ht₀ _ _).const_mul _
  have hH (ab : TuplePair ι m) : Integrable (H ab) μ :=
    ((continuous_character (momentExp ab)).const_mul _).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hkey (v : ι → Fin 3) (hv : v ∈ S) :
      signCount 1 v + signCount 2 v = R ∧ signCount 1 v = signCount 2 v :=
    ⟨(signCount_add v).trans (hsize v hv), by simpa only [signCount_eq_card] using hbalance v hv⟩
  have hterm (ab : TuplePair ι m) (hab : ab ∈ T) :
      (∫ u, L ab u) = (↑(2 * Real.pi * t) : ℂ) * ∫ z, H ab z ∂μ := by
    obtain ⟨ha, hb⟩ := Finset.mem_product.mp hab
    have hcounts (j : Fin m) := And.intro (hkey _ (Fintype.mem_piFinset.mp ha j))
      (hkey _ (Fintype.mem_piFinset.mp hb j))
    have hN : (∑ i, heightPowers 1 2 ab i) = m * R := sum_heightPowers 1 2 ab fun j ↦ by
      obtain ⟨⟨ha₁, ha₂⟩, ⟨hb₁, hb₂⟩⟩ := hcounts j
      omega
    have hD : (∑ i, heightPowers 2 1 ab i) = m * R := sum_heightPowers 2 1 ab fun j ↦ by
      obtain ⟨⟨ha₁, ha₂⟩, ⟨hb₁, hb₂⟩⟩ := hcounts j
      omega
    dsimp only [L, H, μ]
    rw [integral_const_mul, integral_const_mul, integral_shell_character_eq hp hinj hpX hX ht ab hN hD]
    ring
  apply Complex.ofReal_injective
  calc
    _ = ∫ u, (↑(shellKernel t (9 * t / 8) u *
        ‖∑ v ∈ S, c v * monomial v (primeFlow p u)‖ ^ (2 * m)) : ℂ) :=
      (integral_ofReal (𝕜 := ℂ)).symm
    _ = ∫ u, ∑ ab ∈ T, L ab u := by
      apply integral_congr_ae
      filter_upwards with u
      rw [Complex.ofReal_mul, moment_expansion, Finset.mul_sum]
      exact Finset.sum_congr rfl fun ab _ ↦ by dsimp only [L]; ring
    _ = ∑ ab ∈ T, ∫ u, L ab u := integral_finsetSum _ fun ab _ ↦ hL ab
    _ = ∑ ab ∈ T, (↑(2 * Real.pi * t) : ℂ) * ∫ z, H ab z ∂μ := Finset.sum_congr rfl hterm
    _ = (↑(2 * Real.pi * t) : ℂ) * ∫ z, ∑ ab ∈ T, H ab z ∂μ := by
      rw [integral_finsetSum _ fun ab _ ↦ hH ab, Finset.mul_sum]
    _ = (↑(2 * Real.pi * t) : ℂ) *
        (∫ z, (↑(‖∑ v ∈ S, c v * monomial v z‖ ^ (2 * m)) : ℂ) ∂μ) := by
      simp_rw [moment_expansion, H, T]
    _ = _ := by
      simp only [Complex.ofReal_mul]
      congr 1
      exact integral_ofReal (𝕜 := ℂ)

end Masullo.PrimeCubeShellMoment
