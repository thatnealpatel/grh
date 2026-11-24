module

public import Mathlib.Analysis.BoundedVariation
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Nat.Totient
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# The finite centered unit reference

Source: `ec81e8cbeed7:.godel/bob/last-slot-residues.md:34–51`, equation (3)
and its translated refinement; consumed in `.godel/bob/separated-signed-tuples.md:41–51`
at discovery pin `a433ed178`.

This is a reference sum, not a comparison with the actual dependent residue.
Variation is pointwise, including at every sample. The centered endpoints are
real, even for odd moduli, and the lattice indices are signed integers.

Owning check session: `01a20f6c-c41c-70db-8373-949d4b4e2596`.
-/

open Finset MeasureTheory Set
open scoped BigOperators

namespace CenteredUnitReference

private theorem finite_mesh (H : ℝ → ℝ) (hH : Integrable H)
    (hBV : BoundedVariationOn H univ) (a h : ℝ) (hh : 0 < h) (N : ℕ) :
    |h * (∑ i ∈ range N, H (a + (i : ℝ) * h)) -
      (∫ x in a..(a + (N : ℝ) * h), H x)| ≤ h * (eVariationOn H univ).toReal := by
  let x (i : ℕ) := a + (i : ℝ) * h
  have hmono : Monotone x := by
    intro i j hij
    dsimp [x]
    gcongr
  have hfin (s : Set ℝ) : eVariationOn H s ≠ ⊤ :=
    ne_top_of_le_ne_top hBV (eVariationOn.mono H (subset_univ s))
  let v (i : ℕ) := (eVariationOn H (Icc (x i) (x (i + 1)))).toReal
  have hvar : ∑ i ∈ range N, v i ≤ (eVariationOn H univ).toReal := by
    dsimp [v]
    rw [← ENNReal.toReal_sum (fun i _ ↦ hfin _), eVariationOn.sum' H hmono]
    exact ENNReal.toReal_mono hBV (eVariationOn.mono H (subset_univ _))
  have hcell (i : ℕ) :
      |h * H (x i) - (∫ t in x i..x (i + 1), H t)| ≤ h * v i := by
    have hstep : x (i + 1) - x i = h := by simp [x, Nat.cast_add]; ring
    have hle : x i ≤ x (i + 1) := hmono (Nat.le_succ i)
    have hdiff : ∀ t ∈ uIoc (x i) (x (i + 1)), ‖H (x i) - H t‖ ≤ v i := by
      intro t ht
      rw [uIoc_of_le hle] at ht
      have he := eVariationOn.edist_le (f := H) (s := Icc (x i) (x (i + 1)))
        ⟨le_rfl, hle⟩ (Ioc_subset_Icc_self ht)
      simpa [v, edist_dist, Real.dist_eq, Real.norm_eq_abs] using
        ENNReal.toReal_mono (hfin _) he
    have hb := intervalIntegral.norm_integral_le_of_norm_le_const hdiff
    rw [intervalIntegral.integral_sub (intervalIntegrable_const) hH.intervalIntegrable,
      intervalIntegral.integral_const, smul_eq_mul, hstep, abs_of_pos hh,
      Real.norm_eq_abs, mul_comm (v i)] at hb
    exact hb
  suffices |h * (∑ i ∈ range N, H (x i)) - (∫ t in x 0..x N, H t)| ≤
      h * (eVariationOn H univ).toReal by
    simpa only [x, Nat.cast_zero, zero_mul, add_zero] using this
  rw [← intervalIntegral.sum_integral_adjacent_intervals (a := x)
    (fun _ _ ↦ hH.intervalIntegrable), mul_sum, ← sum_sub_distrib]
  calc
    _ ≤ ∑ i ∈ range N, |h * H (x i) - (∫ t in x i..x (i + 1), H t)| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ range N, h * v i := sum_le_sum fun i _ ↦ hcell i
    _ ≤ _ := by rw [← mul_sum]; exact mul_le_mul_of_nonneg_left hvar hh.le

/-- For any translate and any positive spacing `h`, the sum on the signed
lattice differs from the integral divided by `h` by at most the total
variation. The open support interval makes the sum finite. -/
public theorem translated_mesh_error (H : ℝ → ℝ) (hH : Integrable H)
    (hBV : BoundedVariationOn H univ) (a h A B : ℝ) (hh : 0 < h) (hAB : A ≤ B)
    (hzero : ∀ t ∉ Ioo A B, H t = 0) :
    |(∑' n : ℤ, H (a + (n : ℝ) * h)) - h⁻¹ * (∫ t, H t)| ≤
      (eVariationOn H univ).toReal := by
  let p : ℤ := ⌊(A - a) / h⌋
  let q : ℤ := ⌈(B - a) / h⌉
  have hp : a + (p : ℝ) * h ≤ A := by
    have hf := (le_div_iff₀ hh).mp (Int.floor_le ((A - a) / h))
    dsimp [p]
    linarith
  have hq : B ≤ a + (q : ℝ) * h := by
    have hc := (div_le_iff₀ hh).mp (Int.le_ceil ((B - a) / h))
    dsimp [q]
    linarith
  have hmono : StrictMono (fun n : ℤ ↦ a + (n : ℝ) * h) := by
    intro i j hij
    have hij' : (i : ℝ) < (j : ℝ) := by exact_mod_cast hij
    exact add_lt_add_right (mul_lt_mul_of_pos_right hij' hh) a
  have hpq : p ≤ q := hmono.le_iff_le.mp (hp.trans (hAB.trans hq))
  have hs : (∑' n : ℤ, H (a + (n : ℝ) * h)) =
      ∑ i ∈ range (q - p).toNat, H ((a + (p : ℝ) * h) + (i : ℝ) * h) := by
    rw [tsum_eq_sum (s := Finset.Ico p q), Int.Ico_eq_finset_map, sum_map]
    · apply sum_congr rfl
      intro i _
      change H (a + ((p + (i : ℤ) : ℤ) : ℝ) * h) = _
      rw [Int.cast_add, Int.cast_natCast]
      congr 1
      ring
    · intro n hn
      apply hzero
      rintro ⟨hlo, hhi⟩
      exact hn (Finset.mem_Ico.mpr ⟨(hmono.lt_iff_lt.mp (hp.trans_lt hlo)).le,
        hmono.lt_iff_lt.mp (hhi.trans_le hq)⟩)
  have hcast : ((q - p).toNat : ℝ) = (q : ℝ) - (p : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg (sub_nonneg.mpr hpq)
  have hend : (a + (p : ℝ) * h) + ((q - p).toNat : ℝ) * h = a + (q : ℝ) * h := by
    rw [hcast]
    ring
  have hint : (∫ t in (a + (p : ℝ) * h)..(a + (q : ℝ) * h), H t) = ∫ t, H t := by
    rw [intervalIntegral.integral_of_le (hmono.monotone hpq)]
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro t ht
    exact hzero t fun ht' ↦ ht ⟨hp.trans_lt ht'.1, ht'.2.le.trans hq⟩
  have hf := finite_mesh H hH hBV (a + (p : ℝ) * h) h hh (q - p).toNat
  rw [hend, hint, ← hs] at hf
  have heq : h * ((∑' n : ℤ, H (a + (n : ℝ) * h)) - h⁻¹ * (∫ t, H t)) =
      h * (∑' n : ℤ, H (a + (n : ℝ) * h)) - (∫ t, H t) := by
    rw [mul_sub, ← mul_assoc, mul_inv_cancel₀ hh.ne', one_mul]
  rw [← heq, abs_mul, abs_of_pos hh] at hf
  exact le_of_mul_le_mul_left hf hh

/-- The signed integer representatives in the real half-open centered interval. -/
public noncomputable def centered (k : ℕ) : Finset ℤ :=
  Finset.Ioc ⌊-(k : ℝ) / 2⌋ ⌊(k : ℝ) / 2⌋

public theorem mem_centered {k : ℕ} {j : ℤ} :
    j ∈ centered k ↔ -(k : ℝ) / 2 < (j : ℝ) ∧ (j : ℝ) ≤ (k : ℝ) / 2 := by
  simp only [centered, Finset.mem_Ioc, Int.floor_lt, Int.le_floor]

/-- A single divisor/congruence term is an actual translated progression.
The cut to centered representatives loses no nonzero sample. -/
private theorem divisor_mesh (H : ℝ → ℝ) (hH : Integrable H)
    (hBV : BoundedVariationOn H univ) {k Q d : ℕ} (hk : 0 < k) (hQ : 0 < Q)
    (hd : 0 < d) (hdQ : d.Coprime Q) (ℓ : ℤ) {V : ℝ} (hV : 0 < V)
    (hzero : ∀ t ∉ Ioo (-(k : ℝ) / (2 * V)) ((k : ℝ) / (2 * V)), H t = 0) :
    |(∑ j ∈ centered k with Int.ModEq (Q : ℤ) j ℓ ∧ (d : ℤ) ∣ j, H ((j : ℝ) / V)) -
      (V / ((d : ℝ) * (Q : ℝ))) * (∫ t, H t)| ≤ (eVariationOn H univ).toReal := by
  obtain ⟨y, hy⟩ := Int.mod_coprime hdQ
  let r : ℤ := (d : ℤ) * y * ℓ
  let m : ℤ := (d : ℤ) * (Q : ℤ)
  have hrQ : Int.ModEq (Q : ℤ) r ℓ := by simpa [r] using hy.mul_right ℓ
  have hrd : (d : ℤ) ∣ r := ⟨y * ℓ, by simp [r, mul_assoc]⟩
  have hcong (j : ℤ) : Int.ModEq m j r ↔ Int.ModEq (Q : ℤ) j ℓ ∧ (d : ℤ) ∣ j := by
    have hc : (d : ℤ).natAbs.Coprime (Q : ℤ).natAbs := by simpa using hdQ
    dsimp only [m]
    rw [← Int.modEq_and_modEq_iff_modEq_mul hc]
    constructor
    · rintro ⟨hjd, hjQ⟩
      exact ⟨hjQ.trans hrQ, hjd.dvd_iff.mpr hrd⟩
    · rintro ⟨hjQ, hjd⟩
      exact ⟨(Int.modEq_zero_iff_dvd.mpr hjd).trans
        (Int.modEq_zero_iff_dvd.mpr hrd).symm, hjQ.trans hrQ.symm⟩
  let f (n : ℤ) := r + m * n
  have hm : 0 < m := mul_pos (by exact_mod_cast hd) (by exact_mod_cast hQ)
  have hfinj : Function.Injective f := by
    intro n n' hn
    exact mul_left_cancel₀ hm.ne' (add_left_cancel (show r + m * n = r + m * n' from hn))
  let S := (centered k).filter fun j ↦ Int.ModEq (Q : ℤ) j ℓ ∧ (d : ℤ) ∣ j
  have hmem (j : ℤ) : j ∈ S ↔ j ∈ centered k ∧ Int.ModEq m j r := by
    simp only [S, mem_filter, hcong]
  have hsum : (∑ j ∈ S, H ((j : ℝ) / V)) = ∑' n : ℤ, H ((f n : ℝ) / V) := by
    rw [tsum_eq_sum (s := S.preimage f hfinj.injOn)]
    · symm
      refine Finset.sum_preimage f S hfinj.injOn (fun j ↦ H ((j : ℝ) / V)) ?_
      intro j hj hnot
      obtain ⟨n, hn⟩ := Int.modEq_iff_dvd.mp ((hmem j).mp hj).2.symm
      exact (hnot ⟨n, by dsimp [f]; linarith only [hn]⟩).elim
    · intro n hn
      have hfn : Int.ModEq m (f n) r := Int.modEq_add_fac_self
      have hnot : f n ∉ centered k := fun h ↦
        hn (Finset.mem_preimage.mpr ((hmem _).mpr ⟨h, hfn⟩))
      apply hzero
      rintro ⟨hl, hu⟩
      apply hnot
      rw [mem_centered]
      have ht : (-(k : ℝ) / (2 * V)) * V = -(k : ℝ) / 2 := by
        field_simp
      have ht' : ((k : ℝ) / (2 * V)) * V = (k : ℝ) / 2 := by
        field_simp
      exact ⟨ht ▸ (lt_div_iff₀ hV).mp hl, (ht' ▸ (div_lt_iff₀ hV).mp hu).le⟩
  have hstep : 0 < (d : ℝ) * (Q : ℝ) / V :=
    div_pos (mul_pos (by exact_mod_cast hd) (by exact_mod_cast hQ)) hV
  have hAB : -(k : ℝ) / (2 * V) ≤ (k : ℝ) / (2 * V) := by
    apply div_le_div_of_nonneg_right _ (by positivity)
    have hk' : (0 : ℝ) ≤ k := by positivity
    linarith
  have hf (n : ℤ) : (f n : ℝ) / V = (r : ℝ) / V + (n : ℝ) * ((d : ℝ) * (Q : ℝ) / V) := by
    simp only [f, m, Int.cast_add, Int.cast_mul, Int.cast_natCast]
    ring
  change |(∑ j ∈ S, H ((j : ℝ) / V)) - _| ≤ _
  rw [hsum]
  simp_rw [hf]
  simpa only [inv_div] using translated_mesh_error H hH hBV ((r : ℝ) / V)
    ((d : ℝ) * (Q : ℝ) / V) _ _ hstep hAB hzero

open scoped ArithmeticFunction.Moebius

private theorem mobius_coprime (k : ℕ) (hk : 0 < k) (j : ℤ) :
    (∑ d ∈ k.divisors with ((d : ℕ) : ℤ) ∣ j, (μ d : ℝ)) =
      if j.natAbs.Coprime k then 1 else 0 := by
  let g := j.natAbs.gcd k
  have hg : g ≠ 0 := by
    intro hg
    have hgk := Nat.gcd_dvd_right j.natAbs k
    change g ∣ k at hgk
    exact hk.ne' (by simpa [hg] using hgk)
  have hfilter : (k.divisors.filter fun d ↦ ((d : ℕ) : ℤ) ∣ j) = g.divisors := by
    ext d
    simp only [Finset.mem_filter, Nat.mem_divisors, Int.natCast_dvd]
    constructor
    · rintro ⟨⟨hdk, _⟩, hdj⟩
      exact ⟨Nat.dvd_gcd hdj hdk, hg⟩
    · rintro ⟨hdg, _⟩
      exact ⟨⟨hdg.trans (Nat.gcd_dvd_right _ _), hk.ne'⟩, hdg.trans (Nat.gcd_dvd_left _ _)⟩
  have h := congrArg (fun F : ArithmeticFunction ℤ ↦ F g)
    ArithmeticFunction.moebius_mul_coe_zeta
  rw [ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.one_apply] at h
  rw [hfilter, ← Int.cast_sum, h]
  simp [g, Nat.Coprime]

private theorem mobius_totient {k : ℕ} (hk : 0 < k) :
    (∑ d ∈ k.divisors, (μ d : ℝ) * (d : ℝ)⁻¹) = (k.totient : ℝ) / k := by
  have h := (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq
    (f := fun n ↦ (n.totient : ℝ)) (g := fun n ↦ (n : ℝ))).mp
    (fun n _ ↦ by exact_mod_cast Nat.sum_totient n) k hk
  rw [Nat.sum_divisorsAntidiagonal (fun d n ↦ (μ d : ℝ) * (n : ℝ))] at h
  rw [← h, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro d hd
  have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  have hd' : (d : ℝ) ≠ 0 := by exact_mod_cast (Nat.pos_of_mem_divisors hd).ne'
  have hmul : ((k / d : ℕ) : ℝ) * (d : ℝ) = k := by
    exact_mod_cast Nat.div_mul_cancel (Nat.dvd_of_mem_divisors hd)
  have hquot : ((k / d : ℕ) : ℝ) / (k : ℝ) = (d : ℝ)⁻¹ := by
    field_simp
    exact hmul
  rw [mul_div_assoc, hquot]

private theorem card_squarefree_divisors {k : ℕ} (hk : k ≠ 0) :
    (k.divisors.filter Squarefree).card = 2 ^ k.primeFactors.card := by
  have h := congrArg Multiset.card (Nat.divisors_filter_squarefree hk)
  rw [Multiset.card_map] at h
  change (k.divisors.filter Squarefree).card =
    (UniqueFactorizationMonoid.normalizedFactors k).toFinset.powerset.card at h
  rw [Finset.card_powerset, Nat.factors_eq] at h
  exact h

/-- The unnormalized centered unit reference in a congruence class. The error
is one pointwise variation budget per squarefree divisor of `k`. -/
public theorem centered_unit_reference (H : ℝ → ℝ) (hH : Integrable H)
    (hBV : BoundedVariationOn H univ) {k Q : ℕ} (hk : 0 < k) (hQ : 0 < Q)
    (hkQ : k.Coprime Q) (ℓ : ℤ) {V : ℝ} (hV : 0 < V)
    (hzero : ∀ t ∉ Ioo (-(k : ℝ) / (2 * V)) ((k : ℝ) / (2 * V)), H t = 0) :
    |(∑ j ∈ centered k with Int.ModEq (Q : ℤ) j ℓ ∧ j.natAbs.Coprime k,
      H ((j : ℝ) / V)) - (k.totient : ℝ) * V / ((k : ℝ) * (Q : ℝ)) * (∫ t, H t)| ≤
      (2 : ℝ) ^ k.primeFactors.card * (eVariationOn H univ).toReal := by
  let R := (centered k).filter fun j ↦ Int.ModEq (Q : ℤ) j ℓ
  let S (d : ℕ) := (R.filter fun j ↦ (d : ℤ) ∣ j).sum fun j ↦ H ((j : ℝ) / V)
  let M (d : ℕ) := V / ((d : ℝ) * (Q : ℝ)) * (∫ t, H t)
  let var := (eVariationOn H univ).toReal
  have hmesh (d : ℕ) (hd : d ∈ k.divisors) : |S d - M d| ≤ var := by
    simpa only [S, R, M, var, Finset.filter_filter] using
      divisor_mesh H hH hBV hk hQ (Nat.pos_of_mem_divisors hd)
        (Nat.Coprime.coprime_dvd_left (Nat.dvd_of_mem_divisors hd) hkQ) ℓ hV hzero
  have hsum : (∑ j ∈ centered k with Int.ModEq (Q : ℤ) j ℓ ∧ j.natAbs.Coprime k,
      H ((j : ℝ) / V)) = ∑ d ∈ k.divisors, (μ d : ℝ) * S d := by
    rw [← Finset.filter_filter]
    change (∑ j ∈ R with j.natAbs.Coprime k, H ((j : ℝ) / V)) = _
    calc
      _ = ∑ j ∈ R, (∑ d ∈ k.divisors with ((d : ℕ) : ℤ) ∣ j, (μ d : ℝ)) * H ((j : ℝ) / V) := by
        rw [Finset.sum_filter]
        apply sum_congr rfl
        intro j _
        rw [mobius_coprime k hk]
        split <;> simp_all
      _ = ∑ d ∈ k.divisors, (μ d : ℝ) * S d := by
        simp only [S, Finset.sum_filter, Finset.sum_mul, Finset.mul_sum]
        rw [Finset.sum_comm]
        apply sum_congr rfl
        intro d _
        apply sum_congr rfl
        intro j _
        split <;> simp_all
  have hmain : (∑ d ∈ k.divisors, (μ d : ℝ) * M d) =
      (k.totient : ℝ) * V / ((k : ℝ) * (Q : ℝ)) * (∫ t, H t) := calc
    _ = (∑ d ∈ k.divisors, (μ d : ℝ) * (d : ℝ)⁻¹) * (V / Q * (∫ t, H t)) := by
      rw [Finset.sum_mul]
      apply sum_congr rfl
      intro d _
      simp only [M, div_eq_mul_inv, mul_inv_rev]
      ring
    _ = _ := by
      rw [mobius_totient hk]
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
  rw [hsum, ← hmain, ← Finset.sum_sub_distrib]
  simp_rw [← mul_sub]
  calc
    _ ≤ ∑ d ∈ k.divisors, |(μ d : ℝ) * (S d - M d)| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ d ∈ k.divisors, if Squarefree d then var else 0 := by
      apply sum_le_sum
      intro d hd
      simp only [abs_mul, ← Int.cast_abs, ArithmeticFunction.abs_moebius]
      by_cases hs : Squarefree d
      · simpa [hs] using hmesh d hd
      · simp [hs]
    _ = _ := by
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, card_squarefree_divisors hk.ne']
      push_cast
      rfl

/-- The signed reference has zero main term when the kernel has zero integral. -/
public theorem centered_unit_reference_zero_integral (H : ℝ → ℝ) (hH : Integrable H)
    (hBV : BoundedVariationOn H univ) {k Q : ℕ} (hk : 0 < k) (hQ : 0 < Q)
    (hkQ : k.Coprime Q) (ℓ : ℤ) {V : ℝ} (hV : 0 < V)
    (hzero : ∀ t ∉ Ioo (-(k : ℝ) / (2 * V)) ((k : ℝ) / (2 * V)), H t = 0)
    (hmean : (∫ t, H t) = 0) :
    |∑ j ∈ centered k with Int.ModEq (Q : ℤ) j ℓ ∧ j.natAbs.Coprime k, H ((j : ℝ) / V)| ≤
      (2 : ℝ) ^ k.primeFactors.card * (eVariationOn H univ).toReal := by
  simpa only [hmean, mul_zero, sub_zero] using
    centered_unit_reference H hH hBV hk hQ hkQ ℓ hV hzero

/-- Equation (3): the congruence-free reference normalized by the totient. -/
public theorem centered_unit_reference_normalized (H : ℝ → ℝ) (hH : Integrable H)
    (hBV : BoundedVariationOn H univ) {k : ℕ} (hk : 0 < k) {V : ℝ} (hV : 0 < V)
    (hzero : ∀ t ∉ Ioo (-(k : ℝ) / (2 * V)) ((k : ℝ) / (2 * V)), H t = 0) :
    |(∑ j ∈ centered k with j.natAbs.Coprime k, H ((j : ℝ) / V)) / (k.totient : ℝ) -
      V / (k : ℝ) * (∫ t, H t)| ≤
      (2 : ℝ) ^ k.primeFactors.card * (eVariationOn H univ).toReal / (k.totient : ℝ) := by
  have h := centered_unit_reference H hH hBV hk Nat.one_pos (Nat.coprime_one_right k) 0 hV hzero
  simp only [Nat.cast_one, Int.modEq_one, true_and, mul_one] at h
  have hp : (0 : ℝ) < k.totient := by exact_mod_cast Nat.totient_pos.mpr hk
  have hrew : (k.totient : ℝ) * V / (k : ℝ) * (∫ t, H t) =
      (V / (k : ℝ) * (∫ t, H t)) * (k.totient : ℝ) := by ring
  rw [hrew] at h
  rw [← mul_div_cancel_right₀ (V / (k : ℝ) * (∫ t, H t)) hp.ne', ← sub_div,
    abs_div, abs_of_pos hp]
  exact div_le_div_of_nonneg_right h hp.le

end CenteredUnitReference
