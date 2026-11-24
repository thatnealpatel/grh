module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Analysis.Complex.Norm
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# The complex second-moment disk

Source: `0354c85b:.godel/bob/single-shift-decision.md:5–11`.
Consumer: the pointwise disk at height `3t` in `5ab1b80f:.godel/bob/all-pairs-10-2.md:9`.
Discovery pin: `5ab1b80f`. Owning check session: `01a20ce0-1582-79d6-b657-1b3239837bf7`.

For an arbitrary finite probability law on the complex unit circle with first moment `m`,
its second moment lies in the disk centered at `m ^ 2` of radius `1 - ‖m‖ ^ 2`.
Conversely, at most four nodes realize every point of this closed disk, by mixing two
perpendicular chords through `m` (or using one node when `‖m‖ = 1`). The result is pointwise;
it does not assert measurable selection, an integrated image, or a simultaneous completion.
-/

open scoped BigOperators ComplexConjugate

namespace Masullo.SecondMomentDisk

-- The two lengths are positive roots in opposite directions on the line through `m`.
private theorem chord (m u : ℂ) (hu : ‖u‖ = 1) (hR : 0 < 1 - ‖m‖ ^ 2) :
    ∃ (a b : ℝ) (z₀ z₁ : ℂ), 0 ≤ a ∧ 0 ≤ b ∧ ‖z₀‖ = 1 ∧ ‖z₁‖ = 1 ∧
      a + b = 1 ∧ (a : ℂ) * z₀ + (b : ℂ) * z₁ = m ∧
      (a : ℂ) * z₀ ^ 2 + (b : ℂ) * z₁ ^ 2 = m ^ 2 + ((1 - ‖m‖ ^ 2 : ℝ) : ℂ) * u ^ 2 := by
  let R : ℝ := 1 - ‖m‖ ^ 2
  let k : ℝ := (u * conj m).re
  let D : ℝ := Real.sqrt (k ^ 2 + R)
  let p : ℝ := D - k
  let n : ℝ := D + k
  have hD : D ^ 2 = k ^ 2 + R := Real.sq_sqrt (add_nonneg (sq_nonneg k) hR.le)
  have hD₀ : 0 ≤ D := Real.sqrt_nonneg _
  have hkD : |k| < D := by
    apply (sq_lt_sq₀ (abs_nonneg k) hD₀).mp
    rw [sq_abs, hD]
    exact lt_add_of_pos_right _ hR
  have hp : 0 < p := sub_pos.mpr (abs_lt.mp hkD).2
  have hn : 0 < n := by
    dsimp only [n]
    linarith [(abs_lt.mp hkD).1]
  have hpn : 0 < p + n := add_pos hp hn
  have hprod : p * n = R := by
    dsimp only [p, n]
    linear_combination hD
  have hunit (t : ℝ) (ht : t ^ 2 + 2 * k * t = R) : ‖m + (t : ℂ) * u‖ = 1 := by
    apply (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp
    rw [Complex.sq_norm, add_comm m, Complex.normSq_add, Complex.normSq_mul,
      Complex.normSq_ofReal, Complex.normSq_eq_norm_sq u, hu, Complex.normSq_eq_norm_sq m,
      mul_assoc (t : ℂ) u, Complex.re_ofReal_mul]
    change t * t * 1 ^ 2 + ‖m‖ ^ 2 + 2 * (t * k) = (1 : ℝ) ^ 2
    dsimp only [R] at ht
    linear_combination ht
  have hpunit : ‖m + (p : ℂ) * u‖ = 1 := hunit p (by
    dsimp only [p]
    linear_combination hD)
  have hnunit : ‖m + ((-n : ℝ) : ℂ) * u‖ = 1 := hunit (-n) (by
    dsimp only [n]
    linear_combination hD)
  let a : ℝ := n / (p + n)
  let b : ℝ := p / (p + n)
  have hab : a + b = 1 := by
    dsimp only [a, b]
    field_simp [hpn.ne']
    ring
  have hbal : a * p - b * n = 0 := by
    dsimp only [a, b]
    field_simp [hpn.ne']
    ring
  have hvar : a * p ^ 2 + b * n ^ 2 = R := by
    rw [← hprod]
    dsimp only [a, b]
    field_simp [hpn.ne']
  have habC : (a : ℂ) + b = 1 := by exact_mod_cast hab
  have hbalC : (a : ℂ) * p - (b : ℂ) * n = 0 := by exact_mod_cast hbal
  have hvarC : (a : ℂ) * (p : ℂ) ^ 2 + (b : ℂ) * (n : ℂ) ^ 2 = R := by exact_mod_cast hvar
  refine ⟨a, b, m + (p : ℂ) * u, m + ((-n : ℝ) : ℂ) * u,
    div_nonneg hn.le hpn.le, div_nonneg hp.le hpn.le, hpunit, hnunit, hab, ?_, ?_⟩
  · rw [Complex.ofReal_neg]
    linear_combination m * habC + u * hbalC
  · rw [Complex.ofReal_neg]
    linear_combination m ^ 2 * habC + (2 * m * u) * hbalC + u ^ 2 * hvarC

/-- The second moment of any finite probability law on the complex unit circle satisfies
the disk bound at its first moment. -/
public theorem norm_second_sub_sq_le {ι : Type*} (s : Finset ι) (p : ι → ℝ) (z : ι → ℂ)
    {m w : ℂ} (hp : ∀ i ∈ s, 0 ≤ p i) (hz : ∀ i ∈ s, ‖z i‖ = 1)
    (hmass : ∑ i ∈ s, p i = 1) (hm : ∑ i ∈ s, (p i : ℂ) * z i = m)
    (hw : ∑ i ∈ s, (p i : ℂ) * z i ^ 2 = w) :
    ‖w - m ^ 2‖ ≤ 1 - ‖m‖ ^ 2 := by
  have hmassC : ∑ i ∈ s, (p i : ℂ) = 1 := by
    rw [← Complex.ofReal_sum, hmass, Complex.ofReal_one]
  have hcenter : (∑ i ∈ s, (p i : ℂ) * (z i - m) ^ 2) = w - m ^ 2 := by
    calc
      _ = ∑ i ∈ s, ((p i : ℂ) * z i ^ 2 - ((p i : ℂ) * z i) * (2 * m) + (p i : ℂ) * m ^ 2) :=
        Finset.sum_congr rfl fun _ _ ↦ by ring
      _ = _ := by
        simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul, hw, hm, hmassC]
        ring
  have hcross : (∑ i ∈ s, p i * (z i * conj m).re) = ‖m‖ ^ 2 := by
    calc
      _ = (∑ i ∈ s, ((p i : ℂ) * z i) * conj m).re := by
        change _ = Complex.reAddGroupHom (∑ i ∈ s, ((p i : ℂ) * z i) * conj m)
        rw [map_sum]
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        change _ = (((p i : ℂ) * z i) * conj m).re
        rw [mul_assoc, Complex.re_ofReal_mul]
      _ = _ := by
        rw [← Finset.sum_mul, hm, Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
  have hvariance : (∑ i ∈ s, p i * ‖z i - m‖ ^ 2) = 1 - ‖m‖ ^ 2 := by
    calc
      _ = ∑ i ∈ s, (p i + p i * ‖m‖ ^ 2 - (p i * (z i * conj m).re) * 2) := by
        refine Finset.sum_congr rfl fun i hi ↦ ?_
        rw [Complex.sq_norm, Complex.normSq_sub, Complex.normSq_eq_norm_sq (z i),
          Complex.normSq_eq_norm_sq m, hz i hi]
        ring
      _ = _ := by
        simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.sum_mul, hmass, hcross]
        ring
  calc
    ‖w - m ^ 2‖ = ‖∑ i ∈ s, (p i : ℂ) * (z i - m) ^ 2‖ := by rw [hcenter]
    _ ≤ ∑ i ∈ s, ‖(p i : ℂ) * (z i - m) ^ 2‖ := norm_sum_le _ _
    _ = ∑ i ∈ s, p i * ‖z i - m‖ ^ 2 := by
      exact Finset.sum_congr rfl fun i hi ↦ by
        rw [norm_mul, Complex.norm_of_nonneg (hp i hi), norm_pow]
    _ = 1 - ‖m‖ ^ 2 := hvariance

-- At the center the direction is arbitrary; elsewhere take a square root of the unit direction.
private theorem exists_unit_sq_direction (d : ℂ) :
    ∃ u : ℂ, ‖u‖ = 1 ∧ d = (‖d‖ : ℂ) * u ^ 2 := by
  by_cases hd : d = 0
  · exact ⟨1, by simp, by simp [hd]⟩
  have hpos : 0 < ‖d‖ := norm_pos_iff.mpr hd
  have hc : (‖d‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hpos.ne'
  obtain ⟨u, hu⟩ := IsAlgClosed.exists_pow_nat_eq (d / (‖d‖ : ℂ)) (by decide : 0 < (2 : ℕ))
  refine ⟨u, (sq_eq_sq₀ (norm_nonneg u) zero_le_one).mp ?_, ?_⟩
  · rw [← norm_pow, hu, norm_div, Complex.norm_of_nonneg hpos.le, div_self hpos.ne', one_pow]
  · rw [hu, mul_comm, div_mul_cancel₀ _ hc]

/-- Every point of the closed disk is attained by nonnegative masses on at most four unit
nodes. `Fin 4` allows padding with zero masses; the nodes need not be distinct. -/
public theorem exists_four_node_law {m w : ℂ} (hm : ‖m‖ ≤ 1)
    (hw : ‖w - m ^ 2‖ ≤ 1 - ‖m‖ ^ 2) :
    ∃ (p : Fin 4 → ℝ) (z : Fin 4 → ℂ), (∀ i, 0 ≤ p i) ∧ (∀ i, ‖z i‖ = 1) ∧
      (∑ i, p i) = 1 ∧ (∑ i, (p i : ℂ) * z i) = m ∧ (∑ i, (p i : ℂ) * z i ^ 2) = w := by
  let R : ℝ := 1 - ‖m‖ ^ 2
  have hR₀ : 0 ≤ R := by
    have hs := (sq_le_sq₀ (norm_nonneg m) zero_le_one).mpr hm
    simpa [R] using sub_nonneg.mpr hs
  rcases hR₀.eq_or_lt with hR | hR
  · have hnorm : ‖m‖ = 1 := by
      apply (sq_eq_sq₀ (norm_nonneg m) zero_le_one).mp
      dsimp only [R] at hR
      linarith
    have heq : w = m ^ 2 := sub_eq_zero.mp (norm_le_zero_iff.mp (hw.trans hR.ge))
    exact ⟨![1, 0, 0, 0], fun _ ↦ m, by simp [Fin.forall_fin_succ], fun _ ↦ hnorm,
      by simp [Fin.sum_univ_four], by simp [Fin.sum_univ_four], by simp [Fin.sum_univ_four, heq]⟩
  obtain ⟨u, hu, hdir⟩ := exists_unit_sq_direction (w - m ^ 2)
  have hiu : ‖Complex.I * u‖ = 1 := by rw [norm_mul, Complex.norm_I, hu, one_mul]
  obtain ⟨a, b, z₀, z₁, ha, hb, hz₀, hz₁, hab, hfirst, hsecond⟩ := chord m u hu hR
  obtain ⟨c, d, z₂, z₃, hc, hd, hz₂, hz₃, hcd, hfirst', hsecond'⟩ := chord m (Complex.I * u) hiu hR
  rw [mul_pow, Complex.I_sq, neg_one_mul] at hsecond'
  -- Mix the two laws on the diameter with direction `u ^ 2`.
  let r : ℝ := ‖w - m ^ 2‖ / R
  let q₀ : ℝ := (1 + r) / 2
  let q₁ : ℝ := (1 - r) / 2
  have hr₀ : 0 ≤ r := div_nonneg (norm_nonneg _) hR.le
  have hr₁ : r ≤ 1 := (div_le_one₀ hR).mpr hw
  have hq₀ : 0 ≤ q₀ := div_nonneg (add_nonneg zero_le_one hr₀) (by norm_num)
  have hq₁ : 0 ≤ q₁ := div_nonneg (sub_nonneg.mpr hr₁) (by norm_num)
  have hsum : q₀ + q₁ = 1 := by dsimp only [q₀, q₁]; ring
  have hdiff : (q₀ - q₁) * R = ‖w - m ^ 2‖ := by
    have h : q₀ - q₁ = r := by dsimp only [q₀, q₁]; ring
    rw [h]
    exact div_mul_cancel₀ _ hR.ne'
  have hsumC : (q₀ : ℂ) + q₁ = 1 := by exact_mod_cast hsum
  have hdiffC : ((q₀ : ℂ) - q₁) * (R : ℂ) = (‖w - m ^ 2‖ : ℂ) := by exact_mod_cast hdiff
  refine ⟨![q₀ * a, q₀ * b, q₁ * c, q₁ * d], ![z₀, z₁, z₂, z₃], ?_, ?_, ?_, ?_, ?_⟩
  · simp [Fin.forall_fin_succ, mul_nonneg hq₀ ha, mul_nonneg hq₀ hb,
      mul_nonneg hq₁ hc, mul_nonneg hq₁ hd]
  · simp [Fin.forall_fin_succ, hz₀, hz₁, hz₂, hz₃]
  · simp [Fin.sum_univ_four]
    linear_combination q₀ * hab + q₁ * hcd + hsum
  · simp [Fin.sum_univ_four, Complex.ofReal_mul]
    linear_combination (q₀ : ℂ) * hfirst + (q₁ : ℂ) * hfirst' + m * hsumC
  · simp [Fin.sum_univ_four, Complex.ofReal_mul]
    change (a : ℂ) * z₀ ^ 2 + (b : ℂ) * z₁ ^ 2 = m ^ 2 + (R : ℂ) * u ^ 2 at hsecond
    change (c : ℂ) * z₂ ^ 2 + (d : ℂ) * z₃ ^ 2 = m ^ 2 + (R : ℂ) * (-u ^ 2) at hsecond'
    linear_combination (q₀ : ℂ) * hsecond + (q₁ : ℂ) * hsecond' + m ^ 2 * hsumC +
      u ^ 2 * hdiffC - hdir

/-- Exact characterization of attainable complex second moments at a fixed first moment. -/
public theorem second_moment_attainable_iff {m w : ℂ} (hm : ‖m‖ ≤ 1) :
    (∃ (p : Fin 4 → ℝ) (z : Fin 4 → ℂ), (∀ i, 0 ≤ p i) ∧ (∀ i, ‖z i‖ = 1) ∧
      (∑ i, p i) = 1 ∧ (∑ i, (p i : ℂ) * z i) = m ∧ (∑ i, (p i : ℂ) * z i ^ 2) = w) ↔
    ‖w - m ^ 2‖ ≤ 1 - ‖m‖ ^ 2 := by
  constructor
  · rintro ⟨p, z, hp, hz, hmass, hfirst, hsecond⟩
    exact norm_second_sub_sq_le Finset.univ p z (fun i _ ↦ hp i) (fun i _ ↦ hz i)
      hmass hfirst hsecond
  · exact exists_four_node_law hm

end Masullo.SecondMomentDisk
