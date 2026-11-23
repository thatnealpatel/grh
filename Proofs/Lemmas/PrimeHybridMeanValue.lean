module

public import Lemmas.StoppedPrimeProductMoment
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Normed.Ring.Finite
import Mathlib.Data.Nat.Dist
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

/-! # The prime-conductor hybrid mean-value estimate

Source: `85842a8:.godel/alice/prime-conductor-window.md`, lines 25–40; used for the
length-stopped moment in `145f6475:.godel/alice/stopped-conductor-window.md`, lines 23–31.
Source scan: `bb055047`. Owning check session: `01a209a4-4028-76c1-a295-487f5bedcbac`.

The estimate is for arbitrary complex coefficients of a finite Dirichlet polynomial,
averaged over all characters at a single prime modulus (including the principal character).
It uses no sparsity or positivity hypothesis on the coefficients.
-/

open MeasureTheory
open scoped BigOperators

namespace Masullo.PrimeHybridMeanValue

private noncomputable def phase (x u : ℝ) : ℂ :=
  Complex.exp (Complex.I * (x : ℂ) * (u : ℂ))

private theorem continuous_phase (x : ℝ) : Continuous (phase x) := by
  unfold phase
  fun_prop

private theorem phase_mul_conj (x y u : ℝ) :
    phase x u * (starRingEnd ℂ) (phase y u) = phase (x - y) u := by
  rw [phase, phase, phase, ← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  simp only [map_mul, Complex.conj_I, Complex.conj_ofReal, Complex.ofReal_sub]
  ring

private theorem norm_phase (x u : ℝ) : ‖phase x u‖ = 1 := by
  simp [phase, Complex.norm_exp, Complex.mul_re, Complex.mul_im]

private noncomputable def kernel (T x : ℝ) : ℂ := ∫ u in -T..T, phase x u

private theorem kernel_zero (T : ℝ) : kernel T 0 = (↑(2 * T) : ℂ) := by
  simp [kernel, phase, intervalIntegral.integral_const, Complex.real_smul]
  ring

private theorem norm_kernel_le (T : ℝ) {x : ℝ} (hx : x ≠ 0) :
    ‖kernel T x‖ ≤ 2 / |x| := by
  have hc : Complex.I * (x : ℂ) ≠ 0 :=
    mul_ne_zero Complex.I_ne_zero (Complex.ofReal_ne_zero.mpr hx)
  simp only [kernel, phase]
  rw [integral_exp_mul_complex hc, norm_div, norm_mul, Complex.norm_I,
    one_mul, Complex.norm_real, Real.norm_eq_abs]
  apply div_le_div_of_nonneg_right _ (abs_nonneg x)
  exact (norm_sub_le (phase x T) (phase x (-T))).trans_eq (by rw [norm_phase, norm_phase]; norm_num)

private theorem log_gap_ordered {m n N : ℕ} (hm : 1 ≤ m) (h : m < n) (hn : n ≤ N) :
    ((n - m : ℕ) : ℝ) / N ≤ Real.log n - Real.log m := by
  have hm' : 0 < (m : ℝ) := by exact_mod_cast (show 0 < m by omega)
  have hn' : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hnN : (n : ℝ) ≤ N := by exact_mod_cast hn
  have hlog := Real.one_sub_inv_le_log_of_pos (div_pos hn' hm')
  rw [Real.log_div hn'.ne' hm'.ne', inv_div, ← div_self hn'.ne', ← sub_div] at hlog
  rw [Nat.cast_sub h.le]
  exact (div_le_div_of_nonneg_left (sub_nonneg.mpr (by exact_mod_cast h.le)) hn' hnN).trans hlog

private theorem log_gap {m n N : ℕ} (hm : m ∈ Finset.Icc 1 N) (hn : n ∈ Finset.Icc 1 N)
    (hne : m ≠ n) : (m.dist n : ℝ) / N ≤ |Real.log m - Real.log n| := by
  obtain ⟨hm₁, hmN⟩ := Finset.mem_Icc.mp hm
  obtain ⟨hn₁, hnN⟩ := Finset.mem_Icc.mp hn
  rcases lt_or_gt_of_ne hne with h | h
  · rw [Nat.dist_eq_sub_of_le h.le, abs_sub_comm]
    exact (log_gap_ordered hm₁ h hnN).trans (le_abs_self _)
  · rw [Nat.dist_comm, Nat.dist_eq_sub_of_le h.le]
    exact (log_gap_ordered hn₁ h hmN).trans (le_abs_self _)

private theorem norm_kernel_log_le {m n N : ℕ} (T : ℝ)
    (hm : m ∈ Finset.Icc 1 N) (hn : n ∈ Finset.Icc 1 N) (hne : m ≠ n) :
    ‖kernel T (Real.log m - Real.log n)‖ ≤ (2 * (N : ℝ)) * (m.dist n : ℝ)⁻¹ := by
  have hN : 0 < (N : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one
    ((Finset.mem_Icc.mp hm).1.trans (Finset.mem_Icc.mp hm).2))
  have hd : 0 < (m.dist n : ℝ) := by
    rcases lt_or_gt_of_ne hne with h | h
    · rw [Nat.dist_eq_sub_of_le h.le]; exact_mod_cast Nat.sub_pos_of_lt h
    · rw [Nat.dist_comm, Nat.dist_eq_sub_of_le h.le]; exact_mod_cast Nat.sub_pos_of_lt h
  have hgap := log_gap hm hn hne
  have hx : Real.log m - Real.log n ≠ 0 := by
    intro hz
    rw [hz, abs_zero] at hgap
    exact (div_pos hd hN).not_ge hgap
  calc
    _ ≤ 2 / |Real.log m - Real.log n| := norm_kernel_le T hx
    _ ≤ 2 / ((m.dist n : ℝ) / N) := div_le_div_of_nonneg_left (by norm_num) (div_pos hd hN) hgap
    _ = _ := by rw [div_div_eq_mul_div, div_eq_mul_inv]

private theorem conj_char_apply {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {x : ZMod q} (hx : IsUnit x) : (starRingEnd ℂ) (χ x) = χ x⁻¹ := by
  let f : (ZMod q)ˣ →* ℂ := χ.toMonoidHom.comp (Units.coeHom _)
  have hv : ‖χ x‖ = 1 := by
    rw [← hx.unit_spec]
    exact (f.isOfFinOrder (isOfFinOrder_of_finite hx.unit)).norm_eq_one
  rw [← Complex.inv_eq_conj hv]
  apply inv_eq_of_mul_eq_one_left
  rw [← map_mul, (ZMod.inv_mul_eq_one_of_isUnit hx x).mpr rfl, map_one]

private noncomputable def residueIndicator {q : ℕ} (x y : ZMod q) : ℂ := by
  classical exact if IsUnit y ∧ x = y then 1 else 0

private theorem char_sieve {q : ℕ} (hq : q.Prime) (x y : ZMod q) :
    (((q : ℝ) - 1 : ℝ) : ℂ)⁻¹ *
      (∑ χ : DirichletCharacter ℂ q, χ x * (starRingEnd ℂ) (χ y)) =
    residueIndicator x y := by
  classical
  let : NeZero q := ⟨hq.ne_zero⟩
  let : NeZero (Monoid.exponent (ZMod q)ˣ) := ⟨Monoid.exponent_ne_zero_of_finite⟩
  have hq' : 1 < (q : ℝ) := by exact_mod_cast hq.one_lt
  by_cases hy : IsUnit y
  · simp_rw [conj_char_apply _ hy]
    have hcomm : (∑ χ : DirichletCharacter ℂ q, χ x * χ y⁻¹) =
        ∑ χ : DirichletCharacter ℂ q, χ y⁻¹ * χ x :=
      Finset.sum_congr rfl (fun _ _ ↦ mul_comm _ _)
    rw [hcomm, DirichletCharacter.sum_char_inv_mul_char_eq ℂ hy x, Nat.totient_prime hq]
    by_cases hxy : x = y
    · have hcast : ((q - 1 : ℕ) : ℂ) = (((q : ℝ) - 1 : ℝ) : ℂ) := by
        rw [Nat.cast_sub hq.one_lt.le, Complex.ofReal_sub, Complex.ofReal_natCast,
          Complex.ofReal_one, Nat.cast_one]
      simp only [hxy, hy, hcast, residueIndicator, and_self, ite_true]
      exact inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr (sub_ne_zero.mpr hq'.ne'))
    · simp [hxy, Ne.symm hxy, residueIndicator]
  · simp [hy, MulChar.map_nonunit _ hy, residueIndicator]

-- Reindex each side of a congruence row by its strictly positive quotient gap.
private theorem sum_inv_gap_le {s : Finset ℕ} {g : ℕ → ℕ} {q N : ℕ} (hq : 0 < q)
    (hinj : Set.InjOn g (s : Set ℕ)) (hg : ∀ n ∈ s, 0 < g n ∧ g n ≤ N ∧ q ∣ g n) :
    (∑ n ∈ s, (g n : ℝ)⁻¹) ≤ (q : ℝ)⁻¹ * (harmonic N : ℝ) := by
  simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast, Finset.mul_sum]
  have hmul n (hn : n ∈ s) : g n / q * q = g n := Nat.div_mul_cancel (hg n hn).2.2
  apply Finset.sum_le_sum_of_injOn (fun n ↦ g n / q)
  · intro i hi j hj hij
    apply hinj hi hj
    change g i / q = g j / q at hij
    rw [← hmul i hi, ← hmul j hj, hij]
  · intro k hk
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hk
    have hpos : 1 ≤ g n / q := Nat.div_pos (Nat.le_of_dvd (hg n hn).1 (hg n hn).2.2) hq
    exact Finset.mem_Icc.mpr ⟨hpos, (Nat.div_le_self ..).trans (hg n hn).2.1⟩
  · intro n hn
    rw [← mul_inv_rev, ← Nat.cast_mul, hmul n hn]
  · exact fun k _ _ ↦ mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg q))
      (inv_nonneg.mpr (Nat.cast_nonneg k))

private theorem dvd_gap {q m n : ℕ} (h : m ≤ n) (he : (m : ZMod q) = (n : ZMod q)) :
    q ∣ n - m := by
  exact Int.natCast_dvd_natCast.mp (by
    rw [Int.natCast_sub h]
    exact ((ZMod.natCast_eq_natCast_iff m n q).mp he).dvd)

private noncomputable def rowWeight (q N : ℕ) (T : ℝ) (m n : ℕ) : ℝ :=
  if m = n then 2 * T else
    if (m : ZMod q) = (n : ZMod q) then (2 * (N : ℝ)) * (m.dist n : ℝ)⁻¹ else 0

private theorem rowWeight_nonneg {q N : ℕ} {T : ℝ} (hT : 0 ≤ T) (m n : ℕ) :
    0 ≤ rowWeight q N T m n := by
  unfold rowWeight
  split_ifs
  · positivity
  · positivity
  · exact le_rfl

private theorem rowWeight_symm (q N : ℕ) (T : ℝ) (m n : ℕ) :
    rowWeight q N T m n = rowWeight q N T n m := by
  by_cases he : m = n
  · simp [rowWeight, he]
  · by_cases hz : (m : ZMod q) = (n : ZMod q)
    · simp only [rowWeight, ite_eq_right he, ite_eq_right (Ne.symm he), ite_eq_left hz,
        ite_eq_left hz.symm]
      rw [Nat.dist_comm]
    · simp only [rowWeight, ite_eq_right he, ite_eq_right (Ne.symm he), ite_eq_right hz,
        ite_eq_right (Ne.symm hz)]

private theorem sum_rowWeight_le {q N m : ℕ} (hq : 0 < q) (T : ℝ)
    (hm : m ∈ Finset.Icc 1 N) :
    (∑ n ∈ Finset.Icc 1 N, rowWeight q N T m n) ≤
      2 * T + 4 * ((N : ℝ) / q) * (harmonic N : ℝ) := by
  classical
  let s := Finset.Icc 1 N
  let up := s.filter (fun n ↦ m < n ∧ (m : ZMod q) = (n : ZMod q))
  let dn := s.filter (fun n ↦ n < m ∧ (m : ZMod q) = (n : ZMod q))
  have hu : (∑ n ∈ up, ((n - m : ℕ) : ℝ)⁻¹) ≤ (q : ℝ)⁻¹ * (harmonic N : ℝ) := by
    apply sum_inv_gap_le hq
    · intro i hi j hj hij
      have hi' := (Finset.mem_filter.mp hi).2.1
      have hj' := (Finset.mem_filter.mp hj).2.1
      change i - m = j - m at hij
      omega
    · intro n hn
      obtain ⟨hn, hmn, he⟩ := Finset.mem_filter.mp hn
      exact ⟨Nat.sub_pos_of_lt hmn, (Nat.sub_le ..).trans (Finset.mem_Icc.mp hn).2,
        dvd_gap hmn.le he⟩
  have hd : (∑ n ∈ dn, ((m - n : ℕ) : ℝ)⁻¹) ≤ (q : ℝ)⁻¹ * (harmonic N : ℝ) := by
    apply sum_inv_gap_le hq
    · intro i hi j hj hij
      have hi' := (Finset.mem_filter.mp hi).2.1
      have hj' := (Finset.mem_filter.mp hj).2.1
      change m - i = m - j at hij
      omega
    · intro n hn
      obtain ⟨_, hnm, he⟩ := Finset.mem_filter.mp hn
      exact ⟨Nat.sub_pos_of_lt hnm, (Nat.sub_le ..).trans (Finset.mem_Icc.mp hm).2,
        dvd_gap hnm.le he.symm⟩
  calc
    _ = 2 * T + (2 * (N : ℝ)) * ((∑ n ∈ up, ((n - m : ℕ) : ℝ)⁻¹) +
        (∑ n ∈ dn, ((m - n : ℕ) : ℝ)⁻¹)) := by
      have hdiag : (∑ n ∈ s, if m = n then 2 * T else 0) = 2 * T := by
        rw [Finset.sum_ite_eq, ite_eq_left hm]
      conv_rhs => rw [← hdiag]
      simp only [up, dn, Finset.sum_filter, mul_add, Finset.mul_sum, mul_ite, mul_zero,
        ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro n _
      rcases lt_trichotomy m n with h | rfl | h
      · rw [rowWeight, ite_eq_right h.ne, Nat.dist_eq_sub_of_le h.le]
        simp [h, h.ne, h.not_gt]
      · simp [rowWeight]
      · rw [rowWeight, ite_eq_right h.ne', Nat.dist_comm, Nat.dist_eq_sub_of_le h.le]
        simp [h, h.ne', h.not_gt]
    _ ≤ 2 * T + (2 * (N : ℝ)) * ((q : ℝ)⁻¹ * (harmonic N : ℝ) +
        (q : ℝ)⁻¹ * (harmonic N : ℝ)) :=
      add_le_add_right (mul_le_mul_of_nonneg_left (add_le_add hu hd)
        (mul_nonneg (show (0 : ℝ) ≤ 2 by norm_num) (Nat.cast_nonneg N))) _
    _ = _ := by rw [div_eq_mul_inv]; ring

private noncomputable def polynomial {q : ℕ} (s : Finset ℕ) (a : ℕ → ℂ)
    (χ : DirichletCharacter ℂ q) (u : ℝ) : ℂ :=
  ∑ n ∈ s, a n * χ (n : ZMod q) * phase (Real.log n) u

private def amplitude (a : ℕ → ℂ) (m n : ℕ) : ℂ := a m * (starRingEnd ℂ) (a n)

private noncomputable def charPair {q : ℕ} (χ : DirichletCharacter ℂ q) (m n : ℕ) : ℂ :=
  χ (m : ZMod q) * (starRingEnd ℂ) (χ (n : ZMod q))

-- Expand and integrate the finite square before averaging in the character.
private theorem integral_poly_sq {q : ℕ} (s : Finset ℕ) (a : ℕ → ℂ)
    (χ : DirichletCharacter ℂ q) (T : ℝ) :
    ((∫ u in -T..T, ‖polynomial s a χ u‖ ^ 2 : ℝ) : ℂ) =
      ∑ m ∈ s, ∑ n ∈ s, amplitude a m n * charPair χ m n *
        kernel T (Real.log m - Real.log n) := by
  have hexpand (u : ℝ) : (↑(‖polynomial s a χ u‖ ^ 2) : ℂ) =
      ∑ m ∈ s, ∑ n ∈ s, amplitude a m n * charPair χ m n *
        phase (Real.log m - Real.log n) u := by
    rw [← Complex.normSq_eq_norm_sq, ← Complex.mul_conj, polynomial, map_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro m _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n _
    simp only [map_mul, amplitude, charPair]
    rw [← phase_mul_conj]
    ring
  have hcont (m n : ℕ) : Continuous (fun u ↦ amplitude a m n * charPair χ m n *
      phase (Real.log m - Real.log n) u) := continuous_const.mul (continuous_phase _)
  rw [← intervalIntegral.integral_ofReal]
  simp_rw [hexpand]
  rw [intervalIntegral.integral_finsetSum (fun m _ ↦
      (continuous_finsetSum s (fun n _ ↦ hcont m n)).intervalIntegrable _ _)]
  apply Finset.sum_congr rfl
  intro m _
  rw [intervalIntegral.integral_finsetSum (fun n _ ↦ (hcont m n).intervalIntegrable _ _)]
  apply Finset.sum_congr rfl
  intro n _
  exact intervalIntegral.integral_const_mul _ _

private theorem integral_average_eq {q : ℕ} (hq : q.Prime) (s : Finset ℕ) (a : ℕ → ℂ) (T : ℝ) :
    (↑(((q : ℝ) - 1)⁻¹ *
        ∑ χ : DirichletCharacter ℂ q, ∫ u in -T..T, ‖polynomial s a χ u‖ ^ 2) : ℂ) =
      ∑ m ∈ s, ∑ n ∈ s, amplitude a m n * residueIndicator (m : ZMod q) (n : ZMod q) *
        kernel T (Real.log m - Real.log n) := by
  rw [Complex.ofReal_mul, Complex.ofReal_inv, Complex.ofReal_sum]
  simp_rw [integral_poly_sq]
  rw [Finset.sum_comm (s := Finset.univ) (t := s), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m _
  rw [Finset.sum_comm (s := Finset.univ) (t := s), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n _
  simp only [← Finset.sum_mul, ← Finset.mul_sum]
  rw [← char_sieve hq (m : ZMod q) (n : ZMod q)]
  unfold charPair
  ring

private theorem norm_sieved_kernel_le {q N : ℕ} {T : ℝ} (hT : 0 ≤ T)
    {m n : ℕ} (hm : m ∈ Finset.Icc 1 N) (hn : n ∈ Finset.Icc 1 N) :
    ‖residueIndicator (m : ZMod q) (n : ZMod q) * kernel T (Real.log m - Real.log n)‖ ≤
      rowWeight q N T m n := by
  classical
  by_cases h : IsUnit (n : ZMod q) ∧ (m : ZMod q) = (n : ZMod q)
  · rw [residueIndicator, ite_eq_left h, one_mul]
    by_cases he : m = n
    · subst n
      rw [sub_self, kernel_zero, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (mul_nonneg (show (0 : ℝ) ≤ 2 by norm_num) hT), rowWeight, ite_eq_left rfl]
    · rw [rowWeight, ite_eq_right he, ite_eq_left h.2]
      exact norm_kernel_log_le T hm hn he
  · rw [residueIndicator, ite_eq_right h, zero_mul, norm_zero]
    exact rowWeight_nonneg hT m n

-- Charge the absolute pair costs to the diagonal energy using symmetry.
private theorem quadratic_le {s : Finset ℕ} (w : ℕ → ℕ → ℝ) (b : ℕ → ℝ) (R : ℝ)
    (hw : ∀ m n, 0 ≤ w m n) (hsymm : ∀ m n, w m n = w n m)
    (hrow : ∀ m ∈ s, (∑ n ∈ s, w m n) ≤ R) :
    (∑ m ∈ s, ∑ n ∈ s, w m n * b m * b n) ≤ R * ∑ m ∈ s, b m ^ 2 := by
  have hswap : (∑ m ∈ s, ∑ n ∈ s, w m n * b n ^ 2) =
      ∑ m ∈ s, ∑ n ∈ s, w m n * b m ^ 2 := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun m _ ↦
      Finset.sum_congr rfl (fun n _ ↦ by rw [hsymm n m]))
  have hquad : 2 * (∑ m ∈ s, ∑ n ∈ s, w m n * b m * b n) ≤
      ∑ m ∈ s, ∑ n ∈ s, (w m n * b m ^ 2 + w m n * b n ^ 2) := by
    simp only [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro m _
    apply Finset.sum_le_sum
    intro n _
    nlinarith [mul_nonneg (hw m n) (sq_nonneg (b m - b n))]
  simp only [Finset.sum_add_distrib] at hquad
  rw [hswap, ← two_mul] at hquad
  calc
    _ ≤ ∑ m ∈ s, ∑ n ∈ s, w m n * b m ^ 2 := by linarith
    _ ≤ _ := by
      simp_rw [← Finset.sum_mul]
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum (fun m hm ↦ mul_le_mul_of_nonneg_right (hrow m hm) (sq_nonneg _))

private theorem hybrid_harmonic {q N : ℕ} (hq : q.Prime) {T : ℝ} (hT : 0 ≤ T) (a : ℕ → ℂ) :
    ((q : ℝ) - 1)⁻¹ *
        (∑ χ : DirichletCharacter ℂ q, ∫ u in -T..T, ‖polynomial (Finset.Icc 1 N) a χ u‖ ^ 2) ≤
      (2 * T + 4 * ((N : ℝ) / q) * (harmonic N : ℝ)) * ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 := by
  let s := Finset.Icc 1 N
  let avg := ((q : ℝ) - 1)⁻¹ *
    (∑ χ : DirichletCharacter ℂ q, ∫ u in -T..T, ‖polynomial s a χ u‖ ^ 2)
  have hq' : 1 < (q : ℝ) := by exact_mod_cast hq.one_lt
  have havg : 0 ≤ avg := mul_nonneg (inv_nonneg.mpr (sub_nonneg.mpr hq'.le))
    (Finset.sum_nonneg (fun χ _ ↦
      intervalIntegral.integral_nonneg (by linarith) (fun u _ ↦ sq_nonneg _)))
  let A (m n : ℕ) := amplitude a m n * residueIndicator (m : ZMod q) (n : ZMod q) *
    kernel T (Real.log m - Real.log n)
  change avg ≤ _
  calc
    avg = ‖∑ m ∈ s, ∑ n ∈ s, A m n‖ := by
      rw [← integral_average_eq hq s a T, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg havg]
    _ ≤ ∑ m ∈ s, ∑ n ∈ s, ‖A m n‖ :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum (fun m _ ↦ norm_sum_le s (A m)))
    _ ≤ ∑ m ∈ s, ∑ n ∈ s, rowWeight q N T m n * ‖a m‖ * ‖a n‖ := by
      apply Finset.sum_le_sum
      intro m hm
      apply Finset.sum_le_sum
      intro n hn
      change ‖(amplitude a m n * residueIndicator (m : ZMod q) (n : ZMod q)) *
        kernel T (Real.log m - Real.log n)‖ ≤ _
      rw [mul_assoc, norm_mul, amplitude, norm_mul, Complex.norm_conj]
      calc
        _ ≤ (‖a m‖ * ‖a n‖) * rowWeight q N T m n :=
          mul_le_mul_of_nonneg_left (norm_sieved_kernel_le hT hm hn)
            (mul_nonneg (norm_nonneg _) (norm_nonneg _))
        _ = _ := by ring
    _ ≤ _ := quadratic_le (rowWeight q N T) (fun n ↦ ‖a n‖) _ (rowWeight_nonneg hT)
      (rowWeight_symm q N T) (fun _ hm ↦ sum_rowWeight_le hq.pos T hm)

/-- The single-prime hybrid mean-value bound, with real normalization by `q - 1`.
The character sum ranges over every Dirichlet character modulo `q`. -/
public theorem mean_value_le {q N : ℕ} (hq : q.Prime) (_hN : 1 ≤ N)
    {T : ℝ} (hT : 0 < T) (a : ℕ → ℂ) :
    ((q : ℝ) - 1)⁻¹ * (∑ χ : DirichletCharacter ℂ q, ∫ u in -T..T,
      ‖∑ n ∈ Finset.Icc 1 N, a n * χ (n : ZMod q) *
        Complex.exp (Complex.I * (Real.log (n : ℝ) : ℂ) * (u : ℂ))‖ ^ 2) ≤
      (2 * T + 4 * ((N : ℝ) / q) * (1 + Real.log (N : ℝ))) *
        ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 := by
  refine (hybrid_harmonic hq hT.le a).trans ?_
  apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg (fun _ _ ↦ sq_nonneg _))
  apply add_le_add_right
  exact mul_le_mul_of_nonneg_left (harmonic_le_one_add_log N)
    (mul_nonneg (show (0 : ℝ) ≤ 4 by norm_num) (div_nonneg (Nat.cast_nonneg N) (Nat.cast_nonneg q)))

/-- Apply the hybrid bound directly to the length-`k` stopped polynomial. The strict upper
support bound `n < U * X` ensures that `U * X ≤ N + 1` suffices for the cutoff `N`. -/
public theorem stopped_mean_value_le {q N : ℕ} (hq : q.Prime) (hN : 1 ≤ N)
    {T : ℝ} (hT : 0 < T) {S : Finset ℕ} {U X : ℝ} (hU : 1 < U)
    (hprime : ∀ p ∈ S, p.Prime) (hX : ∀ p ∈ S, (p : ℝ) ≤ X)
    (hNX : U * X ≤ (N : ℝ) + 1) (b : ℕ → ℝ) (k : ℕ) :
    ((q : ℝ) - 1)⁻¹ * (∑ χ : DirichletCharacter ℂ q, ∫ u in -T..T,
      ‖∑ n ∈ StoppedPrimeProductMoment.stoppedProducts S U k,
        (StoppedPrimeProductMoment.coefficient S U b k n : ℂ) * χ (n : ZMod q) *
          Complex.exp (Complex.I * (Real.log (n : ℝ) : ℂ) * (u : ℂ))‖ ^ 2) ≤
      (2 * T + 4 * ((N : ℝ) / q) * (1 + Real.log (N : ℝ))) *
        (((k.factorial : ℝ) / Real.sqrt U) * (∑ p ∈ S, Real.sqrt (p : ℝ) * b p ^ 2) ^ k) := by
  let s := StoppedPrimeProductMoment.stoppedProducts S U k
  let d n := StoppedPrimeProductMoment.coefficient S U b k n
  have hs : s ⊆ Finset.Icc 1 N := by
    intro n hn
    obtain ⟨hl, hr⟩ := StoppedPrimeProductMoment.stoppedProducts_window hU hprime hX hn
    have h₁ : (1 : ℝ) ≤ n := hU.le.trans hl
    have h₂ : (n : ℝ) < ((N + 1 : ℕ) : ℝ) := by
      rw [Nat.cast_add, Nat.cast_one]
      exact hr.trans_le hNX
    exact Finset.mem_Icc.mpr ⟨by exact_mod_cast h₁, Nat.lt_succ_iff.mp (by exact_mod_cast h₂)⟩
  have hz (n : ℕ) (hn : n ∉ s) : d n = 0 :=
    StoppedPrimeProductMoment.coefficient_eq_zero_of_notMem b hn
  have hp (χ : DirichletCharacter ℂ q) (u : ℝ) :
      (∑ n ∈ s, (d n : ℂ) * χ (n : ZMod q) * phase (Real.log n) u) =
        ∑ n ∈ Finset.Icc 1 N, (d n : ℂ) * χ (n : ZMod q) * phase (Real.log n) u := by
    apply Finset.sum_subset hs
    intro n _ hn
    rw [hz n hn, Complex.ofReal_zero, zero_mul, zero_mul]
  have he : (∑ n ∈ Finset.Icc 1 N, ‖(d n : ℂ)‖ ^ 2) = ∑ n ∈ s, d n ^ 2 := by
    simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs]
    symm
    apply Finset.sum_subset hs
    intro n _ hn
    simp [hz n hn]
  have hlog : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast hN)
  have hC : 0 ≤ 2 * T + 4 * ((N : ℝ) / q) * (1 + Real.log (N : ℝ)) := by positivity
  change ((q : ℝ) - 1)⁻¹ * (∑ χ : DirichletCharacter ℂ q, ∫ u in -T..T,
    ‖∑ n ∈ s, (d n : ℂ) * χ (n : ZMod q) * phase (Real.log n) u‖ ^ 2) ≤ _
  simp_rw [hp]
  refine (mean_value_le hq hN hT (fun n ↦ (d n : ℂ))).trans ?_
  rw [he]
  exact mul_le_mul_of_nonneg_left (StoppedPrimeProductMoment.sum_coefficient_sq_le hU hprime b k) hC

end Masullo.PrimeHybridMeanValue
