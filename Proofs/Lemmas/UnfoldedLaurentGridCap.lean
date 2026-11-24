module

public import Lemmas.ThreeSiteMomentCompletion
import Mathlib.Algebra.Order.ToIntervalMod
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

/-!
# Cyclic angular grid cap for the unfolded Laurent multiplier

Source: `3042a1a9262e:.godel/bob/unfolded-deletion-33.md:24–35` and
`.godel/bob/check-unfolded-deletion-33.py:144–171` (`complete`, after the correction).
Owning check session: `01a20dea-9bff-7af6-950c-47bd0e521e1e`.

Scope: for any finite set of signed Laurent indices and real coefficients, a cyclic
angular grid bound gives the source's quadratic interpolation allowance for the
unfolded multiplier on the entire real line. The prefactor has unit norm and does
not enter the curvature budget. This proves the grid-to-`hg₁` step for
`ThreeSiteMomentCompletion.exists_unfolded_three_site_law`, not the numerical grid
bounds or the convolution equations for a particular corrected polynomial.
-/

namespace Masullo.UnfoldedLaurentGridCap

open ThreeSiteMomentCompletion (phase laurentMultiplier)
open scoped BigOperators

/-- The finite Laurent polynomial in the angular variable, with negative-exponent
convention and signed indices. -/
@[expose] public noncomputable def angularLaurent (K : Finset ℤ) (v : ℤ → ℝ) (θ : ℝ) : ℂ :=
  ∑ k ∈ K, (v k : ℂ) * phase (-(k : ℝ)) θ

private theorem norm_phase (s θ : ℝ) : ‖phase s θ‖ = 1 := by
  simp [phase, Complex.norm_exp_mul_I]

private theorem norm_multiplier_eq_angular (K : Finset ℤ) (v : ℤ → ℝ) (s₀ h x : ℝ) :
    ‖laurentMultiplier K v s₀ h x‖ = ‖angularLaurent K v (h * x)‖ := by
  rw [laurentMultiplier, norm_mul, norm_phase, one_mul, angularLaurent]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  have he : -((k : ℝ) * h) * x = -(k : ℝ) * (h * x) := by ring
  simp only [phase, he]

private theorem angular_periodic (K : Finset ℤ) (v : ℤ → ℝ) :
    Function.Periodic (angularLaurent K v) (2 * Real.pi) := by
  intro θ
  unfold angularLaurent
  apply Finset.sum_congr rfl
  intro k _
  have he : (((-(k : ℝ) * (θ + 2 * Real.pi) : ℝ) : ℂ) * Complex.I) =
      ((-(k : ℝ) * θ : ℝ) : ℂ) * Complex.I + (-k : ℤ) * (2 * Real.pi * Complex.I) := by
    push_cast
    ring
  simp only [phase, he, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

private noncomputable def frequency (k : ℤ) : ℂ := Complex.ofReal (-(k : ℝ)) * Complex.I

private noncomputable def angularJet (K : Finset ℤ) (v : ℤ → ℝ) (n : ℕ) (θ : ℝ) : ℂ :=
  ∑ k ∈ K, (v k : ℂ) * (phase (-(k : ℝ)) θ * frequency k ^ n)

private theorem hasDerivAt_angularJet (K : Finset ℤ) (v : ℤ → ℝ) (n : ℕ) (θ : ℝ) :
    HasDerivAt (angularJet K v n) (angularJet K v (n + 1) θ) θ := by
  unfold angularJet
  apply HasDerivAt.fun_sum
  intro k _
  have hphase : HasDerivAt (phase (-(k : ℝ)))
      (phase (-(k : ℝ)) θ * frequency k) θ := by
    change HasDerivAt (fun y : ℝ ↦ Complex.exp (↑(-(k : ℝ) * y) * Complex.I)) _ θ
    simpa only [phase, frequency, id_eq, mul_one] using
      ((((hasDerivAt_id θ).const_mul (-(k : ℝ))).ofReal_comp).mul_const Complex.I).cexp
  simpa only [pow_succ', mul_assoc] using ((hphase.mul_const (frequency k ^ n)).const_mul (v k : ℂ))

private theorem norm_angularJet_two_le (K : Finset ℤ) (v : ℤ → ℝ) (θ : ℝ) :
    ‖angularJet K v 2 θ‖ ≤ ∑ k ∈ K, (k : ℝ) ^ 2 * |v k| := by
  unfold angularJet
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ ↦ ?_)
  simp [frequency, norm_pow, Complex.norm_real, Complex.norm_intCast,
    Real.norm_eq_abs, norm_phase, sq_abs, mul_comm]

/-- Convexify a real projection by adding `C / 2 * θ²`. The resulting
endpoint chord has an excess over `β` of at most `h² / 8 * C`. -/
private theorem scalar_cell_cap {f f' f'' : ℝ → ℝ} {C a h r β : ℝ}
    (hC : 0 ≤ C) (hf : ∀ θ, HasDerivAt f (f' θ) θ)
    (hf' : ∀ θ, HasDerivAt f' (f'' θ) θ) (hcurv : ∀ θ, -C ≤ f'' θ)
    (hr : r ∈ Set.Icc (0 : ℝ) 1) (ha : f a ≤ β) (hb : f (a + h) ≤ β) :
    f (a + r * h) ≤ β + h ^ 2 / 8 * C := by
  let g (θ : ℝ) := f θ + C / 2 * θ ^ 2
  have hg (θ : ℝ) : HasDerivAt g (f' θ + C * θ) θ := by
    refine ((hf θ).add (((hasDerivAt_id θ).pow 2).const_mul (C / 2))).congr_deriv ?_
    simp only [id_eq, Nat.cast_ofNat, Nat.reduceSubDiff, pow_one, mul_one]
    ring
  have hg' (θ : ℝ) : HasDerivAt (fun y ↦ f' y + C * y) (f'' θ + C) θ := by
    change HasDerivAt (f' + fun y ↦ C * y) (f'' θ + C) θ
    simpa only [id_eq, mul_one] using (hf' θ).add ((hasDerivAt_id θ).const_mul C)
  have hdg : deriv g = fun θ ↦ f' θ + C * θ := funext fun θ ↦ (hg θ).deriv
  have hconv : ConvexOn ℝ Set.univ g := by
    apply convexOn_of_deriv2_nonneg' convex_univ
    · exact fun θ _ ↦ (hg θ).differentiableAt.differentiableWithinAt
    · rw [hdg]
      exact fun θ _ ↦ (hg' θ).differentiableAt.differentiableWithinAt
    · intro θ _
      change 0 ≤ deriv (deriv g) θ
      rw [hdg, (hg' θ).deriv]
      exact neg_le_iff_add_nonneg.mp (hcurv θ)
  have h₀ : 0 ≤ 1 - r := sub_nonneg.mpr hr.2
  have hc := hconv.2 (Set.mem_univ a) (Set.mem_univ (a + h)) h₀ hr.1
    (by ring : 1 - r + r = 1)
  simp only [smul_eq_mul, show (1 - r) * a + r * (a + h) = a + r * h by ring, g] at hc
  have hm : (1 - r) * f a + r * f (a + h) ≤ β := calc
    _ ≤ (1 - r) * β + r * β :=
      add_le_add (mul_le_mul_of_nonneg_left ha h₀) (mul_le_mul_of_nonneg_left hb hr.1)
    _ = β := by ring
  have hs : 0 ≤ C * (r - 1 / 2) ^ 2 * h ^ 2 := by positivity
  nlinarith only [hc, hm, hs]

private theorem angular_cell_cap (K : Finset ℤ) (v : ℤ → ℝ) {a h r β : ℝ}
    (hr : r ∈ Set.Icc (0 : ℝ) 1) (ha : ‖angularLaurent K v a‖ ≤ β)
    (hb : ‖angularLaurent K v (a + h)‖ ≤ β) :
    ‖angularLaurent K v (a + r * h)‖ ≤ β + h ^ 2 / 8 * ∑ k ∈ K, (k : ℝ) ^ 2 * |v k| := by
  let z := angularLaurent K v (a + r * h)
  -- Fix a norm-attaining real projection at the point being bounded.
  obtain ⟨L, hL, hz⟩ : ∃ L : ℂ →L[ℝ] ℝ, ‖L‖ ≤ 1 ∧ L z = ‖z‖ := by
    by_cases h : ‖z‖ = 0
    · exact ⟨0, by simp, by simp [h]⟩
    · obtain ⟨L, hL, hz⟩ := exists_dual_vector ℝ z h
      exact ⟨L, hL.le, hz⟩
  have hop (w : ℂ) : ‖L w‖ ≤ ‖w‖ :=
    (L.le_opNorm w).trans (by simpa only [one_mul] using
      mul_le_mul_of_nonneg_right hL (norm_nonneg w))
  have h₁ (θ : ℝ) : HasDerivAt (fun y ↦ L (angularLaurent K v y))
      (L (angularJet K v 1 θ)) θ := by
    have hjet : angularJet K v 0 = angularLaurent K v := by
      funext y
      simp [angularJet, angularLaurent]
    rw [← hjet]
    exact L.hasFDerivAt.comp_hasDerivAt θ (hasDerivAt_angularJet K v 0 θ)
  have h₂ (θ : ℝ) : HasDerivAt (fun y ↦ L (angularJet K v 1 y))
      (L (angularJet K v 2 θ)) θ :=
    L.hasFDerivAt.comp_hasDerivAt θ (hasDerivAt_angularJet K v 1 θ)
  have hcurv (θ : ℝ) : -(∑ k ∈ K, (k : ℝ) ^ 2 * |v k|) ≤ L (angularJet K v 2 θ) := by
    have hnorm := (hop (angularJet K v 2 θ)).trans (norm_angularJet_two_le K v θ)
    rw [Real.norm_eq_abs] at hnorm
    exact (abs_le.mp hnorm).1
  change ‖z‖ ≤ _
  rw [← hz]
  exact scalar_cell_cap (Finset.sum_nonneg fun k _ ↦ by positivity) h₁ h₂ hcurv hr
    ((le_abs_self _).trans ((hop _).trans ha)) ((le_abs_self _).trans ((hop _).trans hb))

private theorem angular_grid_cap (K : Finset ℤ) (v : ℤ → ℝ) {N : ℕ} (hN : 1 ≤ N)
    {β : ℝ} (hsample : ∀ j : ℕ, j < N → ‖angularLaurent K v (j * (2 * Real.pi / N))‖ ≤ β)
    (θ : ℝ) :
    ‖angularLaurent K v θ‖ ≤ β + (2 * Real.pi / N) ^ 2 / 8 * ∑ k ∈ K, (k : ℝ) ^ 2 * |v k| := by
  let T := 2 * Real.pi
  let Δ := T / (N : ℝ)
  have hT : 0 < T := by dsimp [T]; positivity
  have hN₀ : 0 < (N : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hN)
  have hΔ : 0 < Δ := div_pos hT hN₀
  have hNΔ : (N : ℝ) * Δ = T := by
    rw [mul_comm]
    exact div_mul_cancel₀ T hN₀.ne'
  let t := toIcoMod hT 0 θ
  have ht : t ∈ Set.Ico 0 T := by simpa only [zero_add] using toIcoMod_mem_Ico hT 0 θ
  have hp := angular_periodic K v
  have htP : angularLaurent K v t = angularLaurent K v θ :=
    hp.sub_zsmul_eq (toIcoDiv hT 0 θ)
  let j := ⌊t / Δ⌋₊
  have hj₀ : 0 ≤ t / Δ := div_nonneg ht.1 hΔ.le
  have hj : j < N := (Nat.floor_lt hj₀).2 ((div_lt_iff₀ hΔ).2 (hNΔ ▸ ht.2))
  have hleft : (j : ℝ) * Δ ≤ t := (le_div_iff₀ hΔ).mp (Nat.floor_le hj₀)
  have hright : t ≤ (j : ℝ) * Δ + Δ := by
    have h := (div_lt_iff₀ hΔ).mp (Nat.lt_succ_floor (t / Δ))
    simpa only [Nat.cast_succ, add_mul, one_mul] using h.le
  have hb : ‖angularLaurent K v ((j : ℝ) * Δ + Δ)‖ ≤ β := by
    rw [show (j : ℝ) * Δ + Δ = ((j + 1 : ℕ) : ℝ) * Δ by push_cast; ring]
    rcases lt_or_eq_of_le (Nat.succ_le_of_lt hj) with h | h
    · exact hsample (j + 1) h
    · -- The final right endpoint is `2π`, so its sample is the zero node.
      -- In particular, this branch covers the only cell when `N = 1`.
      rw [show j + 1 = N from h, hNΔ]
      have hwrap : angularLaurent K v T = angularLaurent K v 0 := by
        simpa only [zero_add] using hp 0
      rw [hwrap]
      simpa only [Nat.cast_zero, zero_mul] using hsample 0 (Nat.zero_lt_of_lt hN)
  let r := (t - (j : ℝ) * Δ) / Δ
  have hr : r ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨div_nonneg (sub_nonneg.mpr hleft) hΔ.le,
      (div_le_iff₀ hΔ).2 (by linarith only [hright])⟩
  have hre : (j : ℝ) * Δ + r * Δ = t := by
    dsimp [r]
    rw [div_mul_cancel₀ _ hΔ.ne']
    ring
  have hcap := angular_cell_cap K v hr (hsample j hj) hb
  rw [hre, htP] at hcap
  exact hcap

/-- From the `N` cyclic angular samples of the finite real Laurent polynomial,
bound the existing unfolded multiplier at every real frequency. -/
public theorem norm_laurentMultiplier_le_of_grid (K : Finset ℤ) (v : ℤ → ℝ)
    {N : ℕ} (hN : 1 ≤ N) {β : ℝ}
    (hsample : ∀ j : ℕ, j < N → ‖angularLaurent K v (j * (2 * Real.pi / N))‖ ≤ β)
    (x : ℝ) :
    ‖laurentMultiplier K v (6 / 25) (13 / 25) x‖ ≤
      β + (2 * Real.pi / N) ^ 2 / 8 * ∑ k ∈ K, (k : ℝ) ^ 2 * |v k| := by
  rw [norm_multiplier_eq_angular]
  exact angular_grid_cap K v hN hsample _

/-- The grid certificate supplies the `hg₁` hypothesis of the unfolded law theorem
whenever the sample bound plus the interpolation allowance is at most one. -/
public theorem laurentMultiplier_cap_of_grid (K : Finset ℤ) (v : ℤ → ℝ)
    {N : ℕ} (hN : 1 ≤ N) {β : ℝ}
    (hsample : ∀ j : ℕ, j < N → ‖angularLaurent K v (j * (2 * Real.pi / N))‖ ≤ β)
    (hbudget : β + (2 * Real.pi / N) ^ 2 / 8 * ∑ k ∈ K, (k : ℝ) ^ 2 * |v k| ≤ 1) :
    ∀ x : ℝ, ‖laurentMultiplier K v (6 / 25) (13 / 25) x‖ ≤ 1 :=
  fun x ↦ (norm_laurentMultiplier_le_of_grid K v hN hsample x).trans hbudget

end Masullo.UnfoldedLaurentGridCap
