module

public import Lemmas.ShortCellTrace
import all Lemmas.LogRampAbel
import Lemmas.IntegralRampAverage
import Mathlib.NumberTheory.LSeries.WeakPNT
import Mathlib.Tactic.FieldSimp

/-!
# The real-cutoff prime ramp and short-cell trace asymptotics

Sources: `8058479edd84:.godel/bob/short-cell-weil-list.md:39–53` and
`a433ed178:.godel/bob/fixed-strip-endpoints.md:37–51` (discovery pin `a433ed178`).
Abel summation and the ordinary prime number theorem give the limit for the
full prime ramp. Nonnegativity gives a one-sided bound for the truncated prime
window in the finite smeared crossing trace. There is no assertion about an
asymptotic equivalent for that window, an operator norm, or replacement of
unsmeared prime shifts.

Owning check session: `01a20f6c-c41c-70db-8373-949d4b4e2596`.
-/

open Filter MeasureTheory Set
open scoped Topology

namespace ShortCellTrace

private noncomputable def primeLogWeight (p : ℕ) : ℝ :=
  if p.Prime then Real.log (p : ℝ) else 0

private theorem primes_zero_eq_filter_Ioc {Y : ℝ} (hY : 0 ≤ Y) {b : ℕ} (hb : b ≤ 1) :
    primes 0 Y = (Finset.Ioc b ⌊Y⌋₊).filter Nat.Prime := by
  ext p
  simp only [mem_primes, Nat.cast_nonneg, true_and, Finset.mem_filter, Finset.mem_Ioc,
    Nat.le_floor_iff hY]
  exact ⟨fun hp ↦ ⟨⟨hb.trans_lt hp.1.one_lt, hp.2⟩, hp.1⟩, fun hp ↦ ⟨hp.2, hp.1.2⟩⟩

private theorem full_log_mass_eq_theta {Y : ℝ} (hY : 0 ≤ Y) :
    (∑ p ∈ primes 0 Y, Real.log (p : ℝ)) = Chebyshev.theta Y := by
  rw [primes_zero_eq_filter_Ioc hY (b := 0) (by decide), Chebyshev.theta]

private theorem partial_sum_eq_theta (t : ℝ) :
    (∑ p ∈ Finset.Icc 0 ⌊t⌋₊, primeLogWeight p) = Chebyshev.theta t := by
  rw [Chebyshev.theta_eq_sum_Icc, Finset.sum_filter]
  rfl

private theorem full_ramp_eq_logRamp {Y : ℝ} (hY : 0 ≤ Y) :
    (∑ p ∈ primes 0 Y, Real.log (p : ℝ) * Real.log (Y / p)) =
      PrimeSquareRamp.logRamp primeLogWeight Y := by
  rw [primes_zero_eq_filter_Ioc hY le_rfl, Finset.sum_filter, PrimeSquareRamp.logRamp]
  exact Finset.sum_congr rfl fun p _ ↦ by
    by_cases hp : p.Prime <;> simp [primeLogWeight, hp, mul_comm]

/-- The full ramp over the actual primes `p ≤ Y`, divided by the real cutoff `Y`, tends to one. -/
public theorem tendsto_prime_logRamp_div :
    Tendsto (fun Y : ℝ ↦ (∑ p ∈ primes 0 Y, Real.log (p : ℝ) * Real.log (Y / p)) / Y)
      atTop (𝓝 1) := by
  have hint (Y : ℝ) (hY : 1 ≤ Y) :
      IntervalIntegrable (fun t ↦ Chebyshev.theta t / t) volume 1 Y := by
    simpa only [partial_sum_eq_theta] using
      PrimeSquareRamp.partialSum_div_intervalIntegrable primeLogWeight hY
  apply (PrimeSquareRamp.tendsto_integral_average hint Chebyshev.tendsto_theta_div_atTop).congr'
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with Y hY
  rw [full_ramp_eq_logRamp (zero_le_one.trans hY),
    PrimeSquareRamp.logRamp_eq_integral primeLogWeight (by simp [primeLogWeight])
      (by simp [primeLogWeight]) hY]
  simp only [partial_sum_eq_theta]

private theorem primes_mono_left (L Y : ℝ) : primes L Y ⊆ primes 0 Y := by
  intro p hp
  have h := mem_primes.mp hp
  exact mem_primes.mpr ⟨h.1, Nat.cast_nonneg p, h.2.2⟩

private theorem window_ramp_le (L Y : ℝ) :
    (∑ p ∈ primes L Y, Real.log (p : ℝ) * Real.log (Y / p)) ≤
      ∑ p ∈ primes 0 Y, Real.log (p : ℝ) * Real.log (Y / p) := by
  refine Finset.sum_le_sum_of_subset_of_nonneg (primes_mono_left L Y) fun p hp _ ↦ ?_
  have h := mem_primes.mp hp
  have hp₀ : 0 < (p : ℝ) := by exact_mod_cast h.1.pos
  exact mul_nonneg (Real.log_natCast_nonneg p) (Real.log_nonneg ((one_le_div hp₀).2 h.2.2))

private theorem eventually_prime_budget_le {α : Type*} {l : Filter α} {X Y L h C : α → ℝ}
    {C₀ ε : ℝ} (hX : Tendsto X l atTop) (hY : Tendsto (fun a ↦ Y a / X a) l (𝓝 1))
    (hsmall : Tendsto (fun a ↦ h a / L a) l (𝓝 0))
    (hC : Tendsto C l (𝓝 C₀)) (hCnonneg : ∀ᶠ a in l, 0 ≤ C a) (hε : 0 < ε) :
    ∀ᶠ a in l,
      C a * ((∑ p ∈ primes (L a) (Y a), Real.log (p : ℝ) * Real.log (Y a / p)) +
        (h a / L a) * ∑ p ∈ primes (L a) (Y a), Real.log (p : ℝ)) ≤ (C₀ + ε) * X a := by
  have hXa : ∀ᶠ a in l, 0 < X a := hX.eventually (eventually_gt_atTop 0)
  have hYa : Tendsto Y l atTop := by
    apply tendsto_atTop_mono' l ?_ (hX.atTop_mul_const (r := (1 : ℝ) / 2) (by norm_num))
    filter_upwards [hXa, hY.eventually_const_lt (show (1 : ℝ) / 2 < 1 by norm_num)] with a hx hy
    exact (mul_comm (X a) _).le.trans ((lt_div_iff₀ hx).mp hy).le
  -- Taking the positive part keeps the comparison valid without any separate sign
  -- condition on the cell-width bound (for example, when the partition is empty).
  have herror : Tendsto (fun a ↦ max (h a / L a) 0) l (𝓝 0) := by
    simpa only [max_self] using hsmall.max (tendsto_const_nhds (x := (0 : ℝ)))
  have hlim := hC.mul (((tendsto_prime_logRamp_div.comp hYa).add
    (herror.mul (Chebyshev.tendsto_theta_div_atTop.comp hYa))).mul hY)
  simp only [mul_one, add_zero] at hlim
  filter_upwards [hXa, hYa.eventually (eventually_gt_atTop 0), hCnonneg,
    hlim.eventually_lt_const (lt_add_of_pos_right C₀ hε)] with a hx hy hc hb
  have hmass : (∑ p ∈ primes (L a) (Y a), Real.log (p : ℝ)) ≤ Chebyshev.theta (Y a) := by
    rw [← full_log_mass_eq_theta hy.le]
    exact Finset.sum_le_sum_of_subset_of_nonneg (primes_mono_left _ _) fun p _ _ ↦
      Real.log_natCast_nonneg p
  have hcoarse := mul_le_mul (le_max_left (h a / L a) 0) hmass
    (Finset.sum_nonneg fun p _ ↦ Real.log_natCast_nonneg p) (le_max_right (h a / L a) 0)
  refine (mul_le_mul_of_nonneg_left (add_le_add (window_ramp_le _ _) hcoarse) hc).trans ?_
  apply (div_le_iff₀ hx).1
  convert hb.le using 1
  dsimp only [Function.comp_apply, Pi.add_apply, Pi.mul_apply]
  field_simp [hx.ne', hy.ne']

/-- The finite symmetric crossing trace is eventually at most `(C₀ + ε) * X` when
`Y = exp D` satisfies `Y / X → 1`, the relative cell width `h / L → 0`, and the
nonnegative budget coefficient tends to `C₀`. The estimate is uniform over partitions,
assignments, and unit inputs satisfying the finite short-cell hypotheses. The cell
budget is stated with the width cleared, as in `symmetricForm_trace_le`. -/
public theorem eventually_symmetricForm_trace_le {α : Type*} {l : Filter α}
    {X D L h C : α → ℝ} {C₀ ε : ℝ} (hX : Tendsto X l atTop)
    (hY : Tendsto (fun a ↦ Real.exp (D a) / X a) l (𝓝 1))
    (hsmall : Tendsto (fun a ↦ h a / L a) l (𝓝 0))
    (hC : Tendsto C l (𝓝 C₀)) (hCnonneg : ∀ᶠ a in l, 0 ≤ C a) (hε : 0 < ε) :
    ∀ᶠ a in l, ∀ {J ι : Type*} [Fintype J] [Fintype ι]
      {P : Partition J (L a) (Real.exp (D a)) (h a)} (A : PrimeAssignment P),
      0 < D a → 0 < L a → L a ≤ Real.exp (D a) → D a / 2 ≤ Real.log (L a) →
      ∀ {m f : ι → ℝ → ℂ} {c : ι → J → ℂ},
        (∀ i j, m i =ᵐ[volume.restrict (Ioo (P.left j) (P.right j))] fun _ ↦ c i j) →
        (∀ j, (P.right j - P.left j) * (∑ i, ‖c i j‖ ^ 2) ≤ C a * A.mass j) →
        (∀ i, MemLp (f i) 2 (volume.restrict (Icc 0 (D a)))) →
        (∀ i, (∫ x in Icc 0 (D a), ‖f i x‖ ^ 2) = 1) →
        (∑ i, (ShortCellCrossing.symmetricForm (D a) (L a) (m i) (f i)) ^ 2) ≤ (C₀ + ε) * X a := by
  filter_upwards [eventually_prime_budget_le hX hY hsmall hC hCnonneg hε] with a ha
  intro J ι _ _ P A hD hL hLY hhalf m f c hconst hcell hf hunit
  exact (symmetricForm_trace_le A hD hL hLY hhalf hconst hcell hf hunit).trans ha

/-- The same eventual bound for the sum of integrals of squared forward kernel
norms, using the quotient cell budget from the source. Only the forward crossing
rectangle contributes to this trace. -/
public theorem eventually_kernel_trace_le_of_div {α : Type*} {l : Filter α}
    {X D L h C : α → ℝ} {C₀ ε : ℝ} (hX : Tendsto X l atTop)
    (hY : Tendsto (fun a ↦ Real.exp (D a) / X a) l (𝓝 1))
    (hsmall : Tendsto (fun a ↦ h a / L a) l (𝓝 0))
    (hC : Tendsto C l (𝓝 C₀)) (hCnonneg : ∀ᶠ a in l, 0 ≤ C a) (hε : 0 < ε) :
    ∀ᶠ a in l, ∀ {J ι : Type*} [Fintype J] [Fintype ι]
      {P : Partition J (L a) (Real.exp (D a)) (h a)} (A : PrimeAssignment P),
      0 < D a → 0 < L a → L a ≤ Real.exp (D a) → D a / 2 ≤ Real.log (L a) →
      ∀ {m : ι → ℝ → ℂ} {c : ι → J → ℂ},
        (∀ i j, m i =ᵐ[volume.restrict (Ioo (P.left j) (P.right j))] fun _ ↦ c i j) →
        (∀ j, (∑ i, ‖c i j‖ ^ 2) ≤ C a * (A.mass j / (P.right j - P.left j))) →
        (∑ i, ∫ x in ShortCellCrossing.leftHalf (D a), ∫ y in ShortCellCrossing.rightHalf (D a),
          ‖ShortCellCrossing.kernel (D a) (L a) (m i) x y‖ ^ 2) ≤ (C₀ + ε) * X a := by
  filter_upwards [eventually_prime_budget_le hX hY hsmall hC hCnonneg hε, hCnonneg] with a ha hc
  intro J ι _ _ P A hD hL hLY hhalf m c hconst hcell
  have hcleared := mul_cellBudget_of_div A hcell fun j _ ↦
    mul_nonneg hc (Finset.sum_nonneg fun p _ ↦ Real.log_natCast_nonneg p.val)
  exact (kernel_trace_le A hD hL hLY hhalf hconst hcleared).trans ha

end ShortCellTrace
