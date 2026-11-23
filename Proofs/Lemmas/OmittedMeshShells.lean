module

public import Lemmas.CenteredHeightMesh
public import Lemmas.SampledPrimePairShell
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Weighted omitted nodes of the genuine centered mesh

Source: `554d2c8:.godel/bob/centered-height-mesh.md`, “Price the omitted sample
points,” and `78091476:.godel/bob/balanced-height-reconstruction.md`, “Pricing
the omitted heights.” The sampled short moment is from `6ebbee0:Proofs/Lemmas/
SampledPrimePairShell.lean`. Owning check session:
`01a20a16-7036-75bb-8ab9-3bc3a536b6e9`.

These are finite-parameter bounds on the original translated grid and the
original center, not quadrature for a truncated weight. The covers can overlap;
their cost is an upper bound. No asymptotic choice of moment or exponent is used.
-/

open scoped BigOperators

namespace Masullo.CenteredHeightMesh

/-- The centered sinc-square kernel is a nonnegative weight. -/
public theorem kernel_nonneg {t : ℝ} (ht : 0 < t) (u : ℝ) : 0 ≤ kernel t u := by
  unfold kernel
  positivity

/-- The global bound, also used for shells meeting the center. -/
public theorem kernel_le_inv {t : ℝ} (ht : 0 < t) (u : ℝ) : kernel t u ≤ t⁻¹ := by
  unfold kernel
  have h := pow_le_pow_left₀ (abs_nonneg _) (Real.abs_sinc_le_one (Real.pi * (u / t - 1))) 2
  rw [sq_abs, one_pow] at h
  simpa only [mul_one] using mul_le_mul_of_nonneg_left h (inv_nonneg.mpr ht.le)

/-- At small absolute heights the kernel uses its double zero at the origin. -/
public theorem kernel_le_near_zero {t u : ℝ} (ht : 0 < t) (hu : |u| ≤ t / 2) :
    kernel t u ≤ 4 * |u| ^ 2 / t ^ 3 := by
  let x := u / t
  have hx : |x| ≤ 1 / 2 := by
    dsimp only [x]
    rw [abs_div, abs_of_pos ht, div_le_iff₀ ht]
    linarith
  have hd : (1 : ℝ) / 2 ≤ |x - 1| := by
    linarith [le_abs_self (x - 1), neg_le_abs (x - 1), le_abs_self x]
  have ha : 0 < |Real.pi * (x - 1)| := by
    rw [abs_mul, abs_of_pos Real.pi_pos]
    exact mul_pos Real.pi_pos (by linarith)
  have hsin : |Real.sin (Real.pi * (x - 1))| ≤ Real.pi * |x| := by
    rw [mul_sub, mul_one, Real.sin_sub_pi, abs_neg]
    simpa only [abs_mul, abs_of_pos Real.pi_pos] using (Real.abs_sin_le_abs (x := Real.pi * x))
  have hsinc : |Real.sinc (Real.pi * (x - 1))| ≤ 2 * |x| := by
    rw [Real.sinc_of_ne_zero (abs_pos.mp ha), abs_div, div_le_iff₀ ha, abs_mul, abs_of_pos Real.pi_pos]
    calc
      _ ≤ Real.pi * |x| := hsin
      _ ≤ (2 * |x|) * (Real.pi * |x - 1|) := by
        nlinarith only [mul_le_mul_of_nonneg_left hd (show 0 ≤ Real.pi * |x| by positivity)]
  have hsq := pow_le_pow_left₀ (abs_nonneg _) hsinc 2
  rw [sq_abs] at hsq
  unfold kernel
  calc
    _ ≤ t⁻¹ * (2 * |x|) ^ 2 := mul_le_mul_of_nonneg_left hsq (inv_nonneg.mpr ht.le)
    _ = _ := by
      dsimp only [x]
      rw [abs_div, abs_of_pos ht]
      field_simp
      ring

/-- At large absolute heights the genuine center is at distance at least `|u|/2`. -/
public theorem kernel_le_far {t u : ℝ} (ht : 0 < t) (hu : 2 * t ≤ |u|) :
    kernel t u ≤ 4 * t / |u| ^ 2 := by
  let x := u / t
  have hx : 2 ≤ |x| := by
    dsimp only [x]
    rwa [abs_div, abs_of_pos ht, le_div_iff₀ ht]
  have hd : |x| / 2 ≤ |x - 1| := by
    linarith [abs_sub_abs_le_abs_sub x 1, abs_one (α := ℝ)]
  have hπ : 1 ≤ Real.pi := by linarith [Real.pi_gt_three]
  have ha : |x| / 2 ≤ |Real.pi * (x - 1)| := by
    rw [abs_mul, abs_of_pos Real.pi_pos]
    exact hd.trans (le_mul_of_one_le_left (abs_nonneg _) hπ)
  have hxpos : 0 < |x| / 2 := by linarith
  have hsinc : |Real.sinc (Real.pi * (x - 1))| ≤ 1 / (|x| / 2) := by
    rw [Real.sinc_of_ne_zero (abs_pos.mp (hxpos.trans_le ha)), abs_div]
    exact (div_le_div_of_nonneg_right (Real.abs_sin_le_one _) (abs_nonneg _)).trans
      (div_le_div_of_nonneg_left zero_le_one hxpos ha)
  have hsq := pow_le_pow_left₀ (abs_nonneg _) hsinc 2
  rw [sq_abs] at hsq
  have hu0 : |u| ≠ 0 := (show 0 < |u| by linarith).ne'
  unfold kernel
  calc
    _ ≤ t⁻¹ * (1 / (|x| / 2)) ^ 2 := mul_le_mul_of_nonneg_left hsq (inv_nonneg.mpr ht.le)
    _ = _ := by
      dsimp only [x]
      rw [abs_div, abs_of_pos ht]
      field_simp
      ring

/-- Explicit small-height, far-height and comparable-height shell constants. -/
@[expose] public noncomputable def shellEnvelope (t T : ℝ) : ℝ :=
  if 2 * T ≤ t / 2 then 16 * T ^ 2 / t ^ 3
  else if 2 * t ≤ T then 4 * t / T ^ 2 else t⁻¹

private theorem shellEnvelope_nonneg {t T : ℝ} (ht : 0 < t) : 0 ≤ shellEnvelope t T := by
  unfold shellEnvelope
  split <;> positivity

/-- Pointwise bound on the inclusive two-sided shell, with the original kernel. -/
public theorem kernel_le_shellEnvelope {t T u : ℝ} (ht : 0 < t) (hT : 0 < T)
    (hu : T ≤ |u| ∧ |u| ≤ 2 * T) : kernel t u ≤ shellEnvelope t T := by
  unfold shellEnvelope
  split
  next h =>
    refine (kernel_le_near_zero ht (hu.2.trans h)).trans ?_
    calc
      4 * |u| ^ 2 / t ^ 3 ≤ 4 * (2 * T) ^ 2 / t ^ 3 :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) hu.2 2) (by norm_num))
          (by positivity)
      _ = _ := by ring
  next _ =>
    split
    next h =>
      exact (kernel_le_far ht (h.trans hu.1)).trans
        (div_le_div_of_nonneg_left (by positivity) (by positivity)
          (pow_le_pow_left₀ hT.le hu.1 2))
    next _ => exact kernel_le_inv ht u

/-- The actual centered kernel has a summable sample sequence for every translated grid. -/
public theorem summable_kernel_samples {t Δ : ℝ} (ht : 0 < t) (hΔ : 0 < Δ) (b : ℝ) :
    Summable (fun j : ℤ ↦ kernel t (b + (j : ℝ) * Δ)) := by
  let I : Finset Unit := {()}
  have hpoly (u : ℝ) : expPolynomial I (fun _ ↦ 1) (fun _ ↦ 0) u = 1 := by
    simp [I, expPolynomial, SignedBlockIntervalMoment.phase]
  simpa only [hpoly, mul_one, Complex.norm_real, Real.norm_of_nonneg (kernel_nonneg ht _)] using
    (summable_norm_samples I (fun _ ↦ 1) (fun _ ↦ 0) ht hΔ b)

/-- With the constant-frequency alias guard, the whole translated grid has mass one. -/
public theorem kernel_sample_mass_one {t Δ : ℝ} (ht : 0 < t) (hΔ : 0 < Δ)
    (hmesh : 2 * Real.pi / t ≤ angularPeriod Δ) (b : ℝ) :
    Δ * (∑' j : ℤ, kernel t (b + (j : ℝ) * Δ)) = 1 := by
  let I : Finset Unit := {()}
  have hpoly (u : ℝ) : expPolynomial I (fun _ ↦ 1) (fun _ ↦ 0) u = 1 := by
    simp [I, expPolynomial, SignedBlockIntervalMoment.phase]
  have hno := no_alias I (fun _ ↦ 1) (fun _ ↦ 0) ht hΔ (M := 0)
    (by simp) (by simpa only [zero_add] using hmesh) b
  have hK : (∫ u : ℝ, (kernel t u : ℂ)) = 1 := by
    simpa [SignedBlockIntervalMoment.phase, triangle] using kernel_transform ht 0
  apply Complex.ofReal_injective
  simpa only [hpoly, mul_one, hK, Complex.ofReal_mul, Complex.ofReal_tsum, Complex.ofReal_one] using hno

end Masullo.CenteredHeightMesh

namespace Masullo.OmittedMeshShells

open CenteredHeightMesh (angularPeriod kernel kernel_nonneg shellEnvelope kernel_le_shellEnvelope)
open PrimePairShellMoment (primePairSum)
open SampledPrimePairShell (frequencyDiameter tsum_shell_moment_le)

/-- Physical height of grid index `j`; no restriction on the real origin `b`. -/
@[expose] public def node (b Δ : ℝ) (j : ℤ) : ℝ := b + (j : ℝ) * Δ

/-- The true frozen amplitude, with the untwisted source obtained at `χ = 1`. -/
@[expose] public noncomputable def amplitude (S : Finset ℕ) (d : ℕ) (w : ℕ → ℝ)
    (χ : ℕ → ℂ) (u : ℝ) : ℝ := ‖primePairSum S d w χ u‖

/-- The `Δ`-weighted contribution on exactly the indicated grid indices. -/
@[expose] public noncomputable def contribution (t b Δ : ℝ) (E : Set ℤ) (f : ℝ → ℝ) : ℝ :=
  Δ * ∑' j : ℤ, E.indicator (fun i ↦ kernel t (node b Δ i) * f (node b Δ i)) j

/-- A finite-cover entry: shell scale, short half-order and amplitude cap. -/
public structure Shell where
  height : ℝ
  order : ℕ
  cap : ℝ

/-- This entry includes both shell endpoints and its amplitude endpoint. -/
@[expose] public def Shell.nodes (q : Shell) (b Δ : ℝ) (s : ℝ → ℝ) : Set ℤ :=
  {j | q.height ≤ |node b Δ j| ∧ |node b Δ j| ≤ 2 * q.height ∧ s (node b Δ j) ≤ q.cap}

/-- Explicit price of one entry. `B` is an upper bound for the squared weight mass. -/
@[expose] public noncomputable def Shell.budget (q : Shell) (t : ℝ) (n : ℕ) (B : ℝ) : ℝ :=
  shellEnvelope t q.height * q.cap ^ (n - 2 * q.order) *
    (16 * Real.pi * q.height * (q.order.factorial : ℝ) * B ^ q.order)

private theorem finite_shell {b Δ T : ℝ} (hΔ : 0 < Δ) :
    {j : ℤ | T ≤ |node b Δ j| ∧ |node b Δ j| ≤ 2 * T}.Finite := by
  obtain ⟨N, hN⟩ := exists_nat_gt ((2 * T + |b|) / Δ)
  refine (Set.finite_Icc (a := -(N : ℤ)) (b := (N : ℤ))).subset ?_
  intro j hj
  have hh : |node b Δ j| ≤ 2 * T := hj.2
  have ha : |(j : ℝ) * Δ| ≤ 2 * T + |b| := by
    calc
      _ = |node b Δ j - b| := by congr 1; unfold node; ring
      _ ≤ |node b Δ j| + |b| := by
        simpa only [sub_eq_add_neg, abs_neg] using abs_add_le (node b Δ j) (-b)
      _ ≤ 2 * T + |b| := add_le_add_left hh _
  rw [abs_mul, abs_of_pos hΔ] at ha
  have hreal : |(j : ℝ)| ≤ (N : ℝ) := ((le_div_iff₀ hΔ).2 ha).trans hN.le
  have hint : |j| ≤ (N : ℤ) := by exact_mod_cast hreal
  exact abs_le.mp hint

private theorem summable_indicator_finite {E : Set ℤ} (hE : E.Finite) (f : ℤ → ℝ) :
    Summable (E.indicator f) :=
  summable_of_ne_finset_zero (s := hE.toFinset) fun _j hj ↦
    Set.indicator_of_notMem (fun h ↦ hj (hE.mem_toFinset.mpr h)) _

/-- Short moment times the genuine kernel envelope and the cap to the remaining order.
`E` may cut the shell further, including cutting strictly at an endpoint. -/
public theorem contribution_le_shellBudget {S : Finset ℕ} {d n : ℕ} {X t b Δ B : ℝ}
    {w : ℕ → ℝ} {χ : ℕ → ℂ} {E : Set ℤ} (q : Shell)
    (hd : 0 < d) (hprime : ∀ p ∈ S, p.Prime ∧ (p + d).Prime)
    (hcap : ∀ p ∈ S, (↑(p + d) : ℝ) ≤ X) (hX : 1 < X)
    (hχ : ∀ p ∈ S, ‖χ p‖ = 1) (ht : 0 < t) (hΔ : 0 < Δ)
    (hB : (∑ p ∈ S, w p ^ 2) ≤ B)
    (hshort : X ^ (2 * q.order) < q.height) (hn : 2 * q.order ≤ n) (ha : 0 ≤ q.cap)
    (hmesh : (q.order : ℝ) * frequencyDiameter S d + 1 / q.height ≤ angularPeriod Δ)
    (hE : E ⊆ q.nodes b Δ (amplitude S d w χ)) :
    contribution t b Δ E (fun u ↦ amplitude S d w χ u ^ n) ≤ q.budget t n B := by
  classical
  let s := amplitude S d w χ
  let U : Set ℤ := {j | q.height ≤ |node b Δ j| ∧ |node b Δ j| ≤ 2 * q.height}
  let M := U.indicator fun j ↦ s (node b Δ j) ^ (2 * q.order)
  let F := E.indicator fun j ↦ kernel t (node b Δ j) * s (node b Δ j) ^ n
  let C := shellEnvelope t q.height * q.cap ^ (n - 2 * q.order)
  have hT : 0 < q.height := (pow_pos (zero_lt_one.trans hX) _).trans hshort
  have hM := summable_indicator_finite (finite_shell (b := b) (T := q.height) hΔ)
    (fun j ↦ s (node b Δ j) ^ (2 * q.order))
  have h0M (j : ℤ) : 0 ≤ M j := by
    by_cases hj : j ∈ U
    · dsimp only [M]; rw [Set.indicator_of_mem hj]; exact pow_nonneg (norm_nonneg _) _
    · dsimp only [M]; rw [Set.indicator_of_notMem hj]
  have hC : 0 ≤ C := mul_nonneg (CenteredHeightMesh.shellEnvelope_nonneg ht) (pow_nonneg ha _)
  have h0F (j : ℤ) : 0 ≤ F j := by
    by_cases hj : j ∈ E
    · dsimp only [F]
      rw [Set.indicator_of_mem hj]
      exact mul_nonneg (kernel_nonneg ht _) (pow_nonneg (norm_nonneg _) _)
    · dsimp only [F]; rw [Set.indicator_of_notMem hj]
  have hdom (j : ℤ) : F j ≤ C * M j := by
    by_cases hj : j ∈ E
    · obtain ⟨hlo, hhi, hcut⟩ := hE hj
      have hU : j ∈ U := ⟨hlo, hhi⟩
      dsimp only [F, M]
      rw [Set.indicator_of_mem hj, Set.indicator_of_mem hU]
      have hp : s (node b Δ j) ^ n ≤
          q.cap ^ (n - 2 * q.order) * s (node b Δ j) ^ (2 * q.order) := by
        conv_lhs => rw [← Nat.sub_add_cancel hn, pow_add]
        exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hcut _)
          (pow_nonneg (norm_nonneg _) _)
      calc
        _ ≤ shellEnvelope t q.height * s (node b Δ j) ^ n :=
          mul_le_mul_of_nonneg_right (kernel_le_shellEnvelope ht hT ⟨hlo, hhi⟩)
            (pow_nonneg (norm_nonneg _) _)
        _ ≤ _ := by
          dsimp only [C]
          rw [mul_assoc]
          exact mul_le_mul_of_nonneg_left hp (CenteredHeightMesh.shellEnvelope_nonneg ht)
    · dsimp only [F]; rw [Set.indicator_of_notMem hj]
      exact mul_nonneg hC (h0M j)
  have hCM : Summable (fun j ↦ C * M j) := hM.mul_left C
  have hmoment : Δ * (∑' j : ℤ, M j) ≤
      16 * Real.pi * q.height * (q.order.factorial : ℝ) * (∑ p ∈ S, w p ^ 2) ^ q.order := by
    have hEq (j : ℤ) : M j = (if q.height ≤ |node b Δ j| ∧ |node b Δ j| ≤ 2 * q.height
        then s (node b Δ j) ^ (2 * q.order) else 0) := by
      by_cases hj : j ∈ U
      · have hj' : q.height ≤ |node b Δ j| ∧ |node b Δ j| ≤ 2 * q.height := hj
        exact (Set.indicator_of_mem hj _).trans (ite_eq_left hj').symm
      · have hj' : ¬(q.height ≤ |node b Δ j| ∧ |node b Δ j| ≤ 2 * q.height) := hj
        exact (Set.indicator_of_notMem hj _).trans (ite_eq_right hj').symm
    simp_rw [hEq, s, amplitude, node]
    exact tsum_shell_moment_le hd hprime hcap hX hT hshort w χ hχ hΔ hmesh b
  change Δ * (∑' j, F j) ≤ _
  calc
    _ ≤ Δ * (∑' j, C * M j) :=
      mul_le_mul_of_nonneg_left ((hCM.of_nonneg_of_le h0F hdom).tsum_le_tsum hdom hCM) hΔ.le
    _ = C * (Δ * (∑' j, M j)) := by rw [tsum_mul_left]; ring
    _ ≤ q.budget t n B := by
      apply mul_le_mul_of_nonneg_left _ hC
      exact hmoment.trans (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _) hB _)
        (by positivity))

/-- The power left after extracting the short even moment is the full truncation saving. -/
public theorem cutoff_pow_eq {X β : ℝ} (hX : 0 < X) (n m : ℕ) (hn : 2 * m ≤ n) :
    (X ^ (-β)) ^ (n - 2 * m) = X ^ (-β * ((n : ℝ) - 2 * (m : ℝ))) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hX.le, Nat.cast_sub hn]
  push_cast
  rfl

/-- A nonnegative weight and its maximum (or any upper bound) give the source's `A w_*`. -/
public theorem sum_sq_le_mass_mul {S : Finset ℕ} {w : ℕ → ℝ} {W : ℝ}
    (hw : ∀ p ∈ S, 0 ≤ w p) (hW : ∀ p ∈ S, w p ≤ W) :
    (∑ p ∈ S, w p ^ 2) ≤ (∑ p ∈ S, w p) * W := by
  rw [Finset.sum_mul]
  exact Finset.sum_le_sum fun p hp ↦ by
    rw [pow_two]
    exact mul_le_mul_of_nonneg_left (hW p hp) (hw p hp)

/-- Without truncating the amplitude, use the total nonnegative weight as the cap. -/
public theorem amplitude_le_mass {S : Finset ℕ} {d : ℕ} {w : ℕ → ℝ} {χ : ℕ → ℂ}
    (hw : ∀ p ∈ S, 0 ≤ w p) (hχ : ∀ p ∈ S, ‖χ p‖ = 1) (u : ℝ) :
    amplitude S d w χ u ≤ ∑ p ∈ S, w p := by
  unfold amplitude primePairSum
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun p hp ↦ ?_)
  simp [Complex.norm_real, Real.norm_of_nonneg (hw p hp), hχ p hp, Complex.norm_exp,
    Complex.mul_re]

/-- An omitted portion of a shell with `s ≤ X⁻ᵝ` pays the explicit centered-kernel
price with the full `X⁻ᵝ⁽ⁿ⁻²ᵐ⁾` saving. -/
public theorem contribution_le_of_amplitude_cutoff {S : Finset ℕ} {d n m : ℕ}
    {X t T b Δ β W : ℝ} {w : ℕ → ℝ} {χ : ℕ → ℂ} {E : Set ℤ}
    (hd : 0 < d) (hprime : ∀ p ∈ S, p.Prime ∧ (p + d).Prime)
    (hcap : ∀ p ∈ S, (↑(p + d) : ℝ) ≤ X) (hX : 1 < X)
    (hw : ∀ p ∈ S, 0 ≤ w p) (hW : ∀ p ∈ S, w p ≤ W) (hχ : ∀ p ∈ S, ‖χ p‖ = 1)
    (ht : 0 < t) (hΔ : 0 < Δ) (hshort : X ^ (2 * m) < T) (hn : 2 * m ≤ n)
    (hmesh : (m : ℝ) * frequencyDiameter S d + 1 / T ≤ angularPeriod Δ)
    (hE : ∀ j ∈ E, T ≤ |node b Δ j| ∧ |node b Δ j| ≤ 2 * T ∧
      amplitude S d w χ (node b Δ j) ≤ X ^ (-β)) :
    contribution t b Δ E (fun u ↦ amplitude S d w χ u ^ n) ≤
      shellEnvelope t T * X ^ (-β * ((n : ℝ) - 2 * (m : ℝ))) *
        (16 * Real.pi * T * (m.factorial : ℝ) * ((∑ p ∈ S, w p) * W) ^ m) := by
  simpa only [Shell.budget, cutoff_pow_eq (zero_lt_one.trans hX) n m hn] using
    (contribution_le_shellBudget ⟨T, m, X ^ (-β)⟩ hd hprime hcap hX hχ ht hΔ
      (sum_sq_le_mass_mul hw hW) hshort hn (Real.rpow_nonneg (zero_lt_one.trans hX).le _) hmesh hE)

private theorem indicator_nonneg {E : Set ℤ} {f : ℤ → ℝ} (hf : ∀ j, 0 ≤ f j) (j : ℤ) :
    0 ≤ E.indicator f j := by
  classical
  by_cases hj : j ∈ E
  · simpa only [Set.indicator_of_mem hj] using hf j
  · rw [Set.indicator_of_notMem hj]

private theorem contribution_le_sum_cover {ι : Type*} {t b Δ : ℝ} {E : Set ℤ}
    {f : ℝ → ℝ} (ht : 0 < t) (hΔ : 0 < Δ) (hf : ∀ u, 0 ≤ f u) (I : Finset ι)
    (U : ι → Set ℤ) (hs : ∀ i ∈ I, Summable
      ((U i).indicator fun j ↦ kernel t (node b Δ j) * f (node b Δ j)))
    (hcover : ∀ j ∈ E, ∃ i ∈ I, j ∈ U i) :
    contribution t b Δ E f ≤ ∑ i ∈ I, contribution t b Δ (U i) f := by
  let g (j : ℤ) := kernel t (node b Δ j) * f (node b Δ j)
  have hg (j : ℤ) : 0 ≤ g j := mul_nonneg (kernel_nonneg ht _) (hf _)
  have hdom (j : ℤ) : E.indicator g j ≤ ∑ i ∈ I, (U i).indicator g j := by
    by_cases hj : j ∈ E
    · obtain ⟨i, hi, hj'⟩ := hcover j hj
      rw [Set.indicator_of_mem hj, ← Set.indicator_of_mem hj' g]
      exact Finset.single_le_sum (fun k _ ↦ indicator_nonneg (E := U k) hg j) hi
    · rw [Set.indicator_of_notMem hj]
      exact Finset.sum_nonneg fun i _ ↦ indicator_nonneg (E := U i) hg j
  have hsum : Summable (fun j ↦ ∑ i ∈ I, (U i).indicator g j) := summable_sum hs
  unfold contribution
  rw [← Finset.mul_sum, ← Summable.tsum_finsetSum hs]
  exact mul_le_mul_of_nonneg_left
    ((hsum.of_nonneg_of_le (indicator_nonneg hg) hdom).tsum_le_tsum hdom hsum) hΔ.le

/-- The contribution on any omitted set is bounded by the sum of its finite shell
cover's prices. Shells can have different orders and caps, and overlaps are safe
because all terms being counted twice are nonnegative. -/
public theorem contribution_le_shellCover {ι : Type*} {S : Finset ℕ} {d n : ℕ}
    {X t b Δ B : ℝ} {w : ℕ → ℝ} {χ : ℕ → ℂ} {E : Set ℤ} (I : Finset ι) (Q : ι → Shell)
    (hd : 0 < d) (hprime : ∀ p ∈ S, p.Prime ∧ (p + d).Prime)
    (hcap : ∀ p ∈ S, (↑(p + d) : ℝ) ≤ X) (hX : 1 < X) (hχ : ∀ p ∈ S, ‖χ p‖ = 1)
    (ht : 0 < t) (hΔ : 0 < Δ) (hB : (∑ p ∈ S, w p ^ 2) ≤ B)
    (hshort : ∀ i ∈ I, X ^ (2 * (Q i).order) < (Q i).height)
    (hn : ∀ i ∈ I, 2 * (Q i).order ≤ n) (ha : ∀ i ∈ I, 0 ≤ (Q i).cap)
    (hmesh : ∀ i ∈ I,
      ((Q i).order : ℝ) * frequencyDiameter S d + 1 / (Q i).height ≤ angularPeriod Δ)
    (hcover : ∀ j ∈ E, ∃ i ∈ I, j ∈ (Q i).nodes b Δ (amplitude S d w χ)) :
    contribution t b Δ E (fun u ↦ amplitude S d w χ u ^ n) ≤ ∑ i ∈ I, (Q i).budget t n B := by
  let s := amplitude S d w χ
  have hs (i : ι) (_hi : i ∈ I) : Summable (((Q i).nodes b Δ s).indicator
      fun j ↦ kernel t (node b Δ j) * s (node b Δ j) ^ n) := by
    apply summable_indicator_finite
    exact (finite_shell (b := b) (T := (Q i).height) hΔ).subset (fun _ hj ↦ ⟨hj.1, hj.2.1⟩)
  refine (contribution_le_sum_cover ht hΔ (fun _ ↦ pow_nonneg (norm_nonneg _) _)
    I (fun i ↦ (Q i).nodes b Δ s) hs hcover).trans (Finset.sum_le_sum fun i hi ↦ ?_)
  exact contribution_le_shellBudget (Q i) hd hprime hcap hX hχ ht hΔ hB
    (hshort i hi) (hn i hi) (ha i hi) (hmesh i hi) (Set.Subset.rfl)

open CenteredHeightMesh (kernel_sample_mass_one summable_kernel_samples kernel_le_near_zero
  kernel_le_far)

private theorem contribution_le_majorant {t b Δ : ℝ} {E : Set ℤ} {f : ℝ → ℝ} {g : ℤ → ℝ}
    (ht : 0 < t) (hΔ : 0 < Δ) (hf : ∀ u, 0 ≤ f u) (hg : ∀ j, 0 ≤ g j) (hs : Summable g)
    (hdom : ∀ j ∈ E, kernel t (node b Δ j) * f (node b Δ j) ≤ g j) :
    contribution t b Δ E f ≤ Δ * ∑' j, g j := by
  let a (j : ℤ) := kernel t (node b Δ j) * f (node b Δ j)
  have h (j : ℤ) : E.indicator a j ≤ g j := by
    by_cases hj : j ∈ E
    · simpa only [Set.indicator_of_mem hj] using hdom j hj
    · simpa only [Set.indicator_of_notMem hj] using hg j
  have hEa := hs.of_nonneg_of_le
    (indicator_nonneg fun j ↦ mul_nonneg (kernel_nonneg ht _) (hf (node b Δ j))) h
  exact mul_le_mul_of_nonneg_left (hEa.tsum_le_tsum h hs) hΔ.le

private theorem summable_contribution {t b Δ M : ℝ} {f : ℝ → ℝ} (E : Set ℤ)
    (ht : 0 < t) (hΔ : 0 < Δ) (hf : ∀ u, 0 ≤ f u) (hM : ∀ u, f u ≤ M) :
    Summable (E.indicator fun j ↦ kernel t (node b Δ j) * f (node b Δ j)) := by
  apply Summable.indicator
  exact ((summable_kernel_samples ht hΔ b).mul_right M).of_nonneg_of_le
    (fun j ↦ mul_nonneg (kernel_nonneg ht (node b Δ j)) (hf _))
    (fun j ↦ mul_le_mul_of_nonneg_left (hM _) (kernel_nonneg ht (node b Δ j)))

private theorem mass_one_of_step_le {t Δ : ℝ} (ht : 0 < t) (hΔ : 0 < Δ)
    (hstep : Δ ≤ t) (b : ℝ) : Δ * (∑' j : ℤ, kernel t (node b Δ j)) = 1 :=
  kernel_sample_mass_one ht hΔ
    (div_le_div_of_nonneg_left (by positivity) hΔ hstep) b

/-- A nonnegative uniform floor in a pointwise bound is charged once to the full
mass-one grid, not once for each shell in a cover. -/
public theorem contribution_abs_le_once {t b Δ C F M : ℝ} {E : Set ℤ} {D f : ℝ → ℝ}
    (ht : 0 < t) (hΔ : 0 < Δ) (hmesh : 2 * Real.pi / t ≤ angularPeriod Δ)
    (hC : 0 ≤ C) (hF : 0 ≤ F) (hf : ∀ u, 0 ≤ f u) (hM : ∀ u, f u ≤ M)
    (hpoint : ∀ j ∈ E, |D (node b Δ j)| ≤ C * f (node b Δ j) + F) :
    contribution t b Δ E (fun u ↦ |D u|) ≤ C * contribution t b Δ E f + F := by
  let a := E.indicator fun j ↦ kernel t (node b Δ j) * f (node b Δ j)
  let k (j : ℤ) := kernel t (node b Δ j)
  have ha : Summable a := summable_contribution E ht hΔ hf hM
  have hk : Summable k := summable_kernel_samples ht hΔ b
  have hmass : Δ * (∑' j, k j) = 1 := kernel_sample_mass_one ht hΔ hmesh b
  calc
    _ ≤ Δ * (∑' j : ℤ, (C * a j + F * k j)) := by
      refine contribution_le_majorant ht hΔ (fun _ ↦ abs_nonneg _)
        (fun j ↦ add_nonneg (mul_nonneg hC (indicator_nonneg
          (fun _ ↦ mul_nonneg (kernel_nonneg ht _) (hf _)) j))
          (mul_nonneg hF (kernel_nonneg ht _))) ((ha.mul_left C).add (hk.mul_left F)) ?_
      intro j hj
      dsimp only [a, k]
      rw [Set.indicator_of_mem hj]
      refine (mul_le_mul_of_nonneg_left (hpoint j hj) (kernel_nonneg ht _)).trans_eq ?_
      ring
    _ = _ := by
      rw [(ha.mul_left C).tsum_add (hk.mul_left F), tsum_mul_left, tsum_mul_left]
      change Δ * (C * (∑' j, a j) + F * (∑' j, k j)) = C * (Δ * (∑' j, a j)) + F
      rw [mul_add, mul_left_comm Δ C, mul_left_comm Δ F, hmass, mul_one]

private theorem quarter_le_sinc_sq {x : ℝ} (h : |x| ≤ 1 / 4) : 1 / 4 ≤ Real.sinc x ^ 2 := by
  have heq : Real.sinc |x| = Real.sinc x := by
    rcases le_total 0 x with hx | hx
    · rw [abs_of_nonneg hx]
    · rw [abs_of_nonpos hx, Real.sinc_neg]
  rw [← heq]
  have hlow : 1 / 2 ≤ Real.sinc |x| := by
    rcases (abs_nonneg x).eq_or_lt with hzero | hx
    · rw [← hzero, Real.sinc_zero]; norm_num
    rw [Real.sinc_of_ne_zero hx.ne', le_div_iff₀ hx]
    have hc := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg x) h 2) (abs_nonneg x)
    linarith only [Real.sin_gt_sub_cube hx, hx, show |x| ^ 3 ≤ (1 / 4 : ℝ) ^ 2 * |x| by
      simpa only [pow_succ _ 2] using hc]
  calc
    _ = (1 / 2 : ℝ) ^ 2 := by norm_num
    _ ≤ _ := pow_le_pow_left₀ (by norm_num) hlow 2

/-- A bounded contribution at the central omitted heights, uniformly in the grid
origin. The `R³/t³` factor combines the double zero with the grid mass at scale `R`. -/
public theorem contribution_le_central {t b Δ R M : ℝ} {E : Set ℤ} {f : ℝ → ℝ}
    (ht : 0 < t) (hΔ : 0 < Δ) (hR : 0 < R) (hRt : R ≤ t / 2) (hstep : Δ ≤ 4 * Real.pi * R)
    (hM : 0 ≤ M) (hf : ∀ u, 0 ≤ f u) (hbound : ∀ j ∈ E, f (node b Δ j) ≤ M)
    (hE : ∀ j ∈ E, |node b Δ j| ≤ R) :
    contribution t b Δ E f ≤ 64 * Real.pi * (R ^ 3 / t ^ 3) * M := by
  let L := 4 * Real.pi * R
  let C := 64 * Real.pi * (R ^ 3 / t ^ 3) * M
  let k (j : ℤ) := kernel L (node (b + L) Δ j)
  have hL : 0 < L := by dsimp only [L]; positivity
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hmass : Δ * (∑' j, k j) = 1 := mass_one_of_step_le hL hΔ hstep (b + L)
  calc
    _ ≤ Δ * (∑' j, C * k j) := by
      refine contribution_le_majorant ht hΔ hf (fun j ↦ mul_nonneg hC (kernel_nonneg hL _))
        ((summable_kernel_samples hL hΔ (b + L)).mul_left C) ?_
      intro j hj
      let u := node b Δ j
      have hu : |u| ≤ R := hE j hj
      have hshift : node (b + L) Δ j = u + L := by unfold u node; ring
      have harg : Real.pi * ((u + L) / L - 1) = u / (4 * R) := by
        dsimp only [L]
        field_simp
        ring
      have hsmall : |u / (4 * R)| ≤ 1 / 4 := by
        rw [abs_div, abs_of_pos (by positivity : 0 < 4 * R), div_le_iff₀ (by positivity)]
        linarith
      have hlower : L⁻¹ * (1 / 4) ≤ k j := by
        dsimp only [k]
        rw [hshift, kernel, harg]
        exact mul_le_mul_of_nonneg_left (quarter_le_sinc_sq hsmall) (inv_nonneg.mpr hL.le)
      calc
        _ ≤ (4 * |u| ^ 2 / t ^ 3) * M := mul_le_mul
          (kernel_le_near_zero ht (hu.trans hRt)) (hbound j hj) (hf _) (by positivity)
        _ ≤ (4 * R ^ 2 / t ^ 3) * M := by gcongr
        _ = C * (L⁻¹ * (1 / 4)) := by dsimp only [C, L]; field_simp; ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hlower hC
    _ = _ := by rw [tsum_mul_left, mul_left_comm Δ C, hmass, mul_one]

private theorem sinc_sq_mul_sq (x : ℝ) : Real.sinc x ^ 2 * x ^ 2 = Real.sin x ^ 2 := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  rw [Real.sinc_of_ne_zero hx, ← mul_pow, div_mul_cancel₀ _ hx]

private theorem kernel_far_le_two_scaled {t R u : ℝ} (ht : 0 < t) (hR : 0 < R)
    (hRsmall : 2 * t ≤ R) (hu : R ≤ |u|) :
    kernel t u ≤ (16 * Real.pi ^ 2 * (t / R)) * (kernel R u + kernel R (u + R / 2)) := by
  let v := u / R
  let x := Real.pi * (v - 1)
  let y := x + Real.pi / 2
  let B := 2 * Real.pi * |v|
  have hv : 1 ≤ |v| := by
    dsimp only [v]
    rwa [abs_div, abs_of_pos hR, le_div_iff₀ hR, one_mul]
  have hB₀ : 0 ≤ B := by dsimp only [B]; positivity
  have hx : |x| ≤ B := by
    dsimp only [x, B]
    rw [abs_mul, abs_of_pos Real.pi_pos]
    have h := abs_add_le v (-1)
    rw [← sub_eq_add_neg, abs_neg, abs_one] at h
    nlinarith only [mul_le_mul_of_nonneg_left (show |v - 1| ≤ 2 * |v| by linarith) Real.pi_pos.le]
  have hy : |y| ≤ B := by
    have hy' : y = Real.pi * (v - 1 / 2) := by dsimp only [y, x]; ring
    rw [hy', abs_mul, abs_of_pos Real.pi_pos]
    have h := abs_add_le v (-(1 / 2 : ℝ))
    rw [← sub_eq_add_neg, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] at h
    exact (mul_le_mul_of_nonneg_left (show |v - 1 / 2| ≤ 2 * |v| by linarith)
      Real.pi_pos.le).trans_eq (by dsimp only [B]; ring)
  have hsin (z : ℝ) (hz : |z| ≤ B) : Real.sin z ^ 2 ≤ Real.sinc z ^ 2 * B ^ 2 := by
    rw [← sinc_sq_mul_sq z]
    refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg z) hz 2
  have hsum : 1 ≤ B ^ 2 * (Real.sinc x ^ 2 + Real.sinc y ^ 2) := by
    have hh := add_le_add (hsin x hx) (hsin y hy)
    have hySin : Real.sin y = Real.cos x := Real.sin_add_pi_div_two x
    rw [hySin, Real.sin_sq_add_cos_sq] at hh
    exact hh.trans_eq (by ring)
  have harg : Real.pi * ((u + R / 2) / R - 1) = y := by
    dsimp only [y, x, v]; field_simp; ring
  have hu0 : |u| ≠ 0 := (hR.trans_le hu).ne'
  calc
    _ ≤ 4 * t / |u| ^ 2 := kernel_le_far ht (hRsmall.trans hu)
    _ ≤ (4 * t / |u| ^ 2) * (B ^ 2 * (Real.sinc x ^ 2 + Real.sinc y ^ 2)) := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hsum (by positivity : 0 ≤ 4 * t / |u| ^ 2)
    _ = _ := by
      rw [kernel, kernel, harg]
      change _ = _ * (R⁻¹ * Real.sinc x ^ 2 + R⁻¹ * Real.sinc y ^ 2)
      dsimp only [B, v]
      rw [abs_div, abs_of_pos hR]
      field_simp
      ring

/-- A bounded contribution at the far omitted heights. Two offset auxiliary mass-one
kernels majorize the reciprocal-square tail (their numerator phases are in quadrature). -/
public theorem contribution_le_tail {t b Δ R M : ℝ} {E : Set ℤ} {f : ℝ → ℝ}
    (ht : 0 < t) (hΔ : 0 < Δ) (hRt : 2 * t ≤ R) (hstep : Δ ≤ R)
    (hM : 0 ≤ M) (hf : ∀ u, 0 ≤ f u) (hbound : ∀ j ∈ E, f (node b Δ j) ≤ M)
    (hE : ∀ j ∈ E, R ≤ |node b Δ j|) :
    contribution t b Δ E f ≤ 32 * Real.pi ^ 2 * (t / R) * M := by
  let C := 16 * Real.pi ^ 2 * (t / R) * M
  let k (j : ℤ) := kernel R (node b Δ j)
  let k' (j : ℤ) := kernel R (node (b + R / 2) Δ j)
  have hR : 0 < R := (by positivity : 0 < 2 * t).trans_le hRt
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hk : Summable k := summable_kernel_samples hR hΔ b
  have hk' : Summable k' := summable_kernel_samples hR hΔ (b + R / 2)
  have hmass : Δ * (∑' j, k j) = 1 := mass_one_of_step_le hR hΔ hstep b
  have hmass' : Δ * (∑' j, k' j) = 1 := mass_one_of_step_le hR hΔ hstep (b + R / 2)
  calc
    _ ≤ Δ * (∑' j, C * (k j + k' j)) := by
      refine contribution_le_majorant ht hΔ hf (fun _ ↦ mul_nonneg hC
        (add_nonneg (kernel_nonneg hR _) (kernel_nonneg hR _))) ((hk.add hk').mul_left C) ?_
      intro j hj
      have hshift : node (b + R / 2) Δ j = node b Δ j + R / 2 := by unfold node; ring
      dsimp only [k, k']
      rw [hshift]
      have hK := kernel_far_le_two_scaled ht hR hRt (hE j hj)
      convert mul_le_mul hK (hbound j hj) (hf _) (kernel_nonneg ht _ |>.trans hK) using 1
      dsimp only [C]
      ring
    _ = _ := by
      rw [tsum_mul_left, hk.tsum_add hk', mul_left_comm Δ C, mul_add Δ, hmass, hmass']
      dsimp only [C]
      ring

/-- Height band with both endpoints retained. -/
@[expose] public def InBand (lo hi u : ℝ) : Prop := lo ≤ |u| ∧ |u| ≤ hi

/-- The reconstruction's lower amplitude exponent. -/
@[expose] public noncomputable def alpha (γ : ℝ) : ℝ := (3 / 4 + γ / 8) / (3 + 2 * γ)

/-- Complement of the two actual retained regions. In particular the upper
amplitude threshold is retained on the wide band, not on the cubic branch. -/
@[expose] public def omittedNodes (X t γ b Δ : ℝ) (s : ℝ → ℝ) : Set ℤ :=
  {j | let u := node b Δ j
       ¬ (InBand (t ^ (7 / 10 : ℝ)) (t ^ (13 / 8 : ℝ)) u ∧ X ^ (-(1 / 10 : ℝ)) ≤ s u ∨
          InBand (t ^ (5 / 6 : ℝ)) (t ^ (7 / 5 : ℝ)) u ∧
            X ^ (-alpha γ) ≤ s u ∧ s u < X ^ (-(1 / 10 : ℝ)))}

/-- The exact complement is covered by the three types of exclusions in the note.
The inequalities at the two amplitude thresholds and the height endpoints are not rounded. -/
public theorem mem_omittedNodes_iff {X t γ b Δ : ℝ} {s : ℝ → ℝ} {j : ℤ}
    (hX : 1 ≤ X) (ht : 1 ≤ t) (hγ : 0 ≤ γ) (hγ' : γ ≤ 1 / 2) :
    j ∈ omittedNodes X t γ b Δ s ↔
      let u := node b Δ j
      ¬ InBand (t ^ (7 / 10 : ℝ)) (t ^ (13 / 8 : ℝ)) u ∨
        (¬ InBand (t ^ (5 / 6 : ℝ)) (t ^ (7 / 5 : ℝ)) u ∧ s u < X ^ (-(1 / 10 : ℝ))) ∨
        s u < X ^ (-alpha γ) := by
  let u := node b Δ j
  let wide := InBand (t ^ (7 / 10 : ℝ)) (t ^ (13 / 8 : ℝ)) u
  let narrow := InBand (t ^ (5 / 6 : ℝ)) (t ^ (7 / 5 : ℝ)) u
  let a := X ^ (-alpha γ)
  let c := X ^ (-(1 / 10 : ℝ))
  have hnc : narrow → wide := fun h ↦
    ⟨(Real.rpow_le_rpow_of_exponent_le ht (by norm_num : (7 / 10 : ℝ) ≤ 5 / 6)).trans h.1,
      h.2.trans (Real.rpow_le_rpow_of_exponent_le ht (by norm_num : (7 / 5 : ℝ) ≤ 13 / 8))⟩
  have hac : a ≤ c := by
    apply Real.rpow_le_rpow_of_exponent_le hX
    have hα : 1 / 10 ≤ alpha γ := by
      unfold alpha
      apply (le_div_iff₀ (by positivity)).2
      linarith
    linarith
  change (¬ (wide ∧ c ≤ s u ∨ narrow ∧ a ≤ s u ∧ s u < c)) ↔
    ¬ wide ∨ (¬ narrow ∧ s u < c) ∨ s u < a
  constructor
  · intro h
    by_cases hw : wide
    · have hc : s u < c := lt_of_not_ge fun h' ↦ h (.inl ⟨hw, h'⟩)
      by_cases hn : narrow
      · exact .inr (.inr (lt_of_not_ge fun ha ↦ h (.inr ⟨hn, ha, hc⟩)))
      · exact .inr (.inl ⟨hn, hc⟩)
    · exact .inl hw
  · rintro (h | ⟨h, hc⟩ | h) (⟨hw, h'⟩ | ⟨hn, h', _⟩)
    · exact h hw
    · exact h (hnc hn)
    · exact (not_le_of_gt hc) h'
    · exact h hn
    · exact (not_le_of_gt h) (hac.trans h')
    · exact (not_le_of_gt h) h'

private theorem contribution_le_union {t b Δ M : ℝ} {E U V : Set ℤ} {f : ℝ → ℝ}
    (ht : 0 < t) (hΔ : 0 < Δ) (hf : ∀ u, 0 ≤ f u) (hM : ∀ u, f u ≤ M)
    (hcover : E ⊆ U ∪ V) :
    contribution t b Δ E f ≤ contribution t b Δ U f + contribution t b Δ V f := by
  let a (A : Set ℤ) := A.indicator fun j ↦ kernel t (node b Δ j) * f (node b Δ j)
  have hsum (A : Set ℤ) : Summable (a A) := summable_contribution A ht hΔ hf hM
  have hnonneg (A : Set ℤ) (j : ℤ) : 0 ≤ a A j := indicator_nonneg
    (fun j ↦ mul_nonneg (kernel_nonneg ht (node b Δ j)) (hf _)) j
  calc
    _ ≤ Δ * (∑' j : ℤ, (a U j + a V j)) := by
      refine contribution_le_majorant ht hΔ hf (fun j ↦ add_nonneg (hnonneg U j) (hnonneg V j))
        ((hsum U).add (hsum V)) ?_
      intro j hj
      rcases hcover hj with hu | hv
      · have heq : a U j = kernel t (node b Δ j) * f (node b Δ j) := Set.indicator_of_mem hu _
        exact heq ▸ le_add_of_nonneg_right (hnonneg V j)
      · have heq : a V j = kernel t (node b Δ j) * f (node b Δ j) := Set.indicator_of_mem hv _
        exact heq ▸ le_add_of_nonneg_left (hnonneg U j)
    _ = _ := by rw [(hsum U).tsum_add (hsum V), mul_add]; rfl

/-- Exact discrete complement bound. `D` is the real signed coefficient with the
source's two pointwise bounds supplied as inputs. Only omitted nodes in the middle
range need a short-moment shell cover. The central and infinite far ranges use the
trivial coefficient bound; the middle range charges the uniform floor just once. -/
public theorem omitted_contribution_abs_le {ι : Type*} {S : Finset ℕ} {d n : ℕ}
    {X t γ b Δ R V W C F : ℝ} {w : ℕ → ℝ} {χ : ℕ → ℂ} {D : ℝ → ℝ}
    (I : Finset ι) (Q : ι → Shell)
    (hd : 0 < d) (hprime : ∀ p ∈ S, p.Prime ∧ (p + d).Prime)
    (hcap : ∀ p ∈ S, (↑(p + d) : ℝ) ≤ X) (hX : 1 < X)
    (hw : ∀ p ∈ S, 0 ≤ w p) (hW : ∀ p ∈ S, w p ≤ W) (hχ : ∀ p ∈ S, ‖χ p‖ = 1)
    (ht : 0 < t) (hΔ : 0 < Δ) (hR : 0 < R) (hRt : R ≤ t / 2) (hV : 2 * t ≤ V)
    (hΔR : Δ ≤ 4 * Real.pi * R) (hΔV : Δ ≤ V) (hmass : 2 * Real.pi / t ≤ angularPeriod Δ)
    (hC : 0 ≤ C) (hF : 0 ≤ F)
    (htrivial : ∀ u, |D u| ≤ (∑ p ∈ S, w p) ^ n)
    (hpoint : ∀ u, |D u| ≤ C * amplitude S d w χ u ^ n + F)
    (hshort : ∀ i ∈ I, X ^ (2 * (Q i).order) < (Q i).height)
    (hn : ∀ i ∈ I, 2 * (Q i).order ≤ n) (ha : ∀ i ∈ I, 0 ≤ (Q i).cap)
    (hmesh : ∀ i ∈ I,
      ((Q i).order : ℝ) * frequencyDiameter S d + 1 / (Q i).height ≤ angularPeriod Δ)
    (hcover : ∀ j ∈ omittedNodes X t γ b Δ (amplitude S d w χ),
      InBand R V (node b Δ j) → ∃ i ∈ I, j ∈ (Q i).nodes b Δ (amplitude S d w χ)) :
    contribution t b Δ (omittedNodes X t γ b Δ (amplitude S d w χ)) (fun u ↦ |D u|) ≤
      F + C * (∑ i ∈ I, (Q i).budget t n ((∑ p ∈ S, w p) * W)) +
        (64 * Real.pi * (R ^ 3 / t ^ 3) + 32 * Real.pi ^ 2 * (t / V)) * (∑ p ∈ S, w p) ^ n := by
  let s := amplitude S d w χ
  let A := ∑ p ∈ S, w p
  let E := omittedNodes X t γ b Δ s
  let J := E ∩ {j | InBand R V (node b Δ j)}
  let L : Set ℤ := {j | |node b Δ j| < R}
  let H : Set ℤ := {j | V < |node b Δ j|}
  have hJ : ∀ j ∈ J, ∃ i ∈ I, j ∈ (Q i).nodes b Δ s := fun j hj ↦ hcover j hj.1 hj.2
  have hUL : E ⊆ L ∪ (J ∪ H) := by
    intro j hj
    rcases lt_or_ge |node b Δ j| R with hlo | hlo
    · exact .inl hlo
    rcases lt_or_ge V |node b Δ j| with hhi | hhi
    · exact .inr (.inr hhi)
    · exact .inr (.inl ⟨hj, hlo, hhi⟩)
  have hA : 0 ≤ A := Finset.sum_nonneg hw
  have hsnonneg (u : ℝ) : 0 ≤ s u := norm_nonneg _
  have hsbound (u : ℝ) : s u ^ n ≤ A ^ n := pow_le_pow_left₀ (hsnonneg u) (amplitude_le_mass hw hχ _) _
  have hmid := contribution_le_shellCover I Q hd hprime hcap hX hχ ht hΔ
    (sum_sq_le_mass_mul hw hW) hshort hn ha hmesh hJ
  have hm := contribution_abs_le_once ht hΔ hmass hC hF
    (fun u ↦ pow_nonneg (hsnonneg u) n) hsbound (fun j (_hj : j ∈ J) ↦ hpoint (node b Δ j))
  have hl := contribution_le_central ht hΔ hR hRt hΔR (pow_nonneg hA n) (fun u ↦ abs_nonneg (D u))
    (fun j (_hj : j ∈ L) ↦ htrivial (node b Δ j)) (fun _ hj ↦ (show _ < R from hj).le)
  have hh := contribution_le_tail ht hΔ hV hΔV (pow_nonneg hA n) (fun u ↦ abs_nonneg (D u))
    (fun j (_hj : j ∈ H) ↦ htrivial (node b Δ j)) (fun _ hj ↦ (show V < _ from hj).le)
  have huv := contribution_le_union (b := b) ht hΔ (fun u ↦ abs_nonneg (D u)) htrivial hUL
  have hvl := contribution_le_union (b := b) ht hΔ (fun u ↦ abs_nonneg (D u)) htrivial
    (Set.Subset.rfl : J ∪ H ⊆ J ∪ H)
  have hm' := hm.trans (add_le_add_left (mul_le_mul_of_nonneg_left hmid hC) F)
  calc
    _ ≤ _ := huv.trans (add_le_add_right hvl _)
    _ ≤ _ := add_le_add hl (add_le_add hm' hh)
    _ = _ := by ring

end Masullo.OmittedMeshShells
