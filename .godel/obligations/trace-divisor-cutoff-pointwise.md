# Uniform cutoff bound: pointwise half

**Status: Lean draft, not elaborated.** This is the pointwise half of the [two-scale cutoff repair](trace-divisor-cutoff.md#uniform-weighted-bounds-for-the-cutoff-family), at project base `e0c7f187278d8b55d15600c56f7302f133251cd4`. The connection to Masullo is indirect: The provisional reading of (13.3.1.2)–(13.3.1.3), p. 522 of the [pinned edition](../sources/masullo/README.md), supplies the setting for the conditional comparison on zero-mean tests. The cutoff estimate below is a project proof, not a manuscript claim or a proof of that comparison. No new manuscript reading is asserted.

## Interface and estimate

Use a **real** scale `N`. For the family indexed by `n : ℕ`, pass `N := (n : ℝ) + 2`; all divides and interval endpoints below are real. On the closed lower layer `I_N = [1/N, 2/N]`, supply bounds `N*M₁`, `N^2*M₂` for the norms of the first and second derivatives of `L`; off it, supply vanishing of both derivatives. For the upper cutoff supply global bounds `M₁/N`, `M₂/N^2`, and first-derivative vanishing off `[N,2*N]`. Upper second-derivative support is not needed here. Both cutoff values belong to `[0,1]`. These inputs follow from the profile bounds in the parent handoff; in particular the global upper bounds follow by splitting the upper indicator into its `1` and `0` cases. With `N ≥ 2`, `2/N ≤ 1 < N`. Thus on the entire closed lower layer, endpoints included, `U' = 0`; off the layer, `L' = 0`. This proves `L' * U' = 0`, rather than assuming the cross term away.

Let `p = L * U`, `f = p • Δ`, `w = exp(a*x)`, `E = exp(-δ*x)`, and `Wⱼ = w * ‖Δ⁽ʲ⁾ x‖`. Iterated Leibniz gives `f'' = p • Δ'' + (2*p') • Δ' + p'' • Δ`, with `p'' = L''*U + 2*L'*U' + L*U''`. The triangle inequality, `‖p‖ ≤ 1`, `‖p'‖ ≤ ‖L'‖ + M₁`, and `‖p''‖ ≤ ‖L''‖ + M₂` give

$$w(\|f\|+\|f''\|)\le W_0+W_2+2M_1W_1+M_2W_0 + (2\|L'\|W_1+\|L''\|W_0).$$

Use `Wⱼ ≤ Aⱼ*E` for the first four terms. Off the lower layer the parenthesis vanishes. On it, `E ≤ 1` implies `W₁ ≤ A₁`; the separately supplied **weighted** bound `W₀ ≤ B*x` gives `N^2*M₂*W₀ ≤ N^2*M₂*B*(2/N) = (2*M₂*B)*N`. In particular no unweighted linear estimate is substituted. Only `x > 0` is claimed and no sign on `a` is needed.

## Lean draft

```lean
import Mathlib

open scoped ContDiff

namespace Masullo

private theorem cutoff_deriv_deriv_mul {L U : ℝ → ℝ}
    (hL : ContDiff ℝ 2 L) (hU : ContDiff ℝ 2 U) (x : ℝ) :
    deriv (deriv (fun y ↦ L y * U y)) x =
      deriv (deriv L) x * U x + 2 * (deriv L x * deriv U x) +
        L x * deriv (deriv U) x := by
  have hL₁ (y : ℝ) : HasDerivAt L (deriv L y) y :=
    (hL.differentiable two_ne_zero y).hasDerivAt
  have hU₁ (y : ℝ) : HasDerivAt U (deriv U y) y :=
    (hU.differentiable two_ne_zero y).hasDerivAt
  have hL₂ := (hL.differentiable_deriv_two x).hasDerivAt
  have hU₂ := (hU.differentiable_deriv_two x).hasDerivAt
  have hfirst : deriv (fun y ↦ L y * U y) =
      (fun y ↦ deriv L y * U y + L y * deriv U y) :=
    funext fun y ↦ ((hL₁ y).mul (hU₁ y)).deriv
  rw [hfirst]
  calc
    _ = (deriv (deriv L) x * U x + deriv L x * deriv U x) +
        (deriv L x * deriv U x + L x * deriv (deriv U) x) :=
      ((hL₂.mul (hU₁ x)).add ((hL₁ x).mul hU₂)).deriv
    _ = _ := by ring

private theorem cutoff_deriv_deriv_smul {p : ℝ → ℝ} {Δ : ℝ → ℂ}
    (hp : ContDiff ℝ 2 p) (hΔ : ContDiff ℝ 2 Δ) (x : ℝ) :
    deriv (deriv (fun y ↦ p y • Δ y)) x =
      p x • deriv (deriv Δ) x + (2 * deriv p x) • deriv Δ x + deriv (deriv p) x • Δ x := by
  have hp₁ (y : ℝ) : HasDerivAt p (deriv p y) y :=
    (hp.differentiable two_ne_zero y).hasDerivAt
  have hΔ₁ (y : ℝ) : HasDerivAt Δ (deriv Δ y) y :=
    (hΔ.differentiable two_ne_zero y).hasDerivAt
  have hp₂ := (hp.differentiable_deriv_two x).hasDerivAt
  have hΔ₂ := (hΔ.differentiable_deriv_two x).hasDerivAt
  have hfirst : deriv (fun y ↦ p y • Δ y) =
      (fun y ↦ p y • deriv Δ y + deriv p y • Δ y) :=
    funext fun y ↦ ((hp₁ y).smul (hΔ₁ y)).deriv
  rw [hfirst]
  calc
    _ = (p x • deriv (deriv Δ) x + deriv p x • deriv Δ x) +
        (deriv p x • deriv Δ x + deriv (deriv p) x • Δ x) :=
      (((hp₁ x).smul hΔ₂).add (hp₂.smul (hΔ₁ x))).deriv
    _ = _ := by
      rw [mul_smul, two_smul ℝ]
      abel

/-- Weighted pointwise estimate with an exponential background and one thin layer. -/
theorem cutoff_pointwise_majorant {L U : ℝ → ℝ} {Δ : ℝ → ℂ}
    {N a δ M₁ M₂ A₀ A₁ A₂ B : ℝ}
    (hN : 2 ≤ N) (hδ : 0 < δ)
    (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂)
    (hA₁ : 0 ≤ A₁) (hB : 0 ≤ B)
    (hL : ContDiff ℝ 2 L) (hU : ContDiff ℝ 2 U) (hΔ : ContDiff ℝ 2 Δ)
    (hL_range : ∀ x, L x ∈ Set.Icc (0 : ℝ) 1)
    (hU_range : ∀ x, U x ∈ Set.Icc (0 : ℝ) 1)
    (hL_layer : ∀ x ∈ Set.Icc (1 / N) (2 / N),
      ‖deriv L x‖ ≤ N * M₁ ∧ ‖deriv (deriv L) x‖ ≤ N ^ 2 * M₂)
    (hL_off : ∀ x ∉ Set.Icc (1 / N) (2 / N),
      deriv L x = 0 ∧ deriv (deriv L) x = 0)
    (hU_bounds : ∀ x, ‖deriv U x‖ ≤ M₁ / N ∧ ‖deriv (deriv U) x‖ ≤ M₂ / N ^ 2)
    (hU_off : ∀ x ∉ Set.Icc N (2 * N), deriv U x = 0)
    (hΔ_exp : ∀ x > 0,
      Real.exp (a * x) * ‖Δ x‖ ≤ A₀ * Real.exp (-δ * x) ∧
      Real.exp (a * x) * ‖deriv Δ x‖ ≤ A₁ * Real.exp (-δ * x) ∧
      Real.exp (a * x) * ‖deriv (deriv Δ) x‖ ≤ A₂ * Real.exp (-δ * x))
    (hΔ_linear : ∀ x > 0, Real.exp (a * x) * ‖Δ x‖ ≤ B * x) :
    let f : ℝ → ℂ := fun y ↦ (L y * U y : ℝ) • Δ y
    let C₀ : ℝ := A₀ + A₂ + 2 * M₁ * A₁ + M₂ * A₀
    let C₁ : ℝ := 2 * M₁ * A₁ + 2 * M₂ * B
    ∀ x > 0, Real.exp (a * x) * (‖f x‖ + ‖deriv (deriv f) x‖) ≤
      C₀ * Real.exp (-δ * x) + (Set.Icc (1 / N) (2 / N)).indicator (fun _ ↦ C₁ * N) x := by
  classical
  intro f C₀ C₁ x hx
  have hNpos : 0 < N := lt_of_lt_of_le (by norm_num) hN
  have hN₁ : 1 ≤ N := le_trans (by norm_num) hN
  have hN₂ : 1 ≤ N ^ 2 := one_le_pow₀ hN₁
  have h2N : 2 / N ≤ 1 := (div_le_iff₀ hNpos).2 (by simpa only [one_mul] using hN)
  have hcross : deriv L x * deriv U x = 0 := by
    by_cases hI : x ∈ Set.Icc (1 / N) (2 / N)
    · have hxN : x < N := lt_of_le_of_lt (hI.2.trans h2N) (lt_of_lt_of_le (by norm_num) hN)
      have hJ : x ∉ Set.Icc N (2 * N) := fun hj ↦ (not_le_of_gt hxN) hj.1
      rw [hU_off x hJ, mul_zero]
    · rw [(hL_off x hI).1, zero_mul]

  let p : ℝ → ℝ := fun y ↦ L y * U y
  have hp : ContDiff ℝ 2 p := hL.mul hU
  have hL₀ : ‖L x‖ ≤ 1 := by
    rw [Real.norm_of_nonneg (hL_range x).1]
    exact (hL_range x).2
  have hU₀ : ‖U x‖ ≤ 1 := by
    rw [Real.norm_of_nonneg (hU_range x).1]
    exact (hU_range x).2
  have hU₁ : ‖deriv U x‖ ≤ M₁ := (hU_bounds x).1.trans (div_le_self hM₁ hN₁)
  have hU₂ : ‖deriv (deriv U) x‖ ≤ M₂ := (hU_bounds x).2.trans (div_le_self hM₂ hN₂)
  have hp₀ : ‖p x‖ ≤ 1 := by
    change ‖L x * U x‖ ≤ 1
    rw [norm_mul]
    simpa only [one_mul] using mul_le_mul hL₀ hU₀ (norm_nonneg (U x)) (zero_le_one' ℝ)
  have hnorm_prod (l u : ℝ) : ‖l * U x + L x * u‖ ≤ ‖l‖ + ‖u‖ := by
    calc
      _ ≤ ‖l * U x‖ + ‖L x * u‖ := norm_add_le _ _
      _ = ‖l‖ * ‖U x‖ + ‖L x‖ * ‖u‖ := by simp only [norm_mul]
      _ ≤ ‖l‖ * 1 + 1 * ‖u‖ := add_le_add
        (mul_le_mul_of_nonneg_left hU₀ (norm_nonneg l))
        (mul_le_mul_of_nonneg_right hL₀ (norm_nonneg u))
      _ = _ := by simp only [mul_one, one_mul]
  have hp₁_eq : deriv p x = deriv L x * U x + L x * deriv U x :=
    (((hL.differentiable two_ne_zero x).hasDerivAt).mul
      ((hU.differentiable two_ne_zero x).hasDerivAt)).deriv
  have hp₂_eq : deriv (deriv p) x = deriv (deriv L) x * U x + L x * deriv (deriv U) x := by
    simpa only [p, hcross, mul_zero, add_zero] using cutoff_deriv_deriv_mul hL hU x
  have hp₁ : ‖deriv p x‖ ≤ ‖deriv L x‖ + M₁ := by
    rw [hp₁_eq]
    exact (hnorm_prod _ _).trans (add_le_add le_rfl hU₁)
  have hp₂ : ‖deriv (deriv p) x‖ ≤ ‖deriv (deriv L) x‖ + M₂ := by
    rw [hp₂_eq]
    exact (hnorm_prod _ _).trans (add_le_add le_rfl hU₂)

  have hf₀ : ‖f x‖ = ‖p x‖ * ‖Δ x‖ := norm_smul (p x) (Δ x)
  have hf₂ : ‖deriv (deriv f) x‖ ≤
      ‖p x‖ * ‖deriv (deriv Δ) x‖ + (2 * ‖deriv p x‖) * ‖deriv Δ x‖ +
        ‖deriv (deriv p) x‖ * ‖Δ x‖ := by
    change ‖deriv (deriv (fun y ↦ p y • Δ y)) x‖ ≤ _
    rw [cutoff_deriv_deriv_smul hp hΔ x]
    calc
      _ ≤ (‖p x • deriv (deriv Δ) x‖ + ‖(2 * deriv p x) • deriv Δ x‖) +
          ‖deriv (deriv p) x • Δ x‖ :=
        (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
      _ = _ := by simp only [norm_smul, norm_mul, Real.norm_ofNat]

  let w := Real.exp (a * x)
  let E := Real.exp (-δ * x)
  let W₀ := w * ‖Δ x‖
  let W₁ := w * ‖deriv Δ x‖
  let W₂ := w * ‖deriv (deriv Δ) x‖
  let layer := 2 * ‖deriv L x‖ * W₁ + ‖deriv (deriv L) x‖ * W₀
  have hw : 0 ≤ w := (Real.exp_pos _).le
  have hW₀ : 0 ≤ W₀ := mul_nonneg hw (norm_nonneg _)
  have hW₁ : 0 ≤ W₁ := mul_nonneg hw (norm_nonneg _)
  have hW₂ : 0 ≤ W₂ := mul_nonneg hw (norm_nonneg _)
  have hWexp : W₀ ≤ A₀ * E ∧ W₁ ≤ A₁ * E ∧ W₂ ≤ A₂ * E := hΔ_exp x hx
  have hWlin : W₀ ≤ B * x := hΔ_linear x hx
  have hTwo : (0 : ℝ) ≤ 2 := by norm_num
  have hbase : W₀ + W₂ + (2 * M₁) * W₁ + M₂ * W₀ ≤ C₀ * E := by
    calc
      _ ≤ A₀ * E + A₂ * E + (2 * M₁) * (A₁ * E) + M₂ * (A₀ * E) :=
        add_le_add (add_le_add (add_le_add hWexp.1 hWexp.2.2)
          (mul_le_mul_of_nonneg_left hWexp.2.1 (mul_nonneg hTwo hM₁)))
          (mul_le_mul_of_nonneg_left hWexp.1 hM₂)
      _ = _ := by dsimp only [C₀]; ring
  have hmain : w * (‖f x‖ + ‖deriv (deriv f) x‖) ≤ C₀ * E + layer := by
    calc
      _ ≤ w * (‖p x‖ * ‖Δ x‖ + (‖p x‖ * ‖deriv (deriv Δ) x‖ +
          (2 * ‖deriv p x‖) * ‖deriv Δ x‖ + ‖deriv (deriv p) x‖ * ‖Δ x‖)) :=
        mul_le_mul_of_nonneg_left (add_le_add hf₀.le hf₂) hw
      _ = ‖p x‖ * W₀ + ‖p x‖ * W₂ + (2 * ‖deriv p x‖) * W₁ + ‖deriv (deriv p) x‖ * W₀ := by
        dsimp only [W₀, W₁, W₂]
        ring
      _ ≤ 1 * W₀ + 1 * W₂ + (2 * (‖deriv L x‖ + M₁)) * W₁ +
          (‖deriv (deriv L) x‖ + M₂) * W₀ :=
        add_le_add (add_le_add (add_le_add (mul_le_mul_of_nonneg_right hp₀ hW₀)
          (mul_le_mul_of_nonneg_right hp₀ hW₂))
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp₁ hTwo) hW₁))
          (mul_le_mul_of_nonneg_right hp₂ hW₀)
      _ = (W₀ + W₂ + (2 * M₁) * W₁ + M₂ * W₀) + layer := by
        dsimp only [layer]
        ring
      _ ≤ _ := add_le_add hbase le_rfl

  change w * (‖f x‖ + ‖deriv (deriv f) x‖) ≤
    C₀ * E + (Set.Icc (1 / N) (2 / N)).indicator (fun _ ↦ C₁ * N) x
  refine hmain.trans (add_le_add le_rfl ?_)
  by_cases hI : x ∈ Set.Icc (1 / N) (2 / N)
  · rw [Set.indicator_of_mem hI (fun _ ↦ C₁ * N)]
    obtain ⟨hL₁, hL₂⟩ := hL_layer x hI
    have hE : E ≤ 1 := Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg
      (neg_nonpos.mpr hδ.le) hx.le)
    have hW₁A : W₁ ≤ A₁ := hWexp.2.1.trans (by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hE hA₁)
    have hthin₁ : 2 * ‖deriv L x‖ * W₁ ≤ 2 * (N * M₁) * A₁ :=
      mul_le_mul (mul_le_mul_of_nonneg_left hL₁ hTwo) hW₁A hW₁
        (mul_nonneg hTwo (mul_nonneg hNpos.le hM₁))
    have hthin₂ : ‖deriv (deriv L) x‖ * W₀ ≤ (2 * M₂ * B) * N := by
      have hcoef : 0 ≤ N ^ 2 * M₂ := mul_nonneg (sq_nonneg N) hM₂
      calc
        _ ≤ (N ^ 2 * M₂) * (B * x) := mul_le_mul hL₂ hWlin hW₀ hcoef
        _ ≤ (N ^ 2 * M₂) * (B * (2 / N)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hI.2 hB) hcoef
        _ = _ := by field_simp [ne_of_gt hNpos] <;> ring
    calc
      layer ≤ 2 * (N * M₁) * A₁ + (2 * M₂ * B) * N := add_le_add hthin₁ hthin₂
      _ = C₁ * N := by dsimp only [C₁]; ring
  · rw [Set.indicator_of_notMem hI (fun _ ↦ C₁ * N)]
    obtain ⟨hL₁, hL₂⟩ := hL_off x hI
    simp only [layer, hL₁, hL₂, norm_zero, mul_zero, zero_mul, add_zero, le_refl]

end Masullo
```

## Integration handoff and static evidence

- Zeta parameters, test support, and integrability are not premises of this algebraic estimate. The conclusion reduces by the three `let`s to the caller's pointwise predicate with exactly `deriv (deriv f)`, the closed `Set.Icc`, and indicator value `C₁ * N`. Pass `hδ` unchanged and `hNpos : 0 < N` (from `hN`) to the caller's integration lemma. Continuity and compact support of `f` and `f''` are separate inputs to the companion integral estimate; this lemma neither constructs admissible smooth tests nor proves anything about integration or dominated convergence.
- Static API sources: Mathlib `fc4f59e577feb1a4956671bc04ac18aaaf8cd842` (the accepted `lake-manifest.json` pin agrees with the local dependency checkout). `Analysis/Calculus/ContDiff/Defs.lean` gives `ContDiff.differentiable` from nonzero regularity; `Analysis/Calculus/ContDiff/Deriv.lean` gives `ContDiff.differentiable_deriv_two` for both real and complex codomains over `ℝ`; `Analysis/Calculus/ContDiff/Operations.lean` gives `ContDiff.mul`. `Analysis/Calculus/Deriv/{Mul,Add,Basic}.lean` gives the derivative rules and `.deriv`; the order of terms differs between `.mul` and `.smul` and is kept explicit in each helper. `Analysis/Normed/MulAction.lean` gives `norm_smul`; `Algebra/Notation/Indicator.lean` supplies the membership rewrites. The pointwise proof uses only nonnegative multipliers for inequality transport. It cancels a single `N` only in the lower second-derivative bound, using `0 < N`.
- Static evidence above covers the Lean block (SHA-256 `f05398bfdcbffd91c835b44068b2edeab48c4a2aab358e481334c372817b530e`, excluding fences). A separate read-only Yah review of a predecessor recovered source evidence for the derivative and indicator APIs but timed out without a completed review. The final independent pass belongs to the caller.
- No invocation of Lean, `lake build`, or proof worker. In particular, elaboration of pointwise Pi operations versus lambda forms in the derivative helpers, `let` introduction and unfolding, scalar-instance inference for `smul`, and the tactic proofs (`ring`, `field_simp`, `abel`, and simplification) remain to be checked. Concrete `smoothTransition` chain-rule bounds and the exponential/weighted mean-value instantiation are follow-ups, not new assumptions on the manuscript. The project checker should build and audit the staged declaration on the designated worker when permitted.
