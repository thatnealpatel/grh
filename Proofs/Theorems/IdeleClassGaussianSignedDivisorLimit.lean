module

public import Theorems.IdeleClassGaussianHorizontalCount
public import Props.CompactLogMellin
import Lemmas.AnalyticSlabSummability
import Lemmas.SignedSlabDivisorLimit
import Mathlib.Tactic.Linarith

/-! # Signed divisor limit for the Gaussian Hecke continuation

The disk count gives absolute convergence on the open slab without excluding
zeros outside it. The signed meromorphic orders remove the two artificial
orders inserted by clearing the possible poles. This supplies the divisor-side
limit associated with the finite rectangle sum in (B.3.2.3), PDF p. 606, and
the Hecke residue sum in (B.4.2.2), PDF p. 614 (provisional source
correspondence). It does not evaluate any contour or locate zeros.

Owning landing-check session: `01a2068a-1ce3-7fa3-a84c-5c3d60318202`.
-/

open Complex Filter IsDedekindDomain NumberField
open scoped ContDiff Topology

namespace Masullo

variable {K : Type*} [Field K] [NumberField K]

local notation "C" => IdeleClassGroup (𝓞 K) K
local notation "I₁" => ideleNormOne (K := K)
local notation "C₁" => ideleClassNormOne (K := K)
local notation "W" => (NumberField.Units.dirichletUnitTheorem.w₀ : InfinitePlace K)
local notation "τ" => ideleClassLogSplit (ideleClassLogSection W) (ideleClassLogNorm_section W)

variable [∀ v : InfinitePlace K, MeasurableSpace v.Completionˣ]
  [∀ v : InfinitePlace K, BorelSpace v.Completionˣ]
  [MeasurableSpace (IdeleClassGroup (𝓞 K) K)] [BorelSpace (IdeleClassGroup (𝓞 K) K)]
  [MeasurableSpace (ideleNormOne (K := K))]
  [MeasurableSpace (ideleClassNormOne (K := K))] [BorelSpace (ideleClassNormOne (K := K))]
  [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)ˣ]
  [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletionIntegers K)ˣ]
  [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)ˣ]
  [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletionIntegers K)ˣ]
  [MeasurableSpace (IdeleGroup (𝓞 K) K)] [BorelSpace (IdeleGroup (𝓞 K) K)]
  [BorelSpace (ideleNormOne (K := K))]

/-- For the continuation of the actual completed Euler product, each possible
pole contributes one clearing factor, whether or not it is a pole. For every
smooth compact log test, the absolute signed weights are summable and the
finite, strictly height-truncated sums tend to their signed sum. -/
public theorem exists_completedHeckeEulerProduct_gaussianContinuation_signed_divisor_limit
    (χ : HeckeCharacter (𝓞 K) K) (hχ : ∀ a : C, ‖χ a‖ = 1)
    (v : InfinitePlace K) (r : ClassGroup (𝓞 K) → I₁)
    (hr : ∀ p, ideleIdealClassNormOne (r p) = p) :
    ∃ (lam : ℝ) (L H : ℂ → ℂ),
      let z₀ := -((lam : ℂ) * I)
      let z₁ := 1 + z₀
      (∀ x : ℝ, χ (τ (Multiplicative.ofAdd x, 1)) = exp (((lam * x : ℝ) : ℂ) * I)) ∧
      Meromorphic L ∧ (∀ s, 1 < s.re → L s = completedHeckeEulerProduct χ hχ s) ∧
      Differentiable ℂ H ∧ (∀ s, s ≠ z₁ → s ≠ z₀ → H s = (s - z₁) * (s - z₀) * L s) ∧
      (∀ z, meromorphicOrderAt L z =
        (((analyticOrderNatAt H z : ℤ) - (if z = z₀ then 1 else 0) -
          (if z = z₁ then 1 else 0) : ℤ) : WithTop ℤ)) ∧
      ∀ (g : ℝ → ℂ), ContDiff ℝ ∞ g → HasCompactSupport g →
        let S := {z : ℂ // -1 < z.re ∧ z.re < 2}
        let ord := fun z : S ↦ (meromorphicOrderAt L z.val).untop₀
        let weight := fun z : S ↦ (ord z : ℂ) * compactLogMellin g z.val
        Summable (fun z ↦ ‖weight z‖) ∧
          ∃ F : ℝ → Finset S,
            (∀ t z, z ∈ F t ↔ ord z ≠ 0 ∧ |z.val.im| < t) ∧
            ∀ t : ℕ → ℝ, Tendsto t atTop atTop →
              Tendsto (fun n ↦ ∑ z ∈ F (t n), weight z) atTop (𝓝 (∑' z, weight z)) := by
  obtain ⟨lam, L, H, hphase, hL, _, _, hEuler, hH, hclear, _, _, C₀, _, hcount, _⟩ :=
    exists_completedHeckeEulerProduct_gaussianContinuation_horizontal χ hχ v r hr
  let z₀ : ℂ := -((lam : ℂ) * I)
  let z₁ : ℂ := 1 + z₀
  have hd : z₀ ≠ z₁ := by
    intro heq
    have h : (0 : ℂ) + z₀ = 1 + z₀ := by simpa only [zero_add] using heq
    exact zero_ne_one (add_right_cancel h)
  have h₂ : H 2 ≠ 0 := by simpa using (hcount 0).1
  refine ⟨lam, L, H, hphase, hL, hEuler, hH, hclear,
    meromorphicOrderAt_eq_sub_clearingOrders hH h₂ hd hclear, ?_⟩
  intro g hg hc
  obtain ⟨B, hB, hdecay⟩ := compactLogMellin_vertical_decay hg hc 2 3
  have hΦ (z : ℂ) (hl : -1 ≤ z.re) (hr : z.re ≤ 2) :
      ‖compactLogMellin g z‖ ≤ B / (1 + |z.im|)^3 := by
    simpa only [Complex.re_add_im] using hdecay z.re z.im (abs_le.mpr ⟨by linarith, hr⟩)
  have hsum := summable_norm_analyticOrder_mul_of_disk_count_on_slab hH h₂ hB.le
    (fun t ↦ (hcount t).2) hΦ
  obtain ⟨F, hF, hsumL, hlimit⟩ := signedSlabDivisor_limit hH h₂ hd hclear hsum
  exact ⟨hsumL, F, hF, hlimit⟩

end Masullo
