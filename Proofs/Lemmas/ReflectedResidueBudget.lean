module

public import Lemmas.ZetaZeroOrders
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Lemmas.RationalCompletedZetaZeros
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Finite reflected residue budget

Source: `4ad642e26a88:.godel/conjectures/closed/zeta-reflected-residue-harmonic-margin.md`,
“Write K₀” and the subsequent harmonic budget, using (1)–(2) of
`e84c4f374513:.godel/bob/endpoint-zero-packets.md` and “Spend the height term once” of
`2f8680b4990a:.godel/alice/single-endpoint-harmonics.md`.

The finite comparison uses actual absolute residue and positive Poisson weights.
The half-log mass bound is a separate input. The harmonic budget assumes the
failure lower bound, the truncated angular envelope, and the per-mode estimates.
No contour, strip, or Hadamard estimate is established here.

Scope baseline: `011d4c8fb1c19cb972449ff1197f9ee30d20d6ff`.
Owning check session: `01a209f7-85a2-71df-a0cc-7987e51e67d1`.
-/

open scoped BigOperators ComplexConjugate

namespace ReflectedResidueBudget

/-- The absolute weight of the residue at `ρ` and frequency `t`. -/
@[expose] public noncomputable def residueWeight (X t : ℝ) (ρ : ℂ) : ℝ :=
  X ^ (ρ.re - 1) / (ρ.re ^ 2 + (ρ.im - t) ^ 2)

/-- The real Poisson summand at `σ + it`, with `σ = 1 + 1 / log X`. -/
@[expose] public noncomputable def poissonWeight (X t : ℝ) (ρ : ℂ) : ℝ :=
  let d := 1 + 1 / Real.log X - ρ.re
  d / (d ^ 2 + (ρ.im - t) ^ 2)

/-- The window parameter in the denominator comparison. -/
@[expose] public noncomputable def windowError (X c : ℝ) : ℝ := 2 * (1 + c) / Real.log X

/-- Reflection across the critical line; the ordinate does not change. -/
@[expose] public def reflect (ρ : ℂ) : ℂ := 1 - conj ρ

@[simp] public theorem reflect_re (ρ : ℂ) : (reflect ρ).re = 1 - ρ.re := by simp [reflect]

@[simp] public theorem reflect_im (ρ : ℂ) : (reflect ρ).im = ρ.im := by simp [reflect]

/-- Identify the real weight with the norm of the complex quantity in (1). -/
public theorem norm_residue_eq {X : ℝ} (hX : 0 < X) (t : ℝ) (ρ : ℂ) :
    ‖(X : ℂ) ^ (ρ - (t : ℂ) * Complex.I - 1) / (ρ - (t : ℂ) * Complex.I) ^ 2‖ =
      residueWeight X t ρ := by
  rw [norm_div, Complex.norm_cpow_eq_rpow_re_of_pos hX, norm_pow, Complex.sq_norm]
  simp only [residueWeight, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im, mul_zero, sub_zero, Complex.one_re, mul_one, add_zero, pow_two]

private theorem residue_kernel_le {δ β : ℝ} (hδ : 0 < δ) (hδ₁ : δ ≤ 1)
    (hβ : δ / 2 ≤ β) (u : ℝ) :
    1 / (β ^ 2 + u ^ 2) ≤ 1 / (δ ^ 2 * ((1 / 4 : ℝ) + u ^ 2)) := by
  have hβs := pow_le_pow_left₀ (show 0 ≤ δ / 2 by positivity) hβ 2
  have hδs := pow_le_pow_left₀ hδ.le hδ₁ 2
  have hu := mul_le_mul_of_nonneg_right hδs (sq_nonneg u)
  apply div_le_div_of_nonneg_left zero_le_one (by positivity)
  nlinarith only [hβs, hu]

private theorem le_poisson_kernel {δ d : ℝ} (hδ : 0 < δ)
    (hd : δ / 2 ≤ d) (hprod : 2 * δ * d ≤ 1) (u : ℝ) :
    (δ / 2) / ((1 / 4 : ℝ) + u ^ 2) ≤ d / (d ^ 2 + u ^ 2) := by
  have hd₀ : 0 < d := (show 0 < δ / 2 by positivity).trans_le hd
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  have h1 := mul_le_mul_of_nonneg_right hprod hd₀.le
  have h2 := mul_le_mul_of_nonneg_right hd (sq_nonneg u)
  nlinarith only [h1, h2]

private theorem numerator_add_reflect {X : ℝ} (hX : 0 < X) (β : ℝ) :
    X ^ (β - 1) + X ^ ((1 - β) - 1) =
      2 * Real.cosh ((β - 1 / 2) * Real.log X) / Real.sqrt X := by
  rw [Real.cosh_eq, Real.sqrt_eq_rpow, Real.rpow_def_of_pos hX, Real.rpow_def_of_pos hX,
    Real.rpow_def_of_pos hX]
  calc
    _ = (Real.exp ((β - 1 / 2) * Real.log X) + Real.exp (-((β - 1 / 2) * Real.log X))) /
        Real.exp (Real.log X * (1 / 2)) := by
      rw [add_div, ← Real.exp_sub, ← Real.exp_sub]
      congr 1 <;> congr 1 <;> ring
    _ = _ := by ring

private theorem residue_add_reflect_le {X c t : ℝ} (hX : 1 < X) (hc : 0 ≤ c)
    (he : windowError X c < 1) (ρ : ℂ) (hρ : |ρ.re - 1 / 2| ≤ c / Real.log X) :
    residueWeight X t ρ + residueWeight X t (reflect ρ) ≤
      2 * (2 * Real.cosh c / (1 - windowError X c) ^ 3 / Real.sqrt X) * poissonWeight X t ρ := by
  let D := Real.log X
  let e := windowError X c
  let δ := 1 - e
  let d := 1 + 1 / D - ρ.re
  let u := ρ.im - t
  have hD : 0 < D := Real.log_pos hX
  have hX₀ : 0 < X := zero_lt_one.trans hX
  have he₀ : 0 ≤ e := div_nonneg (by linarith) hD.le
  have hδ : 0 < δ := sub_pos.mpr he
  have hδ₁ : δ ≤ 1 := sub_le_self _ he₀
  have heq : e / 2 = 1 / D + c / D := by
    dsimp [e, windowError, D]
    ring
  have hβ : δ / 2 ≤ ρ.re := by
    dsimp [δ]; linarith [(abs_le.mp hρ).1, heq, (div_pos one_pos hD)]
  have hrβ : δ / 2 ≤ 1 - ρ.re := by
    dsimp [δ]; linarith [(abs_le.mp hρ).2, heq, (div_pos one_pos hD)]
  have hdlo : δ / 2 ≤ d := by
    dsimp [δ, d]; linarith [(abs_le.mp hρ).2, heq, (div_pos one_pos hD)]
  have hdhi : d ≤ (1 + e) / 2 := by
    dsimp [d]; linarith [(abs_le.mp hρ).1, heq]
  have hdprod : 2 * δ * d ≤ 1 := by
    have hmul := mul_le_mul_of_nonneg_left hdhi (show 0 ≤ 2 * δ by positivity)
    dsimp [δ] at hmul ⊢
    nlinarith only [hmul, sq_nonneg e]
  have hcosh : Real.cosh ((ρ.re - 1 / 2) * D) ≤ Real.cosh c := by
    apply Real.cosh_le_cosh.mpr
    rw [abs_mul, abs_of_pos hD, abs_of_nonneg hc]
    exact (le_div_iff₀ hD).mp hρ
  have hK : 0 < (1 / 4 : ℝ) + u ^ 2 := by positivity
  have hs : 0 < Real.sqrt X := Real.sqrt_pos_of_pos hX₀
  have hcsh : 0 < Real.cosh c := zero_lt_one.trans_le (Real.one_le_cosh c)
  have hpo := le_poisson_kernel hδ hdlo hdprod u
  simp only [residueWeight, poissonWeight, reflect_re, reflect_im]
  change X ^ (ρ.re - 1) / (ρ.re ^ 2 + u ^ 2) + X ^ (1 - ρ.re - 1) / ((1 - ρ.re) ^ 2 + u ^ 2) ≤
    2 * (2 * Real.cosh c / δ ^ 3 / Real.sqrt X) * (d / (d ^ 2 + u ^ 2))
  calc
    _ ≤ (X ^ (ρ.re - 1) + X ^ (1 - ρ.re - 1)) * (1 / (δ ^ 2 * ((1 / 4 : ℝ) + u ^ 2))) := by
      rw [add_mul]
      have hn₁ : 0 ≤ X ^ (ρ.re - 1) := by positivity
      have hn₂ : 0 ≤ X ^ (1 - ρ.re - 1) := by positivity
      exact add_le_add
        (by
          simpa only [div_eq_mul_inv, one_mul] using
            mul_le_mul_of_nonneg_left (residue_kernel_le hδ hδ₁ hβ u) hn₁)
        (by
          simpa only [div_eq_mul_inv, one_mul] using
            mul_le_mul_of_nonneg_left (residue_kernel_le hδ hδ₁ hrβ u) hn₂)
    _ ≤ (2 * Real.cosh c / Real.sqrt X) * (1 / (δ ^ 2 * ((1 / 4 : ℝ) + u ^ 2))) := by
      rw [numerator_add_reflect hX₀]
      gcongr
    _ = 2 * (2 * Real.cosh c / δ ^ 3 / Real.sqrt X) * ((δ / 2) / ((1 / 4 : ℝ) + u ^ 2)) := by
      field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left hpo (by positivity)

/-- The finite comparison, with one entry per location and natural multiplicities.
The reindexing sums the reflected contribution at the **same** ordinate. An
on-line location is a fixed point: averaging gives its own weight, not twice it. -/
public theorem sum_residueWeight_le {ι : Type*} (S : Finset ι) (z : ι → ℂ) (m : ι → ℕ)
    (r : ι → ι) (hr : Function.Involutive r) (hS : ∀ i ∈ S, r i ∈ S)
    (hz : ∀ i ∈ S, z (r i) = reflect (z i)) (hm : ∀ i ∈ S, m (r i) = m i)
    {X c t : ℝ} (hX : 1 < X) (hc : 0 ≤ c) (he : windowError X c < 1)
    (hnear : ∀ i ∈ S, |(z i).re - 1 / 2| ≤ c / Real.log X) :
    ∑ i ∈ S, (m i : ℝ) * residueWeight X t (z i) ≤
      (2 * Real.cosh c / (1 - windowError X c) ^ 3 / Real.sqrt X) *
        ∑ i ∈ S, (m i : ℝ) * poissonWeight X t (z i) := by
  have hsum : ∑ i ∈ S, (m i : ℝ) * residueWeight X t (reflect (z i)) =
      ∑ i ∈ S, (m i : ℝ) * residueWeight X t (z i) := by
    refine Finset.sum_nbij r hS hr.injective.injOn ?_ ?_
    · intro i hi
      exact ⟨r i, hS i hi, hr i⟩
    · intro i hi
      rw [hz i hi, hm i hi]
  have hle := Finset.sum_le_sum (s := S) fun i hi ↦ mul_le_mul_of_nonneg_left
    (residue_add_reflect_le (t := t) hX hc he (z i) (hnear i hi)) (Nat.cast_nonneg (m i) : (0 : ℝ) ≤ m i)
  simp only [mul_add, Finset.sum_add_distrib, hsum] at hle
  rw [show (∑ i ∈ S, (m i : ℝ) *
      (2 * (2 * Real.cosh c / (1 - windowError X c) ^ 3 / Real.sqrt X) * poissonWeight X t (z i))) =
      (2 * (2 * Real.cosh c / (1 - windowError X c) ^ 3 / Real.sqrt X)) *
        ∑ i ∈ S, (m i : ℝ) * poissonWeight X t (z i) by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ ↦ by ring] at hle
  linarith only [hle]

open Masullo

private def reflectZetaZero (ρ : criticalStripZetaZeros) : criticalStripZetaZeros :=
  ⟨reflect (ρ : ℂ), by
    obtain ⟨_, hpos, hlt⟩ := mem_criticalStripZetaZeros.mp ρ.property
    have hne₀ (z : ℂ) (hz : 0 < z.re) : z ≠ 0 := fun h ↦ by simp [h] at hz
    have hne₁ (z : ℂ) (hz : z.re < 1) : z ≠ 1 := fun h ↦ by simp [h] at hz
    rw [← completedZeta_eq_zero_iff_mem_criticalStripZetaZeros
      (hne₀ _ (by simpa using sub_pos.mpr hlt)) (hne₁ _ (by simpa using hpos)),
      reflect, completedRiemannZeta_one_sub, completedRiemannZeta_conj,
      (completedZeta_eq_zero_iff_mem_criticalStripZetaZeros (hne₀ _ hpos) (hne₁ _ hlt)).mpr ρ.property,
      map_zero]⟩

private theorem reflectZetaZero_involutive : Function.Involutive reflectZetaZero := fun ρ ↦ by
  apply Subtype.ext
  exact Complex.ext (by change (reflect (reflect (ρ : ℂ))).re = _; simp) (by
    change (reflect (reflect (ρ : ℂ))).im = _; simp)

private theorem zetaOrder_conj (ρ : criticalStripZetaZeros) :
    analyticOrderAt riemannZeta (conj (ρ : ℂ)) = (zetaZeroOrder ρ : ℕ∞) := by
  have hζ {z : ℂ} (hz : z.re < 1) : AnalyticAt ℂ riemannZeta z :=
    (differentiableOn_riemannZeta.analyticOnNhd isOpen_compl_singleton) _ fun h ↦ by
      have h' : z = 1 := Set.mem_singleton_iff.mp h
      simp [h'] at hz
  have hderiv (n : ℕ) : iteratedDeriv n riemannZeta = conj ∘ iteratedDeriv n riemannZeta ∘ conj := by
    induction n with
    | zero => ext z; simp [riemannZeta_conj]
    | succ n ih => simpa only [iteratedDeriv_succ, deriv_conj_conj] using congrArg deriv ih
  have he (n : ℕ) : iteratedDeriv n riemannZeta (conj (ρ : ℂ)) =
      conj (iteratedDeriv n riemannZeta (ρ : ℂ)) := by
    simpa [Function.comp_def] using congrFun (hderiv n) (conj (ρ : ℂ))
  have hlt := (mem_criticalStripZetaZeros.mp ρ.property).2.2
  have hρ := (analyticOrderAt_eq_nat_iff_iteratedDeriv_eq_zero (hζ hlt)).mp
    (zetaZeroOrder_cast_eq ρ).symm
  exact (analyticOrderAt_eq_nat_iff_iteratedDeriv_eq_zero (hζ (by simpa using hlt))).mpr
    ⟨fun k hk ↦ by simp [he, hρ.1 k hk], by simpa [he] using hρ.2⟩

private theorem reflectZetaZero_order (ρ : criticalStripZetaZeros) :
    zetaZeroOrder (reflectZetaZero ρ) = zetaZeroOrder ρ := by
  obtain ⟨_, hpos, hlt⟩ := mem_criticalStripZetaZeros.mp ρ.property
  have hsymm : entireZeta ∘ (fun z : ℂ ↦ 1 - z) = entireZeta := by
    funext z
    simp only [Function.comp_apply, entireZeta, completedRiemannZeta₀_one_sub]
    ring
  have hcomp := analyticOrderAt_comp_of_deriv_ne_zero (f := entireZeta) (z₀ := conj (ρ : ℂ))
    (g := fun z : ℂ ↦ 1 - z) (analyticAt_const.sub analyticAt_id) (by simp)
  rw [hsymm] at hcomp
  apply ENat.natCast_inj.mp
  rw [zetaZeroOrder_cast_eq, ← analyticOrderAt_entireZeta_eq (s := (reflectZetaZero ρ : ℂ))
    (by change 0 < (reflect (ρ : ℂ)).re; simpa using sub_pos.mpr hlt)
    (by change (reflect (ρ : ℂ)).re < 1; simpa using hpos)]
  exact hcomp.symm.trans ((analyticOrderAt_entireZeta_eq (by simpa using hpos) (by simpa using hlt)).trans
    (zetaOrder_conj ρ))

private theorem nearLineSet_finite (X c t : ℝ) :
    {ρ : criticalStripZetaZeros | |(ρ : ℂ).im - t| ≤ X ^ (3 / 8 : ℝ) * Real.log X ∧
      |(ρ : ℂ).re - 1 / 2| ≤ c / Real.log X}.Finite := by
  let H := X ^ (3 / 8 : ℝ) * Real.log X
  refine (criticalStripZetaZeros_boundedIm_finite (t - H - 1) (t + H + 1)).subset ?_
  intro ρ hρ
  have h : |(ρ : ℂ).im - t| ≤ H := hρ.1
  exact ⟨by linarith [(abs_le.mp h).1], by linarith [(abs_le.mp h).2]⟩

/-- The distinct open-strip ζ zeros in the inclusive height and near-line window. -/
public noncomputable def zetaNearLineZeros (X c t : ℝ) : Finset criticalStripZetaZeros :=
  (nearLineSet_finite X c t).toFinset

public theorem mem_zetaNearLineZeros {X c t : ℝ} {ρ : criticalStripZetaZeros} :
    ρ ∈ zetaNearLineZeros X c t ↔
      |(ρ : ℂ).im - t| ≤ X ^ (3 / 8 : ℝ) * Real.log X ∧
      |(ρ : ℂ).re - 1 / 2| ≤ c / Real.log X :=
  Set.Finite.mem_toFinset _

/-- Absolute residue mass in the window, with actual zeta orders. -/
@[expose] public noncomputable def zetaNearLineResidueMass (X c t : ℝ) : ℝ :=
  ∑ ρ ∈ zetaNearLineZeros X c t, (zetaZeroOrder ρ : ℝ) * residueWeight X t ρ

/-- The finite comparison for the actual near-line ζ window. Reflection preserves
both inclusive cutoffs and the analytic order; each on-line copy counts once. -/
public theorem zeta_nearLine_residue_le {X c t : ℝ} (hX : 1 < X) (hc : 0 ≤ c)
    (he : windowError X c < 1) :
    zetaNearLineResidueMass X c t ≤
      (2 * Real.cosh c / (1 - windowError X c) ^ 3 / Real.sqrt X) *
        ∑ ρ ∈ zetaNearLineZeros X c t, (zetaZeroOrder ρ : ℝ) * poissonWeight X t ρ := by
  refine sum_residueWeight_le _ Subtype.val zetaZeroOrder reflectZetaZero reflectZetaZero_involutive
    ?_ (fun _ _ ↦ rfl) (fun ρ _ ↦ reflectZetaZero_order ρ) hX hc he
    (fun _ h ↦ (mem_zetaNearLineZeros.mp h).2)
  intro ρ hρ
  simp only [mem_zetaNearLineZeros] at hρ ⊢
  change |(reflect (ρ : ℂ)).im - t| ≤ _ ∧ |(reflect (ρ : ℂ)).re - 1 / 2| ≤ _
  simpa only [reflect_re, reflect_im, show ∀ b : ℝ, 1 - b - 1 / 2 = -(b - 1 / 2) from
    fun _ ↦ by ring, abs_neg] using hρ

/-- Poisson weights are positive for every open-strip zero, not just the ones
retained in the near-line window. -/
public theorem poissonWeight_pos {X t : ℝ} (hX : 1 < X) (ρ : criticalStripZetaZeros) :
    0 < poissonWeight X t ρ := by
  have hlt := (mem_criticalStripZetaZeros.mp ρ.property).2.2
  have hd : 0 < 1 + 1 / Real.log X - (ρ : ℂ).re := by
    linarith [div_pos one_pos (Real.log_pos hX)]
  unfold poissonWeight
  exact div_pos hd (by positivity)

/-- Apply the supplied half-log bound on the full Poisson mass. The leading
coefficient is `cosh c`, not `2 * cosh c`; the factor two survives only on the
additive error `E` in the input. -/
public theorem zeta_nearLine_residue_le_of_halfLog {X c t E : ℝ} (hX : 1 < X) (hc : 0 ≤ c)
    (he : windowError X c < 1)
    (hS : Summable (fun ρ : criticalStripZetaZeros ↦ (zetaZeroOrder ρ : ℝ) * poissonWeight X t ρ))
    (hhalf : (∑' ρ : criticalStripZetaZeros, (zetaZeroOrder ρ : ℝ) * poissonWeight X t ρ) ≤
      (1 / 2 : ℝ) * Real.log (2 + |t|) + E) :
    zetaNearLineResidueMass X c t ≤
      (Real.cosh c / (1 - windowError X c) ^ 3) * ((Real.log (2 + |t|) + 2 * E) / Real.sqrt X) := by
  have hδ : 0 < 1 - windowError X c := sub_pos.mpr he
  have hcosh : 0 < Real.cosh c := zero_lt_one.trans_le (Real.one_le_cosh c)
  have hle := (hS.sum_le_tsum (zetaNearLineZeros X c t) fun ρ _ ↦
    mul_nonneg (Nat.cast_nonneg _) (poissonWeight_pos hX ρ).le).trans hhalf
  refine (zeta_nearLine_residue_le hX hc he).trans ((mul_le_mul_of_nonneg_left hle (by positivity)).trans_eq ?_)
  ring

private theorem inv_cube_le {e : ℝ} (he₀ : 0 ≤ e) (he : e ≤ 1 / 2) :
    ((1 - e) ^ 3)⁻¹ ≤ 1 + 24 * e ∧ ((1 - e) ^ 3)⁻¹ ≤ 8 := by
  have hδ : (1 / 2 : ℝ) ≤ 1 - e := by linarith
  have hδ₀ : 0 < 1 - e := by linarith
  have hcube : (1 / 8 : ℝ) ≤ (1 - e) ^ 3 := by
    simpa only [show (1 / 2 : ℝ) ^ 3 = 1 / 8 by norm_num] using
      pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1 / 2) hδ 3
  have hdiff : 1 - (1 - e) ^ 3 ≤ 3 * e := by
    nlinarith only [mul_nonneg (sq_nonneg e) (show 0 ≤ 3 - e by linarith)]
  constructor
  · rw [← one_div, div_le_iff₀ (by positivity)]
    nlinarith only [hdiff, mul_le_mul_of_nonneg_right hcube (show 0 ≤ 24 * e by positivity)]
  · rw [← one_div, div_le_iff₀ (by positivity)]
    linarith only [hcube]

/-- On the height range of the card, the leading coefficient can be taken to
be exactly `cosh c`, with a uniform explicit additive error. For the supplied
`E = C * (1 + (log X)^2)`, the two error terms are of the stated orders
`1 / log X` and `(1 + (log X)^2) / sqrt X`. -/
public theorem zeta_nearLine_residue_le_uniform {X c t E M : ℝ}
    (hX : 1 < X) (hc : 0 ≤ c) (he : windowError X c ≤ 1 / 2) (hE : 0 ≤ E)
    (ht : Real.log (2 + |t|) ≤ M * Real.sqrt X)
    (hS : Summable (fun ρ : criticalStripZetaZeros ↦ (zetaZeroOrder ρ : ℝ) * poissonWeight X t ρ))
    (hhalf : (∑' ρ : criticalStripZetaZeros, (zetaZeroOrder ρ : ℝ) * poissonWeight X t ρ) ≤
      (1 / 2 : ℝ) * Real.log (2 + |t|) + E) :
    zetaNearLineResidueMass X c t ≤ Real.cosh c * (Real.log (2 + |t|) / Real.sqrt X) +
      Real.cosh c * (24 * windowError X c * M + 16 * E / Real.sqrt X) := by
  have he₀ : 0 ≤ windowError X c := div_nonneg (by linarith) (Real.log_pos hX).le
  have he₁ : windowError X c < 1 := he.trans_lt (by norm_num)
  have hcosh : 0 < Real.cosh c := zero_lt_one.trans_le (Real.one_le_cosh c)
  have hL : 0 ≤ Real.log (2 + |t|) := Real.log_nonneg (by linarith [abs_nonneg t])
  have hs : 0 < Real.sqrt X := Real.sqrt_pos_of_pos (zero_lt_one.trans hX)
  let e := windowError X c
  let L := Real.log (2 + |t|) / Real.sqrt X
  let F := ((1 - e) ^ 3)⁻¹
  have hLM : L ≤ M := (div_le_iff₀ hs).mpr ht
  have hL₀ : 0 ≤ L := div_nonneg hL hs.le
  have hF := inv_cube_le he₀ he
  have h₁ := mul_le_mul_of_nonneg_right hF.1 hL₀
  have h₂ := mul_le_mul_of_nonneg_left hLM (show 0 ≤ 24 * e by positivity)
  have h₃ := mul_le_mul_of_nonneg_right hF.2 (show 0 ≤ 2 * E / Real.sqrt X by positivity)
  calc
    _ ≤ (Real.cosh c / (1 - e) ^ 3) * ((Real.log (2 + |t|) + 2 * E) / Real.sqrt X) :=
      zeta_nearLine_residue_le_of_halfLog hX hc he₁ hS hhalf
    _ = Real.cosh c * (F * L + F * (2 * E / Real.sqrt X)) := by simp only [F, L, div_eq_mul_inv]; ring
    _ ≤ Real.cosh c * (L + (24 * e * M + 16 * E / Real.sqrt X)) := by
      apply mul_le_mul_of_nonneg_left _ hcosh.le
      change F * L + F * (2 * E / Real.sqrt X) ≤ L + (24 * e * M + 16 * E / Real.sqrt X)
      change F * L ≤ (1 + 24 * e) * L at h₁
      change F * (2 * E / Real.sqrt X) ≤ 8 * (2 * E / Real.sqrt X) at h₃
      simp only [div_eq_mul_inv] at h₃ ⊢
      linarith only [h₁, h₂, h₃]
    _ = _ := by rw [mul_add]

section Harmonics

open Filter
open scoped Topology

/-- The mean in the cosine envelope of `|cos|`. -/
@[expose] public noncomputable def harmonicMean : ℝ := 2 / Real.pi

/-- Coefficient of the mode `2*(j+1)`, indexed from zero. -/
@[expose] public noncomputable def cosineCoeff (j : ℕ) : ℝ :=
  4 * (-1 : ℝ) ^ j / (Real.pi * (4 * ((j : ℝ) + 1) ^ 2 - 1))

/-- The pole modulus at the mode `2*(j+1)*y`. -/
@[expose] public noncomputable def modePole (j : ℕ) (y : ℝ) : ℝ :=
  1 / (1 + (2 * ((j : ℝ) + 1) * y) ^ 2)

private theorem harmonicMean_pos : 0 < harmonicMean := div_pos (by norm_num) Real.pi_pos

private theorem abs_cosineCoeff_eq (j : ℕ) :
    |cosineCoeff j| = harmonicMean * (1 / (2 * (j : ℝ) + 1) - 1 / (2 * (j : ℝ) + 3)) := by
  have hj : 0 ≤ (j : ℝ) := Nat.cast_nonneg _
  have hd : 0 < 4 * ((j : ℝ) + 1) ^ 2 - 1 := by nlinarith
  have h₁ : 0 < 2 * (j : ℝ) + 1 := by positivity
  have h₃ : 0 < 2 * (j : ℝ) + 3 := by positivity
  rw [cosineCoeff, abs_div, abs_mul, abs_pow, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4),
    abs_neg, abs_one, one_pow, mul_one, abs_of_pos (mul_pos Real.pi_pos hd), harmonicMean]
  field_simp [Real.pi_pos.ne', hd.ne', h₁.ne', h₃.ne']
  ring

private theorem sum_abs_cosineCoeff_shift (L J : ℕ) :
    ∑ j ∈ Finset.range L, |cosineCoeff (J + j)| =
      harmonicMean * (1 / (2 * (J : ℝ) + 1) - 1 / (2 * ((J : ℝ) + L) + 1)) := by
  let f (j : ℕ) : ℝ := 1 / (2 * ((J : ℝ) + j) + 1)
  simp only [abs_cosineCoeff_eq, ← Finset.mul_sum]
  congr 1
  calc
    _ = ∑ j ∈ Finset.range L, (f j - f (j + 1)) := by
      apply Finset.sum_congr rfl
      intro j _
      simp only [f, Nat.cast_add, Nat.cast_one]
      congr 1
      congr 1
      ring
    _ = f 0 - f L := Finset.sum_range_sub' f L
    _ = _ := by simp [f]

/-- The exact retained absolute mass for `J=50`. -/
public theorem retained_mass_50 :
    ∑ j ∈ Finset.range 50, |cosineCoeff j| = 100 * harmonicMean / 101 := by
  have h := sum_abs_cosineCoeff_shift 50 0
  norm_num at h
  rw [h]
  ring

/-- The absolute tail after the first 50 modes, not a per-mode allowance. -/
public theorem tail_mass_50 : HasSum (fun j : ℕ ↦ |cosineCoeff (50 + j)|) (harmonicMean / 101) := by
  apply (hasSum_iff_tendsto_nat_of_nonneg (fun _ ↦ abs_nonneg _) _).mpr
  have htop : Tendsto (fun n : ℕ ↦ 2 * ((50 : ℝ) + n) + 1) atTop atTop :=
    tendsto_atTop_mono (fun n ↦ by linarith [Nat.cast_nonneg (α := ℝ) n]) tendsto_natCast_atTop_atTop
  have hinv : Tendsto (fun n : ℕ ↦ 1 / (2 * ((50 : ℝ) + n) + 1)) atTop (𝓝 0) := by
    have h := htop.inv_tendsto_atTop
    change Tendsto (fun n : ℕ ↦ (2 * ((50 : ℝ) + n) + 1)⁻¹) atTop (𝓝 0) at h
    simpa only [one_div] using h
  simp only [sum_abs_cosineCoeff_shift]
  have hconst : Tendsto (fun _ : ℕ ↦ (1 : ℝ) / (2 * ((50 : ℕ) : ℝ) + 1))
      atTop (𝓝 ((1 : ℝ) / (2 * ((50 : ℕ) : ℝ) + 1))) := tendsto_const_nhds
  have hlim := (hconst.sub hinv).const_mul harmonicMean
  convert hlim using 1
  norm_num [div_eq_mul_inv]

/-- At `|y|≥5` the sum of the retained weighted pole moduli is strictly
smaller than `K/101`, where `K=2/π`. -/
public theorem weighted_pole_lt {y : ℝ} (hy : 5 ≤ |y|) :
    ∑ j ∈ Finset.range 50, |cosineCoeff j| * modePole j y < harmonicMean / 101 := by
  have hp (j : ℕ) : modePole j y ≤ 1 / 101 := by
    have hj : 0 ≤ (j : ℝ) := Nat.cast_nonneg _
    have habs : 10 ≤ |2 * ((j : ℝ) + 1) * y| := by
      rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ (2 : ℝ) * ((j : ℝ) + 1))]
      have h := mul_le_mul (show (2 : ℝ) ≤ 2 * ((j : ℝ) + 1) by linarith) hy
        (by norm_num : (0 : ℝ) ≤ 5) (by positivity)
      norm_num at h
      exact h
    have hs := pow_le_pow_left₀ (show (0 : ℝ) ≤ 10 by norm_num) habs 2
    rw [sq_abs] at hs
    unfold modePole
    exact div_le_div_of_nonneg_left zero_le_one (by norm_num) (by linarith)
  calc
    _ ≤ ∑ j ∈ Finset.range 50, |cosineCoeff j| * (1 / 101) :=
      Finset.sum_le_sum fun j _ ↦ mul_le_mul_of_nonneg_left (hp j) (abs_nonneg _)
    _ = (100 * harmonicMean / 101) * (1 / 101) := by rw [← Finset.sum_mul, retained_mass_50]
    _ < _ := by linarith [harmonicMean_pos]

private theorem two_pow_le_even_factorial (n : ℕ) : 2 ^ n ≤ (2 * n).factorial := by
  cases n with
  | zero => decide
  | succ n =>
    have hn : 2 ≤ 2 * (n + 1) := by omega
    have h := Nat.factorial_mul_pow_sub_le_factorial hn
    have hp : 2 ^ (n + 1) ≤ 2 ^ (2 * (n + 1) - 2 + 1) :=
      pow_le_pow_right₀ (by decide : 1 ≤ (2 : ℕ)) (by omega)
    exact hp.trans (by simpa only [pow_succ, show (2 : ℕ).factorial = 2 by decide, mul_comm] using h)

private theorem cosh_half_le : Real.cosh (1 / 2) ≤ 8 / 7 := by
  rw [Real.cosh_eq_tsum, ← show (∑' n : ℕ, (1 / 8 : ℝ) ^ n) = 8 / 7 by
    rw [tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
    norm_num]
  refine Summable.tsum_le_tsum ?_ (Real.hasSum_cosh _).summable
    (summable_geometric_of_lt_one (by norm_num) (by norm_num))
  intro n
  have hfac : (2 : ℝ) ^ n ≤ ((2 * n).factorial : ℝ) := by
    exact_mod_cast two_pow_le_even_factorial n
  calc
    _ ≤ (1 / 2 : ℝ) ^ (2 * n) / 2 ^ n :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hfac
    _ = (1 / 8 : ℝ) ^ n := by
      rw [pow_mul, ← div_pow]
      norm_num

/-- The finite numerical margin, for every nonnegative normalized height `s`. -/
public theorem strict_margin {s : ℝ} (hs : 0 ≤ s) :
    (17 / 1000 : ℝ) < (2 / 3 - harmonicMean - 2 * harmonicMean / 101) +
      (2 / 3) * (1 - harmonicMean * Real.cosh (1 / 2)) * s := by
  have hπ : (157 / 50 : ℝ) < Real.pi := by linarith [Real.pi_gt_d20]
  have hK : harmonicMean < 100 / 157 := by
    unfold harmonicMean
    apply (div_lt_iff₀ Real.pi_pos).mpr
    linarith
  have hprod := mul_le_mul hK.le cosh_half_le
    (zero_le_one.trans (Real.one_le_cosh (1 / 2))) (by norm_num)
  have hslope : 0 ≤ (2 / 3 : ℝ) * (1 - harmonicMean * Real.cosh (1 / 2)) := by linarith
  linarith [mul_nonneg hslope hs]

/-- The conditional finite harmonic budget at `A=3/2`, `c=1/2`, `J=50`, `|y|≥5`.
`P` can be the maximum remaining per-mode cost (in the card, `C*X^(-1/8)`
times the packet maximum). The failure lower bound, truncated angular envelope
with its tail allowance, and individual mode estimates are inputs. The height
cost is spent once, on the total retained absolute mass. No assertion about
failure, primes, the contour, or the remaining residues is needed here. -/
public theorem strict_harmonic_budget {y s h P Efail Eangular Emode : ℝ} (F : ℕ → ℝ)
    (hy : 5 ≤ |y|) (hs : 0 ≤ s) (hP : 0 ≤ P) (hEmode : 0 ≤ Emode)
    (hfail : (1 + s) / (3 / 2) - Efail ≤ h)
    (henvelope : h ≤ harmonicMean + harmonicMean / 101 +
      (∑ j ∈ Finset.range 50, |cosineCoeff j| * |F j|) + Eangular)
    (hmodes : ∀ j ∈ Finset.range 50,
      |F j| ≤ modePole j y + Real.cosh (1 / 2) * s / (3 / 2) + P + Emode) :
    let E := Efail + Eangular + harmonicMean * Emode
    (2 / 3 - harmonicMean - 2 * harmonicMean / 101) +
        (2 / 3) * (1 - harmonicMean * Real.cosh (1 / 2)) * s ≤ harmonicMean * P + E ∧
      (17 / 1000 : ℝ) < harmonicMean * P + E := by
  let B := Real.cosh (1 / 2) * s / (3 / 2) + P + Emode
  have hc : 0 < Real.cosh (1 / 2) := zero_lt_one.trans_le (Real.one_le_cosh _)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hmass : ∑ j ∈ Finset.range 50, |cosineCoeff j| ≤ harmonicMean := by
    rw [retained_mass_50]
    linarith [harmonicMean_pos]
  have hsum : (∑ j ∈ Finset.range 50, |cosineCoeff j| * |F j|) ≤
      (∑ j ∈ Finset.range 50, |cosineCoeff j| * modePole j y) + harmonicMean * B := by
    calc
      _ ≤ ∑ j ∈ Finset.range 50, |cosineCoeff j| * (modePole j y + B) := by
        apply Finset.sum_le_sum
        intro j hj
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
        dsimp [B]
        linarith only [hmodes j hj]
      _ = (∑ j ∈ Finset.range 50, |cosineCoeff j| * modePole j y) +
          (∑ j ∈ Finset.range 50, |cosineCoeff j|) * B := by
        simp only [mul_add, Finset.sum_add_distrib, Finset.sum_mul]
      _ ≤ _ := add_le_add le_rfl (mul_le_mul_of_nonneg_right hmass hB)
  intro E
  have hgap : (2 / 3 - harmonicMean - 2 * harmonicMean / 101) +
      (2 / 3) * (1 - harmonicMean * Real.cosh (1 / 2)) * s ≤ harmonicMean * P + E := by
    dsimp [B] at hsum
    dsimp [E]
    linarith only [hfail, henvelope, hsum, weighted_pole_lt hy]
  exact ⟨hgap, (strict_margin hs).trans_le hgap⟩

end Harmonics

end ReflectedResidueBudget
