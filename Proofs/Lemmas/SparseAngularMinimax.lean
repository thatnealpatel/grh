module

public import Lemmas.SparseShiftedGridAdvantage
public import Lemmas.SparseSmallDensity
import Lemmas.SparseMissingDivisor
import Lemmas.ConsecutiveHarmonicTransfer
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Sharp exact sparse angular minimax

Source: `fea7eb0b:.godel/alice/sharp-sparse-harmonics.md:3–46` (unchanged from
scan `9af60873` at base `85027edf`). For every budget of `N - 1` distinct
positive orders, an actual circle probability law has those complex moments
zero and absolute half-sine mean at least `C_N`. The first `N - 1` orders
force the reverse inequality for every such law, so their worst-case mean is
exactly `C_N`. Moments use Mathlib's positive-sign `fourier`; the vanishing
conditions do not depend on the sign convention. There is no frequency cap.

The small branch uses the landed damped cosine density. The large branch
places the finite mixture of grid translates on the same circle, counting
coincident atoms with multiplicity. This is the exact-zero witness used in
`b825bc58:.godel/bob/noisy-sparse-harmonics.md:3,11–16`; no near-zero mass
bound for the large branch or noisy minimax bound is asserted here.

Owning check session: `01a20ec7-4115-7a16-8368-f5947df6f1f0`.
-/

open MeasureTheory hiding average
open scoped BigOperators ENNReal

namespace Masullo.SparseAngularMinimax

open SparseSmallDensity (AngularCircle envelope envelope_coe fourier_coe)
open SparseShiftedGrid (average gridMean shiftedQueries translation)
open ConsecutiveHarmonicGrid (node)

/-- The normalized mixture on the circle, with one atom per sign assignment
and grid node, even if their circle images coincide. -/
@[expose] public noncomputable def shiftedGridLaw (n : ℕ) (K : Finset ℕ) : Measure AngularCircle :=
  (((2 ^ K.card * n : ℕ) : ℝ≥0∞)⁻¹) •
    ∑ q ∈ K.powerset ×ˢ Finset.range n,
      Measure.dirac ((node n q.2 + translation K q.1 : ℝ) : AngularCircle)

private theorem shiftedGridLaw_probability {n : ℕ} (hn : 1 ≤ n) (K : Finset ℕ) :
    IsProbabilityMeasure (shiftedGridLaw n K) := by
  have hc : 0 < 2 ^ K.card * n := Nat.mul_pos (by positivity) hn
  constructor
  rw [shiftedGridLaw, smul_apply, sum_apply, smul_eq_mul]
  simp only [measure_univ, Finset.sum_const, nsmul_one]
  rw [Finset.card_product, Finset.card_powerset, Finset.card_range]
  exact ENNReal.inv_mul_cancel (by exact_mod_cast hc.ne') (ENNReal.natCast_ne_top _)

private theorem integral_shiftedGridLaw {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (n : ℕ) (K : Finset ℕ) (f : AngularCircle → E) :
    (∫ s, f s ∂shiftedGridLaw n K) = ((2 : ℝ) ^ K.card * (n : ℝ))⁻¹ •
      ∑ P ∈ K.powerset, ∑ l ∈ Finset.range n, f ((node n l + translation K P : ℝ) : AngularCircle) := by
  rw [shiftedGridLaw, integral_smul_measure,
    integral_finsetSum_measure (fun _ _ ↦ integrable_dirac (by simp))]
  rw [ENNReal.toReal_inv, ENNReal.toReal_natCast, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat,
    Finset.sum_product]
  simp only [integral_dirac]

/-- One probability measure realizes both real-lift averages: all complex
Fourier integrals and the absolute half-sine integral. The identities hold
also for lifts that wrap around the circle. -/
public theorem shiftedGridLaw_spec {n : ℕ} (hn : 1 ≤ n) (K : Finset ℕ) :
    IsProbabilityMeasure (shiftedGridLaw n K) ∧
      (∀ j : ℕ, (∫ s, fourier (j : ℤ) s ∂shiftedGridLaw n K) =
        average n K (fun s ↦ Complex.exp (↑((j : ℝ) * s) * Complex.I))) ∧
      (∫ s, envelope s ∂shiftedGridLaw n K) = average n K (fun s ↦ |Real.sin (s / 2)|) := by
  refine ⟨shiftedGridLaw_probability hn K, fun j ↦ ?_, ?_⟩
  · rw [integral_shiftedGridLaw, average, div_div, div_eq_mul_inv, Complex.real_smul]
    simp only [fourier_coe, Int.cast_natCast, Complex.ofReal_inv, Complex.ofReal_mul,
      Complex.ofReal_pow, Complex.ofReal_ofNat, Complex.ofReal_natCast]
    exact mul_comm _ _
  · rw [integral_shiftedGridLaw, average, div_div, div_eq_mul_inv, smul_eq_mul]
    simp only [envelope_coe]
    exact mul_comm _ _

/-- Every set of at most `N - 1` positive query orders admits a circle
probability law with all queried complex moments zero and mean at least `C_N`. -/
public theorem exists_annihilating_law_mean_ge {N : ℕ} (hN : 1 ≤ N) (J : Finset ℕ)
    (hJpos : ∀ j ∈ J, 0 < j) (hJcard : J.card ≤ N - 1) :
    ∃ μ : Measure AngularCircle, IsProbabilityMeasure μ ∧
      (∀ j ∈ J, (∫ s, fourier (j : ℤ) s ∂μ) = 0) ∧
      gridMean N ≤ ∫ s, envelope s ∂μ := by
  obtain ⟨n, hn, hnN, hmiss, hroute, htop⟩ := exists_sparse_missing_divisor hN J hJpos hJcard
  by_cases hlarge : 3 * N < 4 * n
  · obtain ⟨hmodes, hmean⟩ := SparseShiftedGrid.annihilates_and_mean_ge_of_large_missing_divisor
      hn hnN hlarge J hJpos (hroute hlarge) htop
    obtain ⟨hprob, hfourier, henvelope⟩ := shiftedGridLaw_spec hn (shiftedQueries n J)
    refine ⟨shiftedGridLaw n (shiftedQueries n J), hprob, fun j hj ↦ ?_, ?_⟩
    · rw [hfourier j]
      exact hmodes j hj
    · rw [henvelope]
      exact hmean
  · obtain ⟨hprob, _, _, hmodes, _, hmean, _⟩ := SparseSmallDensity.small_density_witness
      (fun j : {j // j ∈ J} ↦ j.val) (by omega : 2 ≤ N) hn (le_of_not_gt hlarge)
      (fun j ↦ hJpos j.val j.property) (fun j h ↦ hmiss (h ▸ j.property))
    exact ⟨SparseSmallDensity.law n, hprob, fun j hj ↦ hmodes ⟨j, hj⟩, hmean⟩

/-- Vanishing at the consecutive orders `1, …, N - 1` forces the mean to
be at most `C_N`. With the sparse lower bound this gives the sharp value. -/
public theorem mean_le_of_consecutive_moments {N : ℕ} (hN : 1 ≤ N)
    (μ : Measure AngularCircle) [IsProbabilityMeasure μ]
    (hmodes : ∀ j ∈ Finset.Ico 1 N, (∫ s, fourier (j : ℤ) s ∂μ) = 0) :
    (∫ s, envelope s ∂μ) ≤ gridMean N := by
  by_cases h : N = 1
  · subst N
    have hcont : Continuous envelope := Real.continuous_sin.comp (continuous_norm.div_const 2)
    have hbound (s : AngularCircle) : ‖envelope s‖ ≤ 1 := Real.abs_sin_le_one _
    have hi := Integrable.of_bound hcont.aestronglyMeasurable 1 (ae_of_all μ hbound)
    calc
      _ ≤ ∫ _ : AngularCircle, (1 : ℝ) ∂μ :=
        integral_mono hi (integrable_const _) fun s ↦ (le_abs_self _).trans (hbound s)
      _ = gridMean 1 := by norm_num [gridMean, Real.sin_pi_div_two]
  let r (s : AngularCircle) : ℝ := ↑(AddCircle.measurableEquivIoc (2 * Real.pi) 0 s)
  have hr : Measurable r := measurable_subtype_coe.comp (AddCircle.measurableEquivIoc _ _).measurable
  have hcoe (s : AngularCircle) : (r s : AngularCircle) = s := AddCircle.coe_equivIoc (a := 0)
  have henvelope (s : AngularCircle) : |Real.sin (r s / 2)| = envelope s := by
    rw [← envelope_coe, hcoe]
  have hm (j : ℕ) (hj : j ∈ Finset.Ico 1 N) : |∫ s, Real.cos ((j : ℝ) * r s) ∂μ| ≤ 0 := by
    have hi : Integrable (fourier (T := 2 * Real.pi) (j : ℤ)) μ :=
      Integrable.of_bound (fourier (j : ℤ)).continuous.measurable.aestronglyMeasurable 1
        (ae_of_all _ fun s ↦ (Circle.norm_coe (AddCircle.toCircle ((j : ℤ) • s))).le)
    have hcos (s : AngularCircle) : Real.cos ((j : ℝ) * r s) = RCLike.re (fourier (j : ℤ) s) := by
      calc
        _ = (fourier (j : ℤ) (r s : AngularCircle)).re := by
          rw [fourier_coe, Int.cast_natCast, Complex.exp_ofReal_mul_I_re]
        _ = _ := by rw [hcoe]; rfl
    simp only [hcos, integral_re hi, hmodes j hj, map_zero, abs_zero, le_refl]
  simpa only [henvelope, mul_zero, add_zero, ConsecutiveHarmonicTransfer.majorantConstant, gridMean] using
    ConsecutiveHarmonicTransfer.integral_abs_sin_half_le_of_cosine_moments μ hr
      (by omega : 2 ≤ N) hm

end Masullo.SparseAngularMinimax
