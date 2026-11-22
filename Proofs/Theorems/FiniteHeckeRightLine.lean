module

public import Lemmas.FiniteHeckeMajorant
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.Normed.Group.FunctionSeries

/-!
# The finite-place Hecke expansion on a right line

Masullo states the undifferentiated product convergence in Lemma 3.2.1.1,
p. 123, and uses the local geometric series in (B.4.2.7), p. 615. To justify
summation over all places and termwise integration in (B.4.2.8)–(9), we
supply a joint summable majorant on `Re s ≥ a > 1`. This is the finite-place
summation and integral step only, not an identity with the logarithmic
derivative of a global Hecke L-function.
-/

open Complex IsDedekindDomain MeasureTheory NumberField

namespace Masullo

variable {K : Type*} [Field K] [NumberField K]

/-- The positive majorant for the `m = k+1` finite-place term. -/
@[expose] public noncomputable def finiteHeckeMajorant (a : ℝ)
    (p : HeightOneSpectrum (𝓞 K) × ℕ) : ℝ :=
  Real.log (finitePlaceNorm p.1) / finitePlaceNorm p.1 ^ (a * (p.2 + 1))

/-- The unsigned term of the negative local logarithmic derivative in
(B.4.2.7), with the Euler coefficient `z` at the place (zero if omitted). -/
@[expose] public noncomputable def finiteHeckeTerm (z : HeightOneSpectrum (𝓞 K) → ℂ)
    (s : ℂ) (p : HeightOneSpectrum (𝓞 K) × ℕ) : ℂ :=
  let l := (Real.log (finitePlaceNorm p.1) : ℂ)
  l * z p.1 ^ (p.2 + 1) * exp (-((p.2 + 1 : ℕ) : ℂ) * s * l)

/-- The same summable majorant works for every coefficient family of modulus
at most one on the entire closed half-plane to the right of `a > 1`. -/
public theorem finiteHecke_right_line_majorant {a : ℝ} (ha : 1 < a) :
    Summable (finiteHeckeMajorant (K := K) a) ∧
    ∀ (z : HeightOneSpectrum (𝓞 K) → ℂ), (∀ v, ‖z v‖ ≤ 1) →
      ∀ (s : ℂ), a ≤ s.re → ∀ p, ‖finiteHeckeTerm z s p‖ ≤ finiteHeckeMajorant a p := by
  refine ⟨summable_finitePlace_log_powers ha, ?_⟩
  intro z hz s hs p
  let q := finitePlaceNorm p.1
  have hq : 1 ≤ q := (by norm_num : (1 : ℝ) ≤ 2).trans (two_le_finitePlaceNorm p.1)
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  have hl := Real.log_nonneg hq
  unfold finiteHeckeTerm finiteHeckeMajorant
  change ‖(Real.log q : ℂ) * z p.1 ^ (p.2 + 1) *
    exp (-((p.2 + 1 : ℕ) : ℂ) * s * (Real.log q : ℂ))‖ ≤
      Real.log q / q ^ (a * ((p.2 : ℝ) + 1))
  simp only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hl,
    Complex.norm_exp, mul_re, ofReal_re, ofReal_im, natCast_re, natCast_im,
    add_re, add_im, one_re, one_im, neg_re, neg_im, neg_zero,
    zero_add, zero_mul, mul_zero, sub_zero, Nat.cast_add, Nat.cast_one]
  rw [Real.rpow_def_of_pos hq0, div_eq_mul_inv, ← Real.exp_neg]
  have hzpow : ‖z p.1‖ ^ (p.2 + 1) ≤ 1 := pow_le_one₀ (norm_nonneg _) (hz p.1)
  have hzlog : Real.log q * ‖z p.1‖ ^ (p.2 + 1) ≤ Real.log q := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hzpow hl
  refine mul_le_mul hzlog (Real.exp_le_exp.mpr ?_) (Real.exp_nonneg _) hl
  calc
    -((p.2 : ℝ) + 1) * s.re * Real.log q =
        -(Real.log q * (s.re * ((p.2 : ℝ) + 1))) := by ring
    _ ≤ -(Real.log q * (a * ((p.2 : ℝ) + 1))) := by gcongr

/-- Finite-place termwise integration in (B.4.2.8)–(9) after the
parametrization `s = a + it`. The constant `i` in `ds = i dt` can be
absorbed into `W`. Both the series of L¹ norms and the integral of the
pointwise sum are controlled, with no Hecke continuation hypothesis. -/
public theorem finiteHecke_right_line_integrals {a : ℝ} (ha : 1 < a)
    {z : HeightOneSpectrum (𝓞 K) → ℂ} (hz : ∀ v, ‖z v‖ ≤ 1)
    {W : ℝ → ℂ} (hW : Integrable W) :
    let F := fun p (t : ℝ) ↦ W t * finiteHeckeTerm z ((a : ℂ) + (t : ℂ) * I) p
    (∀ p, Integrable (F p)) ∧ (Summable fun p ↦ ∫ t, ‖F p t‖) ∧
    Integrable (fun t ↦ ∑' p, F p t) ∧
    (∫ t, ∑' p, F p t) = ∑' p, ∫ t, F p t := by
  let c := finiteHeckeMajorant (K := K) a
  let u := fun p (t : ℝ) ↦ finiteHeckeTerm z ((a : ℂ) + (t : ℂ) * I) p
  let F := fun p t ↦ W t * u p t
  obtain ⟨hc, hbound⟩ := finiteHecke_right_line_majorant (K := K) ha
  have hcont (p) : Continuous (u p) := by unfold u finiteHeckeTerm; dsimp only; fun_prop
  have hu (p) (t : ℝ) : ‖u p t‖ ≤ c p := hbound z hz _ (by simp) p
  have hF (p) (t : ℝ) : ‖F p t‖ ≤ ‖W t‖ * c p :=
    (norm_mul ..).le.trans (mul_le_mul_of_nonneg_left (hu p t) (norm_nonneg _))
  -- Dominate each term in L¹ by its scalar majorant times `‖W‖`.
  have hi (p) : Integrable (F p) :=
    (hW.norm.mul_const (c p)).mono' (hW.aestronglyMeasurable.mul (hcont p).aestronglyMeasurable)
      (Filter.Eventually.of_forall (hF p))
  have hs : Summable fun p ↦ ∫ t, ‖F p t‖ := by
    refine (hc.mul_left (∫ t, ‖W t‖)).of_nonneg_of_le
      (fun p ↦ integral_nonneg fun t ↦ norm_nonneg (F p t)) (fun p ↦ ?_)
    rw [← integral_mul_const]
    exact integral_mono (hi p).norm (hW.norm.mul_const _) (hF p)
  have hpos (p : HeightOneSpectrum (𝓞 K) × ℕ) : 0 < c p := by
    have hq : 1 < finitePlaceNorm p.1 := lt_of_lt_of_le (by norm_num) (two_le_finitePlaceNorm p.1)
    exact div_pos (Real.log_pos hq) (Real.rpow_pos_of_pos (zero_lt_one.trans hq) _)
  have hsupport : Function.support c = Set.univ := Set.eq_univ_of_forall fun p ↦ (hpos p).ne'
  have : Countable (HeightOneSpectrum (𝓞 K) × ℕ) :=
    Set.countable_univ_iff.mp (hsupport ▸ hc.countable_support)
  -- The unweighted series converges uniformly; multiply its sum by `W`.
  have hsum : Integrable (fun t ↦ ∑' p, F p t) := by
    have hcu := continuous_tsum hcont hc hu
    have hnorm (t : ℝ) : ‖∑' p, u p t‖ ≤ ∑' p, c p := by
      have ht := hc.of_norm_bounded (hu · t)
      exact (norm_tsum_le_tsum_norm ht.norm).trans (ht.norm.tsum_le_tsum (hu · t) hc)
    simp_rw [F, tsum_mul_left]
    refine (hW.norm.mul_const (∑' p, c p)).mono'
      (hW.aestronglyMeasurable.mul hcu.aestronglyMeasurable) (Filter.Eventually.of_forall fun t ↦ ?_)
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hnorm t) (norm_nonneg _)
  exact ⟨hi, hs, hsum, (integral_tsum_of_summable_integral_norm hi hs).symm⟩

end Masullo
