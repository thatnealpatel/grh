module

public import Lemmas.CutoffProfiles
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# From zero-mass test annihilation to a resolvent identity

This project lemma uses the test domain at Masullo's (13.3.1.2), p. 522 of
the pinned edition. The full-versus-capped distribution comparison is an
input, not a consequence of the cutoff construction.
-/

open Filter MeasureTheory Set
open scoped ContDiff Topology

namespace Masullo

private theorem exists_mass_one_positive_test :
    ∃ h : ℝ → ℂ, ContDiff ℝ ∞ h ∧ HasCompactSupport h ∧ tsupport h ⊆ Ioi (0 : ℝ) ∧
      (∫ x in Ioi (0 : ℝ), h x) = 1 := by
  let b : ContDiffBump (2 : ℝ) := ⟨1 / 2, 1, by norm_num, by norm_num⟩
  let h : ℝ → ℂ := fun x ↦ b.normed volume x
  have hs : tsupport h ⊆ tsupport (b.normed volume) :=
    tsupport_comp_subset Complex.ofReal_zero (b.normed volume)
  have ht : tsupport h ⊆ Ioi (0 : ℝ) := by
    rw [b.tsupport_normed_eq] at hs
    intro x hx
    have hx' := hs hx
    rw [Metric.mem_closedBall, Real.dist_eq, abs_le] at hx'
    change -(1 : ℝ) ≤ x - 2 ∧ x - 2 ≤ 1 at hx'
    exact (zero_lt_one' ℝ).trans_le (by linarith [hx'.1])
  refine ⟨h, Complex.ofRealCLM.contDiff.comp (b.contDiff_normed (μ := volume)),
    b.hasCompactSupport_normed.comp_left Complex.ofReal_zero, ht, ?_⟩
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx ↦
    Function.notMem_support.mp (fun hm ↦ hx (ht (subset_tsupport h hm))))]
  change (∫ x : ℝ, (b.normed volume x : ℂ)) = 1
  exact (integral_ofReal (μ := volume) (𝕜 := ℂ) (f := b.normed volume)).trans (by
    rw [b.integral_normed, RCLike.ofReal_one])

private theorem positiveLaplaceTest_sub_mul (w m : ℂ) {f h : ℝ → ℂ}
    (hf : Continuous f) (hcf : HasCompactSupport f)
    (hh : Continuous h) (hch : HasCompactSupport h) :
    positiveLaplaceTest w (fun x ↦ f x - m * h x) =
      positiveLaplaceTest w f - m * positiveLaplaceTest w h := by
  let e : ℝ → ℂ := fun x ↦ Complex.exp (w * (x : ℂ))
  have he : Continuous e := by dsimp [e]; fun_prop
  have hi {k : ℝ → ℂ} (hk : Continuous k) (hck : HasCompactSupport k) :
      Integrable (e * k) (volume.restrict (Ioi (0 : ℝ))) :=
    ((he.mul hk).integrable_of_hasCompactSupport hck.mul_left).integrableOn
  change (∫ x in Ioi (0 : ℝ), e x * (f x - m * h x)) = _
  simp_rw [mul_sub, mul_left_comm (e _) m]
  exact (integral_sub (hi hf hcf) ((hi hh hch).const_mul m)).trans (by
    rw [integral_const_mul]
    rfl)

private theorem norm_weighted_transform_le {w d : ℂ} {a C : ℝ} {f : ℝ → ℂ}
    (hw : w.re ≤ a) (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    (ht : tsupport f ⊆ Ioi (0 : ℝ))
    (hC : (∫ x in Ioi (0 : ℝ), Real.exp (a * x) * ‖f x‖) +
      (∫ x in Ioi (0 : ℝ), Real.exp (a * x) * ‖deriv (deriv f) x‖) ≤ C) :
    ‖d * positiveLaplaceTest w f‖ ≤ C * (‖d‖ / (1 + ‖w‖ ^ 2)) := by
  have hpos : 0 < 1 + ‖w‖ ^ 2 := by positivity
  have h := (norm_positiveLaplaceTest_mul_weight_le w a hw hf hc ht).trans hC
  rw [norm_mul]
  calc
    ‖d‖ * ‖positiveLaplaceTest w f‖ ≤ ‖d‖ * (C / (1 + ‖w‖ ^ 2)) :=
      mul_le_mul_of_nonneg_left ((le_div_iff₀ hpos).2 (by simpa only [mul_comm] using h))
        (norm_nonneg _)
    _ = C * (‖d‖ / (1 + ‖w‖ ^ 2)) := by simp only [div_eq_mul_inv, mul_left_comm]

/-- If the difference distribution annihilates all smooth positive-log tests of mass
zero, the subtracted reciprocal series is absolutely summable in the right half-plane
and equals the stated mass term. Its coefficient is independent of `z`. -/
public theorem hasSum_subtractedReciprocals_of_annihilation {ι : Type*} {w d : ι → ℂ}
    {a z₀ : ℝ} (ha : 0 ≤ a) (hwa : ∀ i, (w i).re ≤ a) (hz₀ : a < z₀)
    (hs : Summable (fun i ↦ ‖d i‖ / (1 + ‖w i‖ ^ 2)))
    (hann : ∀ f : ℝ → ℂ, ContDiff ℝ ∞ f → HasCompactSupport f → tsupport f ⊆ Ioi (0 : ℝ) →
      (∫ x in Ioi (0 : ℝ), f x) = 0 → (∑' i, d i * positiveLaplaceTest (w i) f) = 0) :
    ∃ c : ℂ, ∀ z : ℂ, a < z.re →
      Summable (fun i ↦ ‖d i * ((z - w i)⁻¹ - ((z₀ : ℂ) - w i)⁻¹)‖) ∧
      HasSum (fun i ↦ d i * ((z - w i)⁻¹ - ((z₀ : ℂ) - w i)⁻¹))
        ((z⁻¹ - (z₀ : ℂ)⁻¹) * c) := by
  obtain ⟨h, hh, hch, hth, hmass⟩ := exists_mass_one_positive_test
  let H := fun i ↦ d i * positiveLaplaceTest (w i) h
  have hH : Summable H := by
    let C := (∫ x in Ioi (0 : ℝ), Real.exp (a * x) * ‖h x‖) +
      (∫ x in Ioi (0 : ℝ), Real.exp (a * x) * ‖deriv (deriv h) x‖)
    exact (hs.mul_left C).of_norm_bounded
      (fun i ↦ norm_weighted_transform_le (hwa i) hh hch hth le_rfl)
  refine ⟨∑' i, H i, fun z hz ↦ ?_⟩
  obtain ⟨C, hC⟩ := cutoffTest_uniform hz hz₀
  let f (n : ℕ) := cutoffTest z z₀ ((n : ℝ) + 2)
  let m (n : ℕ) := ∫ x in Ioi (0 : ℝ), f n x
  let F (n : ℕ) (i : ι) := d i * positiveLaplaceTest (w i) (f n)
  let G (i : ι) := d i * ((z - w i)⁻¹ - ((z₀ : ℂ) - w i)⁻¹)
  let B (i : ι) := C * (‖d i‖ / (1 + ‖w i‖ ^ 2))
  have hB : Summable B := hs.mul_left C
  have hf (n : ℕ) := hC ((n : ℝ) + 2) (le_add_of_nonneg_left (Nat.cast_nonneg n))
  have hbound (n : ℕ) (i : ι) : ‖F n i‖ ≤ B i :=
    norm_weighted_transform_le (hwa i) (hf n).1 (hf n).2.1 (hf n).2.2.1 (hf n).2.2.2
  have hpt (i : ι) : Tendsto (fun n ↦ F n i) atTop (𝓝 (G i)) :=
    tendsto_const_nhds.mul (tendsto_positiveLaplaceTest_cutoffTest ((hwa i).trans_lt hz)
      ((hwa i).trans_lt hz₀))
  have hsum : Tendsto (fun n ↦ ∑' i, F n i) atTop (𝓝 (∑' i, G i)) :=
    tendsto_tsum_of_dominated_convergence hB hpt (Eventually.of_forall hbound)
  have habs : Summable (fun i ↦ ‖G i‖) := hB.of_nonneg_of_le (fun _ ↦ norm_nonneg _)
    (fun i ↦ le_of_tendsto ((hpt i).norm) (Eventually.of_forall (fun n ↦ hbound n i)))
  -- Correct the test's mass before invoking annihilation.
  have hcorrect (n : ℕ) : (∑' i, F n i) = m n * ∑' i, H i := by
    let g : ℝ → ℂ := fun x ↦ f n x - m n * h x
    have hsmooth : ContDiff ℝ ∞ g := (hf n).1.sub (contDiff_const.mul hh)
    have hcompact : HasCompactSupport g := (hf n).2.1.sub hch.mul_left
    have hsupport : tsupport g ⊆ Ioi (0 : ℝ) :=
      (tsupport_sub (f n) (fun x ↦ m n * h x)).trans
        (union_subset (hf n).2.2.1 (tsupport_mul_subset_right.trans hth))
    have hmass_g : (∫ x in Ioi (0 : ℝ), g x) = 0 := by
      have he := positiveLaplaceTest_sub_mul 0 (m n) (hf n).1.continuous (hf n).2.1
        hh.continuous hch
      have he' : (∫ x in Ioi (0 : ℝ), g x) = m n - m n * (∫ x in Ioi (0 : ℝ), h x) := by
        simpa only [positiveLaplaceTest, zero_mul, Complex.exp_zero, one_mul] using he
      rw [he', hmass, mul_one, sub_self]
    have hzero := hann g hsmooth hcompact hsupport hmass_g
    have hterm (i : ι) : d i * positiveLaplaceTest (w i) g = F n i - m n * H i := by
      rw [show g = _ from rfl, positiveLaplaceTest_sub_mul _ _ (hf n).1.continuous
        (hf n).2.1 hh.continuous hch]
      simp only [F, H, f, mul_sub, mul_left_comm (d i) (m n)]
    have hF : Summable (F n) := hB.of_norm_bounded (hbound n)
    rw [tsum_congr hterm, hF.tsum_sub (hH.mul_left _), hH.tsum_mul_left] at hzero
    exact sub_eq_zero.mp hzero
  have hm : Tendsto m atTop (𝓝 (z⁻¹ - (z₀ : ℂ)⁻¹)) :=
    tendsto_cutoffTest_mass (ha.trans_lt hz) (ha.trans_lt hz₀)
  have hsum' := (hm.mul_const (∑' i, H i)).congr (fun n ↦ (hcorrect n).symm)
  exact ⟨habs, (tendsto_nhds_unique hsum hsum') ▸ habs.of_norm.hasSum⟩

end Masullo
