module

public import Lemmas.AnnulusKernel
public import Lemmas.CircleSynthesis
public import Lemmas.RealLogLevel
/-! # Hilbert trace of the rational fixed-annulus local operator

No period, input window, summability assumption, or multiplier representation of the level is
required as input. The character modes in the conclusion are Fourier modes of the *test kernel*.
-/

open MeasureTheory Set InnerProductSpace
open scoped InnerProductSpace

namespace Masullo.OperatorTrace.RealLogLevel
noncomputable section

/-- The convolution integrals used below are genuine Lebesgue integrals, for every output
point, rather than just equalities involving Lean's totalized Bochner integral. -/
public theorem integrable_translate (α : ℝ) (r : ℕ) (z : H α r) {φ : ℝ → ℂ}
    (hφ : Continuous φ) {R : ℝ} (hs : Function.support φ ⊆ Icc (-R) R) (x : ℝ) :
    Integrable (fun y => φ (x - y) * z y) := by
  let D := Icc (x - R) (x + R)
  have hz : IntegrableOn (fun y => z y) D := by
    apply (integrable_mul_conj_q_iff α r (x - R) (x + R)).1
    exact MeasureTheory.L2.integrable_inner (q α r (x - R) (x + R)) z
  apply (integrableOn_iff_integrable_of_support_subset (s := D) ?_).1
  · apply IntegrableOn.continuousOn_mul _ hz isCompact_Icc
    exact (hφ.comp (continuous_const.sub continuous_id)).continuousOn
  · intro y hy
    have hne : φ (x - y) ≠ 0 := fun h0 => hy (by simp [h0])
    have ht := hs (show x - y ∈ Function.support φ from hne)
    exact ⟨by linarith [ht.2], by linarith [ht.1]⟩

/-- At any fixed local bandwidth, the actual projected real-line convolution has an absolutely
summable rank-one presentation. Every Hilbert basis gives the same explicitly convergent trace. -/
public theorem fixedAnnulus_fourier_presentation (α : ℝ) (r : ℕ) (Y : ℝ) {p φ : ℝ → ℂ}
    (hp : Continuous p) (hpK : HasCompactSupport p)
    (hφ : ContDiff ℝ 2 φ) (hφK : HasCompactSupport φ) :
    ∃ (R : ℝ) (hR : 0 < R),
      let : Fact (0 < 8 * R) := ⟨by positivity⟩
      ∃ f : C(AddCircle (8 * R), ℂ),
        Function.support p ⊆ Icc (-R) R ∧ Function.support φ ⊆ Icc (-R) R ∧
        EqOn (fun t : ℝ => f (t : AddCircle (8 * R))) φ (Icc (-(4 * R)) (-(4 * R) + 8 * R)) ∧
        Summable (fourierCoeff f) ∧
        let P := (hp.memLp_of_hasCompactSupport (μ := μ α r) hpK).toLp p
        let u := outputMode P f
        let v := fun k : ℤ => W (L := 8 * R) (q α r (-(2 * R)) (2 * R)) (fourier k)
        let QY := Q α r Y
        let term := fun k : ℤ => rankOne ℂ (u k) (QY.adjoint (v k))
        ∃ B : H α r →L[ℂ] H α r,
          (∀ z : H α r, (B z : ℝ → ℂ) =ᵐ[μ α r] fun x => p x * ∫ y, φ (x - y) * (QY z) y) ∧
          (Summable fun k => ‖term k‖) ∧ HasSum term B ∧
          (Summable fun k => ⟪v k, QY (u k)⟫_ℂ) ∧
          ∀ {ι : Type*} (b : HilbertBasis ι ℂ (H α r)),
            HasSum (fun i => ⟪b i, B (b i)⟫_ℂ) (∑' k, ⟪v k, QY (u k)⟫_ℂ) := by
  obtain ⟨R, hR, hsub⟩ :=
    ((show IsCompact (tsupport p) from hpK).union hφK).isBounded.subset_closedBall_lt 0 (0 : ℝ)
  have hball : Metric.closedBall (0 : ℝ) R = Icc (-R) R := by simp [Real.closedBall_eq_Icc]
  rw [hball] at hsub
  have hpR : Function.support p ⊆ Icc (-R) R :=
    fun _ hx => hsub (Or.inl (subset_tsupport _ hx))
  have hφR : Function.support φ ⊆ Icc (-R) R :=
    fun _ hx => hsub (Or.inr (subset_tsupport _ hx))
  refine ⟨R, hR, ?_⟩
  let : Fact (0 < 8 * R) := ⟨by positivity⟩
  obtain ⟨f, hmatch, hf⟩ := exists_circleProfile_of_support (T := 8 * R) (a := -(4 * R)) hφ hφR
    (by linarith) (by linarith)
  let hP : MemLp p 2 (μ α r) := hp.memLp_of_hasCompactSupport (μ := μ α r) hpK
  let P := hP.toLp p
  let qD := q α r (-(2 * R)) (2 * R)
  let QY := Q α r Y
  refine ⟨f, hpR, hφR, hmatch, hf, (windowKernel P qD f).comp QY, ?_, ?_⟩
  · exact annulus_kernel_ae p φ hP hpR hφR qD (fun _ => integral_mul_conj_q ..) f hf
      (fun t ht => hmatch (show t ∈ Icc (-(4 * R)) (-(4 * R) + 8 * R) from
        ⟨by linarith [(abs_le.mp ht).1], by linarith [(abs_le.mp ht).2]⟩)) QY
  · have hrank := windowKernel_rankOne (p := P) (q := qD) hf QY
    refine ⟨hrank.1, hrank.2, ?_, fun b => (windowKernel_trace b P qD f hf QY).2⟩
    obtain ⟨_, b, _⟩ := exists_hilbertBasis ℂ (H α r)
    exact (windowKernel_trace b P qD f hf QY).1

end
end Masullo.OperatorTrace.RealLogLevel
