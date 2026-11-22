module

public import Lemmas.FixedAnnulusFourier

/-! # The Hilbert trace at a fixed rational real annulus

For the trivial compact isotype, the operator in the fixed-annulus version of §12.4.1
is trace class on weighted log `L²`. The two-moment band projection `Q` acts on the
input. No claim about the one-sided cutoff, global theta level, or orbital trace follows.
-/

open MeasureTheory Set InnerProductSpace
open scoped InnerProductSpace

namespace Masullo.OperatorTrace.RealLogLevel

/-- The projected convolution has an absolutely summable rank-one presentation, and
its trace is the same Fourier sum in every Hilbert basis. In the construction
`fixedAnnulus_fourier_presentation`, `u k` is the windowed output character times the
kernel coefficient, and `v k` is the input character windowed by the reciprocal weight. -/
public theorem fixedAnnulus_trace (α : ℝ) (r : ℕ) (Y : ℝ) {p φ : ℝ → ℂ}
    (hp : Continuous p) (hpK : HasCompactSupport p)
    (hφ : ContDiff ℝ 2 φ) (hφK : HasCompactSupport φ) :
    ∃ (R : ℝ) (hR : 0 < R),
      let : Fact (0 < 8 * R) := ⟨by positivity⟩
      ∃ f : C(AddCircle (8 * R), ℂ),
        Function.support p ⊆ Icc (-R) R ∧ Function.support φ ⊆ Icc (-R) R ∧
        EqOn (fun t : ℝ ↦ f (t : AddCircle (8 * R))) φ (Icc (-(4 * R)) (-(4 * R) + 8 * R)) ∧
        Summable (fourierCoeff f) ∧
        let P := (hp.memLp_of_hasCompactSupport (μ := μ α r) hpK).toLp p
        let u := outputMode P f
        let v := fun k : ℤ ↦ W (L := 8 * R) (q α r (-(2 * R)) (2 * R)) (fourier k)
        let QY := Q α r Y
        let term := fun k : ℤ ↦ rankOne ℂ (u k) (QY.adjoint (v k))
        ∃ B : H α r →L[ℂ] H α r,
          (∀ z : H α r, (B z : ℝ → ℂ) =ᵐ[μ α r] fun x ↦ p x * ∫ y, φ (x - y) * (QY z) y) ∧
          (Summable fun k ↦ ‖term k‖) ∧ HasSum term B ∧
          (Summable fun k ↦ ⟪v k, QY (u k)⟫_ℂ) ∧
          ∀ {ι : Type*} (b : HilbertBasis ι ℂ (H α r)),
            HasSum (fun i ↦ ⟪b i, B (b i)⟫_ℂ) (∑' k, ⟪v k, QY (u k)⟫_ℂ) :=
  fixedAnnulus_fourier_presentation α r Y hp hpK hφ hφK

end Masullo.OperatorTrace.RealLogLevel
