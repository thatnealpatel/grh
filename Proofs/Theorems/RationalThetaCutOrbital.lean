module

public import Theorems.RationalThetaCutConvolution
public import Lemmas.RationalThetaOrbitalPeriod
public import Theorems.MonogenicPeriodizationSection

/-!
# Fixed-cutoff rational theta output cannot give a nonzero direct orbital transfer

Theorem 7.4.2.1 (p. 367) computes convolution on the orbital quotient.
To obtain a map on that quotient by postprocessing an already cut global
output as in the model of (11.2.1.8–9), pp. 488–489, the result must not
depend on the orbital representative. The backward telescope shows that
every output on the indicated band already has a representative of orbital
class zero. This is a necessary condition for that direct transfer, not
a claim about every possible comparison of traces in (11.3.2.3–5).
-/

open MeasureTheory Set
open scoped SchwartzMap

namespace Masullo

/-- Pointwise cut output on a genuine generator: Twist the input by `exp(a*x)`,
convolve with `f`, and multiply by `ρ`. This is before Hilbert weight
conjugation and after using the two projections' actions on generators. -/
@[expose] public noncomputable def rationalThetaCutOutput (a : ℝ) (f ρ : ℝ → ℂ)
    (b : 𝓢(ℝ, ℂ)) (x : ℝ) : ℂ :=
  ρ x * (Real.exp (a * x) : ℂ) * ∫ y : ℝ,
    f y * (Real.exp (-a * y) : ℂ) * rationalTheta b (Real.exp (x - y))

/-- At fixed cutoffs, every band generator has exactly the same cut output as
one in the same band whose genuine untwisted orbital period sums are zero. -/
public theorem rationalThetaCutOutput_has_null_representative {p B a ell R : ℝ}
    (hp : 1 < p) (hB : 0 < B) {f ρ : ℝ → ℂ}
    (hf : Function.support f ⊆ Ici ell) (hρ : Function.support ρ ⊆ Iic R)
    {b : 𝓢(ℝ, ℂ)} (hb : b ∈ rationalThetaBandInput B) :
    ∃ d ∈ rationalThetaBandInput B,
      (∀ u : ℝ, HasSum (fun k : ℤ ↦ rationalTheta d (Real.exp (u + (k : ℝ) * Real.log p))) 0) ∧
        rationalThetaCutOutput a f ρ d = rationalThetaCutOutput a f ρ b := by
  obtain ⟨c, hc, hcut⟩ := rationalTheta_cutBand_preimage hp hB (Real.exp_pos (R - ell)) hb
  obtain ⟨hd, hdiff⟩ := rationalTheta_cutBand_difference hp hB hc
  let d := c - dilateSchwartz c p (zero_lt_one.trans hp).ne'
  refine ⟨d, hd, rationalTheta_logPeriod_hasSum_zero_of_difference hp hc hdiff, ?_⟩
  funext x
  by_cases hx : ρ x = 0
  · simp [rationalThetaCutOutput, hx]
  · unfold rationalThetaCutOutput
    apply congrArg (fun z : ℂ ↦ ρ x * (Real.exp (a * x) : ℂ) * z)
    apply logConvolution_eq_of_agree_below (f := fun y ↦ f y * (Real.exp (-a * y) : ℂ))
      (u := fun z ↦ rationalTheta d (Real.exp z)) (v := fun z ↦ rationalTheta b (Real.exp z))
      (a := ell) (R := R)
    · intro y hy
      exact hf (fun h ↦ hy (by simp [h]))
    · intro z hz
      exact (hdiff _ (Real.exp_pos _)).trans
        (hcut _ (Real.exp_pos _) (Real.exp_le_exp.mpr hz))
    · exact hρ hx

/-- Postprocessing the already-cut output cannot induce any nonzero map on
orbital classes of genuine band generators. The postprocessing need not be
linear or continuous. The orbital map must send the zero class to zero. -/
public theorem rationalThetaCutOutput_orbital_comparison_eq_zero {p B a ell R : ℝ}
    (hp : 1 < p) (hB : 0 < B) {f ρ : ℝ → ℂ}
    (hf : Function.support f ⊆ Ici ell) (hρ : Function.support ρ ⊆ Iic R)
    {V : Type*} [Zero V] (E S : (ℝ → ℂ) → V) (hS : S 0 = 0)
    (hcompare : ∀ b ∈ rationalThetaBandInput B,
      E (rationalThetaCutOutput a f ρ b) =
        S (logPeriodization (Real.log p) (fun x ↦ rationalTheta b (Real.exp x))))
    {b : 𝓢(ℝ, ℂ)} (hb : b ∈ rationalThetaBandInput B) :
    S (logPeriodization (Real.log p) (fun x ↦ rationalTheta b (Real.exp x))) = 0 := by
  obtain ⟨d, hd, hperiod, hcut⟩ :=
    rationalThetaCutOutput_has_null_representative hp hB hf hρ hb
  have hz : logPeriodization (Real.log p) (fun x ↦ rationalTheta d (Real.exp x)) = 0 :=
    funext fun u ↦ (hperiod u).tsum_eq
  rw [← hcompare b hb, ← hcut, hcompare d hd, hz, hS]

end Masullo
