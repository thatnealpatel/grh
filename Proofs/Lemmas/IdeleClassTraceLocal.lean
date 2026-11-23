module

public import Lemmas.ArchimedeanCompletionHaar
public import Theorems.FiniteCompletionMultiplicativeHaar

/-!
# Normalized geometric local terms on the idele class group

We use the actual single-place maps: Insert a local unit with all other
coordinates equal to `1`, then pass to the idele class group. The local
terms in Masullo (12.5.1.1–2), p. 519, are for tests vanishing on the
norm-one subgroup. In particular the identity contact and logarithmic
counterterms are zero. These definitions do not assert admissibility or
convergence for an arbitrary function on the idele class group.
-/

open Filter IsDedekindDomain MeasureTheory NumberField Set
open scoped Classical ENNReal Topology

namespace Masullo

variable {K : Type*} [Field K] [NumberField K]

local notation "C" => IdeleClassGroup (𝓞 K) K

/-- The Archimedean local term of (12.5.1.1) on norm-one-vanishing tests.

Use half of real Haar or `1/(2π)` of complex Haar. The Tamagawa densities
are `dx / |x|` and `2 dx dy / ‖z‖²` (A.3.1.2, p. 556; A.3.2.2, p. 560).
We read the denominator `|1 - g|` in (12.5.1.1) as the normalized local
absolute value, as in (12.4.1.25–26) and (B.4.4.2). Thus at a complex
place it is the squared Euclidean norm, and the numerator weight is
`‖g‖`. The physical cutoff is `ε ≤ |1 - g|ᵥ`, translated from the additive
cutoffs in (B.4.3.13–14), p. 619. `RationalRadialStripTrace` uses the
symmetric log cutoff instead, with the same limit for its radial tests.
Each positive cutoff must be integrable before its integral is used. -/
@[expose] public noncomputable def HasArchimedeanTraceValue (v : InfinitePlace K)
    (φ : C → ℂ) (A : ℂ) : Prop :=
  letI : MeasurableSpace v.Completionˣ := borel _
  letI : BorelSpace v.Completionˣ := ⟨rfl⟩
  let μ : Measure v.Completionˣ :=
    if hv : v.IsReal then (1 / 2 : ℝ≥0∞) • realCompletionHaar hv
    else ENNReal.ofReal (1 / (2 * Real.pi)) •
      complexCompletionHaar (InfinitePlace.not_isReal_iff_isComplex.mp hv)
  let displacement (u : v.Completionˣ) := ‖1 - (u : v.Completion)‖ ^ v.mult
  let cutoff (ε : ℝ) := {u | ε ≤ displacement u}
  let f (u : v.Completionˣ) := φ (IdeleClassGroup.ofCompletion (𝓞 K) K v u) *
    (Real.sqrt (‖(u : v.Completion)‖ ^ v.mult) : ℂ) / (displacement u : ℂ)
  (∀ ε > 0, IntegrableOn f (cutoff ε) μ) ∧
    Tendsto (fun ε ↦ ∫ u in cutoff ε, f u ∂μ) (𝓝[>] 0) (𝓝 A)

local notation "V" => HeightOneSpectrum (𝓞 K)
local notation "F" v => HeightOneSpectrum.adicCompletion K v

/-- The integrand of (12.5.1.2) before Haar and residue-size normalization. -/
@[expose] public noncomputable def finiteTraceKernel (v : V) (φ : C → ℂ) (u : (F v)ˣ) : ℂ :=
  φ (IdeleClassGroup.ofAdicCompletion (𝓞 K) K v u) *
    (Real.sqrt ‖(u : F v)‖ : ℂ) / (‖1 - (u : F v)‖ : ℂ)

/-- Absolute integrability of the kernel used by `finiteTraceTerm` with
respect to the finite-place Tamagawa Haar measure. -/
@[expose] public noncomputable def FiniteTraceTermIntegrable (v : V) (φ : C → ℂ) : Prop :=
  letI : MeasurableSpace (F v)ˣ := borel _
  letI : BorelSpace (F v)ˣ := ⟨rfl⟩
  Integrable (finiteTraceKernel v φ) (finiteCompletionMultiplicativeHaar v)

/-- The finite-place term (12.5.1.2), with `qᵥ` the absolute norm of the
prime ideal. Dividing the Tamagawa measure by the mass of the integral
units gives the unit-mass normalization, leaving the factor `log qᵥ`.

For the manuscript's tests the restriction vanishes on the integral
units, hence near the singularity at `1`; (B.4.4.5), p. 620, then uses an
ordinary integral. The value at `1` is totalized to zero by Lean's division.
This function is total; use `FiniteTraceTermIntegrable v φ` to rule out the
zero returned by the integral on nonintegrable input. -/
@[expose] public noncomputable def finiteTraceTerm (v : V) (φ : C → ℂ) : ℂ :=
  letI : MeasurableSpace (F v)ˣ := borel _
  letI : BorelSpace (F v)ˣ := ⟨rfl⟩
  let μ := finiteCompletionMultiplicativeHaar v
  let unitMass := μ.real (range (finiteCompletionUnitInclusion K v))
  (Real.log (v.asIdeal.absNorm : ℝ) / unitMass : ℝ) * ∫ u, finiteTraceKernel v φ u ∂μ

end Masullo
