module

public import Lemmas.FiniteCompletionBoxIntegral
public import Theorems.FiniteBoxCenteredMass
public import Theorems.FiniteBoxTraceDual
import Mathlib.Algebra.FiniteSupport.Basic

/-! # The finite Fourier factors of a translated adelic box

Masullo's Example A.3.1.10, (A.3.1.8), PDF p. 558, gives the transform of the
centered integer ring. The product in (2.2.4.32), p. 92, uses local Fourier
integrals. With the corrected pairing, their finite kernels have positive
sign. For the lattice approach to Theorem 2.2.3.2, p. 82, the local subgroup
integral and translation formula `finiteCompletion_box_fourier` supply the
factors for arbitrary radii and centers. We evaluate their product on the
diagonal, including its vanishing off the trace dual. This is a scalar
identity, not a restricted-product integration theorem. Source reading:
Provisional Markdown and numbered PDF layout.
-/

open Filter Function IsDedekindDomain MeasureTheory NumberField
open scoped BigOperators Classical Masullo nonZeroDivisors Pointwise WithZero

namespace Masullo

variable {K : Type*} [Field K] [NumberField K]

local notation "V" => HeightOneSpectrum (𝓞 K)
local notation "F" => FiniteAdeleRing (𝓞 K) K
local notation "J" => FractionalIdeal (𝓞 K)⁰ K
local notation "K[" v "]" => HeightOneSpectrum.adicCompletion K v
local notation "O[" v "]" => HeightOneSpectrum.adicCompletionIntegers K v
local notation "w[" v "]" => (Valued.v : Valuation K[v] ℤᵐ⁰)
local notation "k[" v "]" => algebraMap K K[v]
local notation "χ[" v "]" => fun x : K[v] ↦ padicStdAddChar (finiteCompletionBasePrime v)
  (Algebra.trace ℚ_[finiteCompletionBasePrime v] K[v] x)
local notation "ν[" v "]" => @finiteCompletionNormalizedHaar K _ _ v (borel K[v])
  (@BorelSpace.mk K[v] _ (borel K[v]) rfl)
local notation "mass[" g "," v "]" => @Measure.real K[v] (borel K[v]) (ν[v])
  (Units.val g v • (O[v] : Set K[v]))
local notation "boxIntegral[" a "," g "," y "," v "]" =>
  @integral K[v] ℂ _ _ (borel K[v])
    (@Measure.restrict K[v] (borel K[v]) (ν[v]) ((a v + ·) '' (Units.val g v • (O[v] : Set K[v]))))
    (fun t ↦ χ[v] (k[v] y * t))

private theorem boxIntegral_eq (a : F) (g : Fˣ) (y : K) (v : V) :
    boxIntegral[a,g,y,v] =
      if ∀ t : O[v], χ[v] (k[v] y * (g.val v * (t : K[v]))) = 1 then
        χ[v] (k[v] y * a v) * (mass[g,v] : ℂ) else 0 := by
  borelize K[v]
  exact finiteCompletion_box_fourier v (finiteCompletionNormalizedHaar v) (a v) (g.val v) (k[v] y)
    ((FiniteAdeleRing.isUnit_iff.mp g.isUnit).1 v)

/-- The actual local Fourier integrals of `a + g ∏ O_v` on diagonal frequencies
are one off a finite set, even when the frequency does not lie in the trace
dual. On the trace dual their product is the positive shift phase times the
reciprocal trace covolume; off it the product is zero. -/
public theorem finiteBox_fourier_finprod (a : F) (g : Fˣ) (x₀ y : K)
    (hx₀ : ∀ v : V, w[v] (k[v] x₀ - a v) ≤ w[v] (g.val v)) :
    (fun v : V ↦ boxIntegral[a,g,y,v]).HasFiniteMulSupport ∧
      (∏ᶠ v : V, boxIntegral[a,g,y,v]) =
        if y ∈ FractionalIdeal.dual ℤ ℚ (finiteIdeleIdeal K g : J) then
          Complex.exp (2 * Real.pi * Complex.I * (Algebra.trace ℚ K (x₀ * y) : ℂ)) *
            ((ZLattice.covolume (archimedeanIdealLattice K (finiteIdeleIdeal K g))
              (archimedeanTraceMeasure K))⁻¹ : ℝ)
        else 0 := by
  obtain ⟨hmass, hmassProd⟩ := finiteBox_centeredMass_finprod g
  -- The frequency, center, and radius are all integral almost everywhere.
  -- The local kernel is then trivial and only the centered mass remains.
  have hfinite : (fun v : V ↦ boxIntegral[a,g,y,v]).HasFiniteMulSupport := by
    apply eventually_cofinite.mp
    filter_upwards [(algebraMap K F y).cofinite_mem_adicCompletionIntegers,
      a.cofinite_mem_adicCompletionIntegers, g.val.cofinite_mem_adicCompletionIntegers,
      eventually_cofinite.mpr hmass] with v hy ha hg hm
    change mass[g,v] = 1 at hm
    have hann (t : O[v]) : χ[v] (k[v] y * (g.val v * (t : K[v]))) = 1 :=
      finiteCompletion_traceChar_eq_one_of_integral v
        ⟨_, (O[v]).toSubring.mul_mem hy ((O[v]).toSubring.mul_mem hg t.property)⟩
    have hphase : χ[v] (k[v] y * a v) = 1 :=
      finiteCompletion_traceChar_eq_one_of_integral v ⟨_, (O[v]).toSubring.mul_mem hy ha⟩
    rw [boxIntegral_eq, ite_eq_left hann, hphase, hm, Complex.ofReal_one, one_mul]
  refine ⟨hfinite, ?_⟩
  by_cases hy : y ∈ FractionalIdeal.dual ℤ ℚ (finiteIdeleIdeal K g : J)
  · have hann := (mem_traceDual_finiteIdeleIdeal_iff g y).mp hy
    obtain ⟨hphase, hphaseProd⟩ := finiteBox_tracePhase_eq_diagonal a g x₀ y hx₀ hy
    have hmassC : (fun v : V ↦ (mass[g,v] : ℂ)).HasFiniteMulSupport :=
      HasFiniteMulSupport.fun_comp hmass (map_one (algebraMap ℝ ℂ))
    simp_rw [boxIntegral_eq, ite_eq_left (hann _), ite_eq_left hy]
    rw [finprod_mul_distrib hphase hmassC, hphaseProd]
    exact congrArg (_ * ·) ((map_finprod (algebraMap ℝ ℂ) hmass).symm.trans
      (congrArg (algebraMap ℝ ℂ) hmassProd))
  · have hn : ¬∀ v : V, ∀ t : O[v], χ[v] (k[v] y * (g.val v * (t : K[v]))) = 1 :=
      mt (mem_traceDual_finiteIdeleIdeal_iff g y).mpr hy
    obtain ⟨v, hv⟩ := not_forall.mp hn
    rw [ite_eq_right hy]
    exact finprod_eq_zero _ v (by rw [boxIntegral_eq, ite_eq_right hv]) hfinite

end Masullo
