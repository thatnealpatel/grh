module

public import Theorems.RationalAdelePrimeMaskLF
public import Theorems.RationalThetaFiniteUnitAverage

/-!
# Theta of the disjoint one-prime unit cut

On a supplied unramified rational tensor, the unit cut at any finite prime
has an LF representative (corrected tensor in Masullo, §1.3.2, p. 26).
Its class theta is the unramified theta minus its inverse-uniformizer translate.
-/

open NumberField IsDedekindDomain
open scoped SchwartzMap

namespace Masullo

local notation "A" => AdeleRing (𝓞 ℚ) ℚ
local notation "C" => IdeleClassGroup (𝓞 ℚ) ℚ
local notation "E" => RationalAdeleSchwartzLF
local notation "vₚ" => Equiv.symm (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ))
local notation "Θ[" f "]" => rationalAdeleClassTheta (Subtype.val (RationalAdeleSchwartzLF.toUnion f))

private theorem primeMasked_finiteUnit_mul (p : Nat.Primes) (b : 𝓢(ℝ, ℂ))
    (u : RationalFiniteUnits) (x : A) :
    rationalAdelePrimeMasked p b ((rationalFiniteUnitIdele u : A) * x) =
      rationalAdelePrimeMasked p b x := by
  classical
  let y := (rationalFiniteUnitIdele u : A) * x
  have hval (v : HeightOneSpectrum (𝓞 ℚ)) : Valued.v (y.2 v) = Valued.v (x.2 v) := by
    change Valued.v ((rationalFiniteUnitIdele u : A).2 v * x.2 v) = _
    rw [map_mul, rationalFiniteUnitIdele_apply_finite,
      HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one.mp (u v).isUnit,
      one_mul]
  have hu : y ∈ rationalAdelePrimeUnits p ↔ x ∈ rationalAdelePrimeUnits p := by
    change Valued.v (y.2 _) = 1 ↔ Valued.v (x.2 _) = 1
    rw [hval]
  have hw : y ∈ (rationalIntegralAdeles : Set A) ↔ x ∈ (rationalIntegralAdeles : Set A) := by
    change (∀ v, y.2 v ∈ v.adicCompletionIntegers ℚ) ↔
      (∀ v, x.2 v ∈ v.adicCompletionIntegers ℚ)
    simp only [HeightOneSpectrum.mem_adicCompletionIntegers, hval]
  have hr : rationalAdeleReal y = rationalAdeleReal x := by
    rw [rationalAdeleReal_apply, rationalAdeleReal_apply]
    change InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace
      (((rationalFiniteUnitIdele u : A).1 * x.1) Rat.infinitePlace) = _
    rw [rationalFiniteUnitIdele_fst, one_mul]
  change rationalAdelePrimeMasked p b y = _
  simp only [rationalAdelePrimeMasked, rationalAdeleUnramified, Set.indicator_apply, hu, hw, hr]

private theorem primeMasked_theta_invariant {p : Nat.Primes} {b : 𝓢(ℝ, ℂ)} {g : E}
    (hg : g.toUnion.val = rationalAdelePrimeMasked p b) :
    ∀ (k : rationalIdeleClassNormOne) (d : C), Θ[g] ((k : C) * d) = Θ[g] d := by
  apply (rationalIdeleClass_normOne_invariant_iff_finiteUnits _).mpr
  intro u d
  rw [← rationalAdeleClassTheta_LFFiniteUnitPull]
  have h : (rationalAdeleLFFiniteUnitPull u g).toUnion.val = g.toUnion.val := by
    funext x
    rw [rationalAdeleLFFiniteUnitPull_apply, hg, primeMasked_finiteUnit_mul]
  change rationalAdeleClassTheta (rationalAdeleLFFiniteUnitPull u g).toUnion.val d = _
  rw [h]

private theorem unramified_theta_norm (b : 𝓢(ℝ, ℂ)) (d : C) :
    rationalAdeleClassTheta (rationalAdeleUnramified b) d = rationalTheta b (ideleClassNorm d) := by
  classical
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective d
  rw [rationalAdeleClassTheta_mk, rationalAdeleTheta, ideleClassNorm_mk]
  rw [← (rationalTheta_eq_unramified_idele_sum b a).2]
  apply tsum_congr
  intro q
  rw [rationalAdeleUnramified, Set.indicator_apply, rationalThetaIdeleTerm, rationalAdeleReal_apply]
  rfl

/-- The literal `p`-unit cut of a supplied unramified LF tensor has an LF witness
on all additive adeles. Its theta equals the inverse-uniformizer difference
on every idele class, with no moment conditions. -/
public theorem exists_rationalAdeleUnramifiedPrimeCut (p : Nat.Primes) (b : 𝓢(ℝ, ℂ)) (f : E)
    (hf : f.toUnion.val = rationalAdeleUnramified b) :
    ∃ g : E, g.toUnion.val = Set.indicator (rationalAdelePrimeUnits p) f.toUnion.val ∧
      ∀ d : C, Θ[g] d = Θ[f] d -
        Θ[f] ((QuotientGroup.mk (rationalThetaRadialUniformizer (vₚ p)) : C)⁻¹ * d) := by
  obtain ⟨g, hg⟩ := exists_rationalAdelePrimeMaskedLF p b
  refine ⟨g, by rw [hg, hf]; rfl, fun d ↦ ?_⟩
  have hp : Rat.HeightOneSpectrum.primesEquiv (vₚ p) = p :=
    (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).apply_symm_apply p
  -- Inverse translation increases the norm, matching the removed indices.
  have hnorm :
      ideleClassNorm ((QuotientGroup.mk (rationalThetaRadialUniformizer (vₚ p)) : C)⁻¹ * d) =
        (p : ℝ) * ideleClassNorm d := by
    rw [map_mul, map_inv, ideleClassNorm_mk, ideleNorm_rationalThetaRadialUniformizer, inv_inv, hp]
  rw [(rationalIdeleClass_normOne_invariant_iff _).mp (primeMasked_theta_invariant hg) d]
  change rationalAdeleClassTheta g.toUnion.val (rationalIdeleClassLogSection
    (Multiplicative.ofAdd (Real.log (ideleClassNorm d)))) = _
  rw [hg, rationalIdeleClassLogSection_apply, rationalAdeleClassTheta_mk, rationalAdeleTheta]
  rw [hf, unramified_theta_norm, unramified_theta_norm, hnorm]
  exact (rationalTheta_eq_primeMasked_idele_sum p b (ideleClassNorm_pos d)).2

end Masullo
