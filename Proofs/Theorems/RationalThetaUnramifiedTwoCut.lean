module

public import Theorems.RationalAdeleLiteralTwoCut
public import Theorems.RationalThetaFiniteUnitAverage

/-!
# Theta of the disjoint prime-two unit cut

On a supplied unramified rational tensor, the corrected finite factor of
Masullo's §1.3.2, p. 26, has an LF representative. Its class theta is the
unramified class theta minus its inverse-uniformizer translate.
-/

open NumberField IsDedekindDomain
open scoped SchwartzMap

namespace Masullo

local notation "A" => AdeleRing (𝓞 ℚ) ℚ
local notation "C" => IdeleClassGroup (𝓞 ℚ) ℚ
local notation "E" => RationalAdeleSchwartzLF
local notation "p₂" => (Subtype.mk 2 Nat.prime_two : Nat.Primes)
local notation "v₂" => Equiv.symm (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)) p₂
local notation "Θ[" f "]" => rationalAdeleClassTheta (Subtype.val (RationalAdeleSchwartzLF.toUnion f))

private theorem exists_primeMasked_two (b : 𝓢(ℝ, ℂ)) :
    ∃ g : E, g.toUnion.val = rationalAdelePrimeMasked p₂ b := by
  classical
  let q : Fin (2 ^ 2) → 𝓢(ℝ, ℂ) := ![0, 0, b, 0]
  refine ⟨rationalAdeleLFAssembly 1 q, ?_⟩
  funext x
  rw [rationalAdeleLFAssembly_toUnion 1 q, rationalAdeleFactorialStageAssembly_val 1 q]
  change ((rationalAdeleStageCoordinates (by decide : 0 < 2)).symm q).val x =
    (rationalAdelePrimeUnits p₂).indicator
      ((rationalIntegralAdeles : Set A).indicator (fun y ↦ b (rationalAdeleReal y))) x
  rw [rationalAdeleStageCoordinates_symm_eq_boxSum (by decide : 0 < 2) q,
    Set.indicator_indicator, Set.inter_comm, ← rationalAdeleStageCell_two_eq_primeUnits.2]
  simp only [rationalAdeleBoxSum, one_mul, rationalAdeleBox_stageCell]
  simp [q, Fin.sum_univ_succ, Set.indicator]

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

/-- The literal prime-two cut of a supplied unramified LF tensor is an LF test.
Its theta agrees at every class with the inverse-uniformizer difference,
without assumptions on the input's zero modes. -/
public theorem exists_rationalAdeleUnramifiedTwoCut (b : 𝓢(ℝ, ℂ)) (f : E)
    (hf : f.toUnion.val = rationalAdeleUnramified b) :
    ∃ g : E, g.toUnion.val = Set.indicator (rationalAdelePrimeUnits p₂) f.toUnion.val ∧
      ∀ d : C, Θ[g] d = Θ[f] d -
        Θ[f] ((QuotientGroup.mk (rationalThetaRadialUniformizer v₂) : C)⁻¹ * d) := by
  obtain ⟨g, hg⟩ := exists_primeMasked_two b
  refine ⟨g, by rw [hg, hf]; rfl, fun d ↦ ?_⟩
  have hp : Rat.HeightOneSpectrum.primesEquiv v₂ = p₂ :=
    (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).apply_symm_apply p₂
  have hnorm :
      ideleClassNorm ((QuotientGroup.mk (rationalThetaRadialUniformizer v₂) : C)⁻¹ * d) =
        (2 : ℝ) * ideleClassNorm d := by
    rw [map_mul, map_inv, ideleClassNorm_mk, ideleNorm_rationalThetaRadialUniformizer, inv_inv, hp]
    rfl
  rw [(rationalIdeleClass_normOne_invariant_iff _).mp (primeMasked_theta_invariant hg) d]
  change rationalAdeleClassTheta g.toUnion.val (rationalIdeleClassLogSection
    (Multiplicative.ofAdd (Real.log (ideleClassNorm d)))) = _
  rw [hg, rationalIdeleClassLogSection_apply, rationalAdeleClassTheta_mk, rationalAdeleTheta]
  rw [hf, unramified_theta_norm, unramified_theta_norm, hnorm]
  exact (rationalTheta_eq_primeMasked_idele_sum p₂ b (ideleClassNorm_pos d)).2

end Masullo
