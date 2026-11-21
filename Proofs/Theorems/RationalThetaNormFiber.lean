module

public import Lemmas.RationalIdeleReal
public import Theorems.RationalThetaUnramified

/-!
# The unramified rational theta sum on every norm fiber

For the tensor of a Schwartz function on the real line with the characteristic functions
of the finite integer rings, the series (2.2.3.1), pp. 81–82, depends only
on the idelic norm. The proof uses the representative from (A.2.2.1)–(A.2.2.4),
p. 546, without requiring the topological splitting or a quotient measure.
-/

open NumberField IsDedekindDomain
open scoped Classical SchwartzMap

namespace Masullo

/-- The contribution of a nonzero rational to the unramified adelic theta sum. -/
@[expose] public noncomputable def rationalThetaIdeleTerm (b : 𝓢(ℝ, ℂ))
    (a : IdeleGroup (𝓞 ℚ) ℚ) (q : ℚˣ) : ℂ :=
  let aq := IdeleGroup.unitEmbedding (𝓞 ℚ) ℚ q * a
  if ∀ v : HeightOneSpectrum (𝓞 ℚ), (aq : AdeleRing (𝓞 ℚ) ℚ).2 v ∈ v.adicCompletionIntegers ℚ
  then b (rationalIdeleReal aq) else 0

private theorem rationalThetaIdeleTerm_of_finite_units (b : 𝓢(ℝ, ℂ)) (a : IdeleGroup (𝓞 ℚ) ℚ)
    (ha : ∀ v : HeightOneSpectrum (𝓞 ℚ), Valued.v ((a : AdeleRing (𝓞 ℚ) ℚ).2 v) = 1)
    (q : ℚˣ) :
    rationalThetaIdeleTerm b a q =
      if ∀ v : HeightOneSpectrum (𝓞 ℚ),
        algebraMap ℚ (v.adicCompletion ℚ) (q : ℚ) ∈ v.adicCompletionIntegers ℚ
      then b (rationalIdeleReal a * ((q : ℚ) : ℝ)) else 0 := by
  dsimp only [rationalThetaIdeleTerm]
  rw [rationalIdeleReal_principal_mul, mul_comm ((q : ℚ) : ℝ)]
  congr 1
  apply propext
  simp only [HeightOneSpectrum.mem_adicCompletionIntegers]
  -- Multiplying by an integral unit does not change the local valuation.
  change (∀ v : HeightOneSpectrum (𝓞 ℚ), Valued.v (algebraMap ℚ (v.adicCompletion ℚ) (q : ℚ) *
    (a : AdeleRing (𝓞 ℚ) ℚ).2 v) ≤ 1) ↔ _
  simp only [map_mul, ha, mul_one]

/-- For any representative, the unramified rational theta series is absolutely
summable and equals the integer lattice theta function at its idelic norm. -/
public theorem rationalTheta_eq_unramified_idele_sum (b : 𝓢(ℝ, ℂ))
    (a : IdeleGroup (𝓞 ℚ) ℚ) :
    Summable (fun q ↦ ‖rationalThetaIdeleTerm b a q‖) ∧
      (∑' q, rationalThetaIdeleTerm b a q) = rationalTheta b (ideleNorm a) := by
  obtain ⟨r, hreal, hfin⟩ := exists_rational_principal_mul_norm_section a
  let a' := IdeleGroup.unitEmbedding (𝓞 ℚ) ℚ r * a
  have hpos : 0 < ideleNorm a := ideleClassNorm_mk a ▸ ideleClassNorm_pos (QuotientGroup.mk a)
  obtain ⟨hsum, htheta⟩ := rationalTheta_eq_unramified_sum b hpos
  -- Multiplying the representative by the principal idele reindexes the sum.
  have hreindex (q : ℚˣ) : rationalThetaIdeleTerm b a' q = rationalThetaIdeleTerm b a (q * r) := by
    simp only [rationalThetaIdeleTerm, a', map_mul, mul_assoc]
  let f (q : {q : ℚ // q ≠ 0}) : ℂ :=
    if ∀ v : HeightOneSpectrum (𝓞 ℚ),
      algebraMap ℚ (v.adicCompletion ℚ) (q : ℚ) ∈ v.adicCompletionIntegers ℚ
    then b (ideleNorm a * ((q : ℚ) : ℝ)) else 0
  change Summable (fun q ↦ ‖f q‖) at hsum
  change (∑' q, f q) = rationalTheta b (ideleNorm a) at htheta
  let e : {q : ℚ // q ≠ 0} ≃ ℚˣ := unitsEquivNeZero.symm.trans (Equiv.mulRight r)
  have hterm (q : {q : ℚ // q ≠ 0}) : rationalThetaIdeleTerm b a (e q) = f q := by
    change rationalThetaIdeleTerm b a (unitsEquivNeZero.symm q * r) = f q
    rw [← hreindex]
    change rationalIdeleReal a' = ideleNorm a at hreal
    have hq : (↑(unitsEquivNeZero.symm q) : ℚ) = (q : ℚ) := rfl
    simp only [rationalThetaIdeleTerm_of_finite_units b a' hfin, hreal, hq, f]
  refine ⟨e.summable_iff.mp ?_, (e.tsum_eq _).symm.trans ?_⟩
  · simpa only [Function.comp_def, hterm] using hsum
  · simpa only [hterm] using htheta

end Masullo
