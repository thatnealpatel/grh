module

public import Theorems.RationalIdeleClassCompact
public import Theorems.FiniteCompletionMultiplicativeHaar
public import Mathlib.NumberTheory.Padics.HeightOneSpectrum
public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
public import Mathlib.RingTheory.DedekindDomain.SInteger
public import Mathlib.RingTheory.PicardGroup
import Mathlib.NumberTheory.NumberField.Discriminant.Different
import Lemmas.FiniteHeckeLocalNormalization

/-!
# The rational prime-two witness for the RHS of (11.3.2.1)

The choice of orbit and norm band is due to the §11.3 counterexample in
`mccorvie/riemann-masullo` (see PR #2885, `OrbitalCutoff.lean`, at
`2c1e159ac7ae92a64db48d4c4d1b6f0ba5e01e4e`). This independent grh
calculation uses the quotient class and the discriminant-normalized measure.
The sum is over all integers, without a Mellin shift. Smoothness is exhibited
in the rational class group's split coordinates; no identification with the
companion's `BruhatCompactSupport` space is assumed.
-/

open NumberField IsDedekindDomain Set MeasureTheory
open scoped ContDiff

namespace Masullo

noncomputable section

local notation "V" => HeightOneSpectrum (𝓞 ℚ)
local notation "C" => IdeleClassGroup (𝓞 ℚ) ℚ

/-- Use the prime equivalence occurring in the first primary layer. -/
public def rationalOrbitalPrimeTwoPlace : V :=
  Rat.HeightOneSpectrum.primesEquiv.symm ⟨2, Nat.prime_two⟩

local notation "v₂" => rationalOrbitalPrimeTwoPlace
local notation "K₂" => HeightOneSpectrum.adicCompletion ℚ rationalOrbitalPrimeTwoPlace

public theorem rationalOrbitalPrimeTwoPlace_asIdeal : (v₂).asIdeal = Ideal.span {(2 : 𝓞 ℚ)} := by
  change (Ideal.span {(2 : ℤ)}).map (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)).symm = _
  simp [Ideal.map_span]

public theorem rationalOrbitalPrimeTwoPlace_absNorm : (v₂).asIdeal.absNorm = 2 := by
  rw [rationalOrbitalPrimeTwoPlace_asIdeal]
  simpa [RingOfIntegers.rank] using Ideal.absNorm_span_natCast (S := 𝓞 ℚ) 2

/-- Two as a unit in the *field*, not in its valuation ring. -/
public def rationalOrbitalPrimeTwoUniformizer : K₂ˣ :=
  Units.map (algebraMap ℚ K₂).toMonoidHom (Units.mk0 (2 : ℚ) (by norm_num))

public theorem rationalOrbitalPrimeTwoUniformizer_isUniformizer :
    Valued.v.IsUniformizer (rationalOrbitalPrimeTwoUniformizer : K₂) := by
  change Valued.v (algebraMap ℚ K₂ 2) = _
  calc
    _ = (v₂).valuation ℚ 2 := (v₂).valuedAdicCompletion_eq_valuation' (2 : ℚ)
    _ = (v₂).intValuation (2 : 𝓞 ℚ) := by
      simpa only [map_ofNat] using (v₂).valuation_of_algebraMap (K := ℚ) (2 : 𝓞 ℚ)
    _ = _ := by
      rw [(v₂).intValuation_singleton (by norm_num) rationalOrbitalPrimeTwoPlace_asIdeal,
        Valuation.IsRankOneDiscrete.generator_eq_exp_neg_one_of_surjective
          ((v₂).valuedAdicCompletion_surjective ℚ)]
      rfl

/-- The class of the single-place idèle, not the class of the principal idèle 2. -/
public def rationalOrbitalPrimeTwoClass : C :=
  IdeleClassGroup.ofAdicCompletion (𝓞 ℚ) ℚ v₂ rationalOrbitalPrimeTwoUniformizer

public theorem rationalOrbitalPrimeTwoClass_norm_zpow (n : ℤ) :
    ideleClassNorm (rationalOrbitalPrimeTwoClass ^ n) = (2 : ℝ) ^ (-n) := by
  unfold rationalOrbitalPrimeTwoClass
  rw [← map_zpow (IdeleClassGroup.ofAdicCompletion (𝓞 ℚ) ℚ v₂), ideleClassNorm_ofAdicCompletion,
    Units.val_zpow_eq_zpow_val, norm_zpow,
    norm_uniformizer_eq_inv_finitePlaceNorm _ _ rationalOrbitalPrimeTwoUniformizer_isUniformizer,
    finitePlaceNorm, rationalOrbitalPrimeTwoPlace_absNorm]
  simp [zpow_neg]

/-- A norm profile with a plateau at two and closed support `[5/3, 7/3]`. -/
@[expose] public def rationalOrbitalPrimeTwoBump : ContDiffBump (2 : ℝ) :=
  ⟨1 / 6, 1 / 3, by norm_num, by norm_num⟩

local notation "B" => rationalOrbitalPrimeTwoBump

public theorem rationalOrbitalPrimeTwoBump_tsupport : tsupport B = Icc (5 / 3) (7 / 3) := by
  rw [(B).tsupport_eq, Real.closedBall_eq_Icc]
  norm_num [rationalOrbitalPrimeTwoBump]

public theorem rationalOrbitalPrimeTwoBump_two : B 2 = 1 :=
  (B).one_of_mem_closedBall (Metric.mem_closedBall_self (B).rIn_pos.le)

/-- Pull back the profile by the descended norm, then include its values in ℂ. -/
@[expose] public def rationalOrbitalPrimeTwoTest (c : C) : ℂ := B (ideleClassNorm c)

local notation "φ" => rationalOrbitalPrimeTwoTest

private theorem test_support_closed :
    tsupport φ ⊆ ideleClassNorm ⁻¹' Icc (5 / 3) (7 / 3) := by
  rw [← rationalOrbitalPrimeTwoBump_tsupport]
  exact (tsupport_comp_subset Complex.ofReal_zero (B ∘ ideleClassNorm)).trans
    (tsupport_comp_subset_preimage B continuous_ideleClassNorm)

public theorem rationalOrbitalPrimeTwoTest_support :
    tsupport φ ⊆ {c | ideleClassNorm c ∈ Ioo (3 / 2) (5 / 2)} := by
  intro c hc
  exact Icc_subset_Ioo (by norm_num) (by norm_num) (test_support_closed hc)

public theorem rationalOrbitalPrimeTwoTest_hasCompactSupport : HasCompactSupport φ :=
  (isCompact_rationalIdeleClass_normStrip (v := 7 / 3) (by norm_num : (0 : ℝ) < 5 / 3)
    ).of_isClosed_subset (isClosed_tsupport _) test_support_closed

public theorem rationalOrbitalPrimeTwoTest_invariant (u x : C) (hu : ideleClassNorm u = 1) :
    φ (u * x) = φ x := by simp [rationalOrbitalPrimeTwoTest, hu]

/-- Component hypotheses from `mem_outsideIntegralIdeleUnits_iff` at `S = ∅`.
Both the coordinate and its inverse must be integral. -/
public theorem rationalOrbitalPrimeTwoTest_finiteUnits (g : IdeleGroup (𝓞 ℚ) ℚ)
    (hinf : g.val.1 = 1) (hf : ∀ v : V, g.val.2 v ∈ v.adicCompletionIntegers ℚ ∧
      (g⁻¹).val.2 v ∈ v.adicCompletionIntegers ℚ) (x : C) :
    φ (QuotientGroup.mk' _ g * x) = φ x := by
  apply rationalOrbitalPrimeTwoTest_invariant
  rw [QuotientGroup.mk'_apply, ideleClassNorm_mk, ideleNorm_eq_abs_rationalIdeleReal]
  · unfold rationalIdeleReal
    rw [hinf]
    change |(InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace) 1| = 1
    rw [map_one, abs_one]
  · intro v
    let u := Units.map (RestrictedProduct.evalMonoidHom (fun w : V ↦ w.adicCompletion ℚ) v)
      (MulEquiv.prodUnits g).2
    exact HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one.mp
      (show u ∈ (v.adicCompletionIntegers ℚ).units from hf v)

/-- In the genuine splitting of the quotient the test is smooth in log norm
and constant in the compact coordinate. -/
public theorem rationalOrbitalPrimeTwoTest_split :
    ContDiff ℝ ∞ (fun t : ℝ ↦ (B (Real.exp t) : ℂ)) ∧
    ∀ (t : ℝ) (u : rationalIdeleClassNormOne),
      φ (rationalIdeleClassLogSplit (Multiplicative.ofAdd t, u)) = (B (Real.exp t) : ℂ) := by
  refine ⟨Complex.ofRealCLM.contDiff.comp ((B).contDiff.comp Real.contDiff_exp), ?_⟩
  intro t u
  rw [rationalIdeleClassLogSplit_apply, rationalOrbitalPrimeTwoTest, map_mul,
    (mem_rationalIdeleClassNormOne _).mp u.property, mul_one,
    rationalIdeleClassLogSection_apply, ideleClassNorm_mk, ideleNorm_logSection]
  rfl

/-- The test is real and nonnegative on the entire class group. -/
public theorem rationalOrbitalPrimeTwoTest_nonneg (x : C) :
    0 ≤ (φ x).re ∧ (φ x).im = 0 := ⟨(B).nonneg, rfl⟩

/-- On the uniformizer orbit the *inverse* is the sole nonzero term. -/
public theorem rationalOrbitalPrimeTwoTest_zpow (n : ℤ) :
    φ (rationalOrbitalPrimeTwoClass ^ n) = if n = -1 then 1 else 0 := by
  rw [rationalOrbitalPrimeTwoTest, rationalOrbitalPrimeTwoClass_norm_zpow]
  split_ifs with hn
  · simp [hn, rationalOrbitalPrimeTwoBump_two]
  · apply Complex.ofReal_eq_zero.mpr
    by_contra h
    have hm := subset_tsupport B h
    rw [rationalOrbitalPrimeTwoBump_tsupport] at hm
    rcases le_or_gt 0 n with h | h
    · have hb := zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (neg_nonpos.mpr h)
      exact (not_le_of_gt (by norm_num : (1 : ℝ) < 5 / 3)) (hm.1.trans (by simpa using hb))
    · have hb := zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (show (2 : ℤ) ≤ -n by omega)
      exact (not_le_of_gt (by norm_num : (7 : ℝ) / 3 < 4)) (by
        simpa only [zpow_ofNat, Nat.cast_ofNat, show (2 : ℝ) ^ 2 = 4 by norm_num] using hb.trans hm.2)

/-- The exact support-side inequality of the printed binder. -/
public theorem rationalOrbitalPrimeTwoTest_support_gt_one :
    tsupport φ ⊆ {c | 1 < ideleClassNorm c} := fun _ hc ↦
  lt_trans (by norm_num : (1 : ℝ) < 3 / 2) (rationalOrbitalPrimeTwoTest_support hc).1

/-- Over ℚ the different has zero exponent at every place, in particular at 2. -/
public theorem rationalOrbital_differentExponent (v : V) :
    multiplicity v.asIdeal (differentIdeal ℤ (𝓞 ℚ)) = 0 := by
  have hd : differentIdeal ℤ (𝓞 ℚ) = ⊤ := Ideal.absNorm_eq_one_iff.mp (by
    rw [absNorm_differentIdeal ℚ, Rat.numberField_discr]; rfl)
  simp [hd]

section Normalization

/-- Use the canonical Borel σ-algebra on the actual local multiplicative group. -/
@[expose] public def rationalOrbitalPrimeTwoUnitMass : ℝ :=
  letI : MeasurableSpace K₂ˣ := borel _
  letI : BorelSpace K₂ˣ := ⟨rfl⟩
  (finiteCompletionMultiplicativeHaar v₂).real ((v₂).adicCompletionIntegers ℚ).units

private theorem primeTwo_unitRange : range (finiteCompletionUnitInclusion ℚ v₂) =
    ((v₂).adicCompletionIntegers ℚ).units := by
  ext x
  constructor
  · rintro ⟨u, rfl⟩
    exact ⟨u.val.property, u.inv.property⟩
  · intro hx
    let O := ((v₂).adicCompletionIntegers ℚ).toSubring.toSubmonoid
    exact ⟨O.unitsEquivUnitsType ⟨x, hx⟩, Units.ext rfl⟩

/-- Evaluate the real mass on the subgroup itself, for grh's actual
*discriminant-normalized* measure (not an arbitrary Haar probability). -/
public theorem rationalOrbitalPrimeTwo_unitMass :
    rationalOrbitalPrimeTwoUnitMass = 1 := by
  unfold rationalOrbitalPrimeTwoUnitMass
  rw [measureReal_def, ← primeTwo_unitRange, finiteCompletionMultiplicativeHaar_unitMass,
    rationalOrbital_differentExponent]
  simp

/-- The unshifted, measure-normalized term for the displayed place in (11.3.2.1). -/
@[expose] public def rationalOrbitalPrimeTwoRHS : ℂ :=
  (Real.log ((v₂).asIdeal.absNorm : ℝ) / rationalOrbitalPrimeTwoUnitMass : ℂ) *
    ∑' n : ℤ, φ (rationalOrbitalPrimeTwoClass ^ n)

public theorem rationalOrbitalPrimeTwo_rhs : rationalOrbitalPrimeTwoRHS = (Real.log 2 : ℂ) := by
  simp [rationalOrbitalPrimeTwoRHS, rationalOrbitalPrimeTwo_unitMass,
    rationalOrbitalPrimeTwoPlace_absNorm, rationalOrbitalPrimeTwoTest_zpow]

public theorem rationalOrbitalPrimeTwo_rhs_ne_zero : rationalOrbitalPrimeTwoRHS ≠ 0 := by
  rw [rationalOrbitalPrimeTwo_rhs]
  exact Complex.ofReal_ne_zero.mpr (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'

end Normalization

/-- The two algebraic base conditions involving ramification and Picard classes
for the empty finite part of the rational base. -/
public theorem rationalOrbital_emptyBase :
    (∀ v : V, v.asIdeal.ramificationIdx (𝓞 ℚ) = 1) ∧
    Subsingleton (CommRing.Pic ((∅ : Set V).integer ℚ)) := by
  constructor
  · intro v
    let : v.asIdeal.IsPrime := v.isPrime
    exact Ideal.ramificationIdx_eq_one _ _
  · rw [integer_empty]
    let R := (⊥ : Subalgebra (𝓞 ℚ) ℚ)
    let e : R ≃+* ℤ := (Algebra.botEquivOfInjective (IsFractionRing.injective (𝓞 ℚ) ℚ)
      ).toRingEquiv.trans Rat.ringOfIntegersEquiv
    let : IsPrincipalIdealRing R := IsPrincipalIdealRing.of_surjective e.symm e.symm.surjective
    exact inferInstanceAs (Subsingleton (CommRing.Pic R))

end
end Masullo
