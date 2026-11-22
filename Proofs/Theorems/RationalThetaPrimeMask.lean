module

public import Theorems.RationalAdeleUnramifiedPeriodization
public import Theorems.RationalIdeleLogSection
public import Theorems.RationalThetaNormFiber

/-!
# A finite prime-unit mask on the rational theta tensor

At the positive section of the idelic norm, replacing the finite integral-ball
factor at `p` by its unit-group indicator keeps exactly the nonzero integers
not divisible by `p` in the theta sum (Masullo, (2.2.3.1), pp. 81–82).
-/

open NumberField IsDedekindDomain
open scoped Classical SchwartzMap

namespace Masullo

local notation "A" => AdeleRing (𝓞 ℚ) ℚ
local notation "J" => IdeleGroup (𝓞 ℚ) ℚ
local notation "vₚ" => Equiv.symm (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ))
local notation "ι" => algebraMap ℚ A
local notation "ιˣ" => IdeleGroup.unitEmbedding (𝓞 ℚ) ℚ
local notation "σ" t => rationalIdeleLogSection (Multiplicative.ofAdd (Real.log t))

/-- Adeles whose coordinate at `p` is an integral unit, expressed by the
valuation-one criterion in the local completion. -/
@[expose] public def rationalAdelePrimeUnits (p : Nat.Primes) : Set A :=
  {a | Valued.v (a.2 (vₚ p)) = 1}

/-- The unramified tensor with its finite factor at `p` restricted to the local units. -/
@[expose] public noncomputable def rationalAdelePrimeMasked (p : Nat.Primes) (b : 𝓢(ℝ, ℂ)) : A → ℂ :=
  (rationalAdelePrimeUnits p).indicator (rationalAdeleUnramified b)

private theorem primeUnit_intCast_iff (p : Nat.Primes) (n : ℤ) :
    ι (n : ℚ) ∈ rationalAdelePrimeUnits p ↔ ¬ (p : ℤ) ∣ n := by
  let v := vₚ p
  change Valued.v ((ι (n : ℚ)).2 v) = 1 ↔ _
  rw [AdeleRing.algebraMap_snd_apply]
  change Valued.v (algebraMap ℚ (v.adicCompletion ℚ) (n : ℚ)) = 1 ↔ _
  rw [map_intCast]
  rw [← show ((n : v.adicCompletionIntegers ℚ) : v.adicCompletion ℚ) = (n : v.adicCompletion ℚ)
    from map_intCast (v.adicCompletionIntegers ℚ).toSubring.subtype n,
    ← HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one]
  let _ : Fact (p : ℕ).Prime := ⟨p.property⟩
  let e := (PadicInt.adicCompletionIntegersEquiv (𝓞 ℚ) p).symm
  rw [← MulEquiv.isUnit_map e.toRingEquiv, map_intCast]
  exact not_not.symm.trans (not_congr
    (PadicInt.not_isUnit_iff.trans (PadicInt.norm_int_lt_one_iff_dvd n)))

private theorem section_finite (t : ℝ) (q : ℚˣ) (v : HeightOneSpectrum (𝓞 ℚ)) :
    ((ιˣ q * σ t : J) : A).2 v = (ι (q : ℚ)).2 v := by
  change (ι (q : ℚ)).2 v * ((σ t : J) : A).2 v = _
  rw [rationalIdeleLogSection_finite, mul_one]

private theorem section_primeUnit_iff (p : Nat.Primes) (t : ℝ) (q : ℚˣ) {n : ℤ}
    (hn : (q : ℚ) = n) :
    ((ιˣ q * σ t : J) : A) ∈ rationalAdelePrimeUnits p ↔ ¬ (p : ℤ) ∣ n := by
  change Valued.v (((ιˣ q * σ t : J) : A).2 (vₚ p)) = 1 ↔ _
  rw [section_finite, hn]
  exact primeUnit_intCast_iff p n

private theorem section_integral_iff (t : ℝ) (q : ℚˣ) :
    ((ιˣ q * σ t : J) : A) ∈ rationalIntegralAdeles ↔ ∃ n : ℤ, (q : ℚ) = n := by
  rw [← algebraMap_mem_rationalIntegralAdeles_iff]
  change (∀ v, ((ιˣ q * σ t : J) : A).2 v ∈ v.adicCompletionIntegers ℚ) ↔
    (∀ v, (ι (q : ℚ)).2 v ∈ v.adicCompletionIntegers ℚ)
  simp only [section_finite]

/-- The finite support condition for the prime-masked unramified tensor on
the section selects exactly the nonzero integer indices prime to `p`.
This condition is independent of the real scale. -/
public theorem rationalAdelePrimeMasked_section_support_iff (p : Nat.Primes) (t : ℝ) (q : ℚˣ) :
    (((ιˣ q * σ t : J) : A) ∈ rationalAdelePrimeUnits p ∧
      ((ιˣ q * σ t : J) : A) ∈ rationalIntegralAdeles) ↔
    ∃ n : ℤ, (q : ℚ) = n ∧ ¬ (p : ℤ) ∣ n := by
  rw [section_integral_iff]
  constructor
  · rintro ⟨hu, n, hn⟩
    exact ⟨n, hn, (section_primeUnit_iff p t q hn).mp hu⟩
  · rintro ⟨n, hn, hp⟩
    exact ⟨(section_primeUnit_iff p t q hn).mpr hp, n, hn⟩

private theorem thetaIdeleTerm_eq_unramified (b : 𝓢(ℝ, ℂ)) (a : J) (q : ℚˣ) :
    rationalThetaIdeleTerm b a q = rationalAdeleUnramified b ((ιˣ q * a : J) : A) := by
  rw [rationalThetaIdeleTerm, rationalAdeleUnramified, Set.indicator_apply, rationalAdeleReal_apply]
  rfl

/-- The actual prime-masked adelic theta series on the positive section is
absolutely summable and equals the unramified theta series less its `p`-dilate. -/
public theorem rationalTheta_eq_primeMasked_idele_sum (p : Nat.Primes) (b : 𝓢(ℝ, ℂ))
    {t : ℝ} (ht : 0 < t) :
    Summable (fun q : ℚˣ ↦ ‖rationalAdelePrimeMasked p b ((ιˣ q * σ t : J) : A)‖) ∧
      (∑' q : ℚˣ, rationalAdelePrimeMasked p b ((ιˣ q * σ t : J) : A)) =
        rationalTheta b t - rationalTheta b ((p : ℝ) * t) := by
  let a (q : ℚˣ) : A := ((ιˣ q * σ t : J) : A)
  let f (q : ℚˣ) : ℂ := rationalAdeleUnramified b (a q)
  let S : Set ℚˣ := {q | a q ∈ rationalAdelePrimeUnits p}
  let d := Sᶜ.indicator f
  change Summable (fun q ↦ ‖S.indicator f q‖) ∧
    (∑' q, S.indicator f q) = rationalTheta b t - rationalTheta b ((p : ℝ) * t)
  obtain ⟨hs, htotal⟩ := rationalTheta_eq_unramified_idele_sum b (σ t)
  simp only [thetaIdeleTerm_eq_unramified, ideleNorm_logSection,
    toAdd_ofAdd, Real.exp_log ht] at hs htotal
  change Summable (fun q ↦ ‖f q‖) at hs
  change (∑' q, f q) = rationalTheta b t at htotal
  have hsum (U : Set ℚˣ) : Summable (fun q ↦ ‖U.indicator f q‖) := by
    refine Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun q ↦ ?_) hs
    by_cases hq : q ∈ U <;> simp [hq]
  refine ⟨hsum S, ?_⟩
  -- Enumerate the removed indices by multiplying the nonzero integers by `p`.
  have hp : (p : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr p.property.ne_zero
  let e (n : {n : ℤ // n ≠ 0}) : ℚˣ :=
    Units.mk0 (↑((p : ℤ) * (n : ℤ)) : ℚ) (Int.cast_ne_zero.mpr (mul_ne_zero hp n.property))
  have he : Function.Injective e := by
    intro m n h
    have hcast : (↑((p : ℤ) * (m : ℤ)) : ℚ) = (↑((p : ℤ) * (n : ℤ)) : ℚ) :=
      congrArg Units.val h
    exact Subtype.ext (mul_left_cancel₀ hp (Int.cast_injective hcast))
  have hd_zero (q : ℚˣ) (hq : q ∉ Set.range e) : d q = 0 := by
    by_cases hu : q ∈ S
    · exact Set.indicator_of_notMem (fun h : q ∈ Sᶜ ↦ h hu) _
    change Sᶜ.indicator f q = 0
    rw [Set.indicator_of_mem (show q ∈ Sᶜ from hu)]
    apply Set.indicator_of_notMem
    intro hi
    obtain ⟨n, hn⟩ := (section_integral_iff t q).mp hi
    have hn_dvd : (p : ℤ) ∣ n := by
      by_contra hnd
      exact hu ((section_primeUnit_iff p t q hn).mpr hnd)
    obtain ⟨m, hm⟩ := hn_dvd
    have hm₀ : m ≠ 0 := by
      intro hz
      exact q.ne_zero (by simp [hn, hm, hz])
    exact hq ⟨⟨m, hm₀⟩, Units.ext (by simpa only [e, Units.val_mk0, hm] using hn.symm)⟩
  have hd_sample (n : {n : ℤ // n ≠ 0}) : d (e n) = b (((p : ℝ) * t) * (n : ℤ)) := by
    have hn : (e n : ℚ) = (↑((p : ℤ) * (n : ℤ)) : ℚ) := rfl
    have hu : e n ∈ Sᶜ := fun h ↦
      (section_primeUnit_iff p t (e n) hn).mp h (dvd_mul_right _ _)
    have hi : a (e n) ∈ rationalIntegralAdeles := (section_integral_iff t (e n)).mpr ⟨_, hn⟩
    change Sᶜ.indicator f (e n) = _
    rw [Set.indicator_of_mem hu]
    change rationalAdeleUnramified b (a (e n)) = _
    rw [rationalAdeleUnramified, Set.indicator_of_mem hi, rationalAdeleReal_apply]
    change b (rationalIdeleReal (ιˣ (e n) * σ t)) = _
    rw [rationalIdeleReal_principal_mul, rationalIdeleReal_logSection,
      toAdd_ofAdd, Real.exp_log ht, hn, Rat.cast_intCast, Int.cast_mul,
      Int.cast_natCast, mul_right_comm]
  have hd : (∑' q, d q) = rationalTheta b ((p : ℝ) * t) := by
    rw [← he.tsum_eq (fun q hq ↦ by by_contra h; exact hq (hd_zero q h))]
    simp only [hd_sample, rationalTheta]
  rw [eq_sub_iff_add_eq, ← hd, ← (hsum S).of_norm.tsum_add (hsum Sᶜ).of_norm, ← htotal]
  exact tsum_congr (fun q ↦ by
    by_cases hq : q ∈ S <;> simp [hq])

end Masullo
