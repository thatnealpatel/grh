module

public import Theorems.RationalAdelePrimeMaskLF

/-!
# The successive two-prime theta cut on rational idele classes

For the corrected disjoint tensor cut (Masullo, §1.3.2, p. 26), the terms
removed at `q` from the `p`-masked theta series ((2.2.3.1), p. 81) are
reindexed by multiplication by `q`. This preserves the condition of
being prime to `p` and replaces the real scale `t` by `q * t`. Both masks
are invariant under finite units, so the section identity gives the class
identity with inverse-uniformizer translation.
-/

open NumberField IsDedekindDomain
open scoped SchwartzMap

namespace Masullo

local notation "A" => AdeleRing (𝓞 ℚ) ℚ
local notation "J" => IdeleGroup (𝓞 ℚ) ℚ
local notation "C" => IdeleClassGroup (𝓞 ℚ) ℚ
local notation "vₚ" => Equiv.symm (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ))
local notation "E" => RationalAdeleSchwartzLF
local notation "ιˣ" => IdeleGroup.unitEmbedding (𝓞 ℚ) ℚ
local notation "σ" t => rationalIdeleLogSection (Multiplicative.ofAdd (Real.log t))

/-- The joint cut at distinct `p` and `q` is absolutely summable on the positive
section. Its theta is the `p`-masked theta minus its `q`-dilate. -/
public theorem rationalTheta_eq_twoPrimeMasked_idele_sum (p q : Nat.Primes) (hpq : p ≠ q)
    (b : 𝓢(ℝ, ℂ)) {t : ℝ} (ht : 0 < t) :
    Summable (fun r : ℚˣ ↦ ‖Set.indicator (rationalAdelePrimeUnits p ∩ rationalAdelePrimeUnits q)
      (rationalAdeleUnramified b) ((ιˣ r * σ t : J) : A)‖) ∧
      rationalAdeleTheta (Set.indicator (rationalAdelePrimeUnits p ∩ rationalAdelePrimeUnits q)
        (rationalAdeleUnramified b)) (σ t) =
        rationalAdeleTheta (rationalAdelePrimeMasked p b) (σ t) -
          rationalAdeleTheta (rationalAdelePrimeMasked p b) (σ ((q : ℝ) * t)) := by
  classical
  let a (s : ℝ) (r : ℚˣ) : A := ((ιˣ r * σ s : J) : A)
  let f (s : ℝ) (r : ℚˣ) := rationalAdelePrimeMasked p b (a s r)
  let U : Set ℚˣ := {r | a t r ∈ rationalAdelePrimeUnits q}
  let j (r : ℚˣ) := Set.indicator (rationalAdelePrimeUnits p ∩ rationalAdelePrimeUnits q)
    (rationalAdeleUnramified b) (a t r)
  have hjoint : j = U.indicator (f t) := by
    funext r
    simp only [j, Set.indicator_apply, Set.mem_inter_iff, U, Set.mem_ofPred_eq, f,
      rationalAdelePrimeMasked]
    by_cases h : a t r ∈ rationalAdelePrimeUnits q
    · simp only [h, and_true, ite_true]
    · simp only [h, and_false, ite_false]
  have hs : Summable (fun r ↦ ‖f t r‖) := (rationalTheta_eq_primeMasked_idele_sum p b ht).1
  have hsum (V : Set ℚˣ) : Summable (fun r ↦ ‖V.indicator (f t) r‖) := by
    refine Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun r ↦ ?_) hs
    by_cases hr : r ∈ V
    · rw [Set.indicator_of_mem hr]
    · rw [Set.indicator_of_notMem hr, norm_zero]
      exact norm_nonneg _
  change Summable (fun r ↦ ‖j r‖) ∧
    (∑' r, j r) = (∑' r, f t r) - (∑' r, f ((q : ℝ) * t) r)
  rw [hjoint]
  refine ⟨hsum U, ?_⟩
  let d := Uᶜ.indicator (f t)
  let P (v : Nat.Primes) (s : ℝ) : Set ℚˣ :=
    {r | a s r ∈ rationalAdelePrimeUnits v ∧ a s r ∈ rationalIntegralAdeles}
  have hP (v s r) : r ∈ P v s ↔ ∃ n : ℤ, (r : ℚ) = n ∧ ¬ (v : ℤ) ∣ n :=
    rationalAdelePrimeMasked_section_support_iff v s r
  have hf (s r) : f s r = if r ∈ P p s then b (rationalAdeleReal (a s r)) else 0 := by
    change (rationalAdelePrimeUnits p).indicator (rationalAdeleUnramified b) (a s r) = _
    simp only [rationalAdeleUnramified, Set.indicator_apply, P, Set.mem_ofPred_eq]
    split <;> split <;> simp_all
  have hU (r : ℚˣ) (hi : a t r ∈ rationalIntegralAdeles) {n : ℤ} (hn : (r : ℚ) = n) :
      r ∈ U ↔ ¬ (q : ℤ) ∣ n := by
    refine ⟨fun hr ↦ ?_, fun h ↦ ((hP q t r).mpr ⟨n, hn, h⟩).1⟩
    obtain ⟨m, hm, hqm⟩ := (hP q t r).mp ⟨hr, hi⟩
    have hmn : m = n := Int.cast_injective (hm.symm.trans hn)
    simpa only [hmn] using hqm
  have hcoprime (m : ℤ) : (p : ℤ) ∣ (q : ℤ) * m ↔ (p : ℤ) ∣ m := by
    have h : ¬ (p : ℤ) ∣ (q : ℤ) := by
      rw [Int.natCast_dvd_natCast, Nat.prime_dvd_prime_iff_eq p.property q.property]
      exact fun h ↦ hpq (Subtype.ext h)
    rw [(Nat.prime_iff_prime_int.mp p.property).dvd_mul, or_iff_right h]
  let Q : ℚˣ := Units.mk0 (q : ℚ) (Nat.cast_ne_zero.mpr q.property.ne_zero)
  let e := Equiv.mulLeft Q
  have he (r : ℚˣ) : (e r : ℚ) = (q : ℚ) * (r : ℚ) := rfl
  have he_int (r : ℚˣ) (m : ℤ) : (e r : ℚ) = ↑((q : ℤ) * m) ↔ (r : ℚ) = m := by
    rw [he, Int.cast_mul, Int.cast_natCast]
    exact (mul_right_injective₀ (Nat.cast_ne_zero.mpr q.property.ne_zero : (q : ℚ) ≠ 0)).eq_iff
  let s := (q : ℝ) * t
  have hs_pos : 0 < s := mul_pos (Nat.cast_pos.mpr q.property.pos) ht
  -- The dilation carries the kept indices at the new scale to the removed indices.
  have hsupport (r : ℚˣ) : e r ∈ P p t \ U ↔ r ∈ P p s := by
    constructor
    · rintro ⟨hp, hq⟩
      obtain ⟨n, hn, hpn⟩ := (hP p t (e r)).mp hp
      have hqn : (q : ℤ) ∣ n := by
        by_contra h
        exact hq ((hU (e r) hp.2 hn).mpr h)
      obtain ⟨m, rfl⟩ := hqn
      exact (hP p s r).mpr ⟨m, (he_int r m).mp hn, fun h ↦ hpn ((hcoprime m).mpr h)⟩
    · intro hr
      obtain ⟨m, hm, hpm⟩ := (hP p s r).mp hr
      have hn := (he_int r m).mpr hm
      have hp := (hP p t (e r)).mpr ⟨_, hn, fun h ↦ hpm ((hcoprime m).mp h)⟩
      exact ⟨hp, fun h ↦ (hU (e r) hp.2 hn).mp h (dvd_mul_right _ _)⟩
  have hd (r : ℚˣ) : d (e r) = f s r := by
    have hreal : rationalAdeleReal (a t (e r)) = rationalAdeleReal (a s r) := by
      rw [rationalAdeleReal_apply, rationalAdeleReal_apply]
      change rationalIdeleReal (ιˣ (e r) * σ t) = rationalIdeleReal (ιˣ r * σ s)
      simp only [rationalIdeleReal_principal_mul, rationalIdeleReal_logSection,
        toAdd_ofAdd, Real.exp_log ht, Real.exp_log hs_pos, he, Rat.cast_mul, Rat.cast_natCast, s]
      ac_rfl
    rw [show d (e r) = (P p t \ U).indicator (fun z ↦ b (rationalAdeleReal (a t z))) (e r) by
      simp only [d, Set.indicator_apply, Set.mem_compl_iff, Set.mem_sdiff, hf]
      by_cases hq : e r ∈ U <;> by_cases hp : e r ∈ P p t <;> simp [hq, hp]]
    simp only [Set.indicator_apply, hsupport, hreal, hf]
  have hd_sum : (∑' r, d r) = ∑' r, f s r := by
    rw [← e.tsum_eq d]
    exact tsum_congr hd
  change (∑' r, U.indicator (f t) r) = (∑' r, f t r) - (∑' r, f s r)
  rw [eq_sub_iff_add_eq, ← hd_sum, ← (hsum U).of_norm.tsum_add (hsum Uᶜ).of_norm]
  refine tsum_congr fun r ↦ ?_
  by_cases hr : r ∈ U
  · simp only [Set.indicator_of_mem hr, Set.indicator_of_notMem (show r ∉ Uᶜ from fun h ↦ h hr),
      add_zero]
  · simp only [Set.indicator_of_notMem hr, Set.indicator_of_mem (show r ∈ Uᶜ from hr), zero_add]

/-- The section identity holds for actual LF witnesses of both masks of a
supplied unramified tensor, with no moment or parity assumptions. -/
public theorem exists_rationalAdeleUnramifiedTwoPrimeCutSection (p q : Nat.Primes) (hpq : p ≠ q)
    (b : 𝓢(ℝ, ℂ)) (f : E) (hf : f.toUnion.val = rationalAdeleUnramified b) :
    ∃ g h : E, g.toUnion.val = rationalAdelePrimeMasked p b ∧
      h.toUnion.val = Set.indicator (rationalAdelePrimeUnits p ∩ rationalAdelePrimeUnits q) f.toUnion.val ∧
      ∀ (t : ℝ), 0 < t →
        Summable (fun r : ℚˣ ↦ ‖h.toUnion.val ((ιˣ r * σ t : J) : A)‖) ∧
        rationalAdeleTheta h.toUnion.val (σ t) =
          rationalAdeleTheta g.toUnion.val (σ t) - rationalAdeleTheta g.toUnion.val (σ ((q : ℝ) * t)) := by
  obtain ⟨g, hg⟩ := exists_rationalAdelePrimeMaskedLF p b
  obtain ⟨h, hh⟩ := exists_rationalAdeleUnramifiedTwoPrimeMaskLF p q b f hf
  refine ⟨g, h, hg, hh, fun t ht ↦ ?_⟩
  rw [hh, hg, hf]
  exact rationalTheta_eq_twoPrimeMasked_idele_sum p q hpq b ht

private theorem masked_theta_section (U : Set A)
    (hU : ∀ (x y : A), (∀ v, Valued.v (y.2 v) = Valued.v (x.2 v)) → (y ∈ U ↔ x ∈ U))
    (b : 𝓢(ℝ, ℂ)) (d : C) :
    rationalAdeleClassTheta (U.indicator (rationalAdeleUnramified b)) d =
      rationalAdeleTheta (U.indicator (rationalAdeleUnramified b)) (σ (ideleClassNorm d)) := by
  classical
  let f := U.indicator (rationalAdeleUnramified b)
  have hmul (u : RationalFiniteUnits) (x : A) : f ((rationalFiniteUnitIdele u : A) * x) = f x := by
    let y := (rationalFiniteUnitIdele u : A) * x
    have hval (v : HeightOneSpectrum (𝓞 ℚ)) : Valued.v (y.2 v) = Valued.v (x.2 v) := by
      change Valued.v ((rationalFiniteUnitIdele u : A).2 v * x.2 v) = _
      rw [map_mul, rationalFiniteUnitIdele_apply_finite,
        HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one.mp (u v).isUnit,
        one_mul]
    have hw : y ∈ (rationalIntegralAdeles : Set A) ↔ x ∈ (rationalIntegralAdeles : Set A) := by
      change (∀ v, y.2 v ∈ v.adicCompletionIntegers ℚ) ↔
        (∀ v, x.2 v ∈ v.adicCompletionIntegers ℚ)
      simp only [HeightOneSpectrum.mem_adicCompletionIntegers, hval]
    have hr : rationalAdeleReal y = rationalAdeleReal x := by
      rw [rationalAdeleReal_apply, rationalAdeleReal_apply]
      change InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace
        (((rationalFiniteUnitIdele u : A).1 * x.1) Rat.infinitePlace) = _
      rw [rationalFiniteUnitIdele_fst, one_mul]
    change f y = f x
    simp only [f, Set.indicator_apply, rationalAdeleUnramified, hU x y hval, hw, hr]
  have hradial := (rationalIdeleClass_normOne_invariant_iff (rationalAdeleClassTheta f)).mp
    ((rationalIdeleClass_normOne_invariant_iff_finiteUnits _).mpr (by
      intro u c
      obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective c
      rw [rationalFiniteUnitClass_coe, ← QuotientGroup.mk_mul,
        rationalAdeleClassTheta_mk, rationalAdeleClassTheta_mk]
      refine tsum_congr fun r ↦ ?_
      rw [mul_left_comm (ιˣ r), Units.val_mul, hmul]))
  rw [hradial d]
  change rationalAdeleClassTheta f (rationalIdeleClassLogSection
    (Multiplicative.ofAdd (Real.log (ideleClassNorm d)))) = _
  rw [rationalIdeleClassLogSection_apply, rationalAdeleClassTheta_mk]

/-- The joint tensor cut at distinct `p` and `q` is the inverse-`q`-uniformizer
class theta difference of the single cut at `p`. -/
public theorem rationalAdeleClassTheta_twoPrimeMasked (p q : Nat.Primes) (hpq : p ≠ q)
    (b : 𝓢(ℝ, ℂ)) (d : C) :
    rationalAdeleClassTheta (Set.indicator (rationalAdelePrimeUnits p ∩ rationalAdelePrimeUnits q)
      (rationalAdeleUnramified b)) d =
        rationalAdeleClassTheta (rationalAdelePrimeMasked p b) d -
          rationalAdeleClassTheta (rationalAdelePrimeMasked p b)
            ((QuotientGroup.mk (rationalThetaRadialUniformizer (vₚ q)) : C)⁻¹ * d) := by
  have hu (v : Nat.Primes) (x y : A) (hval : ∀ w, Valued.v (y.2 w) = Valued.v (x.2 w)) :
      y ∈ rationalAdelePrimeUnits v ↔ x ∈ rationalAdelePrimeUnits v := by
    change Valued.v (y.2 (vₚ v)) = 1 ↔ Valued.v (x.2 (vₚ v)) = 1
    rw [hval]
  have hsingle := masked_theta_section (rationalAdelePrimeUnits p) (hu p) b
  have hjoint := masked_theta_section (rationalAdelePrimeUnits p ∩ rationalAdelePrimeUnits q)
    (fun x y hv ↦ and_congr (hu p x y hv) (hu q x y hv)) b
  have hq : Rat.HeightOneSpectrum.primesEquiv (vₚ q) = q :=
    (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).apply_symm_apply q
  have hnorm : ideleClassNorm ((QuotientGroup.mk (rationalThetaRadialUniformizer (vₚ q)) : C)⁻¹ * d) =
      (q : ℝ) * ideleClassNorm d := by
    rw [map_mul, map_inv, ideleClassNorm_mk, ideleNorm_rationalThetaRadialUniformizer, inv_inv, hq]
  rw [hjoint d, rationalAdelePrimeMasked, hsingle d, hsingle _, hnorm]
  exact (rationalTheta_eq_twoPrimeMasked_idele_sum p q hpq b (ideleClassNorm_pos d)).2

end Masullo
