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

open Filter NumberField IsDedekindDomain MeasureTheory
open scoped FourierTransform SchwartzMap Topology

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

/-- The joint unit-cut theta on any rational idele class is a four-term
inclusion-exclusion of the real lattice theta at scales `t`, `p*t`, `q*t`, and `p*q*t`. -/
public theorem rationalAdeleClassTheta_twoPrimeMasked_eq_rationalTheta
    (p q : Nat.Primes) (hpq : p ≠ q) (b : 𝓢(ℝ, ℂ)) (d : C) :
    let t := ideleClassNorm d
    rationalAdeleClassTheta (Set.indicator (rationalAdelePrimeUnits p ∩ rationalAdelePrimeUnits q)
      (rationalAdeleUnramified b)) d =
        (rationalTheta b t - rationalTheta b ((p : ℝ) * t)) -
          (rationalTheta b ((q : ℝ) * t) - rationalTheta b ((p : ℝ) * ((q : ℝ) * t))) := by
  dsimp only
  have hu (v : Nat.Primes) (x y : A) (hval : ∀ w, Valued.v (y.2 w) = Valued.v (x.2 w)) :
      y ∈ rationalAdelePrimeUnits v ↔ x ∈ rationalAdelePrimeUnits v := by
    change Valued.v (y.2 (vₚ v)) = 1 ↔ Valued.v (x.2 (vₚ v)) = 1
    rw [hval]
  have ht := ideleClassNorm_pos d
  have hqt : 0 < (q : ℝ) * ideleClassNorm d := mul_pos (Nat.cast_pos.mpr q.property.pos) ht
  rw [masked_theta_section _ (fun x y hv ↦ and_congr (hu p x y hv) (hu q x y hv)) b d,
    (rationalTheta_eq_twoPrimeMasked_idele_sum p q hpq b ht).2, rationalAdeleTheta,
    rationalAdeleTheta, (rationalTheta_eq_primeMasked_idele_sum p b ht).2,
    (rationalTheta_eq_primeMasked_idele_sum p b hqt).2]

/-- A profile with zero limit at infinity cannot be invariant under a strictly
expanding real dilation on the positive ray unless it vanishes there. -/
private theorem eq_zero_of_dilation_invariant {f : ℝ → ℂ} {r : ℝ} (hr : 1 < r)
    (h₀ : Tendsto f atTop (𝓝 0)) (hfix : ∀ t : ℝ, 0 < t → f t = f (r * t)) :
    ∀ t : ℝ, 0 < t → f t = 0 := by
  intro t ht
  have hr₀ : 0 < r := zero_lt_one.trans hr
  have hiter (n : ℕ) : f (r ^ n * t) = f t := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ', mul_assoc, ← hfix _ (mul_pos (pow_pos hr₀ n) ht), ih]
  have hscale : Tendsto (fun n : ℕ ↦ r ^ n * t) atTop atTop :=
    (tendsto_pow_atTop_atTop_of_one_lt hr).atTop_mul_const ht
  exact tendsto_nhds_unique tendsto_const_nhds ((h₀.comp hscale).congr hiter)

/-- Vanishing of the repaired joint unit-cut class theta forces the uncut
lattice theta to vanish at every positive scale. No zero modes are prescribed. -/
public theorem rationalTheta_eq_zero_of_twoPrimeMasked_classTheta_eq_zero
    (p q : Nat.Primes) (hpq : p ≠ q) (b : 𝓢(ℝ, ℂ))
    (hmask : ∀ d : C, rationalAdeleClassTheta (Set.indicator
      (rationalAdelePrimeUnits p ∩ rationalAdelePrimeUnits q) (rationalAdeleUnramified b)) d = 0) :
    ∀ t : ℝ, 0 < t → rationalTheta b t = 0 := by
  have hp : 1 < (p : ℝ) := Nat.one_lt_cast.mpr p.property.one_lt
  have hq : 1 < (q : ℝ) := Nat.one_lt_cast.mpr q.property.one_lt
  have hθ : Tendsto (rationalTheta b) atTop (𝓝 0) := by
    obtain ⟨K, _, h⟩ := rationalTheta_uniform_tail_bounds
      (Bornology.isVonNBounded_singleton (𝕜 := ℂ) b) 1
    refine squeeze_zero_norm' ?_ (tendsto_id.const_div_atTop K)
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
    simpa only [pow_one, id_eq] using (h b (Set.mem_singleton b)).1 t ht
  let g (t : ℝ) := rationalTheta b t - rationalTheta b ((p : ℝ) * t)
  have hg : Tendsto g atTop (𝓝 0) := by
    simpa only [g, sub_zero, Function.comp_def, id_eq] using
      hθ.sub (hθ.comp (tendsto_id.const_mul_atTop (zero_lt_one.trans hp)))
  have hgfix (t : ℝ) (ht : 0 < t) : g t = g ((q : ℝ) * t) := by
    have hnorm : ideleClassNorm (QuotientGroup.mk (σ t) : C) = t := by
      rw [ideleClassNorm_mk, ideleNorm_logSection]
      exact Real.exp_log ht
    have h := (rationalAdeleClassTheta_twoPrimeMasked_eq_rationalTheta p q hpq b
      (QuotientGroup.mk (σ t))).symm.trans (hmask (QuotientGroup.mk (σ t)))
    simpa only [g, hnorm] using sub_eq_zero.mp h
  have hgzero := eq_zero_of_dilation_invariant hq hg hgfix
  exact eq_zero_of_dilation_invariant hp hθ fun t ht ↦ sub_eq_zero.mp (hgzero t ht)

/-- For the repaired joint unit cut, the spatial constants cancel and the
small-norm main term has coefficient `(1 - p⁻¹) * (1 - q⁻¹)` times the real mass.
The error estimate is uniform in the idele class. -/
public theorem rationalAdeleClassTheta_twoPrimeMasked_small_norm
    (p q : Nat.Primes) (hpq : p ≠ q) (b : 𝓢(ℝ, ℂ)) (m : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ d : C,
      let t := ideleClassNorm d
      t ≤ 1 / ((p : ℝ) * (q : ℝ)) →
        ‖rationalAdeleClassTheta (Set.indicator
            (rationalAdelePrimeUnits p ∩ rationalAdelePrimeUnits q) (rationalAdeleUnramified b)) d -
          (t⁻¹ * (1 - (p : ℝ)⁻¹) * (1 - (q : ℝ)⁻¹)) • (∫ x : ℝ, b x)‖ ≤ K * t ^ m := by
  let P : ℝ := p
  let Q : ℝ := q
  have hp : 1 ≤ P := Nat.one_le_cast.mpr p.property.one_lt.le
  have hq : 1 ≤ Q := Nat.one_le_cast.mpr q.property.one_lt.le
  have hp₀ := zero_lt_one.trans_le hp
  have hq₀ := zero_lt_one.trans_le hq
  have hmass : (𝓕 b) 0 = ∫ x : ℝ, b x := by
    rw [congrFun (SchwartzMap.fourier_coe b) 0, Real.fourier_real_eq_integral_exp_smul]
    simp
  obtain ⟨B, hB, htail⟩ := rationalTheta_uniform_tail_bounds
    (Bornology.isVonNBounded_singleton (𝕜 := ℂ) b) m
  let R (s : ℝ) := rationalTheta b s - s⁻¹ • (𝓕 b) 0 + b 0
  refine ⟨4 * B * (P * Q) ^ m, by positivity, ?_⟩
  intro d t ht₁
  have ht : 0 < t := ideleClassNorm_pos d
  have hpt := mul_pos hp₀ ht
  have hqt := mul_pos hq₀ ht
  have hpqt := mul_pos hp₀ hqt
  have htop : P * (Q * t) ≤ 1 := by
    rw [← mul_assoc, mul_comm (P * Q), ← le_div_iff₀ (mul_pos hp₀ hq₀)]
    exact ht₁
  have htqt : t ≤ Q * t := le_mul_of_one_le_left ht.le hq
  have hptpqt : P * t ≤ P * (Q * t) := mul_le_mul_of_nonneg_left htqt hp₀.le
  have hqtpqt : Q * t ≤ P * (Q * t) := le_mul_of_one_le_left hqt.le hp
  have hbound {s : ℝ} (hs : 0 < s) (hle : s ≤ P * (Q * t)) :
      ‖R s‖ ≤ B * (P * (Q * t)) ^ m :=
    ((htail b (Set.mem_singleton b)).2 s hs (hle.trans htop)).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hs.le hle _) hB.le)
  have hcoeff : t⁻¹ - (P * t)⁻¹ - ((Q * t)⁻¹ - (P * (Q * t))⁻¹) =
      t⁻¹ * (1 - P⁻¹) * (1 - Q⁻¹) := by
    simp only [mul_inv_rev]
    ring
  rw [rationalAdeleClassTheta_twoPrimeMasked_eq_rationalTheta p q hpq b d, ← hmass]
  change ‖(rationalTheta b t - rationalTheta b (P * t)) -
    (rationalTheta b (Q * t) - rationalTheta b (P * (Q * t))) -
    (t⁻¹ * (1 - P⁻¹) * (1 - Q⁻¹)) • (𝓕 b) 0‖ ≤ _
  -- Expanding the real scalar difference leaves just the four remainders.
  have hrem : (rationalTheta b t - rationalTheta b (P * t)) -
      (rationalTheta b (Q * t) - rationalTheta b (P * (Q * t))) -
      (t⁻¹ * (1 - P⁻¹) * (1 - Q⁻¹)) • ((𝓕 b) 0 : ℂ) =
        (R t - R (P * t)) - (R (Q * t) - R (P * (Q * t))) := by
    rw [← hcoeff]
    simp only [sub_smul, R]
    abel
  rw [hrem]
  calc
    _ ≤ (‖R t‖ + ‖R (P * t)‖) + (‖R (Q * t)‖ + ‖R (P * (Q * t))‖) :=
      (norm_sub_le ..).trans (add_le_add (norm_sub_le ..) (norm_sub_le ..))
    _ ≤ (B * (P * (Q * t)) ^ m + B * (P * (Q * t)) ^ m) +
        (B * (P * (Q * t)) ^ m + B * (P * (Q * t)) ^ m) :=
      add_le_add (add_le_add (hbound ht (htqt.trans hqtpqt)) (hbound hpt hptpqt))
        (add_le_add (hbound hqt hqtpqt) (hbound hpqt le_rfl))
    _ = 4 * B * (P * Q) ^ m * t ^ m := by
      rw [← mul_assoc P, mul_pow]
      ring

end Masullo
