module

public import Theorems.RationalThetaFiniteUnitAverage
public import Theorems.RationalAdeleThetaInversion
import Lemmas.RationalAdeleAffineIntegral
import Mathlib.NumberTheory.ArithmeticFunction.Moebius

/-! # Reduction of finite-unit invariant rational tests to one real profile -/

open NumberField IsDedekindDomain MeasureTheory
open scoped Classical SchwartzMap FourierTransform

namespace Masullo

noncomputable section

local notation "A" => AdeleRing (𝓞 ℚ) ℚ
local notation "F" => FiniteAdeleRing (𝓞 ℚ) ℚ
local notation "J" => IdeleGroup (𝓞 ℚ) ℚ
local notation "C" => IdeleClassGroup (𝓞 ℚ) ℚ
local notation "V" => HeightOneSpectrum (𝓞 ℚ)
local notation "L[" v "]" => HeightOneSpectrum.adicCompletion ℚ v
local notation "O[" v "]" => HeightOneSpectrum.adicCompletionIntegers ℚ v
local notation "W" => rationalIntegralAdeles
local notation "ι" => algebraMap ℚ A
local notation "κ" => algebraMap ℚ F
local notation "unitIdele" => rationalFiniteUnitIdele
local notation "principal" => IdeleGroup.unitEmbedding (𝓞 ℚ) ℚ
local notation "S" => 𝓢(ℝ, ℂ)

private theorem local_unit_residue (v : V) {a m : ℕ} (h : a.Coprime m) :
    ∃ u : O[v]ˣ, (((u.val : O[v]) : L[v]) - (a : L[v])) * (m : L[v])⁻¹ ∈ O[v] := by
  have hc : IsCoprime (a : O[v]) (m : O[v]) := by
    simpa only [map_natCast, eq_intCast] using h.isCoprime.map (Int.castRingHom O[v])
  obtain ⟨r, s, hrs⟩ := hc
  rcases IsLocalRing.isUnit_or_isUnit_of_add_one hrs with ha | hm
  · obtain ⟨u, hu⟩ := isUnit_of_mul_isUnit_right ha
    refine ⟨u, ?_⟩
    rw [hu]
    simp
  · obtain ⟨w, hw⟩ := isUnit_of_mul_isUnit_right hm
    have he : ((↑(w⁻¹).val : L[v])) = (m : L[v])⁻¹ := by
      let k : O[v] →* L[v] := (O[v]).toSubring.subtype.toMonoidHom
      have he' := Units.val_inv_eq_inv_val (Units.map k w)
      change ((w⁻¹).val : L[v]) = ((w.val : L[v]))⁻¹ at he'
      rw [hw] at he'
      exact he'
    refine ⟨1, ?_⟩
    change (1 - (a : L[v])) * (m : L[v])⁻¹ ∈ O[v]
    rw [← he]
    exact (O[v]).mul_mem _ _ ((O[v]).toSubring.sub_mem (O[v]).one_mem
      (natCast_mem (O[v]).toSubring a)) (w⁻¹).val.property

private def slice {M : ℕ} (f : rationalAdeleSchwartzStage M) (d : ℕ) : S :=
  (f.property.2.2 (κ ((d : ℚ) / M))).choose

private theorem slice_apply {M : ℕ} (f : rationalAdeleSchwartzStage M) (d : ℕ) (t : ℝ) :
    slice f d t = f.val (rationalAdeleAt t (κ ((d : ℚ) / M))) :=
  (f.property.2.2 _).choose_spec t

private theorem scaled_gcd_cell {M : ℕ} (hM : 0 < M) (j : Fin (M ^ 2)) :
    ∃ u : RationalFiniteUnits, ∀ t : ℝ,
      (unitIdele u : A) * rationalAdeleAt t (κ (((j.val.gcd (M ^ 2) : ℕ) : ℚ) / M)) ∈
        rationalAdeleStageCell M j := by
  let d := j.val.gcd (M ^ 2)
  have hd := Nat.gcd_pos_of_pos_right j.val (pow_pos hM 2)
  have hM' : (M : ℚ) ≠ 0 := by exact_mod_cast hM.ne'
  have hd' : (d : ℚ) ≠ 0 := by exact_mod_cast hd.ne'
  let a := j.val / d
  let m := M ^ 2 / d
  have hc : a.Coprime m := Nat.coprime_div_gcd_div_gcd hd
  have ha : (j.val : ℚ) = (d : ℚ) * (a : ℚ) := by
    exact_mod_cast (Nat.mul_div_cancel' (Nat.gcd_dvd_left j.val (M ^ 2))).symm
  have hm : (M : ℚ)^2 = (d : ℚ) * (m : ℚ) := by
    exact_mod_cast (Nat.mul_div_cancel' (Nat.gcd_dvd_right j.val (M ^ 2))).symm
  have hm' : (m : ℚ) ≠ 0 := by
    intro h; rw [h, mul_zero] at hm; exact (pow_ne_zero 2 hM') hm
  choose u hu using fun v : V ↦ local_unit_residue v hc
  refine ⟨u, fun t v ↦ ?_⟩
  let k := algebraMap ℚ L[v]
  change (((ι (M : ℚ)⁻¹).2 * ((unitIdele u : A).2 * (rationalAdeleAt t _).2)) -
    (ι ((j.val : ℚ) / (M : ℚ)^2)).2) v ∈ O[v]
  rw [rationalAdeleAt_finite]
  have he (r : ℚ) : (ι r).2 v = k r := rfl
  have he' (r : ℚ) : κ r v = k r := rfl
  change (ι (M : ℚ)⁻¹).2 v * ((unitIdele u : A).2 v * κ ((d : ℚ) / M) v) -
    (ι ((j.val : ℚ) / (M : ℚ)^2)).2 v ∈ O[v]
  simp only [he, he']
  rw [rationalFiniteUnitIdele_apply_finite, ← mul_left_comm, ← map_mul,
    show (M : ℚ)⁻¹ * ((d : ℚ) / M) = (m : ℚ)⁻¹ by field_simp; linear_combination -hm,
    show (j.val : ℚ) / (M : ℚ)^2 = (a : ℚ) * (m : ℚ)⁻¹ by rw [ha, hm]; field_simp,
    map_mul, ← sub_mul]
  simpa only [k, map_inv₀, map_natCast] using hu v

/-- A finite-unit invariant test has just one real slice per gcd stratum of
`M⁻¹ ℤ̂ / M ℤ̂`, including the zero residue (gcd `M²`). -/
private theorem rationalAdeleStageSample_eq_gcd_slice {M : ℕ} (hM : 0 < M)
    (f : rationalAdeleSchwartzStage M)
    (hf : ∀ u : RationalFiniteUnits, ∀ x : A, f.val ((unitIdele u : A) * x) = f.val x)
    (j : Fin (M ^ 2)) :
    rationalAdeleStageSample M f j =
      (f.property.2.2 (κ (((j.val.gcd (M ^ 2) : ℕ) : ℚ) / M))).choose := by
  obtain ⟨u, hu⟩ := scaled_gcd_cell hM j
  ext t
  change rationalAdeleStageSample M f j t = slice f (j.val.gcd (M ^ 2)) t
  rw [slice_apply, ← hf u]
  have h := rationalAdeleStageSample_eq_on_cell hM f (hu t)
  have hr : rationalAdeleReal ((unitIdele u : A) *
      rationalAdeleAt t (κ (((j.val.gcd (M ^ 2) : ℕ) : ℚ) / M))) = t := by
    rw [rationalAdeleReal_apply]
    change InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace
      (((unitIdele u : A).1 * (rationalAdeleAt t _).1) Rat.infinitePlace) = t
    rw [rationalFiniteUnitIdele_fst, one_mul, ← rationalAdeleReal_apply, rationalAdeleReal_at]
  rwa [hr] at h

private theorem diag_div_mem_iff (j : ℕ) {d : ℕ} (hd : 0 < d) :
    ι ((j : ℚ) / d) ∈ W ↔ d ∣ j := by
  have hq : (d : ℚ) ≠ 0 := by exact_mod_cast hd.ne'
  rw [algebraMap_mem_rationalIntegralAdeles_iff]
  constructor
  · rintro ⟨z, hz⟩
    have he : (j : ℤ) = (d : ℤ) * z := by
      exact_mod_cast ((div_eq_iff hq).mp hz).trans (mul_comm (z : ℚ) (d : ℚ))
    exact Int.natCast_dvd_natCast.mp ⟨z, he⟩
  · rintro ⟨a, rfl⟩
    exact ⟨a, by push_cast; field_simp⟩

private theorem scaled_cell_mem_iff {M : ℕ} (hM : 0 < M) {d : ℕ} (hd : 0 < d)
    (hdvd : d ∣ M ^ 2) {x : A} {j : Fin (M ^ 2)} (hx : x ∈ rationalAdeleStageCell M j) :
    ι ((M : ℚ) / d) * x ∈ W ↔ d ∣ j.val := by
  change ι (M : ℚ)⁻¹ * x - ι ((j.val : ℚ) / (M : ℚ)^2) ∈ W at hx
  let m := M ^ 2 / d
  have hm : (M : ℚ)^2 = (d : ℚ) * (m : ℚ) := by
    exact_mod_cast (Nat.mul_div_cancel' hdvd).symm
  have hM' : (M : ℚ) ≠ 0 := by exact_mod_cast hM.ne'
  have hd' : (d : ℚ) ≠ 0 := by exact_mod_cast hd.ne'
  have he := rationalIntegralAdeles.nsmul_mem hx m
  rw [nsmul_eq_mul, ← map_natCast ι, mul_sub, ← mul_assoc, ← map_mul, ← map_mul,
    show (m : ℚ) * (M : ℚ)⁻¹ = (M : ℚ) / d by field_simp; linear_combination -hm,
    show (m : ℚ) * ((j.val : ℚ) / (M : ℚ)^2) = (j.val : ℚ) / d by
      field_simp; linear_combination -(j.val : ℚ) * hm] at he
  rw [← diag_div_mem_iff j.val hd]
  exact ⟨fun h ↦ by simpa only [sub_sub_cancel] using rationalIntegralAdeles.sub_mem h he,
    fun h ↦ by simpa only [sub_add_cancel] using rationalIntegralAdeles.add_mem he h⟩

private theorem stage_support_of_scaled_mem {M d : ℕ} (hd : 0 < d) {x : A}
    (hx : ι ((M : ℚ) / d) * x ∈ W) : x ∈ rationalAdeleStageSupport M := by
  have hd' : (d : ℚ) ≠ 0 := by exact_mod_cast hd.ne'
  have h := rationalIntegralAdeles.nsmul_mem hx d
  rw [nsmul_eq_mul, ← map_natCast ι, ← mul_assoc, ← map_mul,
    show (d : ℚ) * ((M : ℚ) / d) = M by field_simp, map_natCast] at h
  exact h

/-- Finite-unit invariant stage tests are finite sums of real Schwartz slices
on the centered finite balls `(d/M) ℤ̂`, for the positive divisors of `M²`. -/
public theorem exists_rationalAdeleStage_ball_decomposition {M : ℕ} (hM : 0 < M)
    (f : rationalAdeleSchwartzStage M)
    (hf : ∀ u : RationalFiniteUnits, ∀ x : A, f.val ((unitIdele u : A) * x) = f.val x) :
    ∃ c : ℕ → S, ∀ x : A,
      f.val x = ∑ d ∈ (M ^ 2).divisors,
        if ι ((M : ℚ) / d) * x ∈ W then c d (rationalAdeleReal x) else 0 := by
  classical
  let c (n : ℕ) : S := ∑ a ∈ n.divisorsAntidiagonal, ArithmeticFunction.moebius a.1 • slice f a.2
  have hc : ∀ n > 0, ∑ d ∈ n.divisors, c d = slice f n :=
    ArithmeticFunction.sum_eq_iff_sum_smul_moebius_eq.mpr fun _ _ ↦ rfl
  have hN : 0 < M ^ 2 := pow_pos hM 2
  refine ⟨c, fun x ↦ ?_⟩
  by_cases hx : x ∈ rationalAdeleStageSupport M
  · obtain ⟨j, hj, _⟩ := (mem_rationalAdeleStageSupport_iff_existsUnique_cell hM x).mp hx
    let g := j.val.gcd (M ^ 2)
    calc
      f.val x = slice f g (rationalAdeleReal x) := by
        rw [← rationalAdeleStageSample_eq_on_cell hM f hj, rationalAdeleStageSample_eq_gcd_slice hM f hf]
        rfl
      _ = ∑ d ∈ g.divisors, c d (rationalAdeleReal x) := by
        rw [← hc _ (Nat.gcd_pos_of_pos_right _ hN), sum_apply]
      _ = _ := by
        rw [← Nat.divisors_filter_dvd_of_dvd hN.ne' (Nat.gcd_dvd_right j.val (M ^ 2)), Finset.sum_filter]
        refine Finset.sum_congr rfl fun d hd ↦ ?_
        have hdd := (Nat.mem_divisors.mp hd).1
        have he := scaled_cell_mem_iff hM (Nat.pos_of_mem_divisors hd) hdd hj
        exact if_congr
          ⟨fun hh ↦ he.mpr (Nat.dvd_gcd_iff.mp hh).1, fun hh ↦ Nat.dvd_gcd (he.mp hh) hdd⟩ rfl rfl
  · rw [f.property.1 x hx, Finset.sum_eq_zero]
    intro d hd
    exact ite_eq_right fun h ↦ hx (stage_support_of_scaled_mem (Nat.pos_of_mem_divisors hd) h)

local notation "B" => rationalAdeleUnramified

private theorem real_mul (x y : A) :
    rationalAdeleReal (x * y) = rationalAdeleReal x * rationalAdeleReal y := by
  simp only [rationalAdeleReal_apply]
  exact map_mul (InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace) _ _

private theorem real_zero : rationalAdeleReal (0 : A) = 0 := by
  rw [rationalAdeleReal_apply]
  exact map_zero (InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace)

private theorem unramified_zero (b : S) : B b 0 = b 0 := by
  rw [rationalAdeleUnramified, Set.indicator_of_mem rationalIntegralAdeles.zero_mem, real_zero]

private def pull (r : ℚˣ) (f : A → ℂ) : A → ℂ := fun x ↦ f ((principal r : A) * x)

-- The same permutation works for the terms and for the absolute sums.
private theorem pull_term (r q : ℚˣ) (f : A → ℂ) (k : J) :
    pull r f ((principal q * k : J) : A) = f ((principal (q * r) * k : J) : A) := by
  simp only [pull, map_mul, Units.val_mul]
  rw [mul_left_comm, mul_assoc]

private theorem theta_pull (r : ℚˣ) (f : A → ℂ) (k : J) :
    rationalAdeleTheta (pull r f) k = rationalAdeleTheta f k := by
  simpa only [rationalAdeleTheta, pull_term, Equiv.coe_mulRight] using
    (Equiv.mulRight r).tsum_eq (fun q : ℚˣ ↦ f ((principal q * k : J) : A))

private theorem summable_pull (r : ℚˣ) (b : S) (k : J) :
    Summable (fun q : ℚˣ ↦ pull r (B b) ((principal q * k : J) : A)) := by
  simp only [pull_term]
  exact (Equiv.mulRight r).summable_iff.mpr (summable_norm_rationalAdeleUnramified_idele b k).of_norm

private theorem unramified_sum {ι₀ : Type*} (s : Finset ι₀) (b : ι₀ → S) (x : A) :
    B (∑ i ∈ s, b i) x = ∑ i ∈ s, B (b i) x := by
  by_cases hx : x ∈ W <;> simp [rationalAdeleUnramified, hx, sum_apply]

private theorem ball_pull {M d : ℕ} (hM : 0 < M) (hd : 0 < d) (c : S) (x : A) :
    let r := Units.mk0 ((M : ℚ) / d) (by positivity)
    let b := dilateSchwartz c ((d : ℝ) / M) (by positivity)
    pull r (B b) x = if ι ((M : ℚ) / d) * x ∈ W then c (rationalAdeleReal x) else 0 := by
  dsimp only
  change B (dilateSchwartz c _ _) (ι ((M : ℚ) / d) * x) = _
  by_cases hx : ι ((M : ℚ) / d) * x ∈ W
  · rw [rationalAdeleUnramified, Set.indicator_of_mem hx, ite_eq_left hx,
      dilateSchwartz_apply, real_mul, rationalAdeleReal_algebraMap]
    push_cast
    congr 1
    have hM' : (M : ℝ) ≠ 0 := by positivity
    have hd' : (d : ℝ) ≠ 0 := by positivity
    field_simp
  · rw [rationalAdeleUnramified, Set.indicator_of_notMem hx, ite_eq_right hx]

set_option linter.concreteInstances false
variable [MeasurableSpace A] [BorelSpace A]

private theorem fourier_zero (f : A → ℂ) :
    rationalAdeleFourier f 0 = ∫ x, f x ∂rationalAdeleAddHaar := by
  simp only [rationalAdeleFourier, mul_zero, AddChar.map_zero_eq_one, map_one, mul_one]

private theorem unramified_fourier_zero (b : S) : rationalAdeleFourier (B b) 0 = (𝓕 b) 0 := by
  rw [rationalAdeleFourier, integral_rationalAdeleUnramified_mul_conj_char, unramified_zero]

private theorem integral_pull (r : ℚˣ) (f : A → ℂ) :
    ∫ x, pull r f x ∂rationalAdeleAddHaar = ∫ x, f x ∂rationalAdeleAddHaar := by
  have hn : ideleNorm (principal r) = 1 := by
    rw [ideleNorm_apply]
    exact AdeleRing.norm_algebraMap_eq_one_of_ne_zero r.ne_zero
  symm
  simpa only [hn, zero_add, one_smul, pull] using integral_rationalAdele_affine f 0 (principal r)

private theorem integrable_pull (r : ℚˣ) (b : S) :
    Integrable (pull r (B b)) rationalAdeleAddHaar := by
  unfold pull
  simpa only [sub_zero, inv_inv] using
    integrable_rationalAdele_inv_affine (integrable_rationalAdeleUnramified b) 0 (principal r)⁻¹

private theorem normalize_sum {ι₀ : Type*} (s : Finset ι₀) (r : ι₀ → ℚˣ) (b : ι₀ → S) :
    let f : A → ℂ := fun x ↦ ∑ i ∈ s, pull (r i) (B (b i)) x
    let g := B (∑ i ∈ s, b i)
    rationalAdeleClassTheta f = rationalAdeleClassTheta g ∧ f 0 = g 0 ∧
      rationalAdeleFourier f 0 = rationalAdeleFourier g 0 := by
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · funext d
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective d
    rw [rationalAdeleClassTheta_mk, rationalAdeleClassTheta_mk]
    unfold rationalAdeleTheta
    simp_rw [unramified_sum]
    rw [Summable.tsum_finsetSum (fun i _ ↦ summable_pull (r i) (b i) k),
      Summable.tsum_finsetSum (fun i _ ↦ (summable_norm_rationalAdeleUnramified_idele (b i) k).of_norm)]
    exact Finset.sum_congr rfl (fun i _ ↦ theta_pull (r i) (B (b i)) k)
  · simp only [unramified_sum, pull, mul_zero]
  · simp only [fourier_zero, unramified_sum]
    rw [integral_finsetSum s (fun i _ ↦ integrable_pull (r i) (b i)),
      integral_finsetSum s (fun i _ ↦ integrable_rationalAdeleUnramified (b i))]
    exact Finset.sum_congr rfl (fun i _ ↦ integral_pull (r i) (B (b i)))

omit [MeasurableSpace A] [BorelSpace A] in
private theorem pull_neg_one (b : S) (x : A) :
    pull (-1) (B b) x = B (dilateSchwartz b (-1) (by norm_num)) x := by
  change B b (ι (-1) * x) = _
  rw [map_neg, map_one, neg_mul, one_mul]
  have hr : rationalAdeleReal (-x) = -rationalAdeleReal x := by
    simp only [rationalAdeleReal_apply]
    exact map_neg (InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace) _
  have hm : -x ∈ W ↔ x ∈ W := rationalIntegralAdeles.neg_mem_iff
  simp only [rationalAdeleUnramified, Set.indicator_apply, hr, dilateSchwartz_apply, neg_one_mul]
  exact if_congr hm rfl rfl

private theorem even_representative (a : S) :
    ∃ b : S, Function.Even b ∧
      rationalAdeleClassTheta (B a) = rationalAdeleClassTheta (B b) ∧ B a 0 = B b 0 ∧
      rationalAdeleFourier (B a) 0 = rationalAdeleFourier (B b) 0 := by
  let b := (2 : ℂ)⁻¹ • (a + dilateSchwartz a (-1) (by norm_num))
  have he (x : A) : B b x = (2 : ℂ)⁻¹ * (B a x + pull (-1) (B a) x) := by
    rw [pull_neg_one]
    by_cases hx : x ∈ W <;> simp [b, rationalAdeleUnramified, hx, smul_eq_mul, mul_add]
  refine ⟨b, fun t ↦ ?_, ?_, ?_, ?_⟩
  · simp only [b, smul_apply, add_apply, dilateSchwartz_apply, neg_one_mul, neg_neg, add_comm]
  · funext d
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective d
    rw [rationalAdeleClassTheta_mk, rationalAdeleClassTheta_mk]
    unfold rationalAdeleTheta
    simp_rw [he, tsum_mul_left]
    rw [Summable.tsum_add (summable_norm_rationalAdeleUnramified_idele a k).of_norm
      (summable_pull (-1) a k)]
    change rationalAdeleTheta (B a) k = (2 : ℂ)⁻¹ *
      (rationalAdeleTheta (B a) k + rationalAdeleTheta (pull (-1) (B a)) k)
    rw [theta_pull]
    ring
  · rw [he, pull, mul_zero]
    ring
  · simp only [fourier_zero, he]
    rw [integral_const_mul, integral_add (integrable_rationalAdeleUnramified a) (integrable_pull (-1) a),
      integral_pull (-1) (B a)]
    ring

/-- One even real Schwartz function realizes the class theta of a finite-unit
invariant stage test, with both adelic zero modes unchanged. -/
public theorem exists_rationalAdeleStage_even_profile {M : ℕ} (hM : 0 < M)
    (f : rationalAdeleSchwartzStage M)
    (hf : ∀ u : RationalFiniteUnits, ∀ x : A, f.val ((unitIdele u : A) * x) = f.val x) :
    ∃ b : S, Function.Even b ∧ rationalAdeleClassTheta f.val = rationalAdeleClassTheta (B b) ∧
      f.val 0 = b 0 ∧ rationalAdeleFourier f.val 0 = (𝓕 b) 0 := by
  obtain ⟨c, hc⟩ := exists_rationalAdeleStage_ball_decomposition hM f hf
  let r (d : ℕ) : ℚˣ := if hd : 0 < d then Units.mk0 ((M : ℚ) / d) (by positivity) else 1
  let b (d : ℕ) : S := if hd : 0 < d then dilateSchwartz (c d) ((d : ℝ) / M) (by positivity) else 0
  have hsum : f.val = fun x ↦ ∑ d ∈ (M ^ 2).divisors, pull (r d) (B (b d)) x := by
    funext x
    rw [hc]
    refine Finset.sum_congr rfl fun d hd ↦ ?_
    simpa only [r, b, dite_eq_left (Nat.pos_of_mem_divisors hd)] using
      (ball_pull hM (Nat.pos_of_mem_divisors hd) (c d) x).symm
  obtain ⟨hΘ, h₀, hF⟩ := normalize_sum (M ^ 2).divisors r b
  obtain ⟨v, hv, hΘ', h₀', hF'⟩ := even_representative (∑ d ∈ (M ^ 2).divisors, b d)
  exact ⟨v, hv, (hsum ▸ hΘ).trans hΘ', (hsum ▸ h₀).trans (h₀'.trans (unramified_zero v)),
    (hsum ▸ hF).trans (hF'.trans (unramified_fourier_zero v))⟩

omit [MeasurableSpace A] [BorelSpace A] in
/-- The actual class theta of an unramified tensor is the real integer theta
sum at the class norm, not merely a formula on the positive real section. -/
public theorem rationalAdeleClassTheta_unramified (b : S) (d : C) :
    rationalAdeleClassTheta (B b) d = rationalTheta b (ideleClassNorm d) := by
  obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective d
  rw [rationalAdeleClassTheta_mk, ideleClassNorm_mk, rationalAdeleTheta]
  rw [← (rationalTheta_eq_unramified_idele_sum b k).2]
  congr 1
  funext q
  rw [rationalThetaIdeleTerm, rationalAdeleUnramified, Set.indicator_apply, rationalAdeleReal_apply]
  rfl

local notation "E" => RationalAdeleSchwartzLF
local notation "Θ[" f "]" => rationalAdeleClassTheta (Subtype.val (RationalAdeleSchwartzLF.toUnion f))

/-- The finite-unit mean of any represented test is the unramified theta of
one even real Schwartz profile. Its two modes agree with those of the test
before averaging, even when they are nonzero. -/
public theorem exists_rationalAdeleFiniteUnitAverage_even_profile (f : E) :
    ∃ b : S, Function.Even b ∧ rationalAdeleClassThetaFiniteUnitAverage f = rationalAdeleClassTheta (B b) ∧
      f.toUnion.val 0 = b 0 ∧ rationalAdeleFourier f.toUnion.val 0 = (𝓕 b) 0 := by
  let g := rationalAdeleLFFiniteUnitAverage f
  obtain ⟨n, hn⟩ := mem_rationalAdeleSchwartzStageUnion.mp g.toUnion.property
  obtain ⟨b, hb, hΘ, h₀, hF⟩ := exists_rationalAdeleStage_even_profile
    (rationalAdeleFactorialLevel_pos n) ⟨g.toUnion.val, hn⟩
    (rationalAdeleLFFiniteUnitAverage_invariant f)
  obtain ⟨h₀', hF'⟩ := rationalAdeleLFFiniteUnitAverage_zero_modes f
  exact ⟨b, hb, (rationalAdeleClassTheta_LFFiniteUnitAverage f).symm.trans hΘ,
    h₀'.symm.trans h₀, hF'.symm.trans hF⟩

/-- Every actual radial two-mode adelic input has one even real two-mode
Schwartz representative, simultaneously on all idele classes. No
invariance of the original test function itself is required. -/
public theorem exists_rationalThetaRadialInput_even_profile (f : RationalThetaRadialInput) :
    ∃ b : S, Function.Even b ∧ b 0 = 0 ∧ (𝓕 b) 0 = 0 ∧
      ∀ d : C, Θ[f.val] d = rationalTheta b (ideleClassNorm d) := by
  obtain ⟨b, hb, hΘ, h₀, hF⟩ := exists_rationalAdeleFiniteUnitAverage_even_profile f.val
  obtain ⟨hf₀, hfF, hi⟩ := (mem_rationalThetaRadialInputSubmodule f.val).mp f.property
  rw [rationalAdeleClassThetaFiniteUnitAverage_of_invariant f.val hi] at hΘ
  exact ⟨b, hb, h₀.symm.trans hf₀, hF.symm.trans hfF,
    fun d ↦ (congrFun hΘ d).trans (rationalAdeleClassTheta_unramified b d)⟩

omit [MeasurableSpace A] [BorelSpace A] in
/-- Every unramified real Schwartz tensor already lives in the unit stage. -/
public theorem rationalAdeleUnramified_mem_stage_one (b : S) :
    B b ∈ rationalAdeleSchwartzStage 1 := by
  let f := (rationalAdeleStageCoordinates (M := 1) (by decide)).symm (fun _ ↦ b)
  suffices h : f.val = B b by rw [← h]; exact f.property
  funext x
  rw [show f.val = _ from rationalAdeleStageCoordinates_symm_eq_boxSum (M := 1) (by decide) _]
  simp [rationalAdeleBoxSum, rationalAdeleBox_stageCell, rationalAdeleStageCell, rationalAdeleUnramified]

omit [MeasurableSpace A] [BorelSpace A] in
private theorem exists_unramifiedLF (b : S) : ∃ f : E, f.toUnion.val = B b := by
  let e := rationalAdeleStageCoordinates (rationalAdeleFactorialLevel_pos 0)
  let u : rationalAdeleSchwartzStage (rationalAdeleFactorialLevel 0) :=
    ⟨B b, rationalAdeleUnramified_mem_stage_one b⟩
  refine ⟨rationalAdeleLFAssembly 0 (e u), ?_⟩
  rw [rationalAdeleLFAssembly_toUnion, rationalAdeleFactorialStageAssembly_val]
  change (e.symm (e u)).val = B b
  rw [e.symm_apply_apply]

/-- Exactly the algebraic class-theta image: every even real two-mode
profile occurs, and every radial output is of this form. -/
public theorem range_rationalThetaRadialInput_eq_even_profiles :
    Set.range (fun f : RationalThetaRadialInput ↦ Θ[f.val]) =
      Set.range (fun b : {b : S // Function.Even b ∧ b 0 = 0 ∧ (𝓕 b) 0 = 0} ↦
        fun d : C ↦ rationalTheta b.val (ideleClassNorm d)) := by
  refine Set.Subset.antisymm ?_ ?_
  · rintro _ ⟨f, rfl⟩
    obtain ⟨b, hb, h₀, hF, hΘ⟩ := exists_rationalThetaRadialInput_even_profile f
    exact ⟨⟨b, hb, h₀, hF⟩, (funext hΘ).symm⟩
  · rintro _ ⟨⟨b, _, h₀, hF⟩, rfl⟩
    obtain ⟨f, hf⟩ := exists_unramifiedLF b
    have hΘ : ∀ d : C, Θ[f] d = rationalTheta b (ideleClassNorm d) := by
      rw [hf]
      exact rationalAdeleClassTheta_unramified b
    refine ⟨⟨f, (mem_rationalThetaRadialInputSubmodule f).mpr ⟨?_, ?_, ?_⟩⟩, funext hΘ⟩
    · rw [hf, unramified_zero, h₀]
    · rw [hf, unramified_fourier_zero, hF]
    · intro k d
      have hk : ideleClassNorm (k : C) = 1 := (mem_rationalIdeleClassNormOne _).mp k.property
      rw [hΘ, hΘ, map_mul, hk, one_mul]

end

end Masullo
