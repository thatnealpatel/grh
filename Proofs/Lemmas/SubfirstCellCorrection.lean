module

public import Lemmas.SignedSampleCellCorrection
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SumIntegralComparisons

/-!
# Sub-first moments for the signed sample cell correction

Source: `6596fa6e00f4:.godel/conjectures/closed/triangular-weighted-character-zero-divisors.md:140–173`.
Owning check session: `01a20f35-88fa-72a0-aedd-8c10c7068d1c`.

Scope: the compact-uniform sublinear bound on the unit-cell correction, and normal
convergence and holomorphy of the weighted corrections using only moments of order
`0 ≤ v < 1`. No pole or recovery assertion is included.
-/

open Filter MeasureTheory Set
open scoped Interval
open SignedSampleCellCorrection (cell exponent correction halfPlane absolute_tail
  correction_holomorphic)

namespace SubfirstCellCorrection

private theorem norm_cell_le_prefix {n e : ℝ} (hn : 1 ≤ n) (he : 0 ≤ e) {w : ℂ}
    (hew : e ≤ w.re) : ‖cell n w‖ ≤ 2 * n ^ (-e) := by
  have hn0 : 0 < n := zero_lt_one.trans_le hn
  have hpow (x : ℝ) (hx : n ≤ x) : ‖(x : ℂ) ^ (-w)‖ ≤ n ^ (-e) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (hn0.trans_le hx), Complex.neg_re]
    exact (Real.rpow_le_rpow_of_exponent_le (hn.trans hx) (neg_le_neg hew)).trans
      (Real.rpow_le_rpow_of_nonpos hn0 hx (neg_nonpos.mpr he))
  have hint : ‖∫ x : ℝ in n..n + 1, (x : ℂ) ^ (-w)‖ ≤ n ^ (-e) := by
    have hab : n ≤ n + 1 := by linarith
    have h := intervalIntegral.norm_integral_le_of_norm_le_const
      (f := fun x : ℝ => (x : ℂ) ^ (-w)) (C := n ^ (-e)) (fun x hx => by
        rw [uIoc_of_le hab] at hx
        exact hpow x hx.1.le)
    simpa only [show n + 1 - n = 1 by ring, abs_one, mul_one] using h
  unfold cell
  exact (norm_sub_le _ _).trans (by linarith [hpow n le_rfl])

private theorem sum_prefix_rpow_le (N : ℕ) {e : ℝ} (he : 0 ≤ e) (he1 : e < 1) :
    (∑ j ∈ Finset.range N, (↑(1 + j) : ℝ) ^ (-e)) ≤ (N : ℝ) ^ (1 - e) / (1 - e) := by
  have hp : -1 < -e := by linarith
  have hanti : AntitoneOn (fun x : ℝ => x ^ (-e)) (Ioc 0 ((0 : ℝ) + (N : ℝ))) :=
    fun _ hx _ _ hxy => Real.rpow_le_rpow_of_nonpos hx.1 hxy (neg_nonpos.mpr he)
  have hint : IntegrableOn (fun x : ℝ => x ^ (-e)) (Icc 0 ((0 : ℝ) + (N : ℝ))) := by
    rw [integrableOn_Icc_iff_integrableOn_Ioc,
      ← intervalIntegrable_iff_integrableOn_Ioc_of_le (by positivity)]
    exact intervalIntegral.intervalIntegrable_rpow' hp
  calc
    _ ≤ ∫ x : ℝ in 0..(N : ℝ), x ^ (-e) := by
      simpa only [zero_add, Nat.add_comm _ 1] using hanti.sum_le_integral_of_integrableOn hint
    _ = _ := by
      rw [integral_rpow (Or.inl hp), show -e + 1 = 1 - e by ring,
        Real.zero_rpow (by linarith : 1 - e ≠ 0), sub_zero]

/-- Split before cell `L = 1 + ⌈‖w‖⌉`. Bound the prefix without differentiating,
and use the absolute unit-cell tail starting at `L`. -/
private theorem norm_scaled_cellSum_le (B : ℕ) {δ e : ℝ} (hδ : 0 < δ) (he : 0 ≤ e)
    (he1 : e < 1) (heδ : e ≤ δ) {w : ℂ} (hw : δ ≤ w.re) :
    ‖(B : ℂ) * ∑' j : ℕ, cell (↑(1 + j) : ℝ) w‖ ≤
      ((B : ℝ) * 2 / (1 - e) + (B : ℝ) / δ) * (2 + ‖w‖) ^ (1 - e) := by
  let N : ℕ := ⌈‖w‖⌉₊
  let L : ℕ := 1 + N
  have hL : 1 ≤ L := Nat.le_add_right 1 N
  have hLr : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hL0 : (0 : ℝ) < L := zero_lt_one.trans_le hLr
  have hNL : (N : ℝ) ≤ L := by
    simp [L, Nat.cast_add]
  have hnw : ‖w‖ ≤ (L : ℝ) := (Nat.le_ceil ‖w‖).trans hNL
  have hLw : (L : ℝ) ≤ 2 + ‖w‖ := by
    have h := Nat.ceil_lt_add_one (norm_nonneg w)
    simp only [L, Nat.cast_add, Nat.cast_one]
    change (N : ℝ) < ‖w‖ + 1 at h
    linarith
  have hv : 0 < 1 - e := sub_pos.mpr he1
  have hw0 : 0 < w.re := hδ.trans_le hw
  have hprefix :
      (∑ j ∈ Finset.range N, (B : ℝ) * ‖cell (↑(1 + j) : ℝ) w‖) ≤
        ((B : ℝ) * 2 / (1 - e)) * (L : ℝ) ^ (1 - e) := by
    calc
      _ ≤ (B : ℝ) * 2 * ∑ j ∈ Finset.range N, (↑(1 + j) : ℝ) ^ (-e) := by
        rw [Finset.mul_sum]
        refine Finset.sum_le_sum fun j _ => ?_
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left (norm_cell_le_prefix (by simp [Nat.cast_add])
          he (heδ.trans hw)) (Nat.cast_nonneg B)
      _ ≤ (B : ℝ) * 2 * ((N : ℝ) ^ (1 - e) / (1 - e)) :=
        mul_le_mul_of_nonneg_left (sum_prefix_rpow_le N he he1) (by positivity)
      _ ≤ (B : ℝ) * 2 * ((L : ℝ) ^ (1 - e) / (1 - e)) :=
        mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right
          (Real.rpow_le_rpow (Nat.cast_nonneg N) hNL hv.le) hv.le) (by positivity)
      _ = _ := by ring
  have htail : (∑' j : ℕ, (B : ℝ) * ‖cell (↑(L + j) : ℝ) w‖) ≤
      ((B : ℝ) / δ) * (L : ℝ) ^ (1 - e) := by
    calc
      _ ≤ (B : ℝ) * ‖w‖ * (L : ℝ) ^ (-w.re) / w.re := (absolute_tail B L hL hw0).2
      _ ≤ (B : ℝ) * ‖w‖ * (L : ℝ) ^ (-w.re) / δ :=
        div_le_div_of_nonneg_left (by positivity) hδ hw
      _ ≤ (B : ℝ) * (L : ℝ) * (L : ℝ) ^ (-e) / δ := by
        refine div_le_div_of_nonneg_right (mul_le_mul
          (mul_le_mul_of_nonneg_left hnw (Nat.cast_nonneg B))
          (Real.rpow_le_rpow_of_exponent_le hLr (neg_le_neg (heδ.trans hw)))
          (by positivity) (by positivity)) hδ.le
      _ = _ := by
        rw [sub_eq_add_neg, Real.rpow_add hL0, Real.rpow_one]
        ring
  have habs : Summable (fun j : ℕ => ‖cell (↑(1 + j) : ℝ) w‖) := by
    simpa only [Nat.cast_one, one_mul] using (absolute_tail 1 1 le_rfl hw0).1
  calc
    _ ≤ ∑' j : ℕ, (B : ℝ) * ‖cell (↑(1 + j) : ℝ) w‖ := by
      rw [norm_mul, Complex.norm_natCast, tsum_mul_left]
      exact mul_le_mul_of_nonneg_left (norm_tsum_le_tsum_norm habs) (Nat.cast_nonneg B)
    _ = (∑ j ∈ Finset.range N, (B : ℝ) * ‖cell (↑(1 + j) : ℝ) w‖) +
        ∑' j : ℕ, (B : ℝ) * ‖cell (↑(L + j) : ℝ) w‖ := by
      simpa only [L, Nat.add_assoc, Nat.add_comm N] using
        ((absolute_tail B 1 le_rfl hw0).1.sum_add_tsum_nat_add N).symm
    _ ≤ _ := (add_le_add hprefix htail).trans (by
      rw [← add_mul]
      exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hL0.le hLw hv.le) (by positivity))

private def margin (B : ℕ) (a : ℝ) (s : ℂ) : ℝ := 1 + (B : ℝ) * (s.re - a)

private theorem margin_pos {B : ℕ} (hB : 1 ≤ B) {a : ℝ} {s : ℂ}
    (hs : s ∈ halfPlane B a) : 0 < margin B a s := by
  have hB0 : (0 : ℝ) < B := by exact_mod_cast (by omega : 0 < B)
  have hs' : a - 1 / (B : ℝ) < s.re := (le_max_right _ _).trans_lt hs
  have h := (lt_div_iff₀ hB0).mp (show a - s.re < 1 / (B : ℝ) by linarith)
  unfold margin
  rw [show (B : ℝ) * (s.re - a) = -((a - s.re) * (B : ℝ)) by ring]
  linarith

private theorem margin_le_exponent (B : ℕ) {a : ℝ} {z s : ℂ} (hz : z.re ≤ a) :
    margin B a s ≤ (exponent B z s).re := by
  have h : (exponent B z s).re = 1 + (B : ℝ) * (s.re - z.re) := by
    simp [exponent, Complex.add_re, Complex.mul_re, Complex.sub_re]
  rw [h, margin]
  gcongr

private theorem norm_exponent_le (B : ℕ) (z s : ℂ) :
    ‖exponent B z s‖ ≤ 1 + (B : ℝ) * (‖s‖ + ‖z‖) := by
  unfold exponent
  calc
    _ ≤ ‖(1 : ℂ)‖ + ‖(B : ℂ) * (s - z)‖ := norm_add_le _ _
    _ = 1 + (B : ℝ) * ‖s - z‖ := by rw [norm_one, norm_mul, Complex.norm_natCast]
    _ ≤ _ := by gcongr; exact norm_sub_le _ _

/-- A single exponent strictly below one works on the entire compact set, uniformly
for all centers with real part at most `a`. -/
public theorem correction_compact_bound {B : ℕ} (hB : 1 ≤ B) {a : ℝ} {K : Set ℂ}
    (hK : K ⊆ halfPlane B a) (hKc : IsCompact K) :
    ∃ v C : ℝ, 0 ≤ v ∧ v < 1 ∧ 0 ≤ C ∧ ∀ z : ℂ, z.re ≤ a → ∀ s ∈ K,
      ‖correction B z s‖ ≤ C * (1 + ‖z‖) ^ v := by
  by_cases hne : K.Nonempty
  · have hmarg : Continuous (margin B a) := by unfold margin; fun_prop
    obtain ⟨x, hx, hmin⟩ := hKc.exists_isMinOn hne hmarg.continuousOn
    obtain ⟨y, _, hmax⟩ := hKc.exists_isMaxOn hne (continuous_norm (E := ℂ)).continuousOn
    let δ := margin B a x
    let e := min (δ / 2) (1 / 2)
    let M := 3 + (B : ℝ) * (‖y‖ + 1)
    let A := (B : ℝ) * 2 / (1 - e) + (B : ℝ) / δ
    have hδ : 0 < δ := margin_pos hB (hK hx)
    have he : 0 < e := lt_min (by positivity) (by norm_num)
    have he1 : e < 1 := (min_le_right _ _).trans_lt (by norm_num)
    have heδ : e ≤ δ := (min_le_left _ _).trans (by linarith)
    have hv : 0 < 1 - e := sub_pos.mpr he1
    have hM : 0 ≤ M := by dsimp [M]; positivity
    have hA : 0 ≤ A := by dsimp [A]; positivity
    refine ⟨1 - e, A * M ^ (1 - e), hv.le, by linarith, by positivity, fun z hz s hs => ?_⟩
    have hre : δ ≤ (exponent B z s).re := (hmin hs).trans (margin_le_exponent B hz)
    have hnw : 2 + ‖exponent B z s‖ ≤ M * (1 + ‖z‖) := by
      have hnorms : ‖s‖ + ‖z‖ ≤ (‖y‖ + 1) * (1 + ‖z‖) := by
        refine (add_le_add (hmax hs) (le_refl ‖z‖)).trans ?_
        nlinarith [norm_nonneg y, mul_nonneg (norm_nonneg y) (norm_nonneg z)]
      calc
        _ ≤ 3 + (B : ℝ) * (‖s‖ + ‖z‖) := by linarith only [norm_exponent_le B z s]
        _ ≤ 3 * (1 + ‖z‖) + (B : ℝ) * ((‖y‖ + 1) * (1 + ‖z‖)) := by
          gcongr
          linarith [norm_nonneg z]
        _ = _ := by dsimp [M]; ring
    calc
      _ ≤ A * (2 + ‖exponent B z s‖) ^ (1 - e) :=
        norm_scaled_cellSum_le B hδ he.le he1 heδ hre
      _ ≤ A * (M * (1 + ‖z‖)) ^ (1 - e) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) hnw hv.le) hA
      _ = _ := by rw [Real.mul_rpow hM (by positivity), mul_assoc]
  · exact ⟨0, 0, le_rfl, zero_lt_one, le_rfl, fun _ _ s hs => (hne ⟨s, hs⟩).elim⟩

/-- Each compact set uses just the absolute moment at its chosen sub-first exponent. -/
public theorem weighted_corrections_compact_majorant {ι : Type*} {B : ℕ} (hB : 1 ≤ B)
    {a : ℝ} (z c : ι → ℂ) (hz : ∀ i, (z i).re ≤ a)
    (hm : ∀ v : ℝ, 0 ≤ v → v < 1 → Summable (fun i => ‖c i‖ * (1 + ‖z i‖) ^ v))
    {K : Set ℂ} (hK : K ⊆ halfPlane B a) (hKc : IsCompact K) :
    ∃ u : ι → ℝ, Summable u ∧ ∀ i s, s ∈ K → ‖c i * correction B (z i) s‖ ≤ u i := by
  obtain ⟨v, C, hv, hv1, _, hC⟩ := correction_compact_bound hB hK hKc
  refine ⟨fun i => C * (‖c i‖ * (1 + ‖z i‖) ^ v), (hm v hv hv1).mul_left C, fun i s hs => ?_⟩
  dsimp only
  rw [norm_mul, mul_left_comm C]
  exact mul_le_mul_of_nonneg_left (hC (z i) (hz i) s hs) (norm_nonneg _)

/-- Under all sub-first absolute moments, the weighted corrections converge normally
and their sum is holomorphic on `Re s > max(1/2, a - 1/B)`. -/
public theorem weighted_corrections_normal_and_holomorphic {ι : Type*} {B : ℕ} (hB : 1 ≤ B)
    {a : ℝ} (z c : ι → ℂ) (hz : ∀ i, (z i).re ≤ a)
    (hm : ∀ v : ℝ, 0 ≤ v → v < 1 → Summable (fun i => ‖c i‖ * (1 + ‖z i‖) ^ v)) :
    SummableLocallyUniformlyOn (fun i s => c i * correction B (z i) s) (halfPlane B a) ∧
      AnalyticOnNhd ℂ (fun s => ∑' i, c i * correction B (z i) s) (halfPlane B a) := by
  have hopen : IsOpen (halfPlane B a) := isOpen_lt continuous_const Complex.continuous_re
  have hnormal := SummableLocallyUniformlyOn_of_locally_bounded hopen
    (fun _ hK hKc => weighted_corrections_compact_majorant hB z c hz hm hK hKc)
  refine ⟨hnormal, DifferentiableOn.analyticOnNhd ?_ hopen⟩
  have hdiff (i : ι) : DifferentiableOn ℂ (fun s => c i * correction B (z i) s) (halfPlane B a) :=
    ((correction_holomorphic B (z i)).differentiableOn.mono (fun _ hs =>
      (margin_pos hB hs).trans_le (margin_le_exponent B (hz i)))).const_mul _
  obtain ⟨g, hg⟩ := hnormal
  have hlim := hasSumLocallyUniformlyOn_iff_tendstoLocallyUniformlyOn.mp hg
  exact (hlim.congr_right hg.tsum_eqOn.symm).differentiableOn
    (Eventually.of_forall fun T => DifferentiableOn.fun_sum fun i (_ : i ∈ T) => hdiff i) hopen

end SubfirstCellCorrection
