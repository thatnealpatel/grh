module

public import Lemmas.SignedPoissonDefect

/-!
# Right limits and comparison of reflected depth tails

Source: `892abdb1:.godel/bob/uncut-depth-discount.md:5–11`.
Consumer: `d675c849:.godel/bob/deep-retained-excess.md:31–38`, equation (3),
whose signed trace identity is applied here near the supporting vertical.

Scope: a finite indexed reflected packet with multiplicity. A depth-zero
index supplies a single line atom. At every real translate, take the
right limit of the actual exterior trace minus the whole-line Poisson
convolution of the interior trace. Compare two depths on the same strict
tail. No infinite trace, zeta-zero summability, or arithmetic discount is asserted.

Owning check session: `01a20bcd-0340-73f5-9604-3b5724a0ee86`.
-/

open Filter Set MeasureTheory SignedPoissonDefect
open scoped BigOperators Topology

namespace ReflectedDepthTail

/-- The signed trace of atoms at `±b i`, of common ordinate `x i`. An index with
`b i = 0` supplies one line atom. Distinct indices count separately even when
both their depths and ordinates coincide. -/
@[expose] public noncomputable def reflectedTrace {ι : Type*} (pairs : Finset ι)
    (b x : ι → ℝ) (u v : ℝ) : ℝ :=
  atomTrace (pairs.disjSum (pairs.filter fun i ↦ 0 < b i))
    (Sum.elim b (fun i ↦ -b i)) (Sum.elim x x) u v

/-- The defect kernel sum at interior depth `u`, restricted to indices strictly
above depth `cut`. In particular `cut = u` gives the full strict tail. -/
@[expose] public noncomputable def depthTail {ι : Type*} (pairs : Finset ι)
    (b x : ι → ℝ) (A cut u v : ℝ) : ℝ :=
  ∑ i ∈ pairs.filter (fun i ↦ cut < b i),
    (kernel (A - b i) (v - x i) + kernel (A + b i - 2 * u) (v - x i))

private theorem defect_eq_tail_off_support {ι : Type*} (pairs : Finset ι) (b x : ι → ℝ)
    {A u : ℝ} (hu : 0 < u) (huA : u < A) (hb : ∀ i ∈ pairs, b i < A)
    (hsep : ∀ i ∈ pairs, b i ≠ u) (v : ℝ) :
    reflectedTrace pairs b x A v -
        (∫ y : ℝ, poisson (A - u) y * reflectedTrace pairs b x u (v - y)) =
      depthTail pairs b x A u u v := by
  have hleft (i : ι) (hi : i ∈ pairs.filter fun i ↦ 0 < b i) : -b i < u :=
    (neg_lt_zero.mpr (Finset.mem_filter.mp hi).2).trans hu
  have hA' : ∀ i ∈ pairs.disjSum (pairs.filter fun i ↦ 0 < b i),
      Sum.elim b (fun i ↦ -b i) i < A := by
    intro i hi
    cases i with
    | inl i => exact hb i (Finset.inl_mem_disjSum.mp hi)
    | inr i => exact (hleft i (Finset.inr_mem_disjSum.mp hi)).trans huA
  have hsep' : ∀ i ∈ pairs.disjSum (pairs.filter fun i ↦ 0 < b i),
      Sum.elim b (fun i ↦ -b i) i ≠ u := by
    intro i hi
    cases i with
    | inl i => exact hsep i (Finset.inl_mem_disjSum.mp hi)
    | inr i => exact (hleft i (Finset.inr_mem_disjSum.mp hi)).ne
  unfold reflectedTrace depthTail
  rw [finite_atom_defect _ _ _ huA hA' hsep', Finset.sum_filter, Finset.sum_disjSum,
    Finset.sum_filter (s := pairs) (fun i ↦ u < b i)]
  refine (congrArg (fun w : ℝ ↦ _ + w) ?_).trans (add_zero _)
  exact Finset.sum_eq_zero fun i hi ↦ ite_eq_right (hleft i hi).not_gt

/-- The actual exterior trace minus the Poisson-smoothed interior trace has
right limit `D_s` given by the strict `b i > s` sum. Depths equal to `s` are
already below the interior line in the right neighborhood, including when
`v` is their ordinate; no value of a kernel of width zero is used. -/
public theorem tendsto_defect_right {ι : Type*} (pairs : Finset ι) (b x : ι → ℝ)
    {A s : ℝ} (hs : 0 < s) (hsA : s < A) (hb : ∀ i ∈ pairs, 0 ≤ b i ∧ b i < A)
    (v : ℝ) :
    Tendsto (fun u ↦ reflectedTrace pairs b x A v -
      ∫ y : ℝ, poisson (A - u) y * reflectedTrace pairs b x u (v - y))
      (𝓝[>] s) (𝓝 (depthTail pairs b x A s s v)) := by
  -- Each index in the strict tail stays above all sufficiently nearby lines.
  have htail : ∀ᶠ u in 𝓝[>] s, ∀ i ∈ pairs.filter (fun i ↦ s < b i), u < b i :=
    (Finset.eventually_all _).2 fun i hi ↦
      nhdsWithin_le_nhds (Iio_mem_nhds (Finset.mem_filter.mp hi).2)
  have hnear : (fun u ↦ depthTail pairs b x A s u v) =ᶠ[𝓝[>] s]
      (fun u ↦ reflectedTrace pairs b x A v -
        ∫ y : ℝ, poisson (A - u) y * reflectedTrace pairs b x u (v - y)) := by
    filter_upwards [htail, self_mem_nhdsWithin (a := s) (s := Ioi s),
      nhdsWithin_le_nhds (Iio_mem_nhds hsA)] with u htailu hsu huA
    have hsep (i : ι) (hi : i ∈ pairs) : b i ≠ u := by
      by_cases h : s < b i
      · exact (htailu i (Finset.mem_filter.mpr ⟨hi, h⟩)).ne'
      · exact ((le_of_not_gt h).trans_lt hsu.out).ne
    have hstable : pairs.filter (fun i ↦ u < b i) = pairs.filter (fun i ↦ s < b i) := by
      ext i
      simp only [Finset.mem_filter]
      exact ⟨fun ⟨hi, hub⟩ ↦ ⟨hi, hsu.out.trans hub⟩,
        fun ⟨hi, hsb⟩ ↦ ⟨hi, htailu i (Finset.mem_filter.mpr ⟨hi, hsb⟩)⟩⟩
    rw [defect_eq_tail_off_support pairs b x (hs.trans hsu.out) huA
      (fun i hi ↦ (hb i hi).2) hsep, depthTail, depthTail, hstable]
  apply Tendsto.congr' hnear
  unfold depthTail
  apply tendsto_finsetSum
  intro i hi
  have hp : 0 < A + b i - 2 * s := by
    linarith only [hsA, (Finset.mem_filter.mp hi).2]
  have hc : ContinuousAt (fun u ↦ kernel (A + b i - 2 * u) (v - x i)) s := by
    unfold kernel
    exact ContinuousAt.div (by fun_prop) (by fun_prop) (by positivity)
  exact (continuousAt_const.add hc).tendsto.mono_left nhdsWithin_le_nhds

private theorem abs_kernel_sub_le {p q : ℝ} (hp : 0 < p) (hpq : p ≤ q) (z : ℝ) :
    |kernel p z - kernel q z| ≤ (q - p) / p * kernel q z := by
  have hq := hp.trans_le hpq
  have hdp : 0 < p ^ 2 + z ^ 2 := by positivity
  have hdq : 0 < q ^ 2 + z ^ 2 := by positivity
  have hdiff : kernel p z - kernel q z =
      (q - p) * (p * q - z ^ 2) / ((p ^ 2 + z ^ 2) * (q ^ 2 + z ^ 2)) := by
    unfold kernel
    field_simp
    ring
  have habs : |p * q - z ^ 2| / (p ^ 2 + z ^ 2) ≤ q / p := by
    apply (div_le_div_iff₀ hdp hp).2
    have heq : |p * q - z ^ 2| * p = |(p * q - z ^ 2) * p| := by
      rw [abs_mul, abs_of_pos hp]
    rw [heq, abs_le]
    have hx := mul_le_mul_of_nonneg_right hpq (sq_nonneg z)
    have hpx := mul_nonneg hp.le (sq_nonneg z)
    have hqx := mul_nonneg hq.le (sq_nonneg z)
    have hqp := mul_nonneg hq.le (sq_nonneg p)
    constructor <;> nlinarith only [hx, hpx, hqx, hqp]
  calc
    |kernel p z - kernel q z| =
        (q - p) / (q ^ 2 + z ^ 2) * (|p * q - z ^ 2| / (p ^ 2 + z ^ 2)) := by
      rw [hdiff, abs_div, abs_mul, abs_of_nonneg (sub_nonneg.mpr hpq),
        abs_of_pos (mul_pos hdp hdq), div_mul_div_comm, mul_comm (q ^ 2 + z ^ 2)]
    _ ≤ (q - p) / (q ^ 2 + z ^ 2) * (q / p) :=
      mul_le_mul_of_nonneg_left habs (div_nonneg (sub_nonneg.mpr hpq) hdq.le)
    _ = (q - p) / p * kernel q z := by unfold kernel; ring

/-- The error between `D_s` and `D_a` restricted to the same strict `s` tail
is relative to the restricted `D_a`, at every real translate. The reference
sum is the right-limit defect at `a` of the packet filtered by `s < b i`. -/
public theorem abs_depthTail_sub_le {ι : Type*} (pairs : Finset ι) (b x : ι → ℝ)
    {A a s : ℝ} (ha : 0 < a ∧ a < s) (hsA : s < A)
    (hb : ∀ i ∈ pairs, 0 ≤ b i ∧ b i < A) (v : ℝ) :
    |depthTail pairs b x A s s v - depthTail pairs b x A s a v| ≤
      2 * (s - a) / (A - s) * depthTail pairs b x A s a v := by
  unfold depthTail
  rw [← Finset.sum_sub_distrib, Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i hi ↦ ?_)
  obtain ⟨hip, hsi⟩ := Finset.mem_filter.mp hi
  let p := A + b i - 2 * s
  let q := A + b i - 2 * a
  let z := v - x i
  have hAs : 0 < A - s := sub_pos.mpr hsA
  have hpMin : A - s ≤ p := by dsimp [p]; linarith only [hsi]
  have hp := hAs.trans_le hpMin
  have hpq : p ≤ q := by dsimp [p, q]; linarith only [ha.2]
  have hshift : q - p = 2 * (s - a) := by dsimp [p, q]; ring
  have hcoeff_nonneg : 0 ≤ 2 * (s - a) / (A - s) :=
    div_nonneg (mul_nonneg zero_le_two (sub_nonneg.mpr ha.2.le)) hAs.le
  have hcoeff : (q - p) / p ≤ 2 * (s - a) / (A - s) := by
    rw [hshift]
    exact div_le_div_of_nonneg_left (mul_nonneg zero_le_two (sub_nonneg.mpr ha.2.le)) hAs hpMin
  have hkq : 0 ≤ kernel q z := div_nonneg (hp.le.trans hpq) (by positivity)
  have hkext : 0 ≤ kernel (A - b i) z :=
    div_nonneg (sub_nonneg.mpr (hb i hip).2.le) (by positivity)
  change |(kernel (A - b i) z + kernel p z) - (kernel (A - b i) z + kernel q z)| ≤
    2 * (s - a) / (A - s) * (kernel (A - b i) z + kernel q z)
  rw [add_sub_add_left_eq_sub]
  calc
    |kernel p z - kernel q z| ≤ (q - p) / p * kernel q z := abs_kernel_sub_le hp hpq z
    _ ≤ 2 * (s - a) / (A - s) * kernel q z := mul_le_mul_of_nonneg_right hcoeff hkq
    _ ≤ 2 * (s - a) / (A - s) * (kernel (A - b i) z + kernel q z) :=
      mul_le_mul_of_nonneg_left (le_add_of_nonneg_left hkext) hcoeff_nonneg

end ReflectedDepthTail
