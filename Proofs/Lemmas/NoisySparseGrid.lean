module

public import Lemmas.SparseAngularMinimax
import all Lemmas.ConsecutiveHarmonicGrid -- unfold the landed grid node
import Lemmas.SparseMissingDivisor
import Lemmas.NoisyMomentWitness
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Near-zero mass of shifted grids and the noisy sparse witness

Source: `b825bc58:.godel/bob/noisy-sparse-harmonics.md:3–16`, the lower
bound, unchanged from scan `69d5d309` at base `432066cd`. Every translate
of the landed uniform grid has enough mass in the closed central arc,
including across the circle seam. The same bound holds for the actual
shifted-grid mixture. Combining this with the small-density branch and
removing low-envelope mass gives one circle probability law controlling
all queried moments. No noisy minimax equality or prime-distribution
assertion is made.

Owning check session: `01a20ee2-df11-780c-9cc1-8715404fb242`.
-/

open Set
open MeasureTheory hiding average
open scoped BigOperators ENNReal

namespace Masullo.NoisySparseGrid

open ConsecutiveHarmonicGrid (node)
open SparseAngularMinimax (shiftedGridLaw shiftedGridLaw_spec)
open SparseShiftedGrid (gridMean shiftedQueries translation)
open SparseSmallDensity (AngularCircle envelope)

/-- The circle's closed central arc of radius `π(t + 1/n)`. -/
@[expose] public noncomputable def gridArc (n : ℕ) (t : ℝ) : Set AngularCircle :=
  Metric.closedBall 0 (Real.pi * (t + 1 / (n : ℝ)))

/-- One arbitrary translate of the landed grid, with weight `1/n` per node. -/
@[expose] public noncomputable def translatedGridLaw (n : ℕ) (a : ℝ) : Measure AngularCircle :=
  (n : ℝ≥0∞)⁻¹ • ∑ j ∈ Finset.range n, Measure.dirac ((node n j + a : ℝ) : AngularCircle)

-- The residue index selects the same circle point as the lifted integer index.
private theorem coe_node_natMod {n : ℕ} (hn : 0 < n) (a : ℝ) (k : ℤ) :
    ((node n (k.natMod n) + a : ℝ) : AngularCircle) =
      ((a + Real.pi / (n : ℝ) + (k : ℝ) * (2 * Real.pi / (n : ℝ)) : ℝ) : AngularCircle) := by
  have hnR : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have hres : (k.natMod n : ℤ) = k % (n : ℤ) :=
    Int.toNat_of_nonneg (Int.emod_nonneg _ (by exact_mod_cast hn.ne'))
  have hk : (((k / (n : ℤ) : ℤ) : ℝ) * (n : ℝ) + (k.natMod n : ℝ)) = (k : ℝ) := by
    exact_mod_cast (hres ▸ Int.ediv_mul_add_emod k (n : ℤ) :
      k / (n : ℤ) * (n : ℤ) + (k.natMod n : ℤ) = k)
  have hangle : a + Real.pi / (n : ℝ) + (k : ℝ) * (2 * Real.pi / (n : ℝ)) =
      node n (k.natMod n) + a + (k / (n : ℤ)) • (2 * Real.pi) := by
    rw [← hk, zsmul_eq_mul, node]
    field_simp [hnR]
    ring
  rw [hangle, AddCircle.coe_add _ (node n (k.natMod n) + a), AddCircle.coe_zsmul,
    AddCircle.coe_period, smul_zero, add_zero]

-- A real lift in the central interval lies in the circle's closed arc.
private theorem coe_mem_gridArc {n : ℕ} {t x : ℝ}
    (hx : |x| ≤ Real.pi * (t + 1 / (n : ℝ))) : (x : AngularCircle) ∈ gridArc n t := by
  change x ∈ (fun y : ℝ ↦ (y : AngularCircle)) ⁻¹'
    Metric.closedBall ((0 : ℝ) : AngularCircle) (Real.pi * (t + 1 / (n : ℝ)))
  rw [AddCircle.coe_real_preimage_closedBall_eq_iUnion]
  exact Set.mem_iUnion.mpr ⟨0, by simpa [Metric.mem_closedBall, Real.dist_eq] using hx⟩

/-- Every translate of a uniform `n`-point grid puts at least mass `t` in the
closed arc. We count distinct residue indices, with no choice of a seam for
that arc and no restriction on the translation. -/
public theorem translatedGridLaw_arc_mass {n : ℕ} (hn : 1 ≤ n) (a : ℝ) {t : ℝ}
    (ht : 0 ≤ t) (ht₁ : t ≤ 1) :
    ENNReal.ofReal t ≤ translatedGridLaw n a (gridArc n t) := by
  classical
  rcases ht.eq_or_lt with rfl | ht
  · simp
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  let d : ℝ := 2 * Real.pi / (n : ℝ)
  let o : ℝ := a + Real.pi / (n : ℝ)
  let R : ℝ := Real.pi * (t + 1 / (n : ℝ))
  let L : ℝ := (-R - o) / d
  let m : ℕ := ⌈(n : ℝ) * t⌉₊
  have hd : 0 < d := by dsimp [d]; positivity
  have hwidth : d * ((n : ℝ) * t + 1) = 2 * R := by
    dsimp [d, R]
    field_simp [hnR.ne']
  have hL : L * d = -R - o := div_mul_cancel₀ _ hd.ne'
  have hm₁ : m ≤ n := Nat.ceil_le.mpr (by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left ht₁ hnR.le)
  have hm₂ : (m : ℝ) < (n : ℝ) * t + 1 := Nat.ceil_lt_add_one (by positivity)
  let k (i : ℕ) : ℤ := ⌈L⌉ + (i : ℤ)
  let res (i : ℕ) : ℕ := (k i).natMod n
  have hinside (i : ℕ) (hi : i < m) : |o + (k i : ℝ) * d| ≤ R := by
    have hiR : (i : ℝ) + 1 ≤ m := by exact_mod_cast (Nat.succ_le_of_lt hi)
    have hlo : L ≤ (k i : ℝ) := by
      dsimp [k]
      push_cast
      linarith only [Int.le_ceil L, Nat.cast_nonneg (α := ℝ) i]
    have hhi : (k i : ℝ) ≤ L + ((n : ℝ) * t + 1) := by
      dsimp [k]
      push_cast
      linarith only [Int.ceil_lt_add_one L, hiR, hm₂]
    refine abs_le.mpr ⟨?_, ?_⟩
    · linarith only [mul_le_mul_of_nonneg_right hlo hd.le, hL]
    · linarith only [mul_le_mul_of_nonneg_right hhi hd.le, hL, hwidth]
  have hinj : Set.InjOn res (↑(Finset.range m) : Set ℕ) := by
    intro i hi j hj hij
    simp only [Finset.mem_coe, Finset.mem_range] at hi hj
    have hcast (l : ℕ) : (res l : ℤ) = k l % (n : ℤ) :=
      Int.toNat_of_nonneg (Int.emod_nonneg _ (by exact_mod_cast (show n ≠ 0 by omega)))
    have hmod : k i % (n : ℤ) = k j % (n : ℤ) := by rw [← hcast i, ← hcast j, hij]
    have hbound {i j : ℕ} (hij' : i ≤ j) (hj' : j < m)
        (h : k j % (n : ℤ) = k i % (n : ℤ)) : i = j := by
      have hzero := Int.emod_eq_emod_iff_emod_sub_eq_zero.mp h
      have hdiff : k j - k i = (j : ℤ) - (i : ℤ) := by simp [k]
      rw [hdiff, Int.emod_eq_of_lt (by omega) (by omega)] at hzero
      omega
    rcases le_total i j with h | h
    · exact hbound h hj hmod.symm
    · exact (hbound h hi hmod).symm
  let good := (Finset.range n).filter fun j ↦ ((node n j + a : ℝ) : AngularCircle) ∈ gridArc n t
  have hmaps : Set.MapsTo res (↑(Finset.range m) : Set ℕ) (↑good : Set ℕ) := by
    intro i hi
    refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Int.natMod_lt (by omega)), ?_⟩
    change ((node n ((k i).natMod n) + a : ℝ) : AngularCircle) ∈ gridArc n t
    rw [coe_node_natMod hn]
    exact coe_mem_gridArc (hinside i (Finset.mem_range.mp hi))
  have hcard : m ≤ good.card := by
    simpa only [Finset.card_range] using Finset.card_le_card_of_injOn res hmaps hinj
  rw [translatedGridLaw, smul_apply, sum_apply, smul_eq_mul, ← ENNReal.div_eq_inv_mul]
  refine (ENNReal.le_div_iff_mul_le (.inl (by exact_mod_cast (show n ≠ 0 by omega)))
    (.inl (ENNReal.natCast_ne_top n))).mpr ?_
  calc
    ENNReal.ofReal t * (n : ℝ≥0∞) = ENNReal.ofReal (t * (n : ℝ)) := by
      rw [ENNReal.ofReal_mul ht.le, ENNReal.ofReal_natCast]
    _ ≤ (m : ℝ≥0∞) := by
      rw [← ENNReal.ofReal_natCast]
      apply ENNReal.ofReal_le_ofReal
      simpa only [mul_comm t (n : ℝ)] using Nat.le_ceil ((n : ℝ) * t)
    _ ≤ (good.card : ℝ≥0∞) := by exact_mod_cast hcard
    _ = ∑ _ ∈ good, (1 : ℝ≥0∞) := by rw [Finset.sum_const, nsmul_one]
    _ = ∑ j ∈ good, Measure.dirac ((node n j + a : ℝ) : AngularCircle) (gridArc n t) :=
      Finset.sum_congr rfl fun j hj ↦ (Measure.dirac_apply_of_mem (Finset.mem_filter.mp hj).2).symm
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (by simp)

-- The product of the two normalizations gives the landed weight per atom.
private theorem shiftedGridLaw_eq_average (n : ℕ) (K : Finset ℕ) :
    shiftedGridLaw n K = ((2 ^ K.card : ℕ) : ℝ≥0∞)⁻¹ •
      ∑ P ∈ K.powerset, translatedGridLaw n (translation K P) := by
  rw [shiftedGridLaw, Finset.sum_product]
  simp only [translatedGridLaw, ← Finset.smul_sum, smul_smul, Nat.cast_mul]
  rw [ENNReal.mul_inv (.inr (ENNReal.natCast_ne_top _))
    (.inl (ENNReal.natCast_ne_top _))]

/-- The actual shifted-grid mixture retains the same mass bound, with all
its sign assignments and nodes counted at the landed weights. -/
public theorem shiftedGridLaw_arc_mass {n : ℕ} (hn : 1 ≤ n) (K : Finset ℕ) {t : ℝ}
    (ht : 0 ≤ t) (ht₁ : t ≤ 1) :
    ENNReal.ofReal t ≤ shiftedGridLaw n K (gridArc n t) := by
  rw [shiftedGridLaw_eq_average, smul_apply, sum_apply, smul_eq_mul]
  have hK : 0 < 2 ^ K.card := by positivity
  calc
    ENNReal.ofReal t = ((2 ^ K.card : ℕ) : ℝ≥0∞)⁻¹ * ∑ _ ∈ K.powerset, ENNReal.ofReal t := by
      rw [Finset.sum_const, nsmul_eq_mul, Finset.card_powerset, ← mul_assoc,
        ENNReal.inv_mul_cancel (by exact_mod_cast hK.ne') (ENNReal.natCast_ne_top _), one_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun P _ ↦
      translatedGridLaw_arc_mass hn (translation K P) ht ht₁) zero_le

-- On the large branch, `N ≤ 2n` absorbs the radius term due to grid spacing.
private theorem envelope_le_on_gridArc {N n : ℕ} (hN : 2 ≤ N) (hlarge : 3 * N < 4 * n)
    {t : ℝ} (ht : 0 ≤ t) {s : AngularCircle} (hs : s ∈ gridArc n t) :
    envelope s ≤ 8 * Real.pi * t + Real.pi / (N : ℝ) := by
  have hsR : ‖s‖ ≤ Real.pi * (t + 1 / (n : ℝ)) := by
    simpa only [gridArc, Metric.mem_closedBall, dist_zero_right] using hs
  have hNn : (N : ℝ) ≤ 2 * (n : ℝ) := by exact_mod_cast (show N ≤ 2 * n by omega)
  have hrecip : 1 / (2 * (n : ℝ)) ≤ 1 / (N : ℝ) :=
    one_div_le_one_div_of_le (by exact_mod_cast (show 0 < N by omega)) hNn
  have hpi := mul_le_mul_of_nonneg_left hrecip Real.pi_pos.le
  rw [mul_one_div Real.pi (N : ℝ)] at hpi
  calc
    envelope s ≤ ‖s‖ / 2 := Real.sin_le (by positivity)
    _ ≤ Real.pi * (t + 1 / (n : ℝ)) / 2 := div_le_div_of_nonneg_right hsR (by norm_num)
    _ = Real.pi * t / 2 + Real.pi * (1 / (2 * (n : ℝ))) := by ring
    _ ≤ _ := by linarith only [hpi, mul_nonneg Real.pi_pos.le ht]

/-- For at most `N - 1` distinct positive queries, a single circle probability
law obeys every Fourier tolerance and achieves Bob's lower envelope bound. -/
public theorem exists_noisy_sparse_law_mean_ge {N : ℕ} (hN : 2 ≤ N) (J : Finset ℕ)
    (hJpos : ∀ j ∈ J, 0 < j) (hJcard : J.card ≤ N - 1) {e : ℝ}
    (he : 0 ≤ e) (he₁ : e ≤ 1 / 8) :
    ∃ μ : Measure AngularCircle, IsProbabilityMeasure μ ∧
      (∀ j ∈ J, ‖∫ s, fourier (j : ℤ) s ∂μ‖ ≤ e) ∧
      (1 + e) * gridMean N - 8 * Real.pi * e ^ 2 - Real.pi * e / (N : ℝ) ≤
        ∫ s, envelope s ∂μ := by
  let t : ℝ := e / (1 + e)
  have ht : 0 ≤ t := div_nonneg he (by positivity)
  have hte : t ≤ e := div_le_self he (by linarith)
  have ht₁ : t ≤ 1 := hte.trans (he₁.trans (by norm_num))
  let mode (j : {j // j ∈ J}) : AngularCircle → ℂ := fourier (j.val : ℤ)
  obtain ⟨n, hn, hnN, hmiss, hroute, htop⟩ :=
    exists_sparse_missing_divisor (by omega : 1 ≤ N) J hJpos hJcard
  obtain ⟨μ₀, A, hprob, hzero, hmean, hA, hmass, hB⟩ :
      ∃ (μ₀ : Measure AngularCircle) (A : Set AngularCircle), IsProbabilityMeasure μ₀ ∧
        (∀ j, (∫ s, mode j s ∂μ₀) = 0) ∧
        gridMean N ≤ (∫ s, envelope s ∂μ₀) ∧ MeasurableSet A ∧
        ENNReal.ofReal t ≤ μ₀ A ∧ ∀ s ∈ A, envelope s ≤ 8 * Real.pi * t + Real.pi / (N : ℝ) := by
    by_cases hlarge : 3 * N < 4 * n
    · let K := shiftedQueries n J
      obtain ⟨hmodes, hmean⟩ := SparseShiftedGrid.annihilates_and_mean_ge_of_large_missing_divisor
        hn hnN hlarge J hJpos (hroute hlarge) htop
      obtain ⟨hprob, hfourier, henvelope⟩ := shiftedGridLaw_spec hn K
      refine ⟨shiftedGridLaw n K, gridArc n t, hprob, ?_, ?_, measurableSet_closedBall,
        shiftedGridLaw_arc_mass hn K ht ht₁, fun _ hs ↦ envelope_le_on_gridArc hN hlarge ht hs⟩
      · intro j
        exact (hfourier j.val).trans (hmodes j.val j.property)
      · exact hmean.trans_eq henvelope.symm
    · obtain ⟨hprob, _, _, hmodes, _, hmean, harc⟩ := SparseSmallDensity.small_density_witness
        (fun j : {j // j ∈ J} ↦ j.val) hN hn (le_of_not_gt hlarge)
        (fun j ↦ hJpos j.val j.property) (fun j h ↦ hmiss (h ▸ j.property))
      obtain ⟨hA, hmass, hbound⟩ := harc t ht ht₁
      exact ⟨SparseSmallDensity.law n, SparseSmallDensity.arc t, hprob, hmodes, hmean, hA,
        hmass, fun s hs ↦ (hbound s hs).trans (le_add_of_nonneg_right (by positivity))⟩
  let _ := hprob
  have hf : Integrable envelope μ₀ := by
    have hc : Continuous envelope := Real.continuous_sin.comp (continuous_norm.div_const 2)
    exact Integrable.of_bound hc.aestronglyMeasurable 1 (ae_of_all _ fun s ↦ Real.abs_sin_le_one _)
  obtain ⟨μ, hμ, hmodes, hnew⟩ := exists_noisy_moment_witness μ₀ mode
    (fun j ↦ (fourier (j.val : ℤ)).continuous.measurable)
    (fun j s ↦ (Circle.norm_coe (AddCircle.toCircle ((j.val : ℤ) • s))).le)
    hzero envelope hf hmean he hA hmass hB
  refine ⟨μ, hμ, fun j hj ↦ hmodes ⟨j, hj⟩, ?_⟩
  have hcost : e * (8 * Real.pi * t + Real.pi / (N : ℝ)) ≤
      e * (8 * Real.pi * e + Real.pi / (N : ℝ)) := by
    gcongr
  calc
    _ = (1 + e) * gridMean N - e * (8 * Real.pi * e + Real.pi / (N : ℝ)) := by ring
    _ ≤ _ := (sub_le_sub_left hcost _).trans hnew

end Masullo.NoisySparseGrid
