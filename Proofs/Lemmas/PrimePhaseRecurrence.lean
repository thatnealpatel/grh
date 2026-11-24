module

public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Fourier.AddCircleMulti
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.RingTheory.Localization.Module
import Mathlib.Topology.Algebra.Group.SubmonoidClosure
import Mathlib.Topology.UrysohnsLemma
import Mathlib.Tactic

/-!
# Late simultaneous recurrence of the prime phases

Source and consumer: `bdd74f2a:.godel/adhoc/prime-translation-norm.md`, §1,
lines 7–26 (especially line 22). These are the common modulation times used
before the signed prime-translation compression is taken to its untwisted
limit. The operator-norm and compact-correction arguments are not included.
Owning check session: `01a20e58-ec66-7c2b-94b4-741e4461cd8a`.
-/

open Filter MeasureTheory Set UnitAddTorus
open scoped ComplexConjugate Topology

namespace Masullo

variable {ι : Type*} [Fintype ι]

private theorem primeProduct_factorization (p : ι → ℕ) (hp : ∀ i, (p i).Prime)
    (hinj : Function.Injective p) (e : ι → ℕ) (i : ι) :
    (∏ j, p j ^ e j).factorization (p i) = e i := by
  classical
  rw [Nat.factorization_prod_apply (fun j _ ↦ pow_ne_zero _ (hp j).ne_zero)]
  simp [Nat.factorization_pow, (hp _).factorization, Finsupp.single_apply, hinj.eq_iff]

private theorem primeProduct_log (p : ι → ℕ) (hp : ∀ i, (p i).Prime) (e : ι → ℕ) :
    Real.log (∏ j, (p j : ℝ) ^ e j) = ∑ j, (e j : ℝ) * Real.log (p j : ℝ) := by
  rw [Real.log_prod (fun j _ ↦ pow_ne_zero _ (Nat.cast_ne_zero.mpr (hp j).ne_zero))]
  simp only [Real.log_pow]

/-- Signed integer relations among the logarithms of distinct primes are trivial. -/
public theorem primeLog_integerRelation (p : ι → ℕ) (hp : ∀ i, (p i).Prime)
    (hinj : Function.Injective p) (m : ι → ℤ)
    (hm : ∑ i, (m i : ℝ) * Real.log (p i : ℝ) = 0) : m = 0 := by
  classical
  let e (i : ι) := (m i).toNat
  let f (i : ι) := (-m i).toNat
  have hsplit (i : ι) : (e i : ℝ) - (f i : ℝ) = (m i : ℝ) := by
    exact_mod_cast Int.toNat_sub_toNat_neg (m i)
  have hlog : Real.log (∏ i, (p i : ℝ) ^ e i) = Real.log (∏ i, (p i : ℝ) ^ f i) := by
    rw [primeProduct_log p hp, primeProduct_log p hp, ← sub_eq_zero, ← Finset.sum_sub_distrib]
    simpa only [← sub_mul, hsplit] using hm
  have hpos (i : ι) : 0 < (p i : ℝ) := Nat.cast_pos.mpr (hp i).pos
  have hprod : (∏ i, p i ^ e i) = ∏ i, p i ^ f i := by
    have h := congrArg Real.exp hlog
    rw [Real.exp_log (Finset.prod_pos fun i _ ↦ pow_pos (hpos i) _),
      Real.exp_log (Finset.prod_pos fun i _ ↦ pow_pos (hpos i) _)] at h
    exact_mod_cast h
  ext i
  have heq : e i = f i := by
    simpa only [primeProduct_factorization p hp hinj] using
      congrArg (fun n : ℕ ↦ n.factorization (p i)) hprod
  rw [Pi.zero_apply, ← Int.toNat_sub_toNat_neg (m i)]
  exact sub_eq_zero.mpr (congrArg (fun n : ℕ ↦ (n : ℤ)) heq)

/-- The real logarithms of a finite family of distinct primes are rationally linearly
independent. Passing from integers to their fraction field clears denominators. -/
public theorem primeLog_linearIndependent (p : ι → ℕ) (hp : ∀ i, (p i).Prime)
    (hinj : Function.Injective p) : LinearIndependent ℚ (fun i ↦ Real.log (p i : ℝ)) := by
  apply (LinearIndependent.iff_fractionRing ℤ ℚ).mp
  refine Fintype.linearIndependent_iff.mpr fun m hm i ↦ ?_
  have h := primeLog_integerRelation p hp hinj m (by simpa only [zsmul_eq_mul] using hm)
  exact congrFun h i

private noncomputable def phaseFlow (a : ι → ℝ) : ℝ →+ UnitAddTorus ι where
  toFun t i := (t * a i / (2 * Real.pi) : ℝ)
  map_zero' := by ext i; simp
  map_add' s t := by
    ext i
    change ((s + t) * a i / (2 * Real.pi) : ℝ) =
      ((s * a i / (2 * Real.pi) : ℝ) : UnitAddCircle) +
      ((t * a i / (2 * Real.pi) : ℝ) : UnitAddCircle)
    rw [add_mul, add_div, AddCircle.coe_add]

private theorem mFourier_phaseFlow (a : ι → ℝ) (m : ι → ℤ) (t : ℝ) :
    mFourier m (phaseFlow a t) = Complex.exp ((↑(t * ∑ i, (m i : ℝ) * a i) : ℂ) * Complex.I) := by
  change (∏ i, fourier (m i) ((t * a i / (2 * Real.pi) : ℝ) : UnitAddCircle)) = _
  simp_rw [fourier_coe_apply, Complex.ofReal_one, div_one]
  rw [← Complex.exp_sum]
  congr 1
  rw [Complex.ofReal_mul, Complex.ofReal_sum, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  push_cast
  field_simp [Complex.ofReal_ne_zero.mpr Real.pi_ne_zero]

private theorem mFourier_add_point (m : ι → ℤ) (x y : UnitAddTorus ι) :
    mFourier m (x + y) = mFourier m x * mFourier m y := by
  simp only [mFourier, ContinuousMap.coe_mk, Pi.add_apply, fourier_apply, zsmul_add,
    AddCircle.toCircle_add, Circle.coe_mul, Finset.prod_mul_distrib]

private noncomputable def integralAlong {G X : Type*} [TopologicalSpace G] [MeasurableSpace G]
    [BorelSpace G] [CompactSpace G] [TopologicalSpace X] (μ : Measure G) [IsFiniteMeasure μ]
    (g : C(G, X)) : C(X, ℂ) →L[ℂ] ℂ :=
  (L1.integralCLM' ℂ).comp ((ContinuousMap.toLp 1 μ ℂ).comp (g.compCLM ℂ ℂ))

private theorem integralAlong_apply {G X : Type*} [TopologicalSpace G] [MeasurableSpace G]
    [BorelSpace G] [CompactSpace G] [TopologicalSpace X] (μ : Measure G) [IsFiniteMeasure μ]
    (g : C(G, X)) (f : C(X, ℂ)) : integralAlong μ g f = ∫ h, f (g h) ∂μ := by
  let F := ContinuousMap.toLp 1 μ ℂ (f.comp g)
  change L1.integralCLM' ℂ F = _
  have hF := L1.integrable_coeFn F
  rw [← L1.integral_eq', ← Integrable.toL1_coeFn F hF, ← MeasureTheory.integral_eq _ hF]
  exact integral_congr_ae (ContinuousMap.coeFn_toLp μ (f.comp g))

-- If every nonconstant monomial is nontrivial on the flow, Haar averages on its closed
-- range and on every coset agree on monomials, hence on all continuous functions.
private theorem phaseFlow_dense (a : ι → ℝ)
    (ha : ∀ m : ι → ℤ, (∑ i, (m i : ℝ) * a i) = 0 → m = 0) :
    DenseRange (phaseFlow a) := by
  classical
  let H := (phaseFlow a).range.topologicalClosure
  have hH : IsClosed (H : Set (UnitAddTorus ι)) := AddSubgroup.isClosed_topologicalClosure _
  let : CompactSpace H := isCompact_iff_compactSpace.mp hH.isCompact
  let K : TopologicalSpace.PositiveCompacts H := ⟨⟨univ, isCompact_univ⟩, by simp⟩
  let μ := Measure.addHaarMeasure K
  let : IsProbabilityMeasure μ := ⟨Measure.addHaarMeasure_self (K₀ := K)⟩
  let A (z : UnitAddTorus ι) : C(UnitAddTorus ι, ℂ) →L[ℂ] ℂ :=
    integralAlong μ ⟨fun h : H ↦ z + (h : UnitAddTorus ι), continuous_const.add continuous_subtype_val⟩
  have hA (z) (f) : A z f = ∫ h : H, f (z + (h : UnitAddTorus ι)) ∂μ := integralAlong_apply ..
  intro z
  change z ∈ (H : Set (UnitAddTorus ι))
  have hχ : ∀ m : ι → ℤ, m ≠ 0 → ∫ h : H, mFourier m (h : UnitAddTorus ι) ∂μ = 0 := by
    intro m hm
    let s := ∑ i, (m i : ℝ) * a i
    have hs : s ≠ 0 := fun h ↦ hm (ha m h)
    let t := Real.pi / s
    let u : H := ⟨phaseFlow a t, subset_closure ⟨t, rfl⟩⟩
    have hu : mFourier m (u : UnitAddTorus ι) = -1 := by
      change mFourier m (phaseFlow a t) = -1
      rw [mFourier_phaseFlow, show t * s = Real.pi from div_mul_cancel₀ _ hs, Complex.exp_pi_mul_I]
    have htrans := integral_add_left_eq_self (μ := μ)
      (fun h : H ↦ mFourier m (h : UnitAddTorus ι)) u
    simp only [AddSubgroup.coe_add, mFourier_add_point, hu, neg_one_mul, integral_neg] at htrans
    exact (neg_eq_self.mp htrans)
  have hmono : EqOn (A 0) (A z) (range mFourier) := by
    rintro _ ⟨m, rfl⟩
    by_cases hm : m = 0
    · simp [hm, hA, mFourier_zero]
    · simp only [hA, zero_add, mFourier_add_point m z, integral_const_mul, hχ m hm, mul_zero]
  let M : Submodule ℂ C(UnitAddTorus ι, ℂ) := Submodule.span ℂ (range mFourier)
  have hspan : EqOn (A 0) (A z) (↑M : Set C(UnitAddTorus ι, ℂ)) := by
    intro f hf
    exact LinearMap.eqOn_span hmono (show f ∈ M from hf)
  have hall : ∀ f, A 0 f = A z f := by
    intro f
    apply hspan.closure (A 0).continuous (A z).continuous
    rw [← Submodule.topologicalClosure_coe]
    change f ∈ (Submodule.span ℂ (range mFourier)).topologicalClosure
    rw [span_mFourier_closure_eq_top]
    exact Submodule.mem_top
  by_contra hz
  let S := range (fun h : H ↦ z + (h : UnitAddTorus ι))
  have hS : IsClosed S := (isCompact_range (continuous_const.add continuous_subtype_val)).isClosed
  have hd : Disjoint (H : Set (UnitAddTorus ι)) S := by
    refine disjoint_left.mpr ?_
    rintro _ hx ⟨h, rfl⟩
    exact hz (by simpa using H.sub_mem hx h.property)
  obtain ⟨f, hf₀, hf₁, _⟩ := exists_continuous_zero_one_of_isClosed hH hS hd
  let fc : C(UnitAddTorus ι, ℂ) := ⟨fun x ↦ (f x : ℂ), Complex.continuous_ofReal.comp f.continuous⟩
  have h₀ (h : H) : fc (0 + (h : UnitAddTorus ι)) = 0 := by
    change (↑(f (0 + (h : UnitAddTorus ι))) : ℂ) = 0
    simp [hf₀ h.property]
  have h₁ (h : H) : fc (z + (h : UnitAddTorus ι)) = 1 := by
    change (↑(f (z + (h : UnitAddTorus ι))) : ℂ) = 1
    rw [hf₁ (mem_range_self h)]
    simp
  have he := hall fc
  rw [hA, hA] at he
  simp only [h₀, h₁, integral_zero, integral_const, probReal_univ, one_smul] at he
  exact zero_ne_one he

-- Compact-group recurrence adds arbitrarily large positive integers to a real time in
-- the desired open set; it requires no independence condition for the integer-time orbit.
omit [Fintype ι] in
private theorem phaseFlow_hit_after {a : ι → ℝ} (hd : DenseRange (phaseFlow a))
    {U : Set (UnitAddTorus ι)} (hU : IsOpen U) {w : UnitAddTorus ι} (hw : w ∈ U) (R : ℝ) :
    ∃ t : ℝ, R ≤ t ∧ phaseFlow a t ∈ U := by
  obtain ⟨_, hs, ⟨s, rfl⟩⟩ := (mem_closure_iff.mp (hd w)) U hU hw
  have hcluster : MapClusterPt (phaseFlow a s) atTop (fun n : ℕ ↦ phaseFlow a (s + n)) := by
    have hadd : Continuous (fun x : UnitAddTorus ι ↦ phaseFlow a s + x) :=
      (Homeomorph.addLeft (phaseFlow a s)).continuous
    have hn (n : ℕ) : phaseFlow a (s + n) = phaseFlow a s + n • phaseFlow a 1 := by
      rw [map_add, ← map_nsmul, nsmul_eq_mul, mul_one]
    simpa only [Function.comp_def, add_zero, hn] using
      (mapClusterPt_zero_atTop_nsmul (phaseFlow a 1)).continuousAt_comp hadd.continuousAt
  have hfreq := hcluster.frequently (p := (· ∈ U)) (hU.mem_nhds hs)
  obtain ⟨N, hN⟩ := exists_nat_ge (R - s)
  obtain ⟨n, hn, hnu⟩ := frequently_atTop.mp hfreq N
  have hn' : (N : ℝ) ≤ n := by exact_mod_cast hn
  exact ⟨s + n, by linarith, hnu⟩

/-- A continuous real modulation can hit any neighborhood of the prescribed prime phases
at a time at least `R`. No independence condition involving `1` is required. -/
public theorem exists_primePhase_hit_after (p : ι → ℕ) (hp : ∀ i, (p i).Prime)
    (hinj : Function.Injective p) (z : ι → ℂ) (hz : ∀ i, ‖z i‖ = 1) (R : ℝ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ t : ℝ, R ≤ t ∧ ∀ i, dist (Complex.exp (Complex.I * t * Real.log (p i : ℝ))) (z i) < ε := by
  let a (i : ι) := Real.log (p i : ℝ)
  let e := AddCircle.homeomorphCircle (T := 1) one_ne_zero
  let g (x : UnitAddTorus ι) (i : ι) : ℂ := e (x i)
  have hg : Continuous g := continuous_pi fun i ↦
    continuous_subtype_val.comp (e.continuous.comp (continuous_apply i))
  let u (i : ι) : Circle := ⟨z i, by
    change z i ∈ Metric.sphere 0 1
    exact mem_sphere_zero_iff_norm.mpr (hz i)⟩
  let w (i : ι) := e.symm (u i)
  have hw : g w = z := by
    funext i
    exact congrArg (fun v : Circle ↦ (v : ℂ)) (e.apply_symm_apply (u i))
  have hphase (t : ℝ) (i : ι) :
      g (phaseFlow a t) i = Complex.exp (Complex.I * t * Real.log (p i : ℝ)) := by
    change (↑(e ((t * a i / (2 * Real.pi) : ℝ) : UnitAddCircle)) : ℂ) = _
    rw [AddCircle.homeomorphCircle_apply, AddCircle.toCircle_apply_mk, div_one,
      mul_div_cancel₀ _ (by positivity : 2 * Real.pi ≠ 0), Circle.coe_exp, Complex.ofReal_mul]
    dsimp [a]
    congr 1
    ring
  have hU : IsOpen (g ⁻¹' Metric.ball z ε) := Metric.isOpen_ball.preimage hg
  have hwU : w ∈ g ⁻¹' Metric.ball z ε := by
    simpa only [mem_preimage, hw, Metric.mem_ball, dist_self] using hε
  obtain ⟨t, ht, htU⟩ := phaseFlow_hit_after (phaseFlow_dense a (primeLog_integerRelation p hp hinj))
    hU hwU R
  refine ⟨t, ht, fun i ↦ ?_⟩
  rw [← hphase]
  exact (dist_pi_lt_iff hε).mp (Metric.mem_ball.mp htU) i

/-- One sequence of real times tending to `+∞` realizes all the prescribed unit phases
on the given finite family of distinct primes, including the empty family. -/
public theorem exists_primePhaseRecurrence (p : ι → ℕ) (hp : ∀ i, (p i).Prime)
    (hinj : Function.Injective p) (z : ι → ℂ) (hz : ∀ i, ‖z i‖ = 1) :
    ∃ y : ℕ → ℝ, Tendsto y atTop atTop ∧ Tendsto
      (fun j i ↦ Complex.exp (Complex.I * (y j : ℂ) * Real.log (p i : ℝ))) atTop (𝓝 z) := by
  have h (j : ℕ) := exists_primePhase_hit_after p hp hinj z hz ((j : ℝ) + 1)
    (ε := 1 / ((j : ℝ) + 1)) (by positivity)
  choose y hy hdist using h
  refine ⟨y, tendsto_atTop_mono (fun j ↦ (le_add_of_nonneg_right zero_le_one).trans (hy j))
    tendsto_natCast_atTop_atTop, tendsto_pi_nhds.mpr fun i ↦ Metric.tendsto_atTop.mpr ?_⟩
  intro ε hε
  have hsmall := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).eventually_lt_const hε
  obtain ⟨N, hN⟩ := eventually_atTop.mp hsmall
  exact ⟨N, fun j hj ↦ (hdist j i).trans (hN j hj)⟩

/-- If a prime phase tends to the conjugate of the active coefficient `c`, then the
actual modulated coefficient at `p ^ k`, namely `c ^ k * exp (I * y * log (p ^ k))`,
tends to `1`. The power is interpreted in `ℕ` before taking the real logarithm. -/
public theorem tendsto_primePowerPhaseCancellation {α : Type*} {l : Filter α} {y : α → ℝ}
    {p : ℕ} {c : ℂ} (hc : ‖c‖ = 1)
    (h : Tendsto (fun j ↦ Complex.exp (Complex.I * (y j : ℂ) * Real.log (p : ℝ))) l (𝓝 (conj c)))
    (k : ℕ) :
    Tendsto (fun j ↦ c ^ k * Complex.exp (Complex.I * (y j : ℂ) * Real.log ((p ^ k : ℕ) : ℝ)))
      l (𝓝 1) := by
  have hphase (t : ℝ) : (Complex.exp (Complex.I * (t : ℂ) * Real.log (p : ℝ))) ^ k =
      Complex.exp (Complex.I * (t : ℂ) * Real.log ((p ^ k : ℕ) : ℝ)) := by
    rw [← Complex.exp_nat_mul, Nat.cast_pow, Real.log_pow, Complex.ofReal_mul]
    push_cast
    congr 1
    ring
  have hcancel : c * conj c = 1 := by
    simp [Complex.mul_conj, Complex.normSq_eq_norm_sq, hc]
  have hlim := (tendsto_const_nhds (x := c ^ k) (f := l)).mul (h.pow k)
  rw [← mul_pow, hcancel, one_pow] at hlim
  simpa only [hphase] using hlim

/-- With the conjugate target at each active prime, the same late-time sequence cancels
all active prime-power coefficients. For a Dirichlet character, take `c i = χ (p i)`
on the primes coprime to its modulus; multiplicativity gives `χ (p i ^ k) = c i ^ k`.
The prime-power limits hold jointly on any finite set of such powers. -/
public theorem exists_primePowerPhaseCancellation (p : ι → ℕ) (hp : ∀ i, (p i).Prime)
    (hinj : Function.Injective p) (c : ι → ℂ) (hc : ∀ i, ‖c i‖ = 1) :
    ∃ y : ℕ → ℝ, Tendsto y atTop atTop ∧
      Tendsto (fun j i ↦ Complex.exp (Complex.I * (y j : ℂ) * Real.log (p i : ℝ)))
        atTop (𝓝 (fun i ↦ conj (c i))) ∧
      ∀ i k, Tendsto (fun j ↦
        c i ^ k * Complex.exp (Complex.I * (y j : ℂ) * Real.log ((p i ^ k : ℕ) : ℝ))) atTop (𝓝 1) := by
  obtain ⟨y, hy, hphase⟩ := exists_primePhaseRecurrence p hp hinj (fun i ↦ conj (c i))
    (fun i ↦ by simpa using hc i)
  exact ⟨y, hy, hphase, fun i k ↦
    tendsto_primePowerPhaseCancellation (hc i) (tendsto_pi_nhds.mp hphase i) k⟩

end Masullo
