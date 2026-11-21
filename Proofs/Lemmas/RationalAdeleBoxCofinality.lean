module

public import Lemmas.RationalIntegralAdeles
import Mathlib.Order.Filter.Pi

/-! # The two bounds for cofinal rational box stages -/

open NumberField IsDedekindDomain Set Topology Filter
open scoped RestrictedProduct

namespace Masullo

local notation "V" => HeightOneSpectrum (𝓞 ℚ)
local notation "F" => FiniteAdeleRing (𝓞 ℚ) ℚ
local notation "A" => AdeleRing (𝓞 ℚ) ℚ
local notation:max "O" v:max => HeightOneSpectrum.adicCompletionIntegers ℚ v
local notation "pOf" => Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)

/-- The additive subgroup `ℤ̂` inside the rational finite adeles. -/
@[expose] public def rationalFiniteIntegralAdeles : AddSubgroup F where
  carrier := {x | ∀ v : V, x v ∈ O v}
  zero_mem' v := (O v).zero_mem
  add_mem' hx hy v := (O v).add_mem _ _ (hx v) (hy v)
  neg_mem' hx v := (O v).toSubring.neg_mem (hx v)

local notation "W" => rationalFiniteIntegralAdeles

private noncomputable def integralEmbedding : RationalFiniteIntegers → F :=
  RestrictedProduct.structureMap (fun v : V ↦ v.adicCompletion ℚ) (fun v ↦ O v) cofinite

private theorem continuous_integralEmbedding : Continuous integralEmbedding :=
  RestrictedProduct.isEmbedding_structureMap.continuous

public theorem isOpen_rationalFiniteIntegralAdeles : IsOpen (W : Set F) :=
  RestrictedProduct.isOpen_forall_mem
    (fun v : V ↦ Valued.isOpen_valuationSubring (v.adicCompletion ℚ))

public theorem isCompact_rationalFiniteIntegralAdeles : IsCompact (W : Set F) := by
  let := compactSpace_rationalFiniteIntegers
  have hrange : range integralEmbedding = (W : Set F) :=
    RestrictedProduct.range_structureMap _ _
  rw [← hrange]
  exact isCompact_range continuous_integralEmbedding

private theorem nat_mul_mem (n : ℕ) {x : F} (hx : x ∈ W) : (n : F) * x ∈ W := by
  simpa only [nsmul_eq_mul] using rationalFiniteIntegralAdeles.nsmul_mem hx n

/-- Enlarging the level by divisibility enlarges the support subgroup. -/
public theorem rationalFinite_support_mono {n m : ℕ} (h : n ∣ m) :
    ((n : F) * ·) ⁻¹' (W : Set F) ⊆ ((m : F) * ·) ⁻¹' (W : Set F) := by
  obtain ⟨k, rfl⟩ := h
  intro x hx
  change (n : F) * x ∈ W at hx
  change ((n * k : ℕ) : F) * x ∈ W
  rw [Nat.cast_mul, mul_comm (n : F), mul_assoc]
  exact nat_mul_mem k hx

/-- A compact set of finite adeles has a common positive denominator. -/
public theorem exists_rationalFinite_support_bound {K : Set F} (hK : IsCompact K) :
    ∃ D : ℕ, 0 < D ∧ K ⊆ ((D : F) * ·) ⁻¹' (W : Set F) := by
  let U (d : ℕ+) : Set F := ((d.val : F) * ·) ⁻¹' (W : Set F)
  have hU (d : ℕ+) : IsOpen (U d) :=
    isOpen_rationalFiniteIntegralAdeles.preimage (continuous_const.mul continuous_id)
  have hcover : K ⊆ ⋃ d, U d := by
    intro x _
    obtain ⟨d, hd, hx⟩ := exists_nat_mul_mem_rationalIntegralAdeles ((0, x) : A)
    exact mem_iUnion.mpr ⟨⟨d, hd⟩, hx⟩
  obtain ⟨s, hs⟩ := hK.elim_finite_subcover U hU hcover
  classical
  let D := ∏ d ∈ s, d.val
  have hD : 0 < D := Finset.prod_pos fun d _ ↦ d.property
  refine ⟨D, hD, fun x hx ↦ ?_⟩
  obtain ⟨d, hd, hxd⟩ := mem_iUnion₂.mp (hs hx)
  exact rationalFinite_support_mono (Finset.dvd_prod_of_mem (fun d : ℕ+ ↦ d.val) hd) hxd

private theorem exists_local_invariance_level (v : V) {U : Set (O v)} (hU : U ∈ 𝓝 0) :
    ∃ n : ℕ, ∀ y : O v, ((pOf v : ℕ) ^ n : ℕ) • y ∈ U := by
  let p : ℕ := pOf v
  let : Fact p.Prime := ⟨(pOf v).property⟩
  let e : O v ≃A[ℤ] ℤ_[p] := Rat.HeightOneSpectrum.adicCompletionIntegers.padicIntEquiv v
  have hmem : e.symm ⁻¹' U ∈ 𝓝 (0 : ℤ_[p]) := by
    apply (e.symm.continuous.continuousAt (x := 0)).preimage_mem_nhds
    rwa [map_zero]
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hmem
  have hp : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε (inv_lt_one_of_one_lt₀ hp)
  refine ⟨n, fun y ↦ ?_⟩
  have hy : e (((p ^ n : ℕ)) • y) ∈ Metric.ball (0 : ℤ_[p]) ε := by
    rw [mem_ball_zero_iff, map_nsmul, nsmul_eq_mul, Nat.cast_pow, norm_mul,
      PadicInt.norm_p_pow, zpow_neg, zpow_natCast, ← inv_pow]
    exact (mul_le_of_le_one_right (by positivity : 0 ≤ (p : ℝ)⁻¹ ^ n) (PadicInt.norm_le_one (e y))).trans_lt hn
  simpa only [mem_preimage, ContinuousAlgEquiv.symm_apply_apply] using hball hy

/-- An open zero neighborhood contains `N ℤ̂` for a positive integer `N`.
This bound is independent of any compact support set. -/
public theorem exists_rationalFinite_invariance_bound {H : Set F} (hH : H ∈ 𝓝 (0 : F)) :
    ∃ N : ℕ, 0 < N ∧ ((N : F) * ·) '' (W : Set F) ⊆ H := by
  have hpre : integralEmbedding ⁻¹' H ∈ 𝓝 (0 : RationalFiniteIntegers) := by
    have hzero : integralEmbedding 0 = (0 : F) := FiniteAdeleRing.ext ℚ fun _ ↦ rfl
    exact continuous_integralEmbedding.continuousAt.preimage_mem_nhds (hzero.symm ▸ hH)
  rw [nhds_pi] at hpre
  obtain ⟨s, U, hU, hsub⟩ := Filter.mem_pi'.mp hpre
  choose n hn using fun v : V ↦ exists_local_invariance_level v (hU v)
  let f (v : V) : ℕ := (pOf v : ℕ) ^ n v
  let N := ∏ v ∈ s, f v
  have hN : 0 < N := Finset.prod_pos fun v _ ↦ pow_pos (pOf v).property.pos _
  refine ⟨N, hN, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  let y : RationalFiniteIntegers := fun v ↦ N • (⟨x v, hx v⟩ : O v)
  have hy : y ∈ (↑s : Set V).pi U := by
    intro v hv
    obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem f (show v ∈ s from hv)
    change N • (⟨x v, hx v⟩ : O v) ∈ U v
    rw [show N = f v * k from hk, mul_comm (f v) k, mul_nsmul]
    exact hn v _
  have hxy : integralEmbedding y = (N : F) * x := by
    apply FiniteAdeleRing.ext ℚ
    intro v
    change ((N • (⟨x v, hx v⟩ : O v) : O v) : v.adicCompletion ℚ) =
      (N : v.adicCompletion ℚ) * x v
    rw [nsmul_eq_mul]
    rfl
  change (N : F) * x ∈ H
  rw [← hxy]
  exact hsub hy

end Masullo
