module

public import Theorems.IdeleIdealClassStrict
import Mathlib.RingTheory.Algebraic.Integral

/-! # Clearing finite denominators on a compact set of ideles

The fractional-ideal step in the proof of Masullo's Lemma 2.2.2.1(3),
PDF pp. 79–80 (see (2.2.2.10)–(11)), bounds the diagonal indices by one
lattice. Instead of the displayed uniformizer powers on p. 79, we use
the inverse finite ideal of each representative. Its image on a compact
set is finite, since the subgroup of finite integral units is open.
The final denominator is a positive ordinary integer, not merely an
element of the number field's ring of integers.
-/

open Filter IsDedekindDomain NumberField Set Topology
open scoped nonZeroDivisors WithZero

namespace Masullo

variable {K : Type*} [Field K] [NumberField K]

local notation "Ideg" => IdeleGroup (𝓞 K) K
local notation "V" => HeightOneSpectrum (𝓞 K)
local notation "J" => FractionalIdeal (𝓞 K)⁰ K
local notation "d" => IdeleGroup.unitEmbedding (𝓞 K) K

private noncomputable def finiteIdeal : Ideg →* Jˣ :=
  (finiteIdeleIdeal K).comp (ideleFinitePart (K := K))

private theorem finite_image_finiteIdeal {B : Set Ideg} (hB : IsCompact B) :
    (finiteIdeal '' B).Finite := by
  let _ : TopologicalSpace Jˣ := ⊥
  let _ : DiscreteTopology Jˣ := discreteTopology_bot _
  have hc : Continuous (finiteIdeal (K := K)) := by
    apply continuous_of_continuousAt_one
    rw [ContinuousAt, nhds_discrete Jˣ, map_one, tendsto_pure]
    have ho : IsOpen (ideleFiniteUnits (K := K) : Set Ideg) := by
      rw [← range_ideleFiniteStageEmbedding_empty]
      exact (isOpenEmbedding_ideleFiniteStageEmbedding K ∅).isOpen_range
    have hn := ho.mem_nhds (ideleFiniteUnits.one_mem)
    rw [← Filter.eventually_mem_set] at hn
    filter_upwards [hn] with b hb
    change finiteIdeleIdeal K (ideleFinitePart b) = 1
    apply (finiteIdeleIdeal_eq_one_iff _).mpr
    intro v
    rw [ideleFinitePart_apply]
    exact (mem_ideleFiniteUnits b).mp hb v
  exact (hB.image hc).finite_of_discrete

/-- If the finite coordinates of `d(a) * b` are integral, then `a` lies in
    the inverse finite ideal of `b`. The inverse sign comes from
    `(a) I(b) ⊆ 𝓞 K`. -/
private theorem mem_inverse_finiteIdeal (a : Kˣ) (b : Ideg)
    (h : ∀ v : V, ‖(d a * b).val.2 v‖ ≤ 1) : (a : K) ∈ ((finiteIdeal b : J)⁻¹ : J) := by
  have hle : (finiteIdeal (d a * b) : J) ≤ 1 := by
    apply le_one_of_count_nonneg (finiteIdeal _).ne_zero
    intro v
    change 0 ≤ FractionalIdeal.count K v (finiteIdeleIdeal K (ideleFinitePart (d a * b)) : J)
    rw [count_finiteIdeleIdeal, le_neg, neg_zero, ← WithZero.log_one]
    apply (WithZero.log_le_log (finiteIdele_valuation_ne_zero _ _) one_ne_zero).mpr
    rw [ideleFinitePart_apply]
    exact Valued.toNormedField.norm_le_one_iff.mp (h v)
  have hd : (finiteIdeal (d a) : J) = FractionalIdeal.spanSingleton (𝓞 K)⁰ (a : K) := by
    have hp : ideleFinitePart (d a) = FiniteAdeleRing.unitEmbedding (𝓞 K) K a := by
      apply Units.ext
      apply DFunLike.ext
      intro v
      rw [ideleFinitePart_apply, FiniteAdeleRing.unitEmbedding_apply]
      rfl
    change (finiteIdeleIdeal K (ideleFinitePart (d a)) : J) = _
    rw [hp, finiteIdeleIdeal_unitEmbedding]
  rw [map_mul, Units.val_mul, hd] at hle
  have hspan := mul_le_mul_left hle (finiteIdeal b : J)⁻¹
  rw [mul_assoc, mul_inv_cancel₀ (finiteIdeal b).ne_zero, mul_one, one_mul] at hspan
  exact FractionalIdeal.spanSingleton_le_iff_mem.mp hspan

private theorem clear_fractionalIdeal (j : J) :
    ∃ m : ℕ, 0 < m ∧ ∀ x ∈ j, (m : K) * x ∈ (1 : J) := by
  let y := algebraMap (𝓞 K) K j.den.val
  have hy : y ≠ 0 := map_ne_zero_of_mem_nonZeroDivisors _
    (FaithfulSMul.algebraMap_injective (𝓞 K) K) j.den.property
  have ha : IsAlgebraic ℤ y⁻¹ :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ K).mpr
      (NumberField.isAlgebraic K |>.isAlgebraic y⁻¹)
  obtain ⟨m, c, hm, he⟩ := ha.exists_nsmul_eq (𝓞 K)
  rw [nsmul_eq_mul] at he
  refine ⟨m, Nat.pos_of_ne_zero hm, fun x hx ↦ ?_⟩
  have hd : y * x ∈ (1 : J) := by
    refine FractionalIdeal.coeIdeal_le_one (I := j.num) ?_
    rw [← FractionalIdeal.den_mul_self_eq_num']
    exact FractionalIdeal.mul_mem_mul (FractionalIdeal.mem_spanSingleton_self _ _) hx
  have hprod := FractionalIdeal.mul_mem_mul (FractionalIdeal.coe_mem_one (𝓞 K)⁰ (P := K) c) hd
  rw [one_mul, ← he] at hprod
  have heq : ((m : K) * y⁻¹) * (y * x) = (m : K) * (y⁻¹ * y) * x := by ac_rfl
  simpa only [heq, inv_mul_cancel₀ hy, mul_one] using hprod

/-- One strictly positive rational integer clears all admissible diagonal
    indices on a compact set of ideles. `B` need not be in the norm-one
    subgroup; in particular one can use a fixed translate of a compact set. -/
public theorem exists_uniform_denominator_of_isCompact (B : Set Ideg) (hB : IsCompact B) :
    ∃ m : ℕ, 0 < m ∧ ∀ b ∈ B, ∀ a : Kˣ,
      (∀ v : V, ‖(d a * b).val.2 v‖ ≤ 1) →
      (m : K) * (a : K) ∈ Set.range (algebraMap (𝓞 K) K) := by
  classical
  have hf := finite_image_finiteIdeal hB
  choose n hn hc using fun j : Jˣ ↦ clear_fractionalIdeal ((j : J)⁻¹)
  let m := ∏ j ∈ hf.toFinset, n j
  refine ⟨m, Finset.prod_pos (fun j _ ↦ hn j), ?_⟩
  intro b hb a ha
  have hmem : finiteIdeal b ∈ hf.toFinset := hf.mem_toFinset.mpr ⟨b, hb, rfl⟩
  obtain ⟨k, hk : m = _⟩ := Finset.dvd_prod_of_mem n hmem
  have hclear := hc (finiteIdeal b) (a : K) (mem_inverse_finiteIdeal a b ha)
  rw [FractionalIdeal.mem_one_iff] at hclear
  obtain ⟨z, hz⟩ := hclear
  refine ⟨(k : 𝓞 K) * z, ?_⟩
  rw [map_mul, map_natCast, hz, hk, Nat.cast_mul]
  ac_rfl

end Masullo
