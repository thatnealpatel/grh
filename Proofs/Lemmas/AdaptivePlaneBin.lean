module

public import Lemmas.DividedPlaneFilter
public import Mathlib.Algebra.Module.LinearMap.Prod
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Data.Nat.PrimeFin
public import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Nat.Find
import Mathlib.Tactic.Ring

/-!
# The finite nonvertical adaptive-bin price

Source: `1d036a89:.godel/alice/denominator-pair-gap-regions.md:41–47`, “One rank
test per bin,” with the coordinate conventions of the preceding local estimate.
The bin uses one fixed whole plane
lattice `Γ = P ∩ Λ` with injective gap projection. Its width and filtered index
use the index of the image of `Γ`, not the index of a sampled sublattice.

Scope: the determinant bound for the adaptive width and the finite count of
actual triples in that bin. The small divided coordinate recovers the original
`m` and hence the actual triple. Large divided coordinates have smooth crossing
divisors, each of whose fibers contains at most two primitive triples. No
asymptotic enumeration, gcd summation, or other rank branch is asserted.

Owning check session: `01a20e74-7a96-7653-9648-0eb1c4d5d43d`.
-/

namespace AdaptivePlaneBin

open DividedPlaneFilter

variable {Γ : AddSubgroup (ℤ × ℤ × ℤ)}

/-- Determinant of the two integral forms on the standard gap coordinates. -/
@[expose] public def formDet (u w : (ℤ × ℤ) →ₗ[ℤ] ℤ) : ℤ :=
  u (1, 0) * w (0, 1) - w (1, 0) * u (0, 1)

/-- The half-open dyadic bin and the product test at width `T`. -/
@[expose] public def Passes (u w : (ℤ × ℤ) →ₗ[ℤ] ℤ) (M D T : ℝ) (b : ℤ × ℤ) : Prop :=
  M ≤ |(u b : ℝ)| ∧ |(u b : ℝ)| < 2 * M ∧
    |(u b : ℝ) * (w b : ℝ)| ≤ |(formDet u w : ℝ)| * D * T

/-- The width uses the projected index of the entire fixed plane lattice. -/
@[expose] public noncomputable def adaptiveWidth (Γ : AddSubgroup (ℤ × ℤ × ℤ))
    (D T₀ T₁ : ℝ) : ℝ :=
  min T₁ (T₀ * ((gapProjection Γ).range.index : ℝ) / D)

private theorem form_det_identity (u w : (ℤ × ℤ) →ₗ[ℤ] ℤ) (b c : ℤ × ℤ) :
    formDet u w * gapDet b c = u b * w c - u c * w b := by
  have eval (ℓ : (ℤ × ℤ) →ₗ[ℤ] ℤ) (z : ℤ × ℤ) :
      ℓ z = z.1 * ℓ (1, 0) + z.2 * ℓ (0, 1) := by
    have hz : z.1 • ((1, 0) : ℤ × ℤ) + z.2 • ((0, 1) : ℤ × ℤ) = z := by
      ext <;> simp
    calc
      ℓ z = ℓ (z.1 • (1, 0) + z.2 • (0, 1)) := congrArg ℓ hz.symm
      _ = _ := by simp only [map_add, map_smul, smul_eq_mul]
  rw [eval u b, eval w c, eval u c, eval w b]
  unfold formDet gapDet
  ring

private theorem abs_gapDet_le_of_bin {u w : (ℤ × ℤ) →ₗ[ℤ] ℤ} {M D T : ℝ}
    {b c : ℤ × ℤ} (hM : 0 < M) (hdet : formDet u w ≠ 0)
    (hb : Passes u w M D T b) (hc : Passes u w M D T c) :
    |(gapDet b c : ℝ)| ≤ 4 * D * T := by
  let δ : ℝ := |(formDet u w : ℝ)|
  let A : ℝ := δ * D * T / M
  have hδ : 0 < δ := abs_pos.mpr (Int.cast_ne_zero.mpr hdet)
  have hw {z : ℤ × ℤ} (hz : Passes u w M D T z) : |(w z : ℝ)| ≤ A := by
    apply (le_div_iff₀ hM).mpr
    rw [mul_comm]
    exact (mul_le_mul_of_nonneg_right hz.1 (abs_nonneg _)).trans
      (by simpa only [abs_mul] using hz.2.2)
  have hA : 0 ≤ A := (abs_nonneg _).trans (hw hb)
  have hterm {x y : ℤ × ℤ} (hx : Passes u w M D T x) (hy : Passes u w M D T y) :
      |(u x : ℝ)| * |(w y : ℝ)| ≤ 2 * M * A :=
    (mul_le_mul_of_nonneg_left (hw hy) (abs_nonneg _)).trans
      (mul_le_mul_of_nonneg_right hx.2.1.le hA)
  have hid : (formDet u w : ℝ) * (gapDet b c : ℝ) =
      (u b : ℝ) * (w c : ℝ) - (u c : ℝ) * (w b : ℝ) := by
    exact_mod_cast form_det_identity u w b c
  have hAM : A * M = δ * D * T := div_mul_cancel₀ _ hM.ne'
  apply (mul_le_mul_iff_right₀ hδ).mp
  calc
    δ * |(gapDet b c : ℝ)| = |(formDet u w : ℝ) * (gapDet b c : ℝ)| := (abs_mul _ _).symm
    _ ≤ |(u b : ℝ)| * |(w c : ℝ)| + |(u c : ℝ)| * |(w b : ℝ)| := by
      rw [hid]
      simpa only [abs_mul] using abs_sub ((u b : ℝ) * (w c : ℝ)) ((u c : ℝ) * (w b : ℝ))
    _ ≤ 2 * M * A + 2 * M * A := add_le_add (hterm hb hc) (hterm hc hb)
    _ = 4 * (A * M) := by ring
    _ = δ * (4 * D * T) := by rw [hAM]; ring

/-- For passing points the determinant of the forms cancels, yielding `4DT`;
reducing the width in the fixed plane also gives `4DT ≤ 4CT₀`. -/
public theorem gapDet_le_adaptiveWidth {u w : (ℤ × ℤ) →ₗ[ℤ] ℤ} {M D T₀ T₁ : ℝ}
    (hM : 0 < M) (hD : 0 < D) (hdet : formDet u w ≠ 0) {p q : Γ}
    (hp : Passes u w M D (adaptiveWidth Γ D T₀ T₁) (gapProjection Γ p))
    (hq : Passes u w M D (adaptiveWidth Γ D T₀ T₁) (gapProjection Γ q)) :
    |(gapDet (gapProjection Γ p) (gapProjection Γ q) : ℝ)| ≤
        4 * D * adaptiveWidth Γ D T₀ T₁ ∧
      4 * D * adaptiveWidth Γ D T₀ T₁ ≤ 4 * ((gapProjection Γ).range.index : ℝ) * T₀ := by
  refine ⟨abs_gapDet_le_of_bin hM hdet hp hq, ?_⟩
  have hwidth : adaptiveWidth Γ D T₀ T₁ * D ≤ T₀ * ((gapProjection Γ).range.index : ℝ) :=
    (le_div_iff₀ hD).mp (min_le_right _ _)
  calc
    4 * D * adaptiveWidth Γ D T₀ T₁ = 4 * (adaptiveWidth Γ D T₀ T₁ * D) := by ring
    _ ≤ 4 * (T₀ * ((gapProjection Γ).range.index : ℝ)) :=
      mul_le_mul_of_nonneg_left hwidth (by norm_num)
    _ = _ := by ring

/-- Positive `X`-smooth divided coordinates at most `U`. -/
@[expose] public noncomputable def smallDividedR (U : ℝ) (X : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Icc 1 ⌊U⌋₊).filter fun r => ∀ p ∈ r.primeFactors, p ≤ X

/-- Positive `X`-smooth candidates in `(U, U * X]` with a prime predecessor
at most `U`. The list does not enumerate points or planes. -/
@[expose] public noncomputable def eligibleCrossingF (U : ℝ) (X : ℕ) : Finset ℕ := by
  classical
  exact (smallDividedR (U * (X : ℝ)) X).filter fun f =>
    U < (f : ℝ) ∧ ∃ p ∈ f.primeFactors, ((f / p : ℕ) : ℝ) ≤ U

public theorem mem_smallDividedR {U : ℝ} {X r : ℕ} (hU : 0 ≤ U) :
    r ∈ smallDividedR U X ↔ 1 ≤ r ∧ (r : ℝ) ≤ U ∧ ∀ p ∈ r.primeFactors, p ≤ X := by
  simp only [smallDividedR, Finset.mem_filter, Finset.mem_Icc, Nat.le_floor_iff hU, and_assoc]

public theorem mem_eligibleCrossingF {U : ℝ} {X f : ℕ} (hU : 0 ≤ U) :
    f ∈ eligibleCrossingF U X ↔
      (1 ≤ f ∧ (f : ℝ) ≤ U * (X : ℝ) ∧ ∀ p ∈ f.primeFactors, p ≤ X) ∧
        U < (f : ℝ) ∧ ∃ p ∈ f.primeFactors, ((f / p : ℕ) : ℝ) ≤ U := by
  simp only [eligibleCrossingF, Finset.mem_filter, mem_smallDividedR (mul_nonneg hU (Nat.cast_nonneg X))]

/-- The least divisor above `U` has a predecessor below or at `U` after removing
one prime factor. This proves the single-prime overshoot bound and coverage. -/
public theorem exists_crossingDivisor {U : ℝ} {X r : ℕ} (hU : 1 ≤ U) (hr : U < (r : ℝ))
    (hsmooth : ∀ p ∈ r.primeFactors, p ≤ X) :
    ∃ f ∈ eligibleCrossingF U X, f ∣ r := by
  classical
  have hex : ∃ n : ℕ, U < (n : ℝ) ∧ n ∣ r := ⟨r, hr, dvd_refl r⟩
  let f := Nat.find hex
  have hfr : U < (f : ℝ) ∧ f ∣ r := Nat.find_spec hex
  have hr0 : r ≠ 0 := by
    have : (0 : ℝ) < r := zero_lt_one.trans (hU.trans_lt hr)
    exact (Nat.cast_pos.mp this).ne'
  have hf1 : 1 < f := by exact_mod_cast hU.trans_lt hfr.1
  let p := f.minFac
  have hpf : p ∣ f := Nat.minFac_dvd f
  have hp : p.Prime := Nat.minFac_prime (ne_of_gt hf1)
  have hpmem : p ∈ f.primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpf, by omega⟩
  have hsf (q : ℕ) (hq : q ∈ f.primeFactors) : q ≤ X :=
    hsmooth q (Nat.primeFactors_mono hfr.2 hr0 hq)
  have hprev : ((f / p : ℕ) : ℝ) ≤ U := by
    apply le_of_not_gt
    intro h
    exact Nat.find_min hex (Nat.div_lt_self (by omega) hp.one_lt)
      ⟨h, (Nat.div_dvd_of_dvd hpf).trans hfr.2⟩
  have hovershoot : (f : ℝ) ≤ U * (X : ℝ) := calc
    (f : ℝ) = ((f / p : ℕ) : ℝ) * (p : ℝ) := by
      exact_mod_cast (Nat.div_mul_cancel hpf).symm
    _ ≤ U * (p : ℝ) := mul_le_mul_of_nonneg_right hprev (Nat.cast_nonneg p)
    _ ≤ U * (X : ℝ) := mul_le_mul_of_nonneg_left (by exact_mod_cast hsf p hpmem)
      (zero_le_one.trans hU)
  exact ⟨f, (mem_eligibleCrossingF (zero_le_one.trans hU)).mpr
    ⟨⟨hf1.le, hovershoot, hsf⟩, hfr.1, p, hpmem, hprev⟩, hfr.2⟩

/-- In the actual set, equality of divided coordinates recovers the same `m`
and therefore the same triple, without reconstructing arbitrary lattice points. -/
public theorem actualPoint_eq_of_dividedCoordinate (a : NormalizedCoordinate Γ) {S : Finset Γ}
    (hm : Set.InjOn (fun p : Γ => p.val.1) ↑S) {p q : Γ} (hp : p ∈ S) (hq : q ∈ S)
    (hr : a.r p = a.r q) : p = q :=
  hm hp hq (by
    change p.val.1 = q.val.1
    rw [a.m_eq p, a.m_eq q, hr])

/-- On the fixed plane, every crossing fiber of passing primitive triples has
at most two points: its index `C*f` strictly exceeds their determinant bound. -/
public theorem card_le_two_of_crossing (a : NormalizedCoordinate Γ) {F : Finset Γ} {f : ℕ}
    {u w : (ℤ × ℤ) →ₗ[ℤ] ℤ} {M D T₀ T₁ : ℝ}
    (hπ : Function.Injective (gapProjection Γ)) (hC : 0 < (gapProjection Γ).range.index)
    (hM : 0 < M) (hD : 0 < D) (hdet : formDet u w ≠ 0) (hf : 4 * T₀ < (f : ℝ))
    (hdvd : ∀ p ∈ F, f ∣ (a.r p).natAbs)
    (hprim : ∀ p ∈ F, Int.gcd p.val.1 p.val.2.1 = 1)
    (hpass : ∀ p ∈ F, Passes u w M D (adaptiveWidth Γ D T₀ T₁) (gapProjection Γ p)) :
    F.card ≤ 2 := by
  have hCR : (0 : ℝ) < (gapProjection Γ).range.index := Nat.cast_pos.mpr hC
  refine card_le_two_of_small_gapDet (a := a) (f := f) hπ ?_ hprim ?_
  · exact fun p hp => mem_dividedFilter.mpr (Int.natCast_dvd.mpr (hdvd p hp))
  · intro p hp q hq
    obtain ⟨h₁, h₂⟩ := gapDet_le_adaptiveWidth hM hD hdet (hpass p hp) (hpass q hq)
    apply (Nat.cast_lt (α := ℝ)).mp
    rw [Nat.cast_natAbs, Int.cast_abs, Nat.cast_mul]
    calc
      _ ≤ 4 * ((gapProjection Γ).range.index : ℝ) * T₀ := h₁.trans h₂
      _ = ((gapProjection Γ).range.index : ℝ) * (4 * T₀) := by ring
      _ < _ := mul_lt_mul_of_pos_left hf hCR

/-- The finite price of the nonvertical branch of one adaptive bin. Actual
inputs have positive smooth `m`. The single-prime crossing uses `1 ≤ 4*T₀`,
which holds for the source's `T₀ = G q^.160`. Both enumerands depend only on
the threshold and smoothness bound, not on per-filter occupancy. -/
public theorem card_le_small_add_twice_crossing (a : NormalizedCoordinate Γ) {S : Finset Γ}
    {u w : (ℤ × ℤ) →ₗ[ℤ] ℤ} {M D T₀ T₁ : ℝ} {X : ℕ}
    (hπ : Function.Injective (gapProjection Γ)) (hC : 0 < (gapProjection Γ).range.index)
    (hM : 0 < M) (hD : 0 < D) (hU : 1 ≤ 4 * T₀) (hdet : formDet u w ≠ 0)
    (hm : Set.InjOn (fun p : Γ => p.val.1) ↑S)
    (hpos : ∀ p ∈ S, 0 < p.val.1)
    (hsmooth : ∀ p ∈ S, ∀ k ∈ p.val.1.natAbs.primeFactors, k ≤ X)
    (hprim : ∀ p ∈ S, Int.gcd p.val.1 p.val.2.1 = 1)
    (hpass : ∀ p ∈ S, Passes u w M D (adaptiveWidth Γ D T₀ T₁) (gapProjection Γ p)) :
    S.card ≤ (smallDividedR (4 * T₀) X).card + 2 * (eligibleCrossingF (4 * T₀) X).card := by
  classical
  let U : ℝ := 4 * T₀
  let r (p : Γ) := (a.r p).natAbs
  let small := S.filter fun p => (r p : ℝ) ≤ U
  let fiber (f : ℕ) := S.filter fun p => f ∣ r p
  have hU₀ : 0 ≤ U := zero_le_one.trans hU
  have hrpos (p : Γ) (hp : p ∈ S) : 0 < a.r p :=
    (mul_pos_iff_of_pos_left a.j₀_pos).mp (a.m_eq p ▸ hpos p hp)
  have hrsmooth (p : Γ) (hp : p ∈ S) (k : ℕ) (hk : k ∈ (r p).primeFactors) : k ≤ X := by
    have hdvd : r p ∣ p.val.1.natAbs := by
      rw [a.m_eq p, Int.natAbs_mul]
      exact Nat.dvd_mul_left _ _
    exact hsmooth p hp k (Nat.primeFactors_mono hdvd (Int.natAbs_pos.mpr (hpos p hp).ne').ne' hk)
  have hcover : S ⊆ small ∪ (eligibleCrossingF U X).biUnion fiber := by
    intro p hp
    apply Finset.mem_union.mpr
    by_cases h : (r p : ℝ) ≤ U
    · exact Or.inl (Finset.mem_filter.mpr ⟨hp, h⟩)
    · obtain ⟨f, hf, hdvd⟩ := exists_crossingDivisor hU (lt_of_not_ge h) (hrsmooth p hp)
      exact Or.inr (Finset.mem_biUnion.mpr ⟨f, hf, Finset.mem_filter.mpr ⟨hp, hdvd⟩⟩)
  have hsmall : small.card ≤ (smallDividedR U X).card := by
    apply Finset.card_le_card_of_injOn r
    · intro p hp
      obtain ⟨hpS, hpr⟩ := Finset.mem_filter.mp (show p ∈ small from hp)
      exact (mem_smallDividedR hU₀).mpr
        ⟨Int.natAbs_pos.mpr (hrpos p hpS).ne', hpr, hrsmooth p hpS⟩
    · intro p hp q hq he
      have hpS : p ∈ S := (Finset.mem_filter.mp (show p ∈ small from hp)).1
      have hqS : q ∈ S := (Finset.mem_filter.mp (show q ∈ small from hq)).1
      apply actualPoint_eq_of_dividedCoordinate a hm hpS hqS
      rw [← Int.natAbs_of_nonneg (hrpos p hpS).le, ← Int.natAbs_of_nonneg (hrpos q hqS).le]
      exact congrArg (fun n : ℕ => (n : ℤ)) he
  have htwo (f : ℕ) (hf : f ∈ eligibleCrossingF U X) : (fiber f).card ≤ 2 := by
    have hcross := ((mem_eligibleCrossingF hU₀).mp hf).2.1
    exact card_le_two_of_crossing a hπ hC hM hD hdet hcross
      (fun _ hp => (Finset.mem_filter.mp hp).2)
      (fun p hp => hprim p (Finset.mem_filter.mp hp).1)
      (fun p hp => hpass p (Finset.mem_filter.mp hp).1)
  calc
    S.card ≤ (small ∪ (eligibleCrossingF U X).biUnion fiber).card := Finset.card_le_card hcover
    _ ≤ small.card + ((eligibleCrossingF U X).biUnion fiber).card := Finset.card_union_le _ _
    _ ≤ (smallDividedR U X).card + 2 * (eligibleCrossingF U X).card := by
      refine Nat.add_le_add hsmall (Finset.card_biUnion_le.trans ?_)
      calc
        (∑ f ∈ eligibleCrossingF U X, (fiber f).card) ≤ ∑ _f ∈ eligibleCrossingF U X, 2 :=
          Finset.sum_le_sum htwo
        _ = _ := by simp [Nat.mul_comm]

end AdaptivePlaneBin
