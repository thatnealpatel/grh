module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Finset.Prod
public import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Algebra.BigOperators.Associated
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Packing balanced splits of a realized prime ratio

Source: `de4e5e15:.godel/bob/jointly-separated-arc-test.md:58–63`,
“Price the splits,” for the coefficient of `cos z_Q` at a fixed realized `Q`.
Here `n = 2h`. The positive and negative pools are the already recovered starts.
We forget the complementary window and admissibility gates: only the centers
must lie in the first open window, and the exchange images need only be balanced.
This counts splits with their sign pools fixed, not orderings within the two copies.

Owning check session: `01a209a4-4028-76c1-a295-487f5bedcbac`.
-/

open scoped BigOperators
open Finset

namespace BalancedRatioSplitPacking

/-- All splits with `h` starts chosen from each of the two sign pools. -/
@[expose] public def splits (P N : Finset ℕ) (h : ℕ) : Finset (Finset ℕ × Finset ℕ) :=
  P.powersetCard h ×ˢ N.powersetCard h

private noncomputable def label (d p : ℕ) : ℝ := Real.log ((↑(p + d) : ℝ) / p)

/-- The exact signed log coordinate `z_U` of the first copy. -/
@[expose] public noncomputable def coordinate (d : ℕ) (t : ℝ) (U : Finset ℕ × Finset ℕ) : ℝ :=
  t * ((∑ p ∈ U.1, Real.log ((↑(p + d) : ℝ) / p)) -
    (∑ p ∈ U.2, Real.log ((↑(p + d) : ℝ) / p)))

private theorem sum_sdiff_sub (f : ℕ → ℝ) (S T : Finset ℕ) :
    (∑ p ∈ S, f p) - (∑ p ∈ T, f p) =
      (∑ p ∈ S \ T, f p) - (∑ p ∈ T \ S, f p) := by
  have hS := sum_sdiff (f := f) (inter_subset_left (s₁ := S) (s₂ := T))
  have hT := sum_sdiff (f := f) (inter_subset_right (s₁ := S) (s₂ := T))
  rw [sdiff_inter_self_left] at hS
  rw [sdiff_inter_self_right] at hT
  linarith only [hS, hT]

private def cross (d : ℕ) (A B : Finset ℕ) : Finset ℕ := A.image (· + d) ∪ B

private theorem shift_injective (d : ℕ) : Function.Injective (fun p : ℕ ↦ p + d) :=
  fun _ _ h ↦ Nat.add_right_cancel h

private theorem cross_subset {d : ℕ} {I A B : Finset ℕ} (hA : A ⊆ I) (hB : B ⊆ I) :
    cross d A B ⊆ I.image (· + d) ∪ I :=
  union_subset_union (image_subset_image hA) hB

private theorem cross_disjoint {d : ℕ} {I A B : Finset ℕ} (hA : A ⊆ I) (hB : B ⊆ I)
    (hAB : Disjoint A B) (hI : Disjoint I (I.image (· + d))) :
    Disjoint (cross d A B) (cross d B A) := by
  unfold cross
  exact disjoint_union_left.mpr ⟨
    disjoint_union_right.mpr ⟨(disjoint_image (shift_injective d)).mpr hAB,
      hI.symm.mono (image_subset_image hA) hA⟩,
    disjoint_union_right.mpr ⟨hI.mono hB (image_subset_image hB), hAB.symm⟩⟩

private theorem prime_prod_ne {S T : Finset ℕ} (hST : Disjoint S T) (hS : S.Nonempty)
    (hpS : ∀ p ∈ S, p.Prime) (hpT : ∀ p ∈ T, p.Prime) :
    (∏ p ∈ S, p) ≠ ∏ p ∈ T, p := by
  obtain ⟨p, hp⟩ := hS
  intro heq
  have hdvd : p ∣ ∏ q ∈ T, q := heq ▸ dvd_prod_of_mem id hp
  obtain ⟨q, hq, hpq⟩ := ((hpS p hp).prime.dvd_finsetProd_iff id).mp hdvd
  have he : p = q := ((Nat.dvd_prime (hpT q hq)).mp hpq).resolve_left (hpS p hp).ne_one
  exact (disjoint_left.mp hST hp) (he.symm ▸ hq)

private theorem log_cross {d : ℕ} {I A B : Finset ℕ} (hI : Disjoint I (I.image (· + d)))
    (hA : A ⊆ I) (hB : B ⊆ I) (hp : ∀ p ∈ I.image (· + d) ∪ I, p.Prime) :
    Real.log (↑(∏ p ∈ cross d A B, p) : ℝ) =
      (∑ p ∈ A, Real.log (↑(p + d) : ℝ)) + ∑ p ∈ B, Real.log (p : ℝ) := by
  rw [Nat.cast_prod, Real.log_prod (fun p hp' ↦ Nat.cast_ne_zero.mpr
    (hp p (cross_subset hA hB hp')).ne_zero), cross,
    sum_union (hI.symm.mono (image_subset_image hA) hB),
    sum_image (shift_injective d).injOn]

private theorem height {S : Finset ℕ} {X : ℝ} {m : ℕ} (hX : 1 ≤ X) (hm : S.card ≤ m)
    (hb : ∀ p ∈ S, (p : ℝ) ≤ X) : (↑(∏ p ∈ S, p) : ℝ) ≤ X ^ m := by
  rw [Nat.cast_prod]
  calc
    _ ≤ ∏ _p ∈ S, X := prod_le_prod₀ (fun p _ ↦ Nat.cast_nonneg p) hb
    _ = X ^ S.card := prod_const _
    _ ≤ X ^ m := pow_le_pow_right₀ hX hm

-- The same integer-height argument as in `PrimeTupleRedrawSpacing`, applied here
-- to the cross-products after cancellation rather than to an enumeration of slots.
private theorem inv_le_log_div_of_lt {a b : ℕ} (ha : 0 < a) (hab : a < b) :
    (b : ℝ)⁻¹ ≤ Real.log ((b : ℝ) / a) := by
  have haR : 0 < (a : ℝ) := Nat.cast_pos.mpr ha
  have hbR : 0 < (b : ℝ) := Nat.cast_pos.mpr (ha.trans hab)
  have hgap : (a : ℝ) + 1 ≤ b := by exact_mod_cast Nat.succ_le_of_lt hab
  calc
    (b : ℝ)⁻¹ = 1 / (b : ℝ) := (one_div _).symm
    _ ≤ ((b : ℝ) - a) / b := div_le_div_of_nonneg_right (by linarith only [hgap]) hbR.le
    _ = 1 - (a : ℝ) / b := by rw [sub_div, div_self hbR.ne']
    _ ≤ _ := by
      have h := Real.log_le_sub_one_of_pos (div_pos haR hbR)
      rw [Real.log_div haR.ne' hbR.ne'] at h
      rw [Real.log_div hbR.ne' haR.ne']
      linarith only [h]

private theorem log_gap {a b : ℕ} {H : ℝ} (ha : 0 < a) (hb : 0 < b)
    (haH : (a : ℝ) ≤ H) (hbH : (b : ℝ) ≤ H) (hab : a ≠ b) :
    H⁻¹ ≤ |Real.log ((a : ℝ) / b)| := by
  rcases lt_or_gt_of_ne hab with h | h
  · have haR : (a : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr ha.ne'
    have hbR : (b : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hb.ne'
    calc
      _ ≤ (b : ℝ)⁻¹ := inv_anti₀ (Nat.cast_pos.mpr hb) hbH
      _ ≤ Real.log ((b : ℝ) / a) := inv_le_log_div_of_lt ha h
      _ = -Real.log ((a : ℝ) / b) := by rw [Real.log_div hbR haR, Real.log_div haR hbR, neg_sub]
      _ ≤ _ := neg_le_abs _
  · exact (inv_anti₀ (Nat.cast_pos.mpr ha) haH).trans
      ((inv_le_log_div_of_lt hb h).trans (le_abs_self _))

/-- If two distinct splits differ at at most `m` starts, cancelling the shared
labels leaves a nonunit ratio of integer heights at most `X^m`. The distance
between the scaled log coordinates is consequently at least `t / X^m`.

The starts and their translates are internally distinct since the pools are
sets with disjoint signs and translation is injective. `hEndpoints` excludes
collisions between a start and a shifted endpoint. -/
public theorem spacing {P N : Finset ℕ} {h d m : ℕ} {X t : ℝ}
    {U V : Finset ℕ × Finset ℕ} (hPN : Disjoint P N)
    (hEndpoints : Disjoint (P ∪ N) ((P ∪ N).image (· + d)))
    (hp : ∀ p ∈ P ∪ N, p.Prime ∧ (p + d).Prime ∧ (↑(p + d) : ℝ) ≤ X)
    (hd : 0 < d) (hX : 1 < X) (ht : 0 < t) (hU : U ∈ splits P N h) (hV : V ∈ splits P N h)
    (hne : U ≠ V)
    (hm : (U.1 \ V.1).card + (V.1 \ U.1).card + (U.2 \ V.2).card + (V.2 \ U.2).card ≤ m) :
    t / X ^ m ≤ |coordinate d t U - coordinate d t V| := by
  have hUP := (mem_powersetCard.mp (mem_product.mp hU).1).1
  have hUN := (mem_powersetCard.mp (mem_product.mp hU).2).1
  have hVP := (mem_powersetCard.mp (mem_product.mp hV).1).1
  have hVN := (mem_powersetCard.mp (mem_product.mp hV).2).1
  let I := P ∪ N
  let A := (U.1 \ V.1) ∪ (V.2 \ U.2)
  let B := (V.1 \ U.1) ∪ (U.2 \ V.2)
  have hAP : U.1 \ V.1 ⊆ P := sdiff_subset.trans hUP
  have hAN : V.2 \ U.2 ⊆ N := sdiff_subset.trans hVN
  have hBP : V.1 \ U.1 ⊆ P := sdiff_subset.trans hVP
  have hBN : U.2 \ V.2 ⊆ N := sdiff_subset.trans hUN
  have hA : A ⊆ I := union_subset (hAP.trans subset_union_left) (hAN.trans subset_union_right)
  have hB : B ⊆ I := union_subset (hBP.trans subset_union_left) (hBN.trans subset_union_right)
  have hAB : Disjoint A B := by
    dsimp only [A, B]
    exact disjoint_union_left.mpr ⟨
      disjoint_union_right.mpr ⟨sdiff_disjoint.mono_right sdiff_subset, hPN.mono hAP hBN⟩,
      disjoint_union_right.mpr ⟨hPN.symm.mono hAN hBP, sdiff_disjoint.mono_right sdiff_subset⟩⟩
  have hnonempty : A.Nonempty ∨ B.Nonempty := by
    by_contra! he
    have hsA := union_eq_empty.mp he.1
    have hsB := union_eq_empty.mp he.2
    exact hne (Prod.ext (le_antisymm (sdiff_eq_empty_iff_subset.mp hsA.1)
      (sdiff_eq_empty_iff_subset.mp hsB.1)) (le_antisymm
        (sdiff_eq_empty_iff_subset.mp hsB.2) (sdiff_eq_empty_iff_subset.mp hsA.2)))
  have hbounds p (hmem : p ∈ I.image (· + d) ∪ I) : p.Prime ∧ (p : ℝ) ≤ X := by
    rcases mem_union.mp hmem with hmem | hmem
    · obtain ⟨q, hq, rfl⟩ := mem_image.mp hmem
      exact ⟨(hp q hq).2.1, (hp q hq).2.2⟩
    · have hshift : (p : ℝ) < (↑(p + d) : ℝ) := Nat.cast_lt.mpr (Nat.lt_add_of_pos_right hd)
      exact ⟨(hp p hmem).1, hshift.le.trans (hp p hmem).2.2⟩
  -- Each cross-product uses one endpoint per surviving start; the two factor sets
  -- are disjoint, so a prime on either nonempty side cannot divide the other side.
  let C := cross d A B
  let D := cross d B A
  have hc := cross_subset (d := d) hA hB
  have hDsub := cross_subset (d := d) hB hA
  have hcPrime p (hp' : p ∈ C) := (hbounds p (hc hp')).1
  have hdPrime p (hp' : p ∈ D) := (hbounds p (hDsub hp')).1
  have hCD := cross_disjoint hA hB hAB hEndpoints
  have hprod : (∏ p ∈ C, p) ≠ ∏ p ∈ D, p := by
    rcases hnonempty with ⟨p, hp⟩ | ⟨p, hp⟩
    · exact (prime_prod_ne hCD.symm ⟨p, mem_union_right _ hp⟩ hdPrime hcPrime).symm
    · exact prime_prod_ne hCD ⟨p, mem_union_right _ hp⟩ hcPrime hdPrime
  have hsum : A.card + B.card ≤ m := by
    have ha := card_union_le (U.1 \ V.1) (V.2 \ U.2)
    have hb := card_union_le (V.1 \ U.1) (U.2 \ V.2)
    dsimp only [A, B]
    omega
  have hcard (S T : Finset ℕ) (hst : S.card + T.card ≤ m) : (cross d S T).card ≤ m :=
    (card_union_le _ _).trans ((Nat.add_le_add_right card_image_le _).trans hst)
  have hposC : 0 < ∏ p ∈ C, p := prod_pos fun p hp' ↦ (hcPrime p hp').pos
  have hposD : 0 < ∏ p ∈ D, p := prod_pos fun p hp' ↦ (hdPrime p hp').pos
  have hreal : coordinate d t U - coordinate d t V =
      t * Real.log ((↑(∏ p ∈ C, p) : ℝ) / ↑(∏ p ∈ D, p)) := by
    rw [Real.log_div (Nat.cast_ne_zero.mpr hposC.ne') (Nat.cast_ne_zero.mpr hposD.ne'),
      log_cross hEndpoints hA hB (fun p hmem ↦ (hbounds p hmem).1),
      log_cross hEndpoints hB hA (fun p hmem ↦ (hbounds p hmem).1)]
    unfold coordinate
    simp only [A, B, sum_union (hPN.mono hAP hAN), sum_union (hPN.mono hBP hBN)]
    have hlabel (S : Finset ℕ) (hS : S ⊆ I) : (∑ p ∈ S, label d p) =
        (∑ p ∈ S, Real.log (↑(p + d) : ℝ)) - ∑ p ∈ S, Real.log (p : ℝ) := by
      rw [← sum_sub_distrib]
      exact sum_congr rfl fun p hp' ↦ Real.log_div
        (Nat.cast_ne_zero.mpr (hp p (hS hp')).2.1.ne_zero)
        (Nat.cast_ne_zero.mpr (hp p (hS hp')).1.ne_zero)
    change t * ((∑ p ∈ U.1, label d p) - ∑ p ∈ U.2, label d p) -
      t * ((∑ p ∈ V.1, label d p) - ∑ p ∈ V.2, label d p) = _
    rw [← mul_sub, sub_sub_sub_comm, sum_sdiff_sub _ U.1 V.1, sum_sdiff_sub _ U.2 V.2,
      hlabel _ (hAP.trans subset_union_left), hlabel _ (hBP.trans subset_union_left),
      hlabel _ (hBN.trans subset_union_right), hlabel _ (hAN.trans subset_union_right)]
    congr 1
    ring
  rw [hreal, abs_mul, abs_of_pos ht, div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_left (log_gap hposC hposD
    (height hX.le (hcard A B hsum) (fun p hp' ↦ (hbounds p (hc hp')).2))
    (height hX.le (hcard B A (by omega)) (fun p hp' ↦ (hbounds p (hDsub hp')).2)) hprod) ht.le

private def choices (P : Finset ℕ) (k : ℕ) (U : Finset ℕ × Finset ℕ) :
    Finset (Finset ℕ × Finset ℕ) :=
  U.1.powersetCard k ×ˢ (P \ U.1).powersetCard k

private def exchange (U RI : Finset ℕ × Finset ℕ) : Finset ℕ × Finset ℕ :=
  ((U.1 \ RI.1) ∪ RI.2, U.2)

private def exchanges (P : Finset ℕ) (k : ℕ) (U : Finset ℕ × Finset ℕ) :
    Finset (Finset ℕ × Finset ℕ) :=
  (choices P k U).image (exchange U)

-- The two differences recover the chosen removal and insertion, even when k = 0 or h.
private theorem recover {P : Finset ℕ} {k : ℕ} {U RI : Finset ℕ × Finset ℕ}
    (hRI : RI ∈ choices P k U) :
    (U.1 \ (exchange U RI).1, (exchange U RI).1 \ U.1) = RI := by
  obtain ⟨hR, hI⟩ := mem_product.mp hRI
  have hRS := (mem_powersetCard.mp hR).1
  have hIS := (mem_powersetCard.mp hI).1
  apply Prod.ext
  · ext p
    have h₁ : p ∈ RI.1 → p ∈ U.1 := fun hp ↦ hRS hp
    have h₂ : p ∈ RI.2 → p ∉ U.1 := fun hp ↦ (mem_sdiff.mp (hIS hp)).2
    simp only [exchange, mem_sdiff, mem_union]
    tauto
  · ext p
    have h₂ : p ∈ RI.2 → p ∉ U.1 := fun hp ↦ (mem_sdiff.mp (hIS hp)).2
    simp only [exchange, mem_sdiff, mem_union]
    tauto

private theorem card_exchanges {P N : Finset ℕ} {h k : ℕ} {U : Finset ℕ × Finset ℕ}
    (hP : P.card = 2 * h) (hU : U ∈ splits P N h) :
    (exchanges P k U).card = (h.choose k) ^ 2 := by
  obtain ⟨hsub, hcard⟩ := mem_powersetCard.mp (mem_product.mp hU).1
  have hcomp : (P \ U.1).card = h := by
    rw [card_sdiff_of_subset hsub, hP]
    omega
  have hinj : Set.InjOn (exchange U) (choices P k U : Set (Finset ℕ × Finset ℕ)) := by
    intro RI hRI RJ hRJ heq
    rw [← recover (mem_coe.mp hRI), ← recover (mem_coe.mp hRJ), heq]
  rw [exchanges, card_image_of_injOn hinj, choices, card_product, card_powersetCard,
    card_powersetCard, hcomp, hcard, pow_two]

private theorem exchange_spec {P N : Finset ℕ} {h k : ℕ} {U W : Finset ℕ × Finset ℕ}
    (hk : k ≤ h) (hU : U ∈ splits P N h) (hW : W ∈ exchanges P k U) :
    W ∈ splits P N h ∧ W.2 = U.2 ∧ (U.1 \ W.1).card = k ∧ (W.1 \ U.1).card = k := by
  obtain ⟨RI, hRI, rfl⟩ := mem_image.mp hW
  obtain ⟨hR, hI⟩ := mem_product.mp hRI
  obtain ⟨hRS, hRcard⟩ := mem_powersetCard.mp hR
  obtain ⟨hIS, hIcard⟩ := mem_powersetCard.mp hI
  obtain ⟨hUP, hUN⟩ := mem_product.mp hU
  obtain ⟨hUS, hUcard⟩ := mem_powersetCard.mp hUP
  have hdis : Disjoint (U.1 \ RI.1) RI.2 :=
    sdiff_disjoint.symm.mono sdiff_subset hIS
  have hbal : exchange U RI ∈ splits P N h := by
    refine (mem_product (p := exchange U RI)).mpr ⟨mem_powersetCard.mpr ⟨?_, ?_⟩, hUN⟩
    · exact union_subset (sdiff_subset.trans hUS) (hIS.trans sdiff_subset)
    · change ((U.1 \ RI.1) ∪ RI.2).card = h
      rw [card_union_of_disjoint hdis, card_sdiff_of_subset hRS, hUcard, hRcard, hIcard]
      exact Nat.sub_add_cancel hk
  have hrec := recover hRI
  exact ⟨hbal, rfl, (congrArg (fun x : Finset ℕ × Finset ℕ ↦ x.1.card) hrec).trans hRcard,
    (congrArg (fun x : Finset ℕ × Finset ℕ ↦ x.2.card) hrec).trans hIcard⟩

private theorem card_sdiff_triangle (A B C : Finset ℕ) :
    (A \ C).card ≤ (A \ B).card + (B \ C).card := by
  refine (card_le_card ?_).trans (card_union_le (A \ B) (B \ C))
  intro p hp
  obtain ⟨ha, hc⟩ := mem_sdiff.mp hp
  by_cases hb : p ∈ B
  · exact mem_union_right _ (mem_sdiff.mpr ⟨hb, hc⟩)
  · exact mem_union_left _ (mem_sdiff.mpr ⟨ha, hb⟩)

/-- The positive exchanges of radius `k` around the windowed centers do not
collide. Counting them in the full balanced split space gives the fixed-ratio
multiplicity bound, without imposing either window or any gate on the images. -/
public theorem card_mul_choose_sq_le {P N : Finset ℕ} {h k d : ℕ} {X t : ℝ}
    {F : Finset (Finset ℕ × Finset ℕ)}
    (hP : P.card = 2 * h) (hN : N.card = 2 * h) (hPN : Disjoint P N)
    (hEndpoints : Disjoint (P ∪ N) ((P ∪ N).image (· + d)))
    (hp : ∀ p ∈ P ∪ N, p.Prime ∧ (p + d).Prime ∧ (↑(p + d) : ℝ) ≤ X)
    (hd : 0 < d) (hX : 1 < X) (ht : 0 < t) (hk : k ≤ h)
    (htime : 16 * X ^ (4 * k) ≤ t) (hF : F ⊆ splits P N h)
    (hwindow : ∀ U ∈ F, |coordinate d t U| < 2 * Real.pi) :
    F.card * (h.choose k) ^ 2 ≤ ((2 * h).choose h) ^ 2 := by
  have hpair : (F : Set (Finset ℕ × Finset ℕ)).PairwiseDisjoint (exchanges P k) := by
    intro U hUF V hVF hne
    apply disjoint_left.mpr
    intro W hWU hWV
    have hU := hF (mem_coe.mp hUF)
    have hV := hF (mem_coe.mp hVF)
    obtain ⟨_, hWUn, hUW, hWU'⟩ := exchange_spec hk hU hWU
    obtain ⟨_, hWVn, hVW, hWV'⟩ := exchange_spec hk hV hWV
    have hneg : U.2 = V.2 := hWUn.symm.trans hWVn
    have hdist : (U.1 \ V.1).card + (V.1 \ U.1).card +
        (U.2 \ V.2).card + (V.2 \ U.2).card ≤ 4 * k := by
      have h₁ := card_sdiff_triangle U.1 W.1 V.1
      have h₂ := card_sdiff_triangle V.1 W.1 U.1
      rw [hUW, hWV'] at h₁
      rw [hVW, hWU'] at h₂
      simp only [hneg, sdiff_self, bot_eq_empty, card_empty, Nat.add_zero]
      omega
    have hspace := spacing hPN hEndpoints hp hd hX ht hU hV hne hdist
    have h16 : 16 ≤ t / X ^ (4 * k) := (le_div_iff₀ (pow_pos (zero_lt_one.trans hX) _)).mpr htime
    have hdiam := abs_sub (coordinate d t U) (coordinate d t V)
    linarith only [h16.trans hspace, hdiam, hwindow U (mem_coe.mp hUF),
      hwindow V (mem_coe.mp hVF), Real.pi_lt_four]
  have hall : F.biUnion (exchanges P k) ⊆ splits P N h := by
    intro W hW
    obtain ⟨U, hUF, hWU⟩ := mem_biUnion.mp hW
    exact (exchange_spec hk (hF hUF) hWU).1
  calc
    _ = (F.biUnion (exchanges P k)).card := by
      rw [card_biUnion hpair, sum_congr rfl (fun U hUF ↦ card_exchanges hP (hF hUF)),
        sum_const, Nat.nsmul_eq_mul]
    _ ≤ (splits P N h).card := card_le_card hall
    _ = _ := by rw [splits, card_product, card_powersetCard, card_powersetCard, hP, hN, pow_two]

end BalancedRatioSplitPacking
