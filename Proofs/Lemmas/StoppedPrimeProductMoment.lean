module

public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Basic.Complex.Basic
import Mathlib.Basic.Complex.BigOperators
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Nat.Factors

/-! # Stopped ordered prime-product moments

Source: `145f6475:.godel/alice/stopped-conductor-window.md`, lines 17–31.
Owning check session: `01a2095b-3cd7-7c85-a8af-4a73f8cbf3ba`.

The finite coefficients count ordered leaves at the first crossing of a real threshold, with
repeated primes allowed. This is the coefficient bound for the stopped detecting polynomial,
not a prime number theorem estimate or a hybrid mean-value estimate. The finite complex identity
is obtained by conservation of the normalized mass under extension of each active tuple.
-/

open scoped BigOperators

namespace Masullo.StoppedPrimeProductMoment

/-- All ordered length-`k` tuples with entries in `S`, including repetitions. -/
@[expose] public def tuples (S : Finset ℕ) (k : ℕ) : Finset (Fin k → ℕ) :=
  Fintype.piFinset (fun _ ↦ S)

/-- The natural product used to index the coefficient of a tuple. -/
@[expose] public def tupleProduct {k : ℕ} (u : Fin k → ℕ) : ℕ := ∏ i, u i

/-- Product of the entries in positions strictly before `j`. -/
@[expose] public def prefixProduct {k : ℕ} (u : Fin k → ℕ) (j : ℕ) : ℕ :=
  ∏ i ∈ Finset.univ.filter (fun i : Fin k ↦ i.val < j), u i

/-- The full product reaches `U` and every proper prefix is below `U`. -/
@[expose] public def FirstCrossing {k : ℕ} (U : ℝ) (u : Fin k → ℕ) : Prop :=
  (∀ j < k, (prefixProduct u j : ℝ) < U) ∧ U ≤ (tupleProduct u : ℝ)

/-- Exactly the length-`k` leaves of the stopping rule. -/
@[expose] public noncomputable def stoppedTuples (S : Finset ℕ) (U : ℝ) (k : ℕ) :
    Finset (Fin k → ℕ) := by
  classical exact (tuples S k).filter (FirstCrossing U)

/-- Finite index set of actual products of length-`k` leaves. -/
@[expose] public noncomputable def stoppedProducts (S : Finset ℕ) (U : ℝ) (k : ℕ) : Finset ℕ :=
  (stoppedTuples S U k).image tupleProduct

/-- The coefficient `d_{k,n}`; it is zero off `stoppedProducts`. -/
@[expose] public noncomputable def coefficient (S : Finset ℕ) (U : ℝ) (b : ℕ → ℝ)
    (k n : ℕ) : ℝ :=
  ∑ u ∈ (stoppedTuples S U k).filter (fun u ↦ tupleProduct u = n), ∏ i, b (u i)

/-- No tuple contributes to a product off the stopped support. -/
public theorem coefficient_eq_zero_of_notMem {S : Finset ℕ} {U : ℝ} {k n : ℕ}
    (b : ℕ → ℝ) (hn : n ∉ stoppedProducts S U k) : coefficient S U b k n = 0 := by
  have h : (stoppedTuples S U k).filter (fun u ↦ tupleProduct u = n) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro u hu
    have huv : u ∈ stoppedTuples S U k ∧ tupleProduct u = n := Finset.mem_filter.mp hu
    exact hn (Finset.mem_image.mpr ⟨u, huv.1, huv.2⟩)
  rw [coefficient, h, Finset.sum_empty]

private theorem prefixProduct_mono {k : ℕ} {u : Fin k → ℕ} (hu : ∀ i, 1 ≤ u i) :
    Monotone (prefixProduct u) := by
  intro j l hjl
  apply Finset.prod_le_prod_of_subset_of_one_le
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    exact lt_of_lt_of_le hi hjl
  · exact fun i _ _ ↦ hu i

private theorem prefixProduct_pred {k : ℕ} (u : Fin (k + 1) → ℕ) :
    prefixProduct u k = tupleProduct (Fin.init u) := by
  rw [prefixProduct, Finset.prod_filter, Fin.prod_univ_castSucc]
  simp [tupleProduct, Fin.init, Fin.is_lt]

/-- With factors at least one, it is enough to check the immediate predecessor. -/
public theorem firstCrossing_succ_iff {k : ℕ} {U : ℝ} {u : Fin (k + 1) → ℕ}
    (hu : ∀ i, 1 ≤ u i) :
    FirstCrossing U u ↔ (tupleProduct (Fin.init u) : ℝ) < U ∧ U ≤ (tupleProduct u : ℝ) := by
  rw [← prefixProduct_pred]
  constructor
  · exact fun h ↦ ⟨h.1 k (Nat.lt_succ_self k), h.2⟩
  · rintro ⟨hpre, hfull⟩
    refine ⟨fun j hj ↦ lt_of_le_of_lt ?_ hpre, hfull⟩
    exact_mod_cast (prefixProduct_mono hu (Nat.le_of_lt_succ hj))

/-- The empty tuple is not a leaf when `U > 1`. -/
public theorem stoppedTuples_zero (S : Finset ℕ) {U : ℝ} (hU : 1 < U) :
    stoppedTuples S U 0 = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro u hu
  have hc := (Finset.mem_filter.mp hu).2.2
  simp only [tupleProduct, Fin.prod_univ_zero, Nat.cast_one] at hc
  exact hU.not_ge hc

/-- Every stopped product lies in the half-open real window `[U, U * X)`. -/
public theorem stoppedProducts_window {S : Finset ℕ} {U X : ℝ} {k n : ℕ}
    (hU : 1 < U) (hprime : ∀ p ∈ S, p.Prime) (hX : ∀ p ∈ S, (p : ℝ) ≤ X)
    (hn : n ∈ stoppedProducts S U k) : U ≤ (n : ℝ) ∧ (n : ℝ) < U * X := by
  classical
  obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hn
  cases k with
  | zero => simp [stoppedTuples_zero S hU] at hu
  | succ k =>
    obtain ⟨hu, hc⟩ := Finset.mem_filter.mp hu
    have hs := Fintype.mem_piFinset.mp hu
    obtain ⟨hpre, hfull⟩ := (firstCrossing_succ_iff (fun i ↦ (hprime _ (hs i)).one_lt.le)).mp hc
    refine ⟨hfull, ?_⟩
    have hp : 0 < (u (Fin.last k) : ℝ) := by exact_mod_cast (hprime _ (hs _)).pos
    rw [tupleProduct, Fin.prod_univ_castSucc, Nat.cast_mul]
    change (tupleProduct (Fin.init u) : ℝ) * (u (Fin.last k) : ℝ) < U * X
    exact (mul_lt_mul_of_pos_right hpre hp).trans_le
      (mul_le_mul_of_nonneg_left (hX _ (hs _)) (zero_le_one.trans hU.le))

private theorem exists_perm_of_product_eq {S : Finset ℕ} {k : ℕ} {u v : Fin k → ℕ}
    (hprime : ∀ p ∈ S, p.Prime) (hu : u ∈ tuples S k) (hv : v ∈ tuples S k)
    (heq : tupleProduct u = tupleProduct v) : ∃ σ : Equiv.Perm (Fin k), v = u ∘ σ := by
  have hfac (w : Fin k → ℕ) (hw : w ∈ tuples S k) :
      (List.ofFn w).Perm (tupleProduct w).primeFactorsList := by
    apply Nat.primeFactorsList_unique (Fin.prod_ofFn w)
    intro p hp
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hp
    exact hprime _ (Fintype.mem_piFinset.mp hw i)
  have hperm : (List.ofFn v).Perm (List.ofFn u) := by
    exact (hfac v hv).trans (heq ▸ (hfac u hu).symm)
  -- Match the positions of each prime separately, also when primes repeat.
  let e (p : ℕ) : {i // v i = p} ≃ {i // u i = p} := by
    have hcount := hperm.count_eq p
    simp only [List.count_ofFn] at hcount
    rw [← Fintype.card_subtype, ← Fintype.card_subtype] at hcount
    exact Fintype.equivOfCardEq hcount
  exact ⟨Equiv.ofFiberEquiv e, funext (fun i ↦ (Equiv.ofFiberEquiv_map e i).symm)⟩

/-- Each unrestricted ordered product fiber has at most `k!` elements. -/
public theorem card_productFiber_le {S : Finset ℕ} (hprime : ∀ p ∈ S, p.Prime) (k n : ℕ) :
    ((tuples S k).filter (fun u ↦ tupleProduct u = n)).card ≤ k.factorial := by
  classical
  let F := (tuples S k).filter (fun u ↦ tupleProduct u = n)
  change F.card ≤ k.factorial
  by_cases hF : F.Nonempty
  · obtain ⟨u, hu⟩ := hF
    let reindex (σ : Equiv.Perm (Fin k)) := u ∘ σ
    calc
      F.card ≤ (Finset.univ.image reindex).card := by
        apply Finset.card_le_card
        intro v hv
        obtain ⟨hu, hun⟩ := Finset.mem_filter.mp hu
        obtain ⟨hv, hvn⟩ := Finset.mem_filter.mp hv
        obtain ⟨σ, rfl⟩ := exists_perm_of_product_eq hprime hu hv (hun.trans hvn.symm)
        exact Finset.mem_image.mpr ⟨σ, Finset.mem_univ _, rfl⟩
      _ ≤ (Finset.univ : Finset (Equiv.Perm (Fin k))).card := Finset.card_image_le
      _ = k.factorial := by simp only [Finset.card_univ, Fintype.card_perm, Fintype.card_fin]
  · rw [Finset.not_nonempty_iff_eq_empty.mp hF, Finset.card_empty]
    exact Nat.zero_le _

private theorem card_stoppedFiber_le {S : Finset ℕ} {U : ℝ} {k n : ℕ}
    (hprime : ∀ p ∈ S, p.Prime) :
    ((stoppedTuples S U k).filter (fun u ↦ tupleProduct u = n)).card ≤ k.factorial := by
  classical
  refine (Finset.card_le_card ?_).trans (card_productFiber_le hprime k n)
  intro u hu
  obtain ⟨hu, hun⟩ := Finset.mem_filter.mp hu
  exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hu).1, hun⟩

/-- The squared coefficient bound for the stopped prime-product polynomials. The proof
works even for signed weights; allowing zero weights needs no change to the stopping rule. -/
public theorem sum_coefficient_sq_le {S : Finset ℕ} {U : ℝ} (hU : 1 < U)
    (hprime : ∀ p ∈ S, p.Prime) (b : ℕ → ℝ) (k : ℕ) :
    (∑ n ∈ stoppedProducts S U k, coefficient S U b k n ^ 2) ≤
      ((k.factorial : ℝ) / Real.sqrt U) * (∑ p ∈ S, Real.sqrt (p : ℝ) * b p ^ 2) ^ k := by
  classical
  let A := stoppedTuples S U k
  let W (u : Fin k → ℕ) : ℝ := ∏ i, b (u i)
  let w (p : ℕ) : ℝ := Real.sqrt (p : ℝ) * b p ^ 2
  let V (u : Fin k → ℕ) : ℝ := ∏ i, w (u i)
  let F (n : ℕ) := A.filter (fun u ↦ tupleProduct u = n)
  let C : ℝ := (k.factorial : ℝ) / Real.sqrt U
  have hsqrt : 0 < Real.sqrt U := Real.sqrt_pos.2 (zero_lt_one.trans hU)
  have hV (u : Fin k → ℕ) : 0 ≤ V u :=
    Finset.prod_nonneg (fun i _ ↦ mul_nonneg (Real.sqrt_nonneg _) (sq_nonneg _))
  have hweight (u : Fin k → ℕ) (hu : u ∈ A) : W u ^ 2 ≤ V u / Real.sqrt U := by
    have hcross : U ≤ (tupleProduct u : ℝ) := (Finset.mem_filter.mp hu).2.2
    have hV_eq : V u = Real.sqrt (tupleProduct u : ℝ) * W u ^ 2 := by
      dsimp only [V, w, W, tupleProduct]
      rw [Finset.prod_mul_distrib, ← Finset.prod_pow, Nat.cast_prod,
        Real.sqrt_prod Finset.univ (fun i _ ↦ Nat.cast_nonneg (u i))]
    rw [le_div_iff₀ hsqrt, hV_eq, mul_comm (W u ^ 2)]
    exact mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hcross) (sq_nonneg _)
  calc
    _ ≤ ∑ n ∈ stoppedProducts S U k, C * ∑ u ∈ F n, V u := by
      apply Finset.sum_le_sum
      intro n _
      calc
        coefficient S U b k n ^ 2 ≤ ((F n).card : ℝ) * ∑ u ∈ F n, W u ^ 2 := by
          simpa [coefficient, F, A, W] using
            Finset.sum_mul_sq_le_sq_mul_sq (F n) (fun _ ↦ (1 : ℝ)) W
        _ ≤ (k.factorial : ℝ) * ∑ u ∈ F n, W u ^ 2 := by
          apply mul_le_mul_of_nonneg_right
          · exact_mod_cast card_stoppedFiber_le (U := U) (k := k) (n := n) hprime
          · exact Finset.sum_nonneg (fun _ _ ↦ sq_nonneg _)
        _ ≤ (k.factorial : ℝ) * ∑ u ∈ F n, V u / Real.sqrt U := by
          exact mul_le_mul_of_nonneg_left
            (Finset.sum_le_sum (fun u hu ↦ hweight u (Finset.mem_filter.mp hu).1))
            (Nat.cast_nonneg _)
        _ = C * ∑ u ∈ F n, V u := by rw [← Finset.sum_div]; dsimp [C]; ring
    _ = C * ∑ u ∈ A, V u := by
      rw [← Finset.mul_sum]
      congr 1
      exact Finset.sum_fiberwise_of_maps_to (fun u hu ↦ Finset.mem_image_of_mem _ hu) V
    _ ≤ C * ∑ u ∈ tuples S k, V u := by
      apply mul_le_mul_of_nonneg_left _ (div_nonneg (Nat.cast_nonneg _) hsqrt.le)
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun u _ _ ↦ hV u)
    _ = _ := by
      congr 1
      have hprod := Finset.prod_univ_sum (fun _ : Fin k ↦ S) (fun _ p ↦ w p)
      change (∏ _i : Fin k, ∑ p ∈ S, w p) = _ at hprod
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hprod
      exact hprod.symm

private theorem tupleProduct_ge_two_pow {S : Finset ℕ} {k : ℕ} {u : Fin k → ℕ}
    (hprime : ∀ p ∈ S, p.Prime) (hu : u ∈ tuples S k) : (2 : ℝ) ^ k ≤ (tupleProduct u : ℝ) := by
  have h : (∏ _i : Fin k, (2 : ℕ)) ≤ ∏ i, u i :=
    Finset.prod_le_prod (fun i _ ↦ (hprime _ (Fintype.mem_piFinset.mp hu i)).two_le)
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h
  exact_mod_cast h

/-- A finite depth cutoff exists for every real threshold. -/
public theorem exists_stop_depth (U : ℝ) : ∃ N : ℕ, U ≤ (2 : ℝ) ^ N := by
  obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt U (one_lt_two : (1 : ℝ) < 2)
  exact ⟨N, hN.le⟩

/-- If `2^N ≥ U`, no leaf has length greater than `N`. -/
public theorem stopped_length_le {S : Finset ℕ} {U : ℝ} {N k : ℕ} {u : Fin k → ℕ}
    (hprime : ∀ p ∈ S, p.Prime) (hN : U ≤ (2 : ℝ) ^ N) (hu : u ∈ stoppedTuples S U k) :
    k ≤ N := by
  classical
  by_contra! hk
  cases k with
  | zero => omega
  | succ k =>
    obtain ⟨hu, hc⟩ := Finset.mem_filter.mp hu
    have hs := Fintype.mem_piFinset.mp hu
    have hpre := ((firstCrossing_succ_iff (fun i ↦ (hprime _ (hs i)).one_lt.le)).mp hc).1
    have hpow := tupleProduct_ge_two_pow (u := Fin.init u) hprime
      (Fintype.mem_piFinset.mpr (fun i ↦ hs i.castSucc))
    have hmono : (2 : ℝ) ^ N ≤ 2 ^ k := pow_le_pow_right₀ (by norm_num) (Nat.le_of_lt_succ hk)
    exact (hN.trans (hmono.trans hpow)).not_gt hpre

private noncomputable def activeTuples (S : Finset ℕ) (U : ℝ) (k : ℕ) :
    Finset (Fin k → ℕ) := (tuples S k).filter (fun u ↦ (tupleProduct u : ℝ) < U)

private def nodeMass {k : ℕ} (r : ℕ → ℂ) (u : Fin k → ℕ) : ℂ := ∏ i, r (u i)

private theorem normalized_mass_step (S : Finset ℕ) (U : ℝ) (r : ℕ → ℂ) (k : ℕ)
    (hprime : ∀ p ∈ S, p.Prime) (hr : ∑ p ∈ S, r p = 1) :
    (∑ u ∈ activeTuples S U k, nodeMass r u) =
      (∑ u ∈ activeTuples S U (k + 1), nodeMass r u) +
        ∑ u ∈ stoppedTuples S U (k + 1), nodeMass r u := by
  classical
  let E := (tuples S (k + 1)).filter
    (fun v : Fin (k + 1) → ℕ ↦ (Fin.init v : Fin k → ℕ) ∈ activeTuples S U k)
  let below (v : Fin (k + 1) → ℕ) := (tupleProduct v : ℝ) < U
  have hE₁ : E.filter below = activeTuples S U (k + 1) := by
    ext v
    simp only [E, below, activeTuples, Finset.mem_filter]
    constructor
    · rintro ⟨⟨hv, _⟩, hbelow⟩
      exact ⟨hv, hbelow⟩
    · rintro ⟨hv, hbelow⟩
      have hs := Fintype.mem_piFinset.mp hv
      refine ⟨⟨hv, Fintype.mem_piFinset.mpr (fun i ↦ hs i.castSucc), ?_⟩, hbelow⟩
      apply lt_of_le_of_lt _ hbelow
      have hlast : 1 ≤ v (Fin.last k) := (hprime _ (hs _)).one_lt.le
      exact_mod_cast (show tupleProduct (Fin.init v) ≤ tupleProduct v by
        change (∏ i : Fin k, v i.castSucc) ≤ ∏ i, v i
        rw [Fin.prod_univ_castSucc]
        exact Nat.le_mul_of_pos_right _ (Nat.zero_lt_one.trans_le hlast))
  have hE₂ : E.filter (fun v ↦ ¬ below v) = stoppedTuples S U (k + 1) := by
    ext v
    simp only [E, below, activeTuples, stoppedTuples, Finset.mem_filter, not_lt]
    constructor
    · rintro ⟨⟨hv, _, hpre⟩, hcross⟩
      have hs := Fintype.mem_piFinset.mp hv
      exact ⟨hv, (firstCrossing_succ_iff (fun i ↦ (hprime _ (hs i)).one_lt.le)).mpr ⟨hpre, hcross⟩⟩
    · rintro ⟨hv, hc⟩
      have hs := Fintype.mem_piFinset.mp hv
      obtain ⟨hpre, hcross⟩ := (firstCrossing_succ_iff (fun i ↦ (hprime _ (hs i)).one_lt.le)).mp hc
      exact ⟨⟨hv, Fintype.mem_piFinset.mpr (fun i ↦ hs i.castSucc), hpre⟩, hcross⟩
  have hchildren (u : Fin k → ℕ) (hu : u ∈ activeTuples S U k) :
      (∑ p ∈ S, nodeMass r (Fin.snoc u p)) =
        ∑ v ∈ E.filter (fun v ↦ Fin.init v = u), nodeMass r v := by
    refine Finset.sum_bij (fun p _ ↦ Fin.snoc u p) ?_ ?_ ?_ (fun _ _ ↦ rfl)
    · intro p hp
      have hpool := Fintype.mem_piFinset.mp (Finset.mem_filter.mp hu).1
      simp only [E, Finset.mem_filter, Fin.init_snoc, hu, and_true]
      apply Fintype.mem_piFinset.mpr
      intro i
      cases i using Fin.lastCases with
      | last => simpa only [Fin.snoc_last] using hp
      | cast i => simpa only [Fin.snoc_castSucc] using hpool i
    · intro p _ q _ hpq
      simpa only [Fin.snoc_last] using congrFun hpq (Fin.last k)
    · intro v hv
      have hpv := Finset.mem_filter.mp hv
      have hpool := Fintype.mem_piFinset.mp (Finset.mem_filter.mp hpv.1).1
      refine ⟨v (Fin.last k), hpool _, ?_⟩
      rw [← hpv.2, Fin.snoc_init_self]
  calc
    _ = ∑ u ∈ activeTuples S U k, ∑ p ∈ S, nodeMass r (Fin.snoc u p) := by
      apply Finset.sum_congr rfl
      intro u _
      symm
      calc
        _ = ∑ p ∈ S, nodeMass r u * r p := by
          apply Finset.sum_congr rfl
          intro p _
          simp only [nodeMass]
          rw [Fin.prod_univ_castSucc]
          simp only [Fin.snoc_castSucc, Fin.snoc_last]
        _ = nodeMass r u := by rw [← Finset.mul_sum, hr, mul_one]
    _ = ∑ v ∈ E, nodeMass r v := by
      calc
        _ = ∑ u ∈ activeTuples S U k, ∑ v ∈ E.filter (fun v ↦ Fin.init v = u), nodeMass r v :=
          Finset.sum_congr rfl hchildren
        _ = _ := Finset.sum_fiberwise_of_maps_to (s := E) (t := activeTuples S U k)
          (g := fun v ↦ (Fin.init v : Fin k → ℕ)) (fun _ hv ↦ (Finset.mem_filter.mp hv).2) _
    _ = _ := by
      rw [← hE₁, ← hE₂]
      exact (Finset.sum_filter_add_sum_filter_not E below _).symm

private theorem normalized_mass_through (S : Finset ℕ) {U : ℝ} (hU : 1 < U) (r : ℕ → ℂ)
    (hprime : ∀ p ∈ S, p.Prime) (hr : ∑ p ∈ S, r p = 1) (N : ℕ) :
    (1 : ℂ) = (∑ u ∈ activeTuples S U N, nodeMass r u) +
      ∑ k ∈ Finset.range (N + 1), ∑ u ∈ stoppedTuples S U k, nodeMass r u := by
  classical
  induction N with
  | zero =>
    let u₀ : Fin 0 → ℕ := Fin.elim0
    have hroot : activeTuples S U 0 = {u₀} := by
      refine Finset.eq_singleton_iff_unique_mem.mpr ⟨?_, fun u _ ↦ funext (fun i ↦ i.elim0)⟩
      refine Finset.mem_filter.mpr ⟨Fintype.mem_piFinset.mpr (fun i ↦ i.elim0), ?_⟩
      simpa only [tupleProduct, Fin.prod_univ_zero, Nat.cast_one] using hU
    simp [hroot, stoppedTuples_zero S hU, nodeMass]
  | succ k ih =>
    rw [Finset.sum_range_succ, ih, normalized_mass_step S U r k hprime hr]
    ac_rfl

/-- Finite normalized leaf expansion. For any `N` with `U ≤ 2^N`, all leaf lengths
are in `range (N+1)` by `stopped_length_le`. Here `a` is completely multiplicative. -/
public theorem finite_normalized_leaf_expansion {S : Finset ℕ} {U : ℝ} (hU : 1 < U)
    (hprime : ∀ p ∈ S, p.Prime) (b : ℕ → ℝ) (a : ℕ →* ℂ)
    (hz : (∑ p ∈ S, (b p : ℂ) * a p) ≠ 0) (N : ℕ) (hN : U ≤ (2 : ℝ) ^ N) :
    let z := ∑ p ∈ S, (b p : ℂ) * a p
    (1 : ℂ) = ∑ k ∈ Finset.range (N + 1), z⁻¹ ^ k *
      ∑ n ∈ stoppedProducts S U k, (coefficient S U b k n : ℂ) * a n := by
  classical
  let z := ∑ p ∈ S, (b p : ℂ) * a p
  let r (p : ℕ) : ℂ := ((b p : ℂ) * a p) / z
  have hr : ∑ p ∈ S, r p = 1 := by
    dsimp only [r]
    rw [← Finset.sum_div, div_self hz]
  have hempty : activeTuples S U N = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro u hu
    obtain ⟨hu, hbelow⟩ := Finset.mem_filter.mp hu
    exact (hN.trans (tupleProduct_ge_two_pow hprime hu)).not_gt hbelow
  have hmass := normalized_mass_through S hU r hprime hr N
  rw [hempty, Finset.sum_empty, zero_add] at hmass
  refine hmass.trans (Finset.sum_congr rfl (fun k _ ↦ ?_))
  rw [← Finset.sum_fiberwise_of_maps_to (s := stoppedTuples S U k)
    (t := stoppedProducts S U k) (g := tupleProduct)
    (fun _ hu ↦ Finset.mem_image_of_mem tupleProduct hu) (nodeMass r)]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n _
  simp only [coefficient, Complex.ofReal_sum, Complex.ofReal_prod, Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u hu
  have hun := (Finset.mem_filter.mp hu).2
  rw [nodeMass]
  dsimp only [r]
  rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    Finset.prod_mul_distrib, ← map_prod a, ← tupleProduct, hun, div_eq_mul_inv, inv_pow]
  ac_rfl

end Masullo.StoppedPrimeProductMoment
