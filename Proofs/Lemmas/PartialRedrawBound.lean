module

public import Lemmas.PrimeTupleRedrawSpacing
public import Mathlib.Data.Fintype.Pi
import all Lemmas.PrimeTupleRedrawSpacing
import Lemmas.MixedSignPrimeFiber
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Conditional partial redraw under the original finite product law

Source: `db84b3c3:.godel/bob/tuple-redraw-cost.md:7–25`, used by
`last-slot-residues.md` and `isolated-tuple-hits.md`.
Owning check session: `01a20f51-211d-73b8-9726-8aa026238fa2`.

The source and mask are fixed, and the signs remain attached to the labeled
slots. Only masked coordinates are drawn, independently from the original
normalized law. The event requires a change of frequency, not just a change
of tuple. The bounds are finite and make no asymptotic specialization or
comparison of marginal slice masses.
-/

open scoped BigOperators Classical

namespace Masullo.PartialRedrawBound

open PrimeTupleRedrawSpacing MixedSignPrimeFiber

/-- The mass of an event on independent labeled draws from a finite pool. -/
@[expose] public noncomputable def productProbability {ι : Type*} [Fintype ι] [DecidableEq ι]
    {S : Finset ℕ} (ρ : ℕ → ℝ) (E : (ι → S) → Prop) : ℝ := by
  classical
  exact ∑ q ∈ Finset.univ.filter E, ∏ i, ρ (q i)

private theorem productProbability_eq_sum {ι : Type*} [Fintype ι] [DecidableEq ι] {S : Finset ℕ}
    (ρ : ℕ → ℝ) (E : (ι → S) → Prop) :
    productProbability ρ E = ∑ q : ι → S, if E q then ∏ i, ρ (q i) else 0 := by
  exact Finset.sum_filter _ _

/-- Redraw exactly the labeled slots in `M`, leaving all others fixed. -/
@[expose] public def redraw {n : ℕ} {S : Finset ℕ} (M : Finset (Fin n))
    (p : Fin n → S) (q : M → S) (i : Fin n) : ℕ :=
  if h : i ∈ M then q ⟨i, h⟩ else p i

/-- The inclusive spacing cutoff for the partial redraw. -/
@[expose] public noncomputable def cutoff (t X : ℝ) : ℕ :=
  ⌊Real.log (t / 32) / (2 * Real.log X)⌋₊

private theorem budget {t X : ℝ} (ht : 32 < t) (hX : 1 < X) {r : ℕ}
    (hr : r ≤ cutoff t X) : 4 * Real.pi / t < X ^ (-(2 * (r : ℤ))) := by
  have ht0 : 0 < t := by linarith
  have hd := mul_pos (by norm_num : (0 : ℝ) < 2) (Real.log_pos hX)
  have ht32 : 1 < t / 32 := (lt_div_iff₀ (by norm_num)).mpr (by simpa using ht)
  have hl : 0 ≤ Real.log (t / 32) := (Real.log_pos ht32).le
  have hr' := (Nat.le_floor_iff (div_nonneg hl hd.le)).mp hr
  apply (spacing_budget_iff_log (lt_trans zero_lt_one hX) ht0).mpr
  have hpi : 0 < 4 * Real.pi := by positivity
  have hpi' : 4 * Real.pi < 32 := by linarith [Real.pi_lt_four]
  have h := (le_div_iff₀ hd).mp hr'
  have h' : 2 * (r : ℝ) * Real.log X ≤ Real.log (t / 32) := by linarith only [h]
  exact h'.trans_lt (Real.log_lt_log (by positivity) (div_lt_div_of_pos_left ht0 hpi hpi'))

private abbrev glue {ι : Type*} {S : Finset ℕ} (H : ι → Prop) [DecidablePred H]
    (u : {i // H i} → S) (v : {i // ¬ H i} → S) : ι → S :=
  (Equiv.piEquivPiSubtypeProd H (fun _ ↦ S)).symm (u, v)

private theorem glue_pos {ι : Type*} {S : Finset ℕ} (H : ι → Prop) [DecidablePred H]
    (u : {i // H i} → S) (v : {i // ¬ H i} → S) {i} (hi : H i) :
    glue H u v i = u ⟨i, hi⟩ := by simp [glue, Equiv.piEquivPiSubtypeProd_symm_apply, hi]

private theorem glue_neg {ι : Type*} {S : Finset ℕ} (H : ι → Prop) [DecidablePred H]
    (u : {i // H i} → S) (v : {i // ¬ H i} → S) {i} (hi : ¬ H i) :
    glue H u v i = v ⟨i, hi⟩ := by simp [glue, Equiv.piEquivPiSubtypeProd_symm_apply, hi]

private theorem productProbability_split {ι : Type*} [Fintype ι] [DecidableEq ι] {S : Finset ℕ}
    (ρ : ℕ → ℝ) (E : (ι → S) → Prop) (H : ι → Prop) [DecidablePred H] :
    productProbability ρ E = ∑ v : {i // ¬ H i} → S,
      (∏ i, ρ (v i)) * productProbability ρ (fun u ↦ E (glue H u v)) := by
  classical
  simp only [productProbability_eq_sum]
  rw [← Equiv.sum_comp (Equiv.piEquivPiSubtypeProd H (fun _ ↦ S)).symm,
    Fintype.sum_prod_type, Finset.sum_comm]
  refine Finset.sum_congr rfl fun v _ ↦ ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun u _ ↦ ?_
  by_cases h : E (glue H u v)
  · simp only [h, ite_true]
    rw [← Fintype.prod_subtype_mul_prod_subtype H (fun i ↦ ρ (glue H u v i)), mul_comm]
    simp only [fun i : {i // H i} ↦ glue_pos H u v i.2,
      fun i : {i // ¬ H i} ↦ glue_neg H u v i.2]
  · simp [h]

private theorem productWeight_total {ι : Type*} [Fintype ι] [DecidableEq ι] {S : Finset ℕ}
    (ρ : ℕ → ℝ) (hnorm : ∑ p : S, ρ p = 1) :
    ∑ q : ι → S, ∏ i, ρ (q i) = 1 := by
  classical
  rw [← Fintype.prod_sum (fun (_ : ι) (a : S) ↦ ρ a)]
  simp only [hnorm, Finset.prod_const_one]

private theorem productProbability_le {ι : Type*} [Fintype ι] [DecidableEq ι] {S : Finset ℕ}
    {ρ : ℕ → ℝ} (hw : ∀ p ∈ S, 0 ≤ ρ p) {E F : (ι → S) → Prop}
    (hEF : ∀ q, E q → F q) : productProbability ρ E ≤ productProbability ρ F := by
  classical
  simp only [productProbability_eq_sum]
  apply Finset.sum_le_sum
  intro q _
  by_cases h : E q
  · simp [h, hEF q h]
  · have hn : 0 ≤ ∏ i, ρ (q i) := Finset.prod_nonneg fun i _ ↦ hw _ (q i).2
    by_cases h' : F q <;> simp [h, h', hn]

private theorem productProbability_empty {ι : Type*} [Fintype ι] [DecidableEq ι] {S : Finset ℕ}
    {ρ : ℕ → ℝ} {E : (ι → S) → Prop} (hE : ∀ q, ¬ E q) :
    productProbability ρ E = 0 := by
  classical
  simp [productProbability, hE]

private theorem productProbability_fixed {ι : Type*} [Fintype ι] [DecidableEq ι] {S : Finset ℕ}
    {ρ : ℕ → ℝ} {b : ℝ} (hnorm : ∑ p : S, ρ p = 1)
    (hw : ∀ p ∈ S, 0 ≤ ρ p ∧ ρ p ≤ b) (H : ι → Prop) [DecidablePred H]
    (target : ({i // ¬ H i} → S) → ({i // H i} → S)) :
    productProbability ρ (fun q : ι → S ↦ (fun i : {i // H i} ↦ q i) =
      target (fun i : {i // ¬ H i} ↦ q i)) ≤ b ^ Fintype.card {i // H i} := by
  classical
  rw [productProbability_split ρ _ H]
  calc
    _ ≤ ∑ v : {i // ¬ H i} → S, (∏ i, ρ (v i)) * b ^ Fintype.card {i // H i} := by
      refine Finset.sum_le_sum fun v _ ↦ mul_le_mul_of_nonneg_left ?_ ?_
      · have he (u : {i // H i} → S) :
            ((fun i : {i // H i} ↦ glue H u v i) = target
              (fun i : {i // ¬ H i} ↦ glue H u v i)) ↔ u = target v := by
          simp only [fun i : {i // H i} ↦ glue_pos H u v i.2,
            fun i : {i // ¬ H i} ↦ glue_neg H u v i.2]
        simp only [productProbability_eq_sum, he]
        calc
          _ = ∏ i, ρ (target v i) := by
            refine (Fintype.sum_eq_single (target v) ?_).trans ?_
            · intro u hu
              exact ite_eq_right hu
            · exact ite_eq_left rfl
          _ ≤ ∏ _ : {i // H i}, b := Finset.prod_le_prod₀
            (fun i _ ↦ (hw _ (target v i).2).1) (fun i _ ↦ (hw _ (target v i).2).2)
          _ = _ := by rw [Finset.prod_const, Finset.card_univ]
      · exact Finset.prod_nonneg fun i _ ↦ (hw _ (v i).2).1
    _ = _ := by rw [← Finset.sum_mul, productWeight_total ρ hnorm, one_mul]

private theorem signedFiber_le {ι : Type*} [Fintype ι] [DecidableEq ι] {S : Finset ℕ} {d n : ℕ}
    {X lo hi b : ℝ} (s : ι → Bool) (hcard : Fintype.card ι ≤ n) (hd : 0 < d)
    (hp : ∀ p ∈ S, p.Prime ∧ (p + d).Prime) (hX : ∀ p ∈ S, (↑(p + d) : ℝ) ≤ X)
    (hdiam : hi - lo < X ^ (-(2 * (Fintype.card ι : ℤ))))
    {ρ : ℕ → ℝ} (hb : 0 ≤ b) (hw : ∀ p ∈ S, 0 ≤ ρ p ∧ ρ p ≤ b) :
    productProbability ρ (fun u : ι → S ↦ (∑ i, signedLabel d (u i) (s i)) ∈ Set.Icc lo hi ∧
      ∀ i j, s i = true → s j = false → u i ≠ u j) ≤ (n * b) ^ Fintype.card ι := by
  classical
  let P : ι → Prop := fun i ↦ s i = true
  let rP := Fintype.card {i // P i}
  let rN := Fintype.card {i // ¬ P i}
  let ep : {i // P i} ≃ Fin rP := Fintype.equivFin _
  let en : {i // ¬ P i} ≃ Fin rN := Fintype.equivFin _
  let a (u : ι → S) : Assignment rP rN :=
    (fun i ↦ u (ep.symm i), fun i ↦ u (en.symm i))
  have hr : rP + rN = Fintype.card ι := by
    dsimp [rP, rN]
    rw [Fintype.card_subtype_compl]
    exact Nat.add_sub_of_le (Fintype.card_le_of_injective Subtype.val Subtype.val_injective)
  have hneg (i : {i // ¬ P i}) : s i = false := Bool.eq_false_iff.mpr i.2
  have hfreq (u : ι → S) : signedFrequency d (a u) = ∑ i, signedLabel d (u i) (s i) := by
    rw [← Fintype.sum_subtype_add_sum_subtype P]
    unfold signedFrequency
    dsimp only [a]
    rw [Equiv.sum_comp ep.symm (fun i ↦ Real.log ((↑(↑(u i) + d) : ℝ) / ↑(u i))),
      Equiv.sum_comp en.symm (fun i ↦ Real.log ((↑(↑(u i) + d) : ℝ) / ↑(u i)))]
    simp only [signedLabel, show ∀ i : {i // P i}, s i = true from Subtype.property,
      hneg, ite_true, Bool.false_eq_true, ite_false, Finset.sum_neg_distrib, sub_eq_add_neg]
  have hweight (u : ι → S) : productWeight ρ (a u) = ∏ i, ρ (u i) := by
    unfold productWeight
    dsimp only [a]
    rw [Equiv.prod_comp ep.symm (fun i ↦ ρ (u i)), Equiv.prod_comp en.symm (fun i ↦ ρ (u i)),
      Fintype.prod_subtype_mul_prod_subtype P (fun i ↦ ρ (u i))]
  have hinj : Function.Injective a := by
    intro u v h
    funext i
    apply Subtype.ext
    by_cases hi : P i
    · have hh := congrArg (fun z : Assignment rP rN ↦ z.1 (ep ⟨i, hi⟩)) h
      simpa [a] using hh
    · have hh := congrArg (fun z : Assignment rP rN ↦ z.2 (en ⟨i, hi⟩)) h
      simpa [a] using hh
  calc
    _ ≤ ∑ z ∈ intervalFiber S d rP rN lo hi, productWeight ρ z := by
      rw [productProbability]
      apply Finset.sum_le_sum_of_injOn a hinj.injOn
      · intro z hz
        obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hz
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu
        refine mem_intervalFiber.mpr ⟨⟨fun i ↦ (u (ep.symm i)).2,
          fun i ↦ (u (en.symm i)).2⟩, (hfreq u).symm ▸ hu.1, fun i j he ↦ ?_⟩
        exact hu.2 (ep.symm i) (en.symm j) (ep.symm i).2 (hneg _) (Subtype.ext he)
      · exact fun u _ ↦ (hweight u).ge
      · intro z hz _
        obtain ⟨hP, hN⟩ := (mem_intervalFiber.mp hz).1
        exact mul_nonneg (Finset.prod_nonneg fun i _ ↦ (hw _ (hP i)).1)
          (Finset.prod_nonneg fun i _ ↦ (hw _ (hN i)).1)
    _ ≤ ((rP.factorial * rN.factorial : ℕ) : ℝ) * b ^ (rP + rN) :=
      sum_productWeight_intervalFiber_le hd hp hX (by rwa [hr]) ρ hb hw
    _ ≤ _ := by
      have hP : rP ≤ n := by omega
      have hN : rN ≤ n := by omega
      have hfac : rP.factorial * rN.factorial ≤ n ^ (rP + rN) := by
        rw [pow_add]
        exact Nat.mul_le_mul ((Nat.factorial_le_pow _).trans (Nat.pow_le_pow_left hP _))
          ((Nat.factorial_le_pow _).trans (Nat.pow_le_pow_left hN _))
      rw [← hr, mul_pow, ← Nat.cast_pow]
      exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hfac) (pow_nonneg hb _)

private def partners {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Finset ι) (f : A → ι) : Finset ι :=
  Finset.univ.image f

private def remaining {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Finset ι) (f : A → ι) : Finset ι :=
  Finset.univ \ (A ∪ partners A f)

private structure Matching {ι : Type*} (s : ι → Bool) (A : Finset ι) (f : A → ι) : Prop where
  inj : Function.Injective f
  plus : ∀ i : A, s i = true
  minus : ∀ i : A, s (f i) = false

private def Paired {ι α : Type*} {A : Finset ι} (f : A → ι) (q : ι → α) : Prop :=
  ∀ i : A, q i = q (f i)

private def NoOpposite {ι α : Type*} (s : ι → Bool) (R : Finset ι) (q : ι → α) : Prop :=
  ∀ i ∈ R, ∀ j ∈ R, s i = true → s j = false → q i ≠ q j

private theorem mem_partners {ι : Type*} [Fintype ι] [DecidableEq ι] {A : Finset ι} {f : A → ι} {j : ι} :
    j ∈ partners A f ↔ ∃ i : A, f i = j := by simp [partners]

private theorem disjoint_partners {ι : Type*} [Fintype ι] [DecidableEq ι] {s : ι → Bool}
    {A : Finset ι} {f : A → ι} (h : Matching s A f) : Disjoint A (partners A f) := by
  apply Finset.disjoint_left.mpr
  intro i hi hj
  obtain ⟨j, rfl⟩ := mem_partners.mp hj
  have ht := h.plus ⟨f j, hi⟩
  rw [h.minus j] at ht
  contradiction

private theorem card_partners {ι : Type*} [Fintype ι] [DecidableEq ι] {s : ι → Bool}
    {A : Finset ι} {f : A → ι} (h : Matching s A f) : (partners A f).card = A.card := by
  rw [partners, Finset.card_image_of_injective _ h.inj, Finset.card_univ, Fintype.card_coe]

private theorem exists_matching {ι α : Type*} [Fintype ι] [DecidableEq ι] (s : ι → Bool) (q : ι → α) :
    ∃ (A : Finset ι) (f : A → ι), Matching s A f ∧ Paired f q ∧
      NoOpposite s (remaining A f) q := by
  classical
  let C : Finset (Σ A : Finset ι, A → ι) := Finset.univ.filter
    (fun x ↦ Matching s x.1 x.2 ∧ Paired x.2 q)
  have ne : C.Nonempty := by
    let f : (∅ : Finset ι) → ι := Subtype.val
    have h (i : (∅ : Finset ι)) : False := Finset.notMem_empty _ i.2
    exact ⟨⟨∅, f⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      ⟨fun i _ _ ↦ (h i).elim, fun i ↦ (h i).elim, fun i ↦ (h i).elim⟩,
      fun i ↦ (h i).elim⟩⟩
  obtain ⟨⟨A, f⟩, hx, hmax⟩ := Finset.exists_max_image C (fun x ↦ x.1.card) ne
  obtain ⟨hm, hq⟩ := (Finset.mem_filter.mp hx).2
  refine ⟨A, f, hm, hq, ?_⟩
  intro i hi j hj hplus hminus he
  have hiA : i ∉ A := fun h ↦ (Finset.mem_sdiff.mp hi).2 (Finset.mem_union_left _ h)
  have hjB : j ∉ partners A f := fun h ↦ (Finset.mem_sdiff.mp hj).2 (Finset.mem_union_right _ h)
  let g : (↑(insert i A : Finset ι) : Type _) → ι := fun a ↦
    if ha : a.val = i then j else f ⟨a, Finset.mem_of_mem_insert_of_ne a.2 ha⟩
  have hnew : Matching s (insert i A) g := by
    constructor
    · intro a b hab
      by_cases ha : a.val = i <;> by_cases hb : b.val = i
      · exact Subtype.ext (ha.trans hb.symm)
      · have hx : j = f ⟨b, Finset.mem_of_mem_insert_of_ne b.2 hb⟩ := by simpa [g, ha, hb] using hab
        exact (hjB (mem_partners.mpr ⟨_, hx.symm⟩)).elim
      · have hx : f ⟨a, Finset.mem_of_mem_insert_of_ne a.2 ha⟩ = j := by simpa [g, ha, hb] using hab
        exact (hjB (mem_partners.mpr ⟨_, hx⟩)).elim
      · have hx : f ⟨a, Finset.mem_of_mem_insert_of_ne a.2 ha⟩ =
            f ⟨b, Finset.mem_of_mem_insert_of_ne b.2 hb⟩ := by simpa [g, ha, hb] using hab
        exact Subtype.ext (congrArg (fun z : A ↦ z.val) (hm.inj hx))
    · intro a
      by_cases ha : a.val = i
      · simpa only [ha] using hplus
      · exact hm.plus ⟨a, Finset.mem_of_mem_insert_of_ne a.2 ha⟩
    · intro a
      by_cases ha : a.val = i
      · simpa [g, ha] using hminus
      · simpa [g, ha] using hm.minus ⟨a, Finset.mem_of_mem_insert_of_ne a.2 ha⟩
  have hg : Paired g q := by
    intro a
    by_cases ha : a.val = i
    · simpa [g, ha] using he
    · simpa [g, ha] using hq ⟨a, Finset.mem_of_mem_insert_of_ne a.2 ha⟩
  have h := hmax ⟨insert i A, g⟩ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hnew, hg⟩)
  exact (not_le_of_gt (by simp [Finset.card_insert_of_notMem hiA] : A.card < (insert i A).card)) h

private theorem frequency_redraw {n d : ℕ} {S : Finset ℕ} (M : Finset (Fin n))
    (s : Fin n → Bool) (p : Fin n → S) (q : M → S) :
    frequency d s (redraw M p q) = (∑ i : M, signedLabel d (q i) (s i)) +
      ∑ i : {i // i ∉ M}, signedLabel d (p i) (s i) := by
  rw [frequency, ← Fintype.sum_subtype_add_sum_subtype (fun i ↦ i ∈ M)]
  simp only [redraw, (fun i : M ↦ i.2), (fun i : {i // i ∉ M} ↦ i.2),
    dite_true, dite_false]
  apply congrArg (fun x : ℝ ↦ x + _)
  exact Finset.sum_congr (Finset.ext fun _ ↦ by simp) fun _ _ ↦ rfl

private theorem redraw_mem {n : ℕ} {S : Finset ℕ} {M : Finset (Fin n)}
    (p : Fin n → S) (q : M → S) (i : Fin n) : redraw M p q i ∈ S := by
  unfold redraw
  split <;> exact Subtype.property _

private theorem changedSlots_redraw_subset {n : ℕ} {S : Finset ℕ} {M : Finset (Fin n)}
    (p : Fin n → S) (q : M → S) : changedSlots (fun i ↦ (p i : ℕ)) (redraw M p q) ⊆ M := by
  intro i hi
  by_contra h
  exact (Finset.mem_filter.mp hi).2 (by simp [redraw, h])

-- Pack a matched pair into a single changed slot by putting the old minus start in both slots.
-- The new pair still cancels, and its minus coordinate is now unchanged.
private theorem frequency_packed {n d : ℕ} {S : Finset ℕ} {M : Finset (Fin n)}
    (s : Fin n → Bool) (p : Fin n → S) {q : M → S}
    {A : Finset M} {f : A → M} (hm : Matching (fun i : M ↦ s i) A f) (hq : Paired f q) :
    ∃ v : M → S, frequency d s (redraw M p v) = frequency d s (redraw M p q) ∧
      (changedSlots (fun i ↦ (p i : ℕ)) (redraw M p v)).card ≤ M.card - A.card := by
  classical
  let B := partners A f
  let R := remaining A f
  let v (i : M) : S := if i ∈ B then p i else if hi : i ∈ A then p (f ⟨i, hi⟩) else q i
  have hdj := disjoint_partners hm
  have hv : Paired f v := by
    intro i
    have hB : i.val ∉ B := fun h ↦ Finset.disjoint_left.mp hdj i.2 h
    have hf : f i ∈ B := mem_partners.mpr ⟨i, rfl⟩
    simp [v, hB, hf, i.2]
  have hsum (u : M → S) (hu : Paired f u) :
      (∑ i : M, signedLabel d (u i) (s i)) = ∑ i ∈ R, signedLabel d (u i) (s i) := by
    let L (i : M) := signedLabel d (u i) (s i)
    change (∑ i, L i) = ∑ i ∈ R, L i
    have hB : (∑ i ∈ B, L i) = ∑ i : A, L (f i) :=
      Finset.sum_image (fun _ _ _ _ h ↦ hm.inj h)
    have hA : (∑ i ∈ A, L i) = ∑ i : A, L i := Finset.sum_subtype A (fun _ ↦ Iff.rfl) _
    have hcancel : (∑ i ∈ A, L i) + (∑ i ∈ B, L i) = 0 := by
      rw [hA, hB, ← Finset.sum_add_distrib]
      apply Finset.sum_eq_zero
      intro i _
      simp [L, signedLabel, hm.plus i, hm.minus i, hu i]
    have hsd := Finset.sum_sdiff (f := L) (Finset.subset_univ (A ∪ B))
    rw [Finset.sum_union hdj, hcancel, add_zero] at hsd
    exact hsd.symm
  refine ⟨v, ?_, ?_⟩
  · rw [frequency_redraw, frequency_redraw, hsum v hv, hsum q hq]
    congr 1
    refine Finset.sum_congr rfl fun i hi ↦ ?_
    have hn := (Finset.mem_sdiff.mp hi).2
    simp [v, show i ∉ A from fun h ↦ hn (Finset.mem_union_left _ h),
      show i ∉ B from fun h ↦ hn (Finset.mem_union_right _ h)]
  · let BI := B.image (fun i : M ↦ i.val)
    have hBI : BI ⊆ M := by
      intro i hi
      obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hi
      exact j.2
    have hs : changedSlots (fun i ↦ (p i : ℕ)) (redraw M p v) ⊆ M \ BI := by
      intro i hi
      refine Finset.mem_sdiff.mpr ⟨changedSlots_redraw_subset p v hi, ?_⟩
      intro h
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp h
      exact (Finset.mem_filter.mp hi).2 (by simp [redraw, j.2, v, hj])
    calc
      _ ≤ (M \ BI).card := Finset.card_le_card hs
      _ = _ := by rw [Finset.card_sdiff_of_subset hBI, Finset.card_image_of_injective _ Subtype.val_injective,
        card_partners hm]

/-- A redraw reaches the band and has a different log frequency from its source. -/
@[expose] public def success {n d : ℕ} {S : Finset ℕ} (t : ℝ) (s : Fin n → Bool)
    (M : Finset (Fin n)) (p : Fin n → S) (q : M → S) : Prop :=
  |t * frequency d s (redraw M p q)| ≤ 2 * Real.pi ∧
    frequency d s (redraw M p q) ≠ frequency d s (fun i ↦ p i)

private theorem bounded_pool {n d : ℕ} {S : Finset ℕ} {X : ℝ}
    (hp : ∀ p ∈ S, p.Prime ∧ (p + d).Prime) (hSX : ∀ p ∈ S, (↑(p + d) : ℝ) ≤ X)
    {u : Fin n → ℕ} (hu : ∀ i, u i ∈ S) : BoundedStarts X d u :=
  fun i ↦ ⟨(hp _ (hu i)).1.pos, hSX _ (hu i)⟩

/-- An inclusive spacing obstruction: no draw in a mask of at most `cutoff t X`
slots can change the source's frequency and remain in the band. -/
public theorem productProbability_success_eq_zero {n d : ℕ} {S : Finset ℕ} {t X : ℝ}
    (ht : 32 < t) (hX : 1 < X) (hd : 0 < d)
    (hp : ∀ a ∈ S, a.Prime ∧ (a + d).Prime) (hSX : ∀ a ∈ S, (↑(a + d) : ℝ) ≤ X)
    (s : Fin n → Bool) (M : Finset (Fin n)) (p : Fin n → S)
    (hpBand : |t * frequency d s (fun i ↦ p i)| ≤ 2 * Real.pi)
    (hM : M.card ≤ cutoff t X) (ρ : ℕ → ℝ) :
    productProbability ρ (success (d := d) t s M p) = 0 := by
  apply productProbability_empty
  intro q ⟨hband, hne⟩
  exact hne (eq_of_survivors hd (by linarith) s (bounded_pool hp hSX fun i ↦ (p i).2)
    (bounded_pool hp hSX (redraw_mem p q)) (Finset.card_le_card (changedSlots_redraw_subset p q))
    hpBand hband (budget ht hX hM))

private def Witness {n d : ℕ} {S : Finset ℕ} (t : ℝ) (s : Fin n → Bool)
    {M : Finset (Fin n)} (p : Fin n → S) (A : Finset M) (f : A → M) (q : M → S) : Prop :=
  success (d := d) t s M p q ∧ Matching (fun i : M ↦ s i) A f ∧ Paired f q ∧
    NoOpposite (fun i : M ↦ s i) (remaining A f) q

-- First split off the hidden slots; then each paired partner is prescribed by a distinct
-- revealed plus slot. Both steps use sections of the original product law.
set_option maxHeartbeats 600000 in
private theorem witness_sections_le {n d : ℕ} {S : Finset ℕ} {t X b : ℝ}
    (ht : 32 < t) (hX : 1 < X) (hd : 0 < d)
    (hp : ∀ a ∈ S, a.Prime ∧ (a + d).Prime) (hSX : ∀ a ∈ S, (↑(a + d) : ℝ) ≤ X)
    (s : Fin n → Bool) {M : Finset (Fin n)} (p : Fin n → S)
    {ρ : ℕ → ℝ} (hnorm : ∑ a : S, ρ a = 1) (hb : 0 ≤ b)
    (hw : ∀ a ∈ S, 0 ≤ ρ a ∧ ρ a ≤ b) {A : Finset M} {f : A → M}
    (hm : Matching (fun i : M ↦ s i) A f) {H : Finset M} (hH : H ⊆ remaining A f)
    (hHK : H.card ≤ cutoff t X) :
    productProbability ρ (Witness (d := d) t s p A f) ≤ (n * b) ^ H.card * b ^ A.card := by
  classical
  let B := partners A f
  let V := {i : M // i ∉ H}
  have hAV (i : A) : i.val ∉ H := fun hi ↦
    (Finset.mem_sdiff.mp (hH hi)).2 (Finset.mem_union_left _ i.2)
  have hBV {i : M} (hi : i ∈ B) : i ∉ H := fun hj ↦
    (Finset.mem_sdiff.mp (hH hj)).2 (Finset.mem_union_right _ hi)
  let l (i : A) : V := ⟨i, hAV i⟩
  let r (i : A) : V := ⟨f i, hBV (mem_partners.mpr ⟨i, rfl⟩)⟩
  let Q (v : V → S) : Prop := ∀ i : A, v (l i) = v (r i)
  let J (i : V) : Prop := i.val ∈ B
  let e : A ≃ {i : V // J i} := Equiv.ofBijective
    (fun i ↦ ⟨r i, mem_partners.mpr ⟨i, rfl⟩⟩) ⟨by
      intro i j hij
      exact hm.inj (congrArg (fun z : {i : V // J i} ↦ z.val.val) hij), by
      intro j
      obtain ⟨i, hi⟩ := mem_partners.mp j.2
      exact ⟨i, Subtype.ext (Subtype.ext hi)⟩⟩
  have he (j : {i : V // J i}) : r (e.symm j) = j :=
    congrArg Subtype.val (e.apply_symm_apply j)
  let target (v : {i : V // ¬ J i} → S) (j : {i : V // J i}) : S :=
    v ⟨l (e.symm j), fun hj ↦ Finset.disjoint_left.mp (disjoint_partners hm) (e.symm j).2 hj⟩
  have hQ : productProbability ρ Q ≤ b ^ A.card := by
    calc
      _ ≤ productProbability ρ (fun v : V → S ↦ (fun j : {i : V // J i} ↦ v j) =
          target (fun j : {i : V // ¬ J i} ↦ v j)) := by
        apply productProbability_le (fun a ha ↦ (hw a ha).1)
        intro v hv
        funext j
        have h := (hv (e.symm j)).symm
        dsimp only [target]
        rwa [he] at h
      _ ≤ b ^ Fintype.card {i : V // J i} := productProbability_fixed hnorm hw J target
      _ = _ := by rw [← Fintype.card_congr e, Fintype.card_coe]
  let C := (n * b) ^ H.card
  have hc : 0 ≤ C := by dsimp [C]; positivity
  have hsection (v : V → S) :
      productProbability ρ (fun u ↦ Witness (d := d) t s p A f
        (glue (fun i ↦ i ∈ H) u v)) ≤ if Q v then C else 0 := by
    by_cases hq : Q v
    · rw [ite_eq_left hq]
      let c := (∑ i : V, signedLabel d (v i) (s i.val)) +
        ∑ i : {i // i ∉ M}, signedLabel d (p i) (s i)
      let lo := -(2 * Real.pi) / t - c
      let hi := (2 * Real.pi) / t - c
      have hdiam : hi - lo < X ^ (-(2 * (Fintype.card H : ℤ))) := by
        rw [Fintype.card_coe, show hi - lo = 4 * Real.pi / t by dsimp [hi, lo]; ring]
        exact budget ht hX hHK
      have hcard : Fintype.card H ≤ n :=
        Fintype.card_le_of_injective (fun i : H ↦ i.val.val)
          (fun _ _ h ↦ Subtype.ext (Subtype.ext h)) |>.trans_eq (Fintype.card_fin n)
      calc
        _ ≤ productProbability ρ (fun u : H → S ↦
            (∑ i : H, signedLabel d (u i) (s i.val)) ∈ Set.Icc lo hi ∧
              ∀ i j : H, s i.val = true → s j.val = false → u i ≠ u j) := by
          apply productProbability_le (fun a ha ↦ (hw a ha).1)
          intro u hu
          have hf : frequency d s (redraw M p (glue (fun i ↦ i ∈ H) u v)) =
              (∑ i : H, signedLabel d (u i) (s i.val)) + c := by
            rw [frequency_redraw, ← Fintype.sum_subtype_add_sum_subtype (fun i : M ↦ i ∈ H)
              (fun i ↦ signedLabel d (glue (fun j ↦ j ∈ H) u v i) (s i))]
            simp only [fun i : H ↦ glue_pos (fun j ↦ j ∈ H) u v i.2,
              fun i : V ↦ glue_neg (fun j ↦ j ∈ H) u v i.2, c, add_assoc]
            apply congrArg₂ (· + ·)
            · exact Finset.sum_congr (Finset.ext fun _ ↦ by simp) fun _ _ ↦ rfl
            · apply congrArg (fun x : ℝ ↦ x + _)
              exact Finset.sum_congr (Finset.ext fun _ ↦ by simp) fun _ _ ↦ rfl
          have hband := abs_le.mp hu.1.1
          rw [hf] at hband
          have ht0 : 0 < t := by linarith
          refine ⟨⟨?_, ?_⟩, ?_⟩
          · have h := (div_le_iff₀ ht0).mpr (by simpa [mul_comm t] using hband.1)
            exact sub_le_iff_le_add.mpr h
          · have h := (le_div_iff₀ ht0).mpr (by simpa [mul_comm t] using hband.2)
            exact le_sub_iff_add_le.mpr h
          · intro i j hsi hsj hval
            apply hu.2.2.2 i (hH i.2) j (hH j.2) hsi hsj
            simpa only [glue_pos (fun x ↦ x ∈ H) u v i.2,
              glue_pos (fun x ↦ x ∈ H) u v j.2] using hval
        _ ≤ C := by
          simpa only [C, Fintype.card_coe] using
            (signedFiber_le (fun i : H ↦ s i.val) hcard hd hp hSX hdiam hb hw)
    · rw [ite_eq_right hq, productProbability_empty]
      intro u hu
      apply hq
      intro i
      have h := hu.2.2.1 i
      change glue (fun j ↦ j ∈ H) u v (i : M) = glue (fun j ↦ j ∈ H) u v (f i) at h
      rw [glue_neg (fun j ↦ j ∈ H) u v (hAV i),
        glue_neg (fun j ↦ j ∈ H) u v (hBV (mem_partners.mpr ⟨i, rfl⟩))] at h
      exact h
  have hF : Subtype.fintype (fun i : M ↦ i ∈ H) = Finset.Subtype.fintype H := Subsingleton.elim _ _
  rw [productProbability_split ρ _ (fun i : M ↦ i ∈ H), hF]
  calc
    _ ≤ ∑ v : V → S, (∏ i, ρ (v i)) * (if Q v then C else 0) :=
      Finset.sum_le_sum fun v _ ↦ mul_le_mul_of_nonneg_left (hsection v)
        (Finset.prod_nonneg fun i _ ↦ (hw _ (v i).2).1)
    _ = C * productProbability ρ Q := by
      rw [productProbability_eq_sum, Finset.mul_sum]
      exact Finset.sum_congr rfl fun v _ ↦ by by_cases h : Q v <;> simp [h, mul_comm]
    _ ≤ _ := mul_le_mul_of_nonneg_left hQ hc

private theorem productProbability_cover_le {ι J : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype J] {S : Finset ℕ} {ρ : ℕ → ℝ} (hw : ∀ a ∈ S, 0 ≤ ρ a)
    {E : (ι → S) → Prop} {W : J → (ι → S) → Prop}
    (hcover : ∀ q, E q → ∃ j, W j q) :
    productProbability ρ E ≤ ∑ j, productProbability ρ (W j) := by
  classical
  simp only [productProbability_eq_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro q _
  have hnonneg (j : J) : 0 ≤ if W j q then ∏ i, ρ (q i) else 0 :=
    ite_nonneg (Finset.prod_nonneg fun i _ ↦ hw _ (q i).2) le_rfl
  by_cases he : E q
  · obtain ⟨j, hj⟩ := hcover q he
    simpa only [he, hj, ite_true] using
      (Finset.single_le_sum (f := fun j ↦ if W j q then ∏ i, ρ (q i) else 0)
        (fun j _ ↦ hnonneg j) (Finset.mem_univ j))
  · simpa only [he, ite_false] using (Finset.sum_nonneg fun j _ ↦ hnonneg j)

/-- Given a fixed band source, a partial redraw from the original normalized product
law changes its frequency and stays in the band with mass at most
`(n + 1) * 2^n * (n * b)^(cutoff t X)`. The mask is arbitrary. -/
public theorem productProbability_success_le {n d : ℕ} {S : Finset ℕ} {t X b : ℝ}
    (ht : 32 < t) (hX : 1 < X) (hd : 0 < d)
    (hp : ∀ a ∈ S, a.Prime ∧ (a + d).Prime) (hSX : ∀ a ∈ S, (↑(a + d) : ℝ) ≤ X)
    (s : Fin n → Bool) (M : Finset (Fin n)) (p : Fin n → S)
    (hpBand : |t * frequency d s (fun i ↦ p i)| ≤ 2 * Real.pi)
    {ρ : ℕ → ℝ} (hnorm : ∑ a : S, ρ a = 1) (hb : 0 ≤ b)
    (hw : ∀ a ∈ S, 0 ≤ ρ a ∧ ρ a ≤ b) (hnb : (n : ℝ) * b < 1) :
    productProbability ρ (success (d := d) t s M p) ≤
      ((n : ℝ) + 1) * 2 ^ n * ((n : ℝ) * b) ^ cutoff t X := by
  classical
  let K := cutoff t X
  let z : ℝ := n * b
  have hz : 0 ≤ z := mul_nonneg (Nat.cast_nonneg _) hb
  have hM : M.card ≤ n := by simpa using (M.card_le_univ : M.card ≤ Fintype.card (Fin n))
  have hstrict {A : Finset M} {f : A → M} {q : M → S}
      (hwit : Witness (d := d) t s p A f q) : K < M.card - A.card := by
    by_contra! hK
    obtain ⟨v, hfreq, hslots⟩ := frequency_packed s p hwit.2.1 hwit.2.2.1
    have hfreq' := eq_of_survivors hd (by linarith) s
      (bounded_pool hp hSX fun i ↦ (p i).2) (bounded_pool hp hSX (redraw_mem p v)) hslots
      hpBand (by rw [hfreq]; exact hwit.1.1) (budget ht hX hK)
    exact hwit.1.2 (hfreq ▸ hfreq')
  -- For a fixed set of plus slots, count partner maps before summing over sets.
  -- This saves the extra sum over pairing sizes in the source bound.
  have hrow (A : Finset M) :
      (∑ f : A → M, productProbability ρ (Witness (d := d) t s p A f)) ≤ z ^ K := by
    by_cases hA : K < M.card - A.card
    · let r := min (M.card - 2 * A.card) K
      have hr : K ≤ A.card + r := by dsimp [r]; omega
      have hf (f : A → M) :
          productProbability ρ (Witness (d := d) t s p A f) ≤ z ^ r * b ^ A.card := by
        by_cases hm : Matching (fun i : M ↦ s i) A f
        · have hrem : (remaining A f).card = M.card - 2 * A.card := by
            rw [remaining, Finset.card_sdiff_of_subset (Finset.subset_univ _),
              Finset.card_union_of_disjoint (disjoint_partners hm), card_partners hm,
              Finset.card_univ, Fintype.card_coe, two_mul]
          obtain ⟨H, hH, hcard⟩ := Finset.exists_subset_card_eq
            (show r ≤ (remaining A f).card by rw [hrem]; exact min_le_left _ _)
          have hHK : H.card ≤ K := hcard.le.trans (min_le_right _ _)
          simpa only [z, hcard] using
            witness_sections_le ht hX hd hp hSX s p hnorm hb hw hm hH hHK
        · rw [productProbability_empty (fun _ h ↦ hm h.2.1)]
          exact mul_nonneg (pow_nonneg hz _) (pow_nonneg hb _)
      calc
        _ ≤ ∑ _ : A → M, z ^ r * b ^ A.card := Finset.sum_le_sum fun f _ ↦ hf f
        _ = (M.card : ℝ) ^ A.card * (z ^ r * b ^ A.card) := by
          simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_fun,
            Fintype.card_coe, Nat.cast_pow]
        _ ≤ (n : ℝ) ^ A.card * (z ^ r * b ^ A.card) := by
          gcongr
        _ = z ^ (A.card + r) := by rw [pow_add]; simp only [z, mul_pow]; ring
        _ ≤ _ := pow_le_pow_of_le_one hz hnb.le hr
    · calc
        _ = 0 := Finset.sum_eq_zero fun f _ ↦
          productProbability_empty fun _ h ↦ hA (hstrict (f := f) h)
        _ ≤ _ := pow_nonneg hz _
  calc
    _ ≤ ∑ j : (Σ A : Finset M, A → M), productProbability ρ
        (Witness (d := d) t s p j.1 j.2) := by
      apply productProbability_cover_le (fun a ha ↦ (hw a ha).1)
      intro q hq
      obtain ⟨A, f, hm, hpair, hfree⟩ := exists_matching (fun i : M ↦ s i) q
      exact ⟨⟨A, f⟩, hq, hm, hpair, hfree⟩
    _ = ∑ A : Finset M, ∑ f : A → M, productProbability ρ
        (Witness (d := d) t s p A f) := Fintype.sum_sigma _
    _ ≤ ∑ _ : Finset M, z ^ K := Finset.sum_le_sum fun A _ ↦ hrow A
    _ = 2 ^ M.card * z ^ K := by
      simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_finset,
        Fintype.card_coe, Nat.cast_pow, Nat.cast_ofNat]
    _ ≤ 2 ^ n * z ^ K := by
      gcongr
      norm_num
    _ ≤ _ := by
      have hn : 1 ≤ (n : ℝ) + 1 := le_add_of_nonneg_left (Nat.cast_nonneg _)
      simpa only [one_mul] using
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hn (by positivity : (0 : ℝ) ≤ 2 ^ n))
          (pow_nonneg hz K))

end Masullo.PartialRedrawBound
