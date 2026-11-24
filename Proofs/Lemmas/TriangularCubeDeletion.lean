module

public import Lemmas.TriangularGapDifferencing
import Mathlib.Logic.Equiv.Prod
import Mathlib.Tactic.Ring

/-!
# Deletion of repeated vertices in triangular cubes

Source: `dcc11ec5:.godel/bob/signed-gap-cube-screen.md:34–48,56`.
Owning check session: `01a20b8b-65a1-7430-ae92-47e2bde881a8`.

The finite deletion estimate starts with the accepted cyclic `averagedDifference`.
It deletes entire summands only after all the differences, preserving the uniform
averages over gaps, cyclic starts, and independent ordered interval draws. The
integer lift is justified on nonzero summands by finite band margins. This does
not include a frequency estimate, triangular-law coalescing, or an asymptotic screen.
-/

open scoped BigOperators ComplexConjugate

namespace Masullo.TriangularCubeDeletion

open TriangularGapDifferencing

/-- The gap label `g` represents `g.val + 1`, and the cyclic start order is `2G+1`. -/
public abbrev Start (G : ℕ) := ZMod (2 * G + 1)

/-- Each coordinate stores both ordered interval draws, not just their difference. -/
public abbrev Draws (H k : ℕ) := Fin k → Fin H × Fin H

/-- A subset of the difference coordinates, followed by the two offset bits. -/
public abbrev VertexLabel (k : ℕ) := (Fin k → Bool) × Bool × Bool

/-- A coordinate's signed integer displacement before reduction modulo the start order. -/
@[expose] public def intShift {H : ℕ} (a : Fin H × Fin H) : ℤ :=
  (a.1.val + 1 : ℤ) - (a.2.val + 1 : ℤ)

/-- The signed integer displacement of a subset of coordinates. -/
@[expose] public def subsetShift {H k : ℕ} (a : Draws H k) (s : Fin k → Bool) : ℤ :=
  ∑ i, if s i then intShift (a i) else 0

/-- The source's integer-lift vertex at a labelled corner and offset. -/
@[expose] public def vertex {G H k : ℕ} (d : ℤ) (g : Fin G) (a : Draws H k)
    (p : Start G) (v : VertexLabel k) : ℤ :=
  (p.val : ℤ) + subsetShift a v.1 + (if v.2.1 then (g.val : ℤ) + 1 else 0) +
    (if v.2.2 then d else 0)

private abbrev term {G H k : ℕ} (f : Fin G → Start G → ℂ) (g : Fin G)
    (a : Draws H k) (p : Start G) : ℂ :=
  iteratedDifference (intervalDraw (2 * G + 1) H) (f g) k a p

/-- `S`: the original normalized average with a zero at each deleted draw tuple.
In particular, it is not renormalized on the set of surviving tuples. -/
@[expose] public noncomputable def survivingAverage {G H : ℕ} (d : ℤ)
    (f : Fin G → Start G → ℂ) (k : ℕ) : ℂ := by
  classical
  exact 𝔼 g, 𝔼 a : Draws H k, 𝔼 p,
    if Function.Injective (vertex d g a p) then
      iteratedDifference (intervalDraw (2 * G + 1) H) (f g) k a p else 0

private theorem term_norm_le_one {G H k : ℕ} {f : Fin G → Start G → ℂ}
    (hf : ∀ g p, ‖f g p‖ ≤ 1) (g : Fin G) (a : Draws H k) (p : Start G) :
    ‖term f g a p‖ ≤ 1 := by
  induction k generalizing p with
  | zero => exact hf g p
  | succ k ih =>
    simp only [term, iteratedDifference, difference, norm_mul, Complex.norm_conj]
    simpa only [one_mul] using
      mul_le_mul (ih (Fin.init a) _) (ih (Fin.init a) p) (norm_nonneg _) zero_le_one

private theorem intShift_cast {N H : ℕ} (a : Fin H × Fin H) :
    (intShift a : ZMod N) = intervalDraw N H a.1 - intervalDraw N H a.2 := by
  simp [intShift, intervalDraw]

private theorem subsetShift_succ {H k : ℕ} (a : Draws H (k + 1))
    (s : Fin (k + 1) → Bool) :
    subsetShift a s = subsetShift (Fin.init a) (Fin.init s) +
      (if s (Fin.last k) then intShift (a (Fin.last k)) else 0) := by
  simp only [subsetShift, Fin.sum_univ_castSucc, Fin.init_def]
  rfl

private theorem corner_ne_zero {G H k : ℕ} {f : Fin G → Start G → ℂ} {g : Fin G}
    {a : Draws H k} {p : Start G} (hn : term f g a p ≠ 0) (s : Fin k → Bool) :
    f g (p + (subsetShift a s : Start G)) ≠ 0 := by
  induction k generalizing p with
  | zero => simpa [subsetShift, term, iteratedDifference] using hn
  | succ k ih =>
    simp only [term, iteratedDifference, difference, mul_ne_zero_iff, map_ne_zero] at hn
    rw [subsetShift_succ]
    cases hs : s (Fin.last k) with
    | false =>
      simpa [hs] using ih hn.2 (Fin.init s)
    | true =>
      simpa [hs, intShift_cast, ← add_assoc, add_right_comm] using
        ih hn.1 (Fin.init s)

private theorem root_ne_zero {G H k : ℕ} {f : Fin G → Start G → ℂ} {g : Fin G}
    {a : Draws H k} {p : Start G} (hn : term f g a p ≠ 0) : f g p ≠ 0 := by
  simpa [subsetShift] using corner_ne_zero hn (fun _ => false)

private theorem abs_subsetShift_le {H k : ℕ} (a : Draws H k) (s : Fin k → Bool) :
    |subsetShift a s| ≤ (k : ℤ) * ((H : ℤ) - 1) := by
  unfold subsetShift
  calc
    |∑ i, if s i then intShift (a i) else 0| ≤
        ∑ i, |if s i then intShift (a i) else 0| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin k, ((H : ℤ) - 1) := by
      refine Finset.sum_le_sum fun i _ => ?_
      have hx := (a i).1.isLt
      have hy := (a i).2.isLt
      cases s i
      · simp only [Bool.false_eq_true, ↓reduceIte, abs_zero]
        omega
      · simp only [↓reduceIte, abs_le, intShift]
        omega
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- No wrap on a contributing tuple. If the integer support has room for the
largest possible subset displacement, each corner representative is its integer
lift. The offsets are then applied to that representative in the integers,
as in the definition of `f`; `hband` keeps the resulting vertices in range. -/
public theorem vertex_on_support {G H k : ℕ} {d : ℤ} {f : Fin G → Start G → ℂ}
    {g : Fin G} {a : Draws H k} {p : Start G}
    (hn : iteratedDifference (intervalDraw (2 * G + 1) H) (f g) k a p ≠ 0)
    (hd : 0 ≤ d)
    (hband : ∀ q, f g q ≠ 0 →
      (k : ℤ) * ((H : ℤ) - 1) ≤ (q.val : ℤ) ∧
      (q.val : ℤ) + (k : ℤ) * ((H : ℤ) - 1) < ((2 * G + 1 : ℕ) : ℤ) ∧
      (q.val : ℤ) + (g.val : ℤ) + 1 + d < ((2 * G + 1 : ℕ) : ℤ))
    (v : VertexLabel k) :
    let q := p + (subsetShift a v.1 : Start G)
    f g q ≠ 0 ∧
      vertex d g a p v = (q.val : ℤ) + (if v.2.1 then (g.val : ℤ) + 1 else 0) +
        (if v.2.2 then d else 0) ∧
      0 ≤ vertex d g a p v ∧ vertex d g a p v < ((2 * G + 1 : ℕ) : ℤ) := by
  dsimp only
  let q : Start G := p + (subsetShift a v.1 : Start G)
  have hq : f g q ≠ 0 := corner_ne_zero hn v.1
  have hroot := hband p (root_ne_zero hn)
  have hshift := abs_le.mp (abs_subsetShift_le a v.1)
  have hlo : 0 ≤ (p.val : ℤ) + subsetShift a v.1 := by omega
  have hhi : (p.val : ℤ) + subsetShift a v.1 < ((2 * G + 1 : ℕ) : ℤ) := by omega
  have hcast : (((p.val : ℤ) + subsetShift a v.1 : ℤ) : Start G) = q := by
    simp only [q, Int.cast_add, Int.cast_natCast, ZMod.natCast_zmod_val]
  have hval : (q.val : ℤ) = (p.val : ℤ) + subsetShift a v.1 := by
    rw [← hcast, ZMod.val_intCast, Int.emod_eq_of_lt hlo hhi]
  have hv : vertex d g a p v = (q.val : ℤ) + (if v.2.1 then (g.val : ℤ) + 1 else 0) +
      (if v.2.2 then d else 0) := by rw [vertex, hval]
  refine ⟨hq, hv, ?_⟩
  have hright := (hband q hq).2.2
  rw [hv]
  cases v.2.1 <;> cases v.2.2 <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega

private theorem label_eq_of_subset_eq {G H k : ℕ} {d : ℤ} {g : Fin G} {a : Draws H k}
    {p : Start G} {u v : VertexLabel k} (hd : 0 < d) (hg : d < (g.val : ℤ) + 1)
    (hs : u.1 = v.1) (hv : vertex d g a p u = vertex d g a p v) : u = v := by
  obtain ⟨s, e, b⟩ := u
  obtain ⟨t, e', b'⟩ := v
  change s = t at hs
  subst t
  cases e <;> cases b <;> cases e' <;> cases b' <;> simp [vertex] at hv ⊢ <;> omega

private noncomputable def collision {G H k : ℕ} (d : ℤ) (g : Fin G) (a : Draws H k)
    (p : Start G) (uv : VertexLabel k × VertexLabel k) : ℝ := by
  classical
  exact if uv.1.1 ≠ uv.2.1 ∧ vertex d g a p uv.1 = vertex d g a p uv.2 then 1 else 0

private theorem collision_nonneg {G H k : ℕ} (d : ℤ) (g : Fin G) (a : Draws H k)
    (p : Start G) (uv : VertexLabel k × VertexLabel k) : 0 ≤ collision d g a p uv := by
  classical
  unfold collision
  split <;> norm_num

private theorem norm_deleted_le {G H k : ℕ} {d : ℤ} {f : Fin G → Start G → ℂ}
    (hf : ∀ g p, ‖f g p‖ ≤ 1)
    (hsep : ∀ g p, f g p ≠ 0 → 0 < d ∧ d < (g.val : ℤ) + 1)
    (g : Fin G) (a : Draws H k) (p : Start G) :
    ‖(if Function.Injective (vertex d g a p) then 0 else term f g a p)‖ ≤
      ∑ uv, collision d g a p uv := by
  classical
  by_cases hi : Function.Injective (vertex d g a p)
  · simp only [ite_eq_left hi, norm_zero]
    exact Finset.sum_nonneg fun uv _ => collision_nonneg d g a p uv
  simp only [ite_eq_right hi]
  by_cases hz : term f g a p = 0
  · rw [hz, norm_zero]
    exact Finset.sum_nonneg fun uv _ => collision_nonneg d g a p uv
  obtain ⟨hd, hg⟩ := hsep g p (root_ne_zero hz)
  obtain ⟨u, v, hv, huv⟩ : ∃ u v, vertex d g a p u = vertex d g a p v ∧ u ≠ v := by
    simpa only [Function.Injective, not_forall, not_imp, exists_prop] using hi
  have hs : u.1 ≠ v.1 := fun h => huv (label_eq_of_subset_eq hd hg h hv)
  calc
    ‖term f g a p‖ ≤ 1 := term_norm_le_one hf g a p
    _ = collision d g a p (u, v) := by simp [collision, hs, hv]
    _ ≤ ∑ uv, collision d g a p uv :=
      Finset.single_le_sum (fun uv _ => collision_nonneg d g a p uv) (Finset.mem_univ _)

private theorem expect_le_of_nonneg {α : Type*} [Fintype α] (F : α → ℝ) {c : ℝ}
    (hc : 0 ≤ c) (hF : ∀ x, F x ≤ c) : (𝔼 x, F x) ≤ c := by
  classical
  by_cases h : (Finset.univ : Finset α).Nonempty
  · exact Finset.expect_le h fun x _ => hF x
  · rw [Finset.not_nonempty_iff_eq_empty.mp h, Finset.expect_empty]
    exact hc

private theorem expect_fiber_le {H : ℕ} (P : Fin H → Prop) [DecidablePred P]
    (h : ∀ x y, P x → P y → x = y) :
    (𝔼 x, if P x then (1 : ℝ) else 0) ≤ 1 / (H : ℝ) := by
  let T := Finset.univ.filter P
  have hT : T.card ≤ 1 := Finset.card_le_one.mpr fun x hx y hy =>
    h x y (Finset.mem_filter.mp hx).2 (Finset.mem_filter.mp hy).2
  rw [Finset.expect_eq_sum_div_card, ← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one, Finset.card_univ, Fintype.card_fin]
  exact div_le_div_of_nonneg_right (by exact_mod_cast hT) (Nat.cast_nonneg H)

private theorem expect_prod {α β M : Type*} [Fintype α] [Fintype β]
    [AddCommMonoid M] [Module ℚ≥0 M] (F : α × β → M) :
    (𝔼 x, F x) = 𝔼 a, 𝔼 b, F (a, b) := by
  rw [← Finset.expect_product', Finset.univ_product_univ]

private theorem vertex_eq_fiber {G H k : ℕ} (d : ℤ) (g : Fin G) (p : Start G)
    (u v : VertexLabel k) (i : Fin k) (hi : u.1 i ≠ v.1 i)
    (a a' : Draws H k) (hrest : ∀ j, j ≠ i → a j = a' j)
    (hsnd : (a i).2 = (a' i).2)
    (ha : vertex d g a p u = vertex d g a p v)
    (ha' : vertex d g a' p u = vertex d g a' p v) : (a i).1 = (a' i).1 := by
  have hsplit (s : Fin k → Bool) :
      subsetShift a s - (if s i then intShift (a i) else 0) =
        subsetShift a' s - (if s i then intShift (a' i) else 0) := by
    have heq : (∑ j ∈ Finset.univ.erase i, if s j then intShift (a j) else 0) =
        ∑ j ∈ Finset.univ.erase i, if s j then intShift (a' j) else 0 := by
      exact Finset.sum_congr rfl fun j hj => by rw [hrest j (Finset.mem_erase.mp hj).1]
    unfold subsetShift
    rw [← Finset.sum_erase_add Finset.univ _ (Finset.mem_univ i),
      ← Finset.sum_erase_add Finset.univ _ (Finset.mem_univ i)]
    simpa using heq
  have hu := hsplit u.1
  have hv := hsplit v.1
  simp only [vertex] at ha ha'
  cases hus : u.1 i <;> cases hvs : v.1 i
  all_goals try exact (hi (hus.trans hvs.symm)).elim
  all_goals
    simp only [hus, hvs, Bool.false_eq_true, ↓reduceIte] at hu hv
    apply Fin.ext
    have hsndval := congrArg Fin.val hsnd
    simp only [intShift] at hu hv
    omega

/-- Each ordered pair of differently masked vertices collides on at most a
`1/H` fraction of the original ordered draw tuples. -/
private theorem expect_collision_le {G H k : ℕ} (d : ℤ) (g : Fin G) (p : Start G)
    (uv : VertexLabel k × VertexLabel k) : (𝔼 a, collision (H := H) d g a p uv) ≤ 1 / (H : ℝ) := by
  classical
  by_cases hs : uv.1.1 = uv.2.1
  · simp [collision, hs]
  have hex : ∃ i, uv.1.1 i ≠ uv.2.1 i := by
    by_contra! hh
    exact hs (funext hh)
  obtain ⟨i, hi⟩ := hex
  let e := Equiv.piSplitAt i (fun _ => Fin H × Fin H)
  rw [← Fintype.expect_equiv e.symm _ (fun a => collision d g a p uv) (fun _ => rfl),
    expect_prod, Finset.expect_comm]
  refine expect_le_of_nonneg _ (by positivity) fun rest => ?_
  rw [expect_prod, Finset.expect_comm]
  refine expect_le_of_nonneg _ (by positivity) fun y => ?_
  let A (x : Fin H) : Draws H k := e.symm ((x, y), rest)
  have hA (x : Fin H) : A x i = (x, y) ∧ ∀ j : {j // j ≠ i}, A x j = rest j := by
    have he := e.apply_symm_apply ((x, y), rest)
    change (A x i, fun j : {j // j ≠ i} => A x j.val) = ((x, y), rest) at he
    exact ⟨congrArg Prod.fst he, fun j => congrFun (congrArg Prod.snd he) j⟩
  change (𝔼 x, collision d g (A x) p uv) ≤ _
  simp only [collision]
  refine expect_fiber_le _ fun x x' hx hx' => ?_
  have hxx := vertex_eq_fiber d g p uv.1 uv.2 i hi (A x) (A x')
    (fun j hj => ((hA x).2 ⟨j, hj⟩).trans ((hA x').2 ⟨j, hj⟩).symm)
    (by rw [(hA x).1, (hA x').1]) hx.2 hx'.2
  simpa only [(hA x).1, (hA x').1] using hxx

/-- On the original uniform gap, ordered draw and cyclic start domains, the
mass removed by discarding repeated integer-lift vertices is at most `R²/H`,
where `R = 4 * 2^k`. The four offsets need be distinct only on the support
of `f`. Empty averages are zero, with no positivity assumptions on `G`, `H`
or `k` needed for this estimate. -/
public theorem cyclic_iteratedDifference_deletion_bound {G H k : ℕ} (d : ℤ)
    (f : Fin G → Start G → ℂ) (hf : ∀ g p, ‖f g p‖ ≤ 1)
    (hsep : ∀ g p, f g p ≠ 0 → 0 < d ∧ d < (g.val : ℤ) + 1) :
    ‖averagedDifference (intervalDraw (2 * G + 1) H) f k - survivingAverage (H := H) d f k‖ ≤
      (4 * 2 ^ k : ℝ) ^ 2 / (H : ℝ) := by
  classical
  simp only [averagedDifference, survivingAverage, ← Finset.expect_sub_distrib]
  have hdeleted (g : Fin G) (a : Draws H k) (p : Start G) :
      term f g a p - (if Function.Injective (vertex d g a p) then term f g a p else 0) =
        if Function.Injective (vertex d g a p) then 0 else term f g a p := by
    split <;> simp_all
  simp only [hdeleted]
  refine (RCLike.norm_expect_le (K := ℂ)).trans (expect_le_of_nonneg _ (by positivity) fun g => ?_)
  refine (RCLike.norm_expect_le (K := ℂ)).trans ?_
  refine (Finset.expect_le_expect fun a _ => (RCLike.norm_expect_le (K := ℂ)).trans
    (Finset.expect_le_expect fun p _ => norm_deleted_le hf hsep g a p)).trans ?_
  rw [Finset.expect_comm]
  refine expect_le_of_nonneg _ (by positivity) fun p => ?_
  rw [Finset.expect_sum_comm]
  calc
    (∑ uv, 𝔼 a, collision (H := H) d g a p uv) ≤
        ∑ _uv : VertexLabel k × VertexLabel k, (1 : ℝ) / (H : ℝ) :=
      Finset.sum_le_sum fun uv _ => expect_collision_le d g p uv
    _ = (4 * 2 ^ k : ℝ) ^ 2 / (H : ℝ) := by
      simp only [Finset.sum_const, Finset.card_univ, VertexLabel, Fintype.card_prod,
        Fintype.card_fun, Fintype.card_fin, Fintype.card_bool, nsmul_eq_mul, Nat.cast_mul,
        Nat.cast_pow, Nat.cast_ofNat]
      ring

end Masullo.TriangularCubeDeletion
