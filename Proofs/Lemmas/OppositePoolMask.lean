module

public import Lemmas.MixedPoolMoment
import Lemmas.PrimeShiftProductInjective
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Source masks for opposite signs in a log-frequency pool

Source: `23e865ff:.godel/bob/net-pool-supply.md:20–28`, “An extra small sum is
necessary” and the three input windows of “Price the ambiguity” (Rank 6).
Owning check session: `01a209f7-85a2-71df-a0cc-7987e51e67d1`.

The sign hypothesis is on the sign-averaged **log** product, with the actual
compact taper. We do not average the original finite arithmetic kernel here.
The permutation matches positions in the disjoint union of the two copies;
there is no distinctness requirement across copies. Within-copy separation
is used only for distinctness of the starts and hence nonvanishing of a
nonempty signed prime-ratio frequency. Balance and the other completed gates
are not needed for this implication. The majority windows are centered at
the negatives of the respective oriented minority sums. The fixed-mask mass
estimate, subsequent union over masks, and asymptotic loss are not proved here.
-/

open scoped BigOperators

namespace Masullo.OppositePoolMask

open SignedBlockIntervalMoment (signedSum)

variable {α : Type*} {n : ℕ}

/-- `true` keeps a sign, `false` reverses it. -/
@[expose] public def orient (g s : Bool) : Bool := if g then s else !s

/-- The corresponding action on a real frequency. -/
@[expose] public def act (g : Bool) (x : ℝ) : ℝ := if g then x else -x

/-- A copy has one label and one sign per occurrence. -/
public structure Copy (α : Type*) (n : ℕ) where
  start : Fin n → α
  positive : Fin n → Bool

@[expose] public noncomputable def Copy.frequency (a : Copy α n) (labels : α → ℝ) : ℝ :=
  signedSum labels a.positive a.start

@[expose] public noncomputable def Copy.blockSum (a : Copy α n) (labels : α → ℝ)
    (g : Bool) (S : Finset (Fin n)) : ℝ :=
  ∑ i ∈ S, act (orient g (a.positive i)) (labels (a.start i))

@[expose] public noncomputable def taper (z : ℝ) : ℝ := max (1 - |z| / (2 * Real.pi)) 0

@[expose] public noncomputable def taperedCos (z : ℝ) : ℝ := taper z * Real.cos z

/-- The exact log-coordinate kernel after averaging orientations. -/
@[expose] public noncomputable def poolTerm (t x y : ℝ) : ℝ :=
  taperedCos (t * x) * taperedCos (t * y)

/-- Two minority masks and the signs orienting the original copies. -/
public structure Mask (n : ℕ) where
  g₁ : Bool
  g₂ : Bool
  first : Finset (Fin n)
  second : Finset (Fin n)

@[expose] public noncomputable def Mask.minoritySum (M : Mask n) (labels : α → ℝ)
    (a b : Copy α n) : ℝ := a.blockSum labels M.g₁ M.first + b.blockSum labels M.g₂ M.second

/-- The size constraints, extra small sum and two translated majority windows. -/
public structure Mask.Hits (M : Mask n) (t : ℝ) (labels : α → ℝ) (a b : Copy α n) : Prop where
  first_le : M.first.card ≤ n / 2
  second_le : M.second.card ≤ n / 2
  minority_pos : 0 < |M.minoritySum labels a b|
  minority_le : |M.minoritySum labels a b| ≤ 4 * Real.pi / t
  first_window :
    |a.blockSum labels M.g₁ M.firstᶜ - (-a.blockSum labels M.g₁ M.first)| ≤ 2 * Real.pi / t
  second_window :
    |b.blockSum labels M.g₂ M.secondᶜ - (-b.blockSum labels M.g₂ M.second)| ≤ 2 * Real.pi / t

/-- The sign assigned to each target occurrence in the sum or difference of target frequencies. -/
@[expose] public def targetSign (a' b' : Copy α n) (ε : Bool) : Fin n ⊕ Fin n → Bool :=
  Sum.elim a'.positive (fun i ↦ orient ε (b'.positive i))

/-- Compare the incoming signs at source positions with the oriented source signs. -/
@[expose] public def disagree (σ τ : Fin n → Bool) (g : Bool) : Finset (Fin n) :=
  Finset.univ.filter fun i ↦ orient g (σ i) ≠ τ i

/-- A witness on the source positions. The permutation runs from source to target. -/
public structure Mask.IsWitness (M : Mask n) (t : ℝ) (labels : α → ℝ)
    (a b a' b' : Copy α n) (e : Equiv.Perm (Fin n ⊕ Fin n)) (ε : Bool) : Prop where
  first_eq : M.first = disagree a.positive (fun i ↦ targetSign a' b' ε (e (.inl i))) M.g₁
  second_eq : M.second = disagree b.positive (fun i ↦ targetSign a' b' ε (e (.inr i))) M.g₂
  outside : ∀ g₁ g₂ : Bool, a'.frequency labels + act ε (b'.frequency labels) ≠
    act g₁ (a.frequency labels) + act g₂ (b.frequency labels)
  twice_minority : 2 * M.minoritySum labels a b =
    act M.g₁ (a.frequency labels) + act M.g₂ (b.frequency labels) -
      (a'.frequency labels + act ε (b'.frequency labels))
  hits : M.Hits t labels a b

private theorem abs_act (g : Bool) (x : ℝ) : |act g x| = |x| := by
  cases g <;> simp [act]

private theorem sum_act (s : Finset (Fin n)) (g : Bool) (f : Fin n → ℝ) :
    ∑ i ∈ s, act g (f i) = act g (∑ i ∈ s, f i) := by
  cases g <;> simp [act, Finset.sum_neg_distrib]

private theorem act_orient (g s : Bool) (x : ℝ) : act (orient g s) x = act g (act s x) := by
  cases g <;> cases s <;> simp [act, orient]

private theorem blockSum_univ (a : Copy α n) (labels : α → ℝ) (g : Bool) :
    a.blockSum labels g Finset.univ = act g (a.frequency labels) := by
  change (∑ i, act (orient g (a.positive i)) (labels (a.start i))) =
    act g (∑ i, act (a.positive i) (labels (a.start i)))
  simp only [act_orient, sum_act]

private theorem abs_lt_of_taper_pos {z : ℝ} (h : 0 < taper z) : |z| < 2 * Real.pi := by
  have hπ : 0 < 2 * Real.pi := by positivity
  have ht := (lt_max_iff.mp h).resolve_right (lt_irrefl _)
  exact (div_lt_one hπ).mp (by linarith only [ht])

private theorem opposite_products {t x y x' y' : ℝ} (ht : 0 < t)
    (h : poolTerm t x y * poolTerm t x' y' < 0) :
    |x| < 2 * Real.pi / t ∧ |y| < 2 * Real.pi / t ∧
      |x'| < 2 * Real.pi / t ∧ |y'| < 2 * Real.pi / t ∧
      (Real.cos (t * x) * Real.cos (t * y)) *
        (Real.cos (t * x') * Real.cos (t * y')) < 0 := by
  let K := (taper (t * x) * taper (t * y)) * (taper (t * x') * taper (t * y'))
  have heq : poolTerm t x y * poolTerm t x' y' = K *
      ((Real.cos (t * x) * Real.cos (t * y)) * (Real.cos (t * x') * Real.cos (t * y'))) := by
    unfold K poolTerm taperedCos
    ring
  have hnonneg z : 0 ≤ taper z := le_max_right _ _
  have hpos (z : ℝ) (hz : taper z ≠ 0) : |z| < 2 * Real.pi :=
    abs_lt_of_taper_pos (lt_of_le_of_ne (hnonneg z) (Ne.symm hz))
  rw [heq] at h
  have hK : K ≠ 0 := left_ne_zero_of_mul (ne_of_lt h)
  have hKpos : 0 < K := lt_of_le_of_ne
    (mul_nonneg (mul_nonneg (hnonneg _) (hnonneg _)) (mul_nonneg (hnonneg _) (hnonneg _))) hK.symm
  obtain ⟨hx, hy⟩ := mul_ne_zero_iff.mp (left_ne_zero_of_mul hK)
  obtain ⟨hx', hy'⟩ := mul_ne_zero_iff.mp (right_ne_zero_of_mul hK)
  have window (u : ℝ) (hu : taper (t * u) ≠ 0) : |u| < 2 * Real.pi / t := by
    have hh := hpos (t * u) hu
    rwa [abs_mul, abs_of_pos ht, mul_comm, ← lt_div_iff₀ ht] at hh
  refine ⟨window x hx, window y hy, window x' hx', window y' hy', ?_⟩
  by_contra! hc
  exact (not_lt_of_ge (mul_nonneg hKpos.le hc)) h

private def SameClass (u v : ℝ) : Prop := u = v ∨ u = -v

private theorem cos_eq_of_class {u v : ℝ} (h : SameClass u v) (t : ℝ) :
    Real.cos (t * u) = Real.cos (t * v) := by
  rcases h with h | h <;> simp [h, mul_neg, Real.cos_neg]

private theorem signed_pair_class (g₁ g₂ : Bool) (x y : ℝ) :
    SameClass (act g₁ x + act g₂ y) (x + y) ∨ SameClass (act g₁ x + act g₂ y) (x - y) := by
  cases g₁ <;> cases g₂
  · exact Or.inl (Or.inr (by simp [act, add_comm]))
  · exact Or.inr (Or.inr (by simp [act]; ring))
  · exact Or.inr (Or.inl (by simp [act, sub_eq_add_neg]))
  · exact Or.inl (Or.inl rfl)

private theorem cos_sum_diff (t x y : ℝ) :
    Real.cos (t * (x + y)) + Real.cos (t * (x - y)) =
      2 * (Real.cos (t * x) * Real.cos (t * y)) := by
  rw [mul_add, mul_sub, Real.cos_add, Real.cos_sub]
  ring

private theorem exists_outside {t x y x' y' : ℝ} (hx' : x' ≠ 0) (hy' : y' ≠ 0)
    (hc : (Real.cos (t * x) * Real.cos (t * y)) *
      (Real.cos (t * x') * Real.cos (t * y')) < 0) :
    ∃ ε : Bool, ∀ g₁ g₂ : Bool, x' + act ε y' ≠ act g₁ x + act g₂ y := by
  by_contra! h
  have hp : SameClass (x' + y') (x + y) ∨ SameClass (x' + y') (x - y) := by
    obtain ⟨g₁, g₂, he⟩ := h true
    rw [show x' + y' = act g₁ x + act g₂ y from he]
    exact signed_pair_class g₁ g₂ x y
  have hm : SameClass (x' - y') (x + y) ∨ SameClass (x' - y') (x - y) := by
    obtain ⟨g₁, g₂, he⟩ := h false
    rw [show x' - y' = act g₁ x + act g₂ y by simpa [act, sub_eq_add_neg] using he]
    exact signed_pair_class g₁ g₂ x y
  have different (v : ℝ) (h₁ : SameClass (x' + y') v) (h₂ : SameClass (x' - y') v) : False := by
    rcases h₁ with h₁ | h₁ <;> rcases h₂ with h₂ | h₂
    · exact hy' (by linarith only [h₁, h₂])
    · exact hx' (by linarith only [h₁, h₂])
    · exact hx' (by linarith only [h₁, h₂])
    · exact hy' (by linarith only [h₁, h₂])
  have heq : Real.cos (t * x') * Real.cos (t * y') = Real.cos (t * x) * Real.cos (t * y) := by
    have h₁ := cos_sum_diff t x y
    have h₂ := cos_sum_diff t x' y'
    rcases hp with hp | hp <;> rcases hm with hm | hm
    · exact (different _ hp hm).elim
    · rw [cos_eq_of_class hp t, cos_eq_of_class hm t] at h₂
      linarith only [h₁, h₂]
    · rw [cos_eq_of_class hp t, cos_eq_of_class hm t] at h₂
      linarith only [h₁, h₂]
    · exact (different _ hp hm).elim
  rw [heq] at hc
  exact (not_lt_of_ge (mul_self_nonneg _)) hc

private theorem exists_minor_orientation (σ τ : Fin n → Bool) :
    ∃ g : Bool, (disagree σ τ g).card ≤ n / 2 := by
  by_cases h : (disagree σ τ true).card ≤ n / 2
  · exact ⟨true, h⟩
  refine ⟨false, ?_⟩
  have hc : disagree σ τ false = (disagree σ τ true)ᶜ := by
    ext i
    cases hs : σ i <;> cases ht : τ i <;> simp [disagree, orient, hs, ht]
  rw [hc, Finset.card_compl, Fintype.card_fin]
  omega

private theorem diff_eq_twice_block (a : Copy α n) (labels : α → ℝ)
    (τ : Fin n → Bool) (g : Bool) :
    act g (a.frequency labels) - signedSum labels τ a.start =
      2 * a.blockSum labels g (disagree a.positive τ g) := by
  rw [← blockSum_univ]
  simp only [Copy.blockSum, disagree, signedSum, ← Finset.sum_sub_distrib,
    Finset.mul_sum, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  cases hs : orient g (a.positive i) <;> cases ht : τ i <;> simp [act, *] <;> ring

private theorem transported_sum (labels : α → ℝ) (a b a' b' : Copy α n)
    (e : Equiv.Perm (Fin n ⊕ Fin n))
    (he : ∀ j, Sum.elim a'.start b'.start (e j) = Sum.elim a.start b.start j) (ε : Bool) :
    signedSum labels (fun i ↦ targetSign a' b' ε (e (.inl i))) a.start +
      signedSum labels (fun i ↦ targetSign a' b' ε (e (.inr i))) b.start =
        a'.frequency labels + act ε (b'.frequency labels) := by
  let f : Fin n ⊕ Fin n → ℝ := fun j ↦
    act (targetSign a' b' ε j) (labels (Sum.elim a'.start b'.start j))
  calc
    _ = ∑ j, f (e j) := by
      rw [Fintype.sum_sum_type]
      simp only [f, he, Sum.elim_inl, Sum.elim_inr, signedSum, act]
    _ = ∑ j, f j := Equiv.sum_comp e f
    _ = _ := by
      rw [Fintype.sum_sum_type, ← blockSum_univ b' labels ε]
      rfl

private theorem majority_window (a : Copy α n) (labels : α → ℝ) (g : Bool)
    (S : Finset (Fin n)) {R : ℝ} (h : |a.frequency labels| ≤ R) :
    |a.blockSum labels g Sᶜ - (-a.blockSum labels g S)| ≤ R := by
  rw [sub_neg_eq_add]
  have heq : a.blockSum labels g Sᶜ + a.blockSum labels g S = a.blockSum labels g Finset.univ :=
    Finset.sum_compl_add_sum S _
  rwa [heq, blockSum_univ, abs_act]

/-- Finite mask implication for arbitrary labels and signed copies. The only frequency
nonvanishing required in the class argument is that of the two target copies. -/
public theorem exists_mask_of_opposite {t : ℝ} (ht : 0 < t) (labels : α → ℝ)
    (a b a' b' : Copy α n) (e : Equiv.Perm (Fin n ⊕ Fin n))
    (he : ∀ j, Sum.elim a'.start b'.start (e j) = Sum.elim a.start b.start j)
    (ha' : a'.frequency labels ≠ 0) (hb' : b'.frequency labels ≠ 0)
    (hopp : poolTerm t (a.frequency labels) (b.frequency labels) *
      poolTerm t (a'.frequency labels) (b'.frequency labels) < 0) :
    ∃ (ε : Bool) (M : Mask n), M.IsWitness t labels a b a' b' e ε := by
  obtain ⟨ha, hb, ha'w, hb'w, hcos⟩ := opposite_products ht hopp
  obtain ⟨ε, hout⟩ := exists_outside ha' hb' hcos
  let τ₁ i := targetSign a' b' ε (e (.inl i))
  let τ₂ i := targetSign a' b' ε (e (.inr i))
  obtain ⟨g₁, hg₁⟩ := exists_minor_orientation a.positive τ₁
  obtain ⟨g₂, hg₂⟩ := exists_minor_orientation b.positive τ₂
  let M : Mask n := ⟨g₁, g₂, disagree a.positive τ₁ g₁, disagree b.positive τ₂ g₂⟩
  have hsum := transported_sum labels a b a' b' e he ε
  have hW : 2 * M.minoritySum labels a b = act g₁ (a.frequency labels) +
      act g₂ (b.frequency labels) - (a'.frequency labels + act ε (b'.frequency labels)) := by
    have h₁ := diff_eq_twice_block a labels τ₁ g₁
    have h₂ := diff_eq_twice_block b labels τ₂ g₂
    change signedSum labels τ₁ a.start + signedSum labels τ₂ b.start = _ at hsum
    dsimp [Mask.minoritySum, M]
    linarith only [h₁, h₂, hsum]
  have hWne : M.minoritySum labels a b ≠ 0 := by
    intro heq
    apply hout g₁ g₂
    rw [heq, mul_zero] at hW
    linarith only [hW]
  have hbound := abs_sub (act g₁ (a.frequency labels) + act g₂ (b.frequency labels))
    (a'.frequency labels + act ε (b'.frequency labels))
  have hs := abs_add_le (act g₁ (a.frequency labels)) (act g₂ (b.frequency labels))
  have hh := abs_add_le (a'.frequency labels) (act ε (b'.frequency labels))
  rw [← hW, abs_mul, abs_of_nonneg (show 0 ≤ (2 : ℝ) by norm_num)] at hbound
  rw [abs_act, abs_act] at hs
  rw [abs_act] at hh
  refine ⟨ε, M, rfl, rfl, hout, hW, hg₁, hg₂, abs_pos.mpr hWne, ?_,
    majority_window a labels g₁ _ ha.le, majority_window b labels g₂ _ hb.le⟩
  rw [show 4 * Real.pi / t = 2 * (2 * Real.pi / t) by ring]
  linarith only [hbound, hs, hh, ha, hb, ha'w, hb'w]

/-- Enumerate a block of source positions, retaining their oriented signs and values. -/
@[expose] public noncomputable def Copy.restrict (a : Copy α n) (g : Bool)
    (S : Finset (Fin n)) : Copy α S.card where
  start i := a.start (S.equivFin.symm i)
  positive i := orient g (a.positive (S.equivFin.symm i))

private theorem frequency_restrict (a : Copy α n) (labels : α → ℝ) (g : Bool)
    (S : Finset (Fin n)) : (a.restrict g S).frequency labels = a.blockSum labels g S := by
  calc
    _ = ∑ i : S, act (orient g (a.positive i)) (labels (a.start i)) :=
      S.equivFin.symm.sum_comp _
    _ = _ := Finset.sum_coe_sort S fun i ↦ act (orient g (a.positive i)) (labels (a.start i))

/-- The same witness gives the existing fixed-mask gates after enumerating its four blocks. -/
public theorem Mask.Hits.threeHits {M : Mask n} {t : ℝ} {labels : α → ℝ} {a b : Copy α n}
    (h : M.Hits t labels a b) :
    let aₘ := a.restrict M.g₁ M.first
    let bₘ := b.restrict M.g₂ M.second
    let aᵣ := a.restrict M.g₁ M.firstᶜ
    let bᵣ := b.restrict M.g₂ M.secondᶜ
    MixedPoolMoment.ThreeHits t labels aₘ.positive bₘ.positive aᵣ.positive bᵣ.positive
      (Fin.append aₘ.start bₘ.start) aᵣ.start bᵣ.start := by
  dsimp only
  unfold MixedPoolMoment.ThreeHits
  have happend {m k : ℕ} (u : Copy α m) (v : Copy α k) :
      signedSum labels (Fin.append u.positive v.positive) (Fin.append u.start v.start) =
        u.frequency labels + v.frequency labels := by
    simp only [Copy.frequency, signedSum, Fin.sum_univ_add, Fin.append_left, Fin.append_right]
  have hfreq {k : ℕ} (u : Copy α k) :
      signedSum labels u.positive u.start = u.frequency labels := rfl
  simp only [happend, Function.comp_def, Fin.append_left, Fin.append_right, hfreq,
    frequency_restrict]
  exact ⟨⟨h.minority_pos, h.minority_le⟩,
    by simpa only [sub_neg_eq_add] using h.first_window,
    by simpa only [sub_neg_eq_add] using h.second_window⟩

/-- Unscaled log label for a start at the fixed positive shift `d`. -/
@[expose] public noncomputable def logRatio (d p : ℕ) : ℝ :=
  Real.log ((↑(p + d) : ℝ) / p)

/-- On positive starts this is the manuscript's `log(1+d/p)`. -/
public theorem logRatio_eq_log_one_add (d : ℕ) {p : ℕ} (hp : 0 < p) :
    logRatio d p = Real.log (1 + (d : ℝ) / p) := by
  rw [logRatio, Nat.cast_add, add_div, div_self (Nat.cast_pos.mpr hp).ne']

/-- Both endpoints of every start in this copy are primes at shift `d`. -/
@[expose] public def Copy.PrimeStarts (a : Copy ℕ n) (d : ℕ) : Prop :=
  ∀ i, (a.start i).Prime ∧ (a.start i + d).Prime

private def num (d p : ℕ) (s : Bool) : ℕ := if s then p + d else p
private def den (d p : ℕ) (s : Bool) : ℕ := if s then p else p + d

private theorem slot_bounds {d p : ℕ} (s : Bool) (hp : 0 < p) :
    0 < num d p s ∧ 0 < den d p s ∧ num d p s ≤ p + d ∧ den d p s ≤ p + d := by
  have h := Nat.le_add_right p d
  have h' := hp.trans_le h
  cases s <;> simp [num, den, hp, h, h']

private theorem frequency_eq_logs (d : ℕ) (a : Copy ℕ n) (hp : ∀ i, 0 < a.start i) :
    a.frequency (logRatio d) = Real.log (↑(∏ i, num d (a.start i) (a.positive i)) : ℝ) -
      Real.log (↑(∏ i, den d (a.start i) (a.positive i)) : ℝ) := by
  have hnum i : (num d (a.start i) (a.positive i) : ℝ) ≠ 0 :=
    (Nat.cast_pos.mpr (slot_bounds (a.positive i) (hp i)).1).ne'
  have hden i : (den d (a.start i) (a.positive i) : ℝ) ≠ 0 :=
    (Nat.cast_pos.mpr (slot_bounds (a.positive i) (hp i)).2.1).ne'
  rw [Nat.cast_prod, Nat.cast_prod, Real.log_prod (fun i _ ↦ hnum i),
    Real.log_prod (fun i _ ↦ hden i), ← Finset.sum_sub_distrib, Copy.frequency, signedSum]
  apply Finset.sum_congr rfl
  intro i _
  have hi : (a.start i : ℝ) ≠ 0 := (Nat.cast_pos.mpr (hp i)).ne'
  have hi' : (↑(a.start i + d) : ℝ) ≠ 0 :=
    (Nat.cast_pos.mpr ((hp i).trans_le (Nat.le_add_right _ _))).ne'
  simp only [logRatio, Real.log_div hi' hi]
  cases a.positive i
  · simp [num, den, neg_sub]
  · simp [num, den]

/-- A nonempty, internally distinct copy at a positive prime shift has nonzero
frequency, for any sign pattern. Prime-shift decoding cancels incoming occurrences
from smaller starts, so does not require disjointness of starts and shifted endpoints. -/
public theorem Copy.frequency_logRatio_ne_zero (a : Copy ℕ n) {d : ℕ}
    (hd : 0 < d) (hn : 0 < n) (ha : a.PrimeStarts d) (hinj : Function.Injective a.start) :
    a.frequency (logRatio d) ≠ 0 := by
  let P := (Finset.univ.filter fun i : Fin n ↦ a.positive i = true).val.map a.start
  let Q := (Finset.univ.filter fun i : Fin n ↦ ¬ a.positive i = true).val.map a.start
  have hP z : z ∈ P ↔ ∃ i, a.positive i = true ∧ a.start i = z := by
    simp [P, Multiset.mem_map]
  have hQ z : z ∈ Q ↔ ∃ i, a.positive i ≠ true ∧ a.start i = z := by
    simp only [Q, Multiset.mem_map, ← Finset.mem_def, Finset.mem_filter, Finset.mem_univ, true_and]
  intro hz
  have hp i := (ha i).1.pos
  rw [frequency_eq_logs d a hp, sub_eq_zero] at hz
  have hnum : 0 < ∏ i, num d (a.start i) (a.positive i) :=
    Finset.prod_pos fun i _ ↦ (slot_bounds (a.positive i) (hp i)).1
  have hden : 0 < ∏ i, den d (a.start i) (a.positive i) :=
    Finset.prod_pos fun i _ ↦ (slot_bounds (a.positive i) (hp i)).2.1
  have hprod := Nat.cast_injective (R := ℝ)
    (Real.log_injOn_pos (Nat.cast_pos.mpr hnum) (Nat.cast_pos.mpr hden) hz)
  have heq : P = Q := by
    apply PrimeShiftProductInjective.eq_of_cross_mul_eq hd
    · intro z hz
      obtain ⟨i, _, rfl⟩ := (hP z).mp hz
      exact ha i
    · intro z hz
      obtain ⟨i, _, rfl⟩ := (hQ z).mp hz
      exact ha i
    rw [show (P.map (fun p ↦ p + d)).prod * Q.prod = ∏ i, num d (a.start i) (a.positive i) by
      simp only [num, Finset.prod_ite]
      simp only [Finset.prod_eq_multiset_prod, P, Q, Multiset.map_map, Function.comp_def],
      show (Q.map (fun p ↦ p + d)).prod * P.prod = ∏ i, den d (a.start i) (a.positive i) by
        simp only [den, Finset.prod_ite]
        simp only [Finset.prod_eq_multiset_prod, P, Q, Multiset.map_map, Function.comp_def]
        rw [mul_comm]]
    exact hprod
  let i : Fin n := ⟨0, hn⟩
  by_cases hi : a.positive i = true
  · have hm : a.start i ∈ P := (hP _).mpr ⟨i, hi, rfl⟩
    rw [heq] at hm
    obtain ⟨j, hj, hij⟩ := (hQ _).mp hm
    exact hj (hinj hij ▸ hi)
  · have hm : a.start i ∈ Q := (hQ _).mpr ⟨i, hi, rfl⟩
    rw [← heq] at hm
    obtain ⟨j, hj, hij⟩ := (hP _).mp hm
    exact hi (hinj hij ▸ hj)

private theorem inv_le_log_sub_of_lt {u v : ℕ} (hu : 0 < u) (huv : u < v) :
    (v : ℝ)⁻¹ ≤ Real.log (v : ℝ) - Real.log (u : ℝ) := by
  have huR : (0 : ℝ) < u := Nat.cast_pos.mpr hu
  have hvR : (0 : ℝ) < v := Nat.cast_pos.mpr (hu.trans huv)
  have hstep : (u : ℝ) + 1 ≤ v := by exact_mod_cast Nat.succ_le_of_lt huv
  have hlog := Real.log_le_sub_one_of_pos (div_pos huR hvR)
  rw [Real.log_div huR.ne' hvR.ne'] at hlog
  calc
    (v : ℝ)⁻¹ = 1 / (v : ℝ) := (one_div _).symm
    _ ≤ ((v : ℝ) - u) / v := div_le_div_of_nonneg_right (by linarith only [hstep]) hvR.le
    _ = 1 - (u : ℝ) / v := by rw [sub_div, div_self hvR.ne']
    _ ≤ _ := by linarith only [hlog]

/-- A nonzero small sum of `m` signed log ratios of positive integer endpoints bounded by
`X` needs at least `log(t/(4π))/log X` occurrences. No distinctness (and not even primality)
is needed for this spacing step. -/
public theorem Copy.log_lower_bound_of_small_frequency {t X : ℝ} (ht : 0 < t) (hX : 1 < X)
    (a : Copy ℕ n) (d : ℕ) (hp : ∀ i, 0 < a.start i) (hbound : ∀ i, (↑(a.start i + d) : ℝ) ≤ X)
    (hne : a.frequency (logRatio d) ≠ 0) (hsmall : |a.frequency (logRatio d)| ≤ 4 * Real.pi / t) :
    Real.log (t / (4 * Real.pi)) / Real.log X ≤ (n : ℝ) := by
  let A := ∏ i, num d (a.start i) (a.positive i)
  let B := ∏ i, den d (a.start i) (a.positive i)
  have hA : 0 < A := Finset.prod_pos fun i _ ↦ (slot_bounds (a.positive i) (hp i)).1
  have hB : 0 < B := Finset.prod_pos fun i _ ↦ (slot_bounds (a.positive i) (hp i)).2.1
  have hheight (f : Fin n → ℕ) (hf : ∀ i, f i ≤ a.start i + d) : (↑(∏ i, f i) : ℝ) ≤ X ^ n := by
    rw [Nat.cast_prod]
    calc
      _ ≤ ∏ _i : Fin n, X := Finset.prod_le_prod₀ (fun _ _ ↦ Nat.cast_nonneg _)
        (fun i _ ↦ (Nat.cast_le.mpr (hf i)).trans (hbound i))
      _ = _ := by simp
  have hAX : (A : ℝ) ≤ X ^ n := hheight _ fun i ↦ (slot_bounds (a.positive i) (hp i)).2.2.1
  have hBX : (B : ℝ) ≤ X ^ n := hheight _ fun i ↦ (slot_bounds (a.positive i) (hp i)).2.2.2
  have hlog : a.frequency (logRatio d) = Real.log (A : ℝ) - Real.log (B : ℝ) :=
    frequency_eq_logs d a hp
  have hneAB : A ≠ B := by
    intro h
    exact hne (by rw [hlog, h, sub_self])
  have hspacing : (X ^ n)⁻¹ ≤ |a.frequency (logRatio d)| := by
    rw [hlog]
    rcases lt_or_gt_of_ne hneAB with h | h
    · calc
        _ ≤ (B : ℝ)⁻¹ := inv_anti₀ (Nat.cast_pos.mpr hB) hBX
        _ ≤ Real.log (B : ℝ) - Real.log (A : ℝ) := inv_le_log_sub_of_lt hA h
        _ = -(Real.log (A : ℝ) - Real.log (B : ℝ)) := (neg_sub _ _).symm
        _ ≤ _ := neg_le_abs _
    · exact (inv_anti₀ (Nat.cast_pos.mpr hA) hAX).trans
        ((inv_le_log_sub_of_lt hB h).trans (le_abs_self _))
  have hpX : 0 < X ^ n := pow_pos (zero_lt_one.trans hX) n
  have hπ : 0 < 4 * Real.pi := by positivity
  have hratio := hspacing.trans hsmall
  rw [← one_div] at hratio
  have hcross := (div_le_div_iff₀ hpX ht).mp hratio
  have hpow : t / (4 * Real.pi) ≤ X ^ n :=
    (div_le_iff₀ hπ).mpr (by simpa only [one_mul, mul_one, mul_comm] using hcross)
  have h := (Real.log_le_log_iff (div_pos ht hπ) hpX).mpr hpow
  rw [Real.log_pow] at h
  exact (div_le_iff₀ (Real.log_pos hX)).mpr h

/-- Prime-shift source-mask implication, including the arithmetic order of the third hit.
Only the two target copies need within-copy injectivity; repeated labels across copies
remain separate occurrences in both the mask and the height estimate. -/
public theorem exists_prime_mask_of_opposite {t X : ℝ} (ht : 0 < t) {d : ℕ} (hd : 0 < d)
    (a b a' b' : Copy ℕ n) (e : Equiv.Perm (Fin n ⊕ Fin n))
    (he : ∀ j, Sum.elim a'.start b'.start (e j) = Sum.elim a.start b.start j)
    (ha : a.PrimeStarts d) (hb : b.PrimeStarts d) (ha' : a'.PrimeStarts d) (hb' : b'.PrimeStarts d)
    (hia' : Function.Injective a'.start) (hib' : Function.Injective b'.start)
    (hXa : ∀ i, (↑(a.start i + d) : ℝ) ≤ X) (hXb : ∀ i, (↑(b.start i + d) : ℝ) ≤ X)
    (hopp : poolTerm t (a.frequency (logRatio d)) (b.frequency (logRatio d)) *
      poolTerm t (a'.frequency (logRatio d)) (b'.frequency (logRatio d)) < 0) :
    ∃ (ε : Bool) (M : Mask n), M.IsWitness t (logRatio d) a b a' b' e ε ∧
      Real.log (t / (4 * Real.pi)) / Real.log X ≤ (↑(M.first.card + M.second.card) : ℝ) := by
  have hn : 0 < n := by
    by_contra! h
    have hn0 : n = 0 := by omega
    subst n
    simp only [Copy.frequency, signedSum, Finset.univ_eq_empty, Finset.sum_empty] at hopp
    exact (not_lt_of_ge (mul_self_nonneg _)) hopp
  have hX : 1 < X := by
    let i : Fin n := ⟨0, hn⟩
    have hp : (1 : ℝ) < (a.start i : ℝ) := by exact_mod_cast (ha i).1.one_lt
    exact hp.trans_le ((Nat.cast_le.mpr (Nat.le_add_right _ _)).trans (hXa i))
  obtain ⟨ε, M, hM⟩ := exists_mask_of_opposite ht (logRatio d) a b a' b' e he
    (a'.frequency_logRatio_ne_zero hd hn ha' hia') (b'.frequency_logRatio_ne_zero hd hn hb' hib') hopp
  let u := a.restrict M.g₁ M.first
  let v := b.restrict M.g₂ M.second
  let w : Copy ℕ (M.first.card + M.second.card) :=
    ⟨Fin.append u.start v.start, Fin.append u.positive v.positive⟩
  have hw : w.frequency (logRatio d) = M.minoritySum (logRatio d) a b := by
    have h : w.frequency (logRatio d) = u.frequency (logRatio d) + v.frequency (logRatio d) := by
      simp only [w, Copy.frequency, signedSum, Fin.sum_univ_add, Fin.append_left, Fin.append_right]
    rw [h]
    exact congrArg₂ (· + ·) (frequency_restrict _ _ _ _) (frequency_restrict _ _ _ _)
  refine ⟨ε, M, hM, w.log_lower_bound_of_small_frequency ht hX d ?_ ?_ ?_ ?_⟩
  · intro i
    refine Fin.addCases ?_ ?_ i
    · intro j
      simpa only [w, Fin.append_left, u, Copy.restrict] using (ha (M.first.equivFin.symm j)).1.pos
    · intro j
      simpa only [w, Fin.append_right, v, Copy.restrict] using (hb (M.second.equivFin.symm j)).1.pos
  · intro i
    refine Fin.addCases ?_ ?_ i
    · intro j
      simpa only [w, Fin.append_left, u, Copy.restrict] using hXa (M.first.equivFin.symm j)
    · intro j
      simpa only [w, Fin.append_right, v, Copy.restrict] using hXb (M.second.equivFin.symm j)
  · rw [hw]
    exact abs_pos.mp hM.hits.minority_pos
  · rw [hw]
    exact hM.hits.minority_le

end Masullo.OppositePoolMask
