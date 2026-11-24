module

public import Lemmas.TriangularCubeCoefficients
public import Lemmas.PrimeCubeShellTail
public import Lemmas.SignedBlockIntervalMoment
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Continuous shell estimate for the signed gap cube

Paper: `dcc11ec5:.godel/bob/signed-gap-cube-screen.md:34–66`, the explicit
finite part of (2). Owning check session: `01a20d17-2b2a-7097-a6d0-937638b43d97`.

The starts are cyclic, the gap index is shifted by one, and the cube uses
both ordered draws at each coordinate. Vertices are evaluated on the integer
lift (the no-wrap regime of the source). We delete repeated vertices and sum
with the original denominator `(2G+1) G H^(2k)`, not the number of survivors.
The normalized real corner amplitudes retain the zeros of the gap and prime
band masks. We prove the continuous-shell estimate at any positive threshold
under the strict frequency cutoff. At `m = k`, `η = δ/4` this gives the finite
bound used in (2); no asymptotic or cell-count estimate is included.
-/

open MeasureTheory
open scoped BigOperators ComplexConjugate

namespace Masullo.SignedCubeShell

open TriangularCubeDeletion
open TriangularCubeCoefficients
open PrimeCubeShellMoment (primeFlow)
open ProductLaurentMoment (monomial phaseFactor supportSize)
open SignedBlockIntervalMoment (phase)

variable {G H k : ℕ}

/-- The angular frequency on the integer lift: shifted factors are taken with
positive sign and unshifted factors are conjugated at each difference. Within
one corner the gap-pair phase uses `log ((p+d)/p) - log ((p+g+d)/(p+g))`. -/
@[expose] public noncomputable def cubeFrequency (d : ℤ) (x : Label G H k) : ℝ :=
  ∑ s : Fin k → Bool, (((-1 : ℤ) ^ (Finset.univ.filter (fun i => s i = false)).card : ℤ) : ℝ) *
    (Real.log ((labelVertex d x (s, false, true) : ℝ) /
        (labelVertex d x (s, false, false) : ℝ)) -
      Real.log ((labelVertex d x (s, true, true) : ℝ) /
        (labelVertex d x (s, true, false) : ℝ)))

/-- The original ordered-draw sum on collision-free prime labels. The weights
are the real amplitudes before uniform averaging, including any masked zeros. -/
@[expose] public noncomputable def survivingSum (d : ℤ) (w : Label G H k → ℝ) (u : ℝ) : ℂ :=
  (∑ x ∈ survivors d, (w x : ℂ) * phase (u * cubeFrequency d x)) /
    (normalizer G H k : ℂ)

private theorem vertexNat_cast {d : ℤ} {x : Label G H k} (hx : Survives d x)
    (v : VertexLabel k) : ((labelVertex d x v).toNat : ℤ) = labelVertex d x v := by
  apply Int.toNat_of_nonneg
  by_contra! h
  exact (hx.2 v).ne_zero (Int.toNat_of_nonpos h.le)

private theorem vertexReal_cast {d : ℤ} {x : Label G H k} (hx : Survives d x)
    (v : VertexLabel k) : ((labelVertex d x v).toNat : ℝ) = (labelVertex d x v : ℝ) := by
  exact_mod_cast vertexNat_cast hx v

private theorem vertexReal_ne_zero {d : ℤ} {x : Label G H k} (hx : Survives d x)
    (v : VertexLabel k) : (labelVertex d x v : ℝ) ≠ 0 := by
  rw [← vertexReal_cast hx v]
  exact_mod_cast (hx.2 v).ne_zero

private theorem cornerSign_cases (v : VertexLabel k) : cornerSign v = 1 ∨ cornerSign v = -1 := by
  unfold cornerSign
  generalize (Finset.univ.filter (fun i => v.1 i = false)).card +
    (if v.2.1 then 1 else 0) + (if v.2.2 then 0 else 1) = n
  induction n with
  | zero => simp
  | succ n ih => rcases ih with h | h <;> simp [pow_succ, h]

private theorem cubeFrequency_eq {d : ℤ} {x : Label G H k} (hx : Survives d x) :
    cubeFrequency d x = ∑ v : VertexLabel k, (cornerSign v : ℝ) *
      Real.log (labelVertex d x v : ℝ) := by
  unfold cubeFrequency
  simp only [VertexLabel, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro s _
  simp only [Fintype.sum_bool, Real.log_div (vertexReal_ne_zero hx _)
    (vertexReal_ne_zero hx _), cornerSign, Bool.false_eq_true, ↓reduceIte,
    Nat.add_zero, pow_succ, Int.cast_mul, Int.cast_neg, Int.cast_one]
  ring

private noncomputable def alphabet (X : ℝ) : Finset ℕ :=
  (Finset.range (⌊X⌋₊ + 1)).filter Nat.Prime

private theorem mem_alphabet {X : ℝ} (hX : 0 ≤ X) (q : ℕ) :
    q ∈ alphabet X ↔ q.Prime ∧ (q : ℝ) ≤ X := by
  rw [alphabet, Finset.mem_filter, Finset.mem_range, Nat.lt_succ_iff, Nat.le_floor_iff hX, and_comm]

private def digit (a : ℤ) : Fin 3 := if a = 1 then 1 else if a = -1 then 2 else 0

private def undigit (a : Fin 3) : ℤ := if a = 1 then 1 else if a = 2 then -1 else 0

private theorem undigit_digit {a : ℤ} (h : a = 0 ∨ a = 1 ∨ a = -1) : undigit (digit a) = a := by
  rcases h with rfl | rfl | rfl <;> decide

private def encode (X : ℝ) (v : ℕ →₀ ℤ) (q : alphabet X) : Fin 3 := digit (v q.val)

private def vertexCoord {d : ℤ} {x : Label G H k} {X : ℝ} (hX : 0 ≤ X)
    (hx : Survives d x) (hbound : ∀ v, (labelVertex d x v : ℝ) ≤ X) :
    VertexLabel k ↪ alphabet X where
  toFun v := ⟨(labelVertex d x v).toNat, (mem_alphabet hX _).mpr
    ⟨hx.2 v, (vertexReal_cast hx v).symm ▸ hbound v⟩⟩
  inj' := by
    intro v w hvw
    apply hx.1
    have h := congrArg (fun q : alphabet X => (q.val : ℤ)) hvw
    simpa only [vertexNat_cast hx] using h

private theorem encode_vertex {d : ℤ} {x : Label G H k} {X : ℝ} (hX : 0 ≤ X)
    (hx : Survives d x) (hbound : ∀ v, (labelVertex d x v : ℝ) ≤ X) (v : VertexLabel k) :
    encode X (valuationKey d x) (vertexCoord hX hx hbound v) = digit (cornerSign v) := by
  change digit (valuationKey d x (labelVertex d x v).toNat) = _
  rw [valuationKey_apply_vertex hx]

private theorem filter_encode_eq_map {d : ℤ} {x : Label G H k} {X : ℝ} (hX : 0 ≤ X)
    (hx : Survives d x) (hbound : ∀ v, (labelVertex d x v : ℝ) ≤ X)
    (P : Fin 3 → Prop) [DecidablePred P] (hP : ¬ P 0) :
    (Finset.univ.filter fun q => P (encode X (valuationKey d x) q)) =
      (Finset.univ.filter fun v => P (digit (cornerSign v))).map (vertexCoord hX hx hbound) := by
  classical
  ext q
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map]
  constructor
  · intro hq
    have hs : q.val ∈ (valuationKey d x).support := by
      rw [Finsupp.mem_support_iff]
      intro hz
      exact hP (by simpa only [encode, hz, show digit 0 = 0 by decide] using hq)
    rw [valuationKey_support hx, Finset.mem_image] at hs
    obtain ⟨v, _, hv⟩ := hs
    have he : vertexCoord hX hx hbound v = q := Subtype.ext hv
    refine ⟨v, ?_, he⟩
    rw [← he, encode_vertex] at hq
    exact hq
  · rintro ⟨v, hv, rfl⟩
    rwa [encode_vertex]

private theorem supportSize_valuation {d : ℤ} {x : Label G H k} {X : ℝ} (hX : 0 ≤ X)
    (hx : Survives d x) (hbound : ∀ v, (labelVertex d x v : ℝ) ≤ X) :
    supportSize (encode X (valuationKey d x)) = 4 * 2 ^ k := by
  classical
  have hv : (Finset.univ.filter fun v : VertexLabel k => digit (cornerSign v) ≠ 0) =
      Finset.univ := by
    apply Finset.filter_true_of_mem
    intro v _
    rcases cornerSign_cases v with h | h <;> rw [h] <;> decide
  rw [supportSize, filter_encode_eq_map hX hx hbound (· ≠ 0) (by simp), hv, Finset.card_map]
  simp [VertexLabel, mul_comm]

private def flip (v : VertexLabel k) : VertexLabel k := (v.1, v.2.1, !v.2.2)

private theorem flip_flip (v : VertexLabel k) : flip (flip v) = v := by
  obtain ⟨s, e, b⟩ := v
  cases b <;> rfl

private theorem cornerSign_flip (v : VertexLabel k) : cornerSign (flip v) = -cornerSign v := by
  obtain ⟨s, e, b⟩ := v
  cases b <;> simp [flip, cornerSign, pow_succ]

private theorem digit_flip (v : VertexLabel k) :
    digit (cornerSign (flip v)) = 2 ↔ digit (cornerSign v) = 1 := by
  rw [cornerSign_flip]
  rcases cornerSign_cases v with h | h <;> rw [h] <;> decide

private theorem balance_valuation {d : ℤ} {x : Label G H k} {X : ℝ} (hX : 0 ≤ X)
    (hx : Survives d x) (hbound : ∀ v, (labelVertex d x v : ℝ) ≤ X) :
    (Finset.univ.filter fun q => encode X (valuationKey d x) q = 1).card =
      (Finset.univ.filter fun q => encode X (valuationKey d x) q = 2).card := by
  classical
  rw [filter_encode_eq_map hX hx hbound (· = 1) (by decide),
    filter_encode_eq_map hX hx hbound (· = 2) (by decide), Finset.card_map, Finset.card_map]
  apply Finset.card_bij (fun v _ => flip v)
  · intro v hv
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and, digit_flip] using hv
  · intro v _ w _ h
    simpa only [flip_flip] using congrArg flip h
  · intro v hv
    refine ⟨flip v, ?_, flip_flip v⟩
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and, ← digit_flip (flip v), flip_flip]
      using hv

private theorem phase_neg (a : ℝ) : phase (-a) = conj (phase a) := by
  rw [phase, phase, ← Complex.exp_conj]
  simp

private theorem phase_sum {α : Type*} (s : Finset α) (f : α → ℝ) :
    phase (∑ i ∈ s, f i) = ∏ i ∈ s, phase (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [phase]
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.prod_insert hi, ← ih]
    simp only [phase, Complex.ofReal_add, add_mul, Complex.exp_add]

private theorem monomial_valuation {d : ℤ} {x : Label G H k} {X : ℝ} (hX : 0 ≤ X)
    (hx : Survives d x) (hbound : ∀ v, (labelVertex d x v : ℝ) ≤ X) (u : ℝ) :
    monomial (encode X (valuationKey d x)) (primeFlow Subtype.val u) =
      phase (u * cubeFrequency d x) := by
  classical
  let P (q : alphabet X) := encode X (valuationKey d x) q ≠ 0
  have hs : Finset.univ.filter P = Finset.univ.map (vertexCoord hX hx hbound) := by
    rw [filter_encode_eq_map hX hx hbound (· ≠ 0) (by simp)]
    congr 1
    apply Finset.filter_true_of_mem
    intro v _
    rcases cornerSign_cases v with h | h <;> rw [h] <;> decide
  unfold monomial
  rw [← Finset.prod_subset (Finset.filter_subset P Finset.univ), hs, Finset.prod_map,
    cubeFrequency_eq hx, Finset.mul_sum, phase_sum]
  · apply Finset.prod_congr rfl
    intro v _
    rw [encode_vertex]
    have hz : (primeFlow Subtype.val u (vertexCoord hX hx hbound v) : ℂ) =
        phase (u * Real.log (labelVertex d x v : ℝ)) := by
      change phase (u * Real.log ((labelVertex d x v).toNat : ℝ)) = _
      rw [vertexReal_cast hx]
    rcases cornerSign_cases v with h | h
    · have hd : digit 1 = 1 := by decide
      rw [h, hd]
      simpa [phaseFactor] using hz
    · have hd : digit (-1) = 2 := by decide
      rw [h, hd]
      simpa [phaseFactor, ← phase_neg] using congrArg (starRingEnd ℂ) hz
  · intro q _ hq
    have hz : encode X (valuationKey d x) q = 0 := by simpa [P] using hq
    simp [phaseFactor, hz]

private theorem mem_survivors {d : ℤ} {x : Label G H k} : x ∈ survivors d ↔ Survives d x := by
  classical
  simp [survivors]

private noncomputable def boundedKeys (G H k : ℕ) (d : ℤ) (X : ℝ) : Finset (ℕ →₀ ℤ) := by
  classical
  exact (keys G H k d).filter fun v => ∀ q ∈ v.support, (q : ℝ) ≤ X

private theorem boundedKey_witness {d : ℤ} {X : ℝ} {v : ℕ →₀ ℤ}
    (hv : v ∈ boundedKeys G H k d X) :
    ∃ x : Label G H k, Survives d x ∧ (∀ i, (labelVertex d x i : ℝ) ≤ X) ∧
      valuationKey d x = v := by
  classical
  obtain ⟨hkey, hbound⟩ := Finset.mem_filter.mp hv
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hkey
  have hs := mem_survivors.mp hx
  refine ⟨x, hs, fun i => ?_, rfl⟩
  rw [← vertexReal_cast hs i]
  apply hbound
  rw [valuationKey_support hs]
  exact Finset.mem_image_of_mem _ (Finset.mem_univ i)

private theorem apply_key_cases {d : ℤ} {x : Label G H k} (hx : Survives d x) (q : ℕ) :
    valuationKey d x q = 0 ∨ valuationKey d x q = 1 ∨ valuationKey d x q = -1 := by
  classical
  by_cases hq : q ∈ (valuationKey d x).support
  · rw [valuationKey_support hx, Finset.mem_image] at hq
    obtain ⟨v, _, rfl⟩ := hq
    exact Or.inr (valuationKey_apply_vertex hx v ▸ cornerSign_cases v)
  · exact Or.inl (Finsupp.notMem_support_iff.mp hq)

/-- The actual coalesced keys inject into the ternary key space. Outside the
alphabet a bounded key is zero, so no additional coalescing occurs here. -/
private def keyEmbedding {d : ℤ} {X : ℝ} (hX : 0 ≤ X) :
    boundedKeys G H k d X ↪ (alphabet X → Fin 3) where
  toFun v := encode X v.val
  inj' := by
    classical
    intro v v' he
    apply Subtype.ext
    ext q
    obtain ⟨x, hx, _, hv⟩ := boundedKey_witness v.property
    obtain ⟨x', hx', _, hv'⟩ := boundedKey_witness v'.property
    by_cases hq : q ∈ alphabet X
    · have h := congrArg undigit (congrFun he ⟨q, hq⟩)
      change undigit (digit (v.val q)) = undigit (digit (v'.val q)) at h
      rwa [undigit_digit (hv ▸ apply_key_cases hx q), undigit_digit (hv' ▸ apply_key_cases hx' q)] at h
    · have hz (y : boundedKeys G H k d X) : y.val q = 0 := by
        obtain ⟨z, hz, _, hzy⟩ := boundedKey_witness y.property
        by_contra h
        have hqs : q ∈ y.val.support := Finsupp.mem_support_iff.mpr h
        apply hq
        apply (mem_alphabet hX q).mpr
        refine ⟨?_, (Finset.mem_filter.mp y.property).2 q hqs⟩
        rw [← hzy, valuationKey_support hz, Finset.mem_image] at hqs
        obtain ⟨i, _, rfl⟩ := hqs
        exact hz.2 i
      rw [hz v, hz v']

private theorem sum_boundedKeys_eq {d : ℤ} {X : ℝ} (w : Label G H k → ℝ)
    (hwX : ∀ x, Survives d x → w x ≠ 0 → ∀ i, (labelVertex d x i : ℝ) ≤ X) (u : ℝ)
    (hX : 0 ≤ X) :
    (∑ v ∈ boundedKeys G H k d X, (coefficient d w v : ℂ) *
      monomial (encode X v) (primeFlow Subtype.val u)) = survivingSum d w u := by
  classical
  let K := boundedKeys G H k d X
  let T := (survivors (G := G) (H := H) (k := k) d).filter fun x => valuationKey d x ∈ K
  let F (x : Label G H k) := (w x : ℂ) * phase (u * cubeFrequency d x)
  have hmaps : ∀ x ∈ T, valuationKey d x ∈ K := fun x hx => (Finset.mem_filter.mp hx).2
  have hfiber (v : ℕ →₀ ℤ) (hv : v ∈ K) :
      keyFiber (G := G) (H := H) (k := k) d v = T.filter (fun x => valuationKey d x = v) := by
    ext x
    simp only [keyFiber, T, Finset.mem_filter]
    exact ⟨fun ⟨hx, he⟩ => ⟨⟨hx, he.symm ▸ hv⟩, he⟩, fun ⟨⟨hx, _⟩, he⟩ => ⟨hx, he⟩⟩
  have hsum : ∑ x ∈ T, F x = ∑ x ∈ survivors d, F x := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro x hx hnot
    have hs := mem_survivors.mp hx
    have hz : w x = 0 := by
      by_contra hn
      apply hnot
      apply Finset.mem_filter.mpr
      refine ⟨hx, Finset.mem_filter.mpr ⟨Finset.mem_image_of_mem _ hx, ?_⟩⟩
      intro q hq
      rw [valuationKey_support hs, Finset.mem_image] at hq
      obtain ⟨i, _, rfl⟩ := hq
      rw [vertexReal_cast hs i]
      exact hwX x hs hn i
    simp [F, hz]
  calc
    _ = (∑ v ∈ K, ∑ x ∈ T.filter (fun x => valuationKey d x = v), F x) /
        (normalizer G H k : ℂ) := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro v hv
      rw [coefficient, hfiber v hv, Complex.ofReal_div, div_mul_eq_mul_div]
      push_cast
      rw [Finset.sum_mul]
      congr 1
      apply Finset.sum_congr rfl
      intro x hx
      obtain ⟨hxt, hkey⟩ := Finset.mem_filter.mp hx
      have hs := mem_survivors.mp (Finset.mem_filter.mp hxt).1
      have hb : ∀ i, (labelVertex d x i : ℝ) ≤ X := by
        intro i
        rw [← vertexReal_cast hs i]
        apply (Finset.mem_filter.mp hv).2
        rw [← hkey, valuationKey_support hs]
        exact Finset.mem_image_of_mem _ (Finset.mem_univ i)
      rw [← hkey, monomial_valuation hX hs hb]
    _ = survivingSum d w u := by
      rw [Finset.sum_fiberwise_of_maps_to hmaps F, hsum, survivingSum]

/-- The finite continuous-shell bound for the collision-free signed gap cube.
Only prime vertices of *nonzero* surviving terms must be at most `X`; the
masked zeros need not lie in the prime band. The threshold is inclusive. -/
public theorem volume_survivingSum_le (d : ℤ) (w : Label G H k → ℝ)
    {X t η : ℝ} {m : ℕ} (hG : 0 < G) (hH : 0 < H) (hX : 1 ≤ X)
    (hm : 1 ≤ m) (ht : X ^ (m * (4 * 2 ^ k)) < t) (hη : 0 < η)
    (hw : ∀ x, 0 ≤ w x ∧ w x ≤ 1)
    (hwX : ∀ x, Survives d x → w x ≠ 0 → ∀ i, (labelVertex d x i : ℝ) ≤ X) :
    volume {u : ℝ | u ∈ Set.Icc t (5 * t / 4) ∧ η ≤ ‖survivingSum d w u‖} ≤
      ENNReal.ofReal (8 * Real.pi * t * (((4 * (m : ℝ) - 2) ^ (4 * 2 ^ k) *
        (4 * 2 ^ k : ℝ) ^ (k + 2)) / (((2 * G + 1 : ℕ) : ℝ) * G * (H : ℝ) ^ k * η ^ 2)) ^ m) := by
  classical
  let X₀ := zero_le_one.trans hX
  let K := boundedKeys G H k d X
  let e : K ↪ (alphabet X → Fin 3) := keyEmbedding X₀
  let S := Finset.univ.map e
  let c : (alphabet X → Fin 3) → ℂ := Function.extend e (fun v : K => (coefficient d w v.val : ℂ)) 0
  have hc (v : K) : c (e v) = (coefficient d w v.val : ℂ) := e.injective.extend_apply _ _ v
  have hp (q : alphabet X) := (mem_alphabet X₀ q.val).mp q.property
  have hsize (v : alphabet X → Fin 3) (hv : v ∈ S) : supportSize v = 4 * 2 ^ k := by
    obtain ⟨y, _, rfl⟩ := Finset.mem_map.mp hv
    obtain ⟨x, hx, hb, he⟩ := boundedKey_witness y.property
    change supportSize (encode X y.val) = _
    rw [← he]
    exact supportSize_valuation X₀ hx hb
  have hbalance (v : alphabet X → Fin 3) (hv : v ∈ S) :
      (Finset.univ.filter fun i => v i = 1).card = (Finset.univ.filter fun i => v i = 2).card := by
    obtain ⟨y, _, rfl⟩ := Finset.mem_map.mp hv
    obtain ⟨x, hx, hb, he⟩ := boundedKey_witness y.property
    change (Finset.univ.filter fun i => encode X y.val i = 1).card =
      (Finset.univ.filter fun i => encode X y.val i = 2).card
    rw [← he]
    exact balance_valuation X₀ hx hb
  have hphase (u : ℝ) : (∑ v ∈ S, c v * monomial v (primeFlow Subtype.val u)) =
      survivingSum d w u := by
    rw [Finset.sum_map]
    simp only [hc]
    change (∑ v ∈ K.attach, (coefficient d w v.val : ℂ) *
      monomial (encode X v.val) (primeFlow Subtype.val u)) = _
    rw [Finset.sum_attach K (fun v => (coefficient d w v : ℂ) *
      monomial (encode X v) (primeFlow Subtype.val u))]
    exact sum_boundedKeys_eq w hwX u X₀
  have hbudget : (∑ v ∈ S, ‖c v‖ ^ 2) ≤
      (4 * 2 ^ k : ℝ) ^ (k + 2) / (((2 * G + 1 : ℕ) : ℝ) * G * (H : ℝ) ^ k) := by
    rw [Finset.sum_map]
    simp only [hc, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    change (∑ v ∈ K.attach, coefficient d w v.val ^ 2) ≤ _
    rw [Finset.sum_attach K (fun v => coefficient d w v ^ 2)]
    exact (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun _ _ _ => sq_nonneg _)).trans (sum_coefficient_sq_le hG hH d w hw)
  have hshell := PrimeCubeShellTail.volume_shell_superlevel_le
    (fun q => (hp q).1) Subtype.val_injective (fun q => (hp q).2) hX hm ht hη S c hsize hbalance
  simp only [hphase] at hshell
  refine hshell.trans (ENNReal.ofReal_le_ofReal ?_)
  have ht₀ : 0 < t := (pow_pos (zero_lt_one.trans_le hX) _).trans ht
  have hm₁ : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hcharge : 0 ≤ 4 * (m : ℝ) - 2 := by linarith
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply pow_le_pow_left₀ (by positivity)
  simpa only [← mul_div_assoc, div_div] using
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hbudget (pow_nonneg hcharge (4 * 2 ^ k)))
      (sq_nonneg η)

/-- The cube amplitude is the product of the normalized gap-pair amplitudes
at all integer-lift corners. The input `a` includes the dense-gap and
present-pair masks and the factor `(8D²/X)⁻²` from the source. -/
@[expose] public noncomputable def cubeWeight (a : Fin G → ℤ → ℝ) (x : Label G H k) : ℝ :=
  ∏ s : Fin k → Bool, a x.2.1 ((x.1.val : ℤ) + subsetShift x.2.2 s)

/-- The finite shell estimate for the product weights of the signed gap cube.
For a nonzero gap-pair amplitude, its upper prime endpoint `p+g+d` is at most
`X`. This is the only upper-band input needed for the product weights. -/
public theorem volume_survivingCube_le (d : ℤ) (a : Fin G → ℤ → ℝ)
    {X t η : ℝ} {m : ℕ} (hG : 0 < G) (hH : 0 < H) (hd : 0 ≤ d) (hX : 1 ≤ X)
    (hm : 1 ≤ m) (ht : X ^ (m * (4 * 2 ^ k)) < t) (hη : 0 < η)
    (ha : ∀ g p, 0 ≤ a g p ∧ a g p ≤ 1)
    (haX : ∀ g p, a g p ≠ 0 → ((p + (g.val : ℤ) + 1 + d : ℤ) : ℝ) ≤ X) :
    volume {u : ℝ | u ∈ Set.Icc t (5 * t / 4) ∧
        η ≤ ‖survivingSum d (cubeWeight (H := H) (k := k) a) u‖} ≤
      ENNReal.ofReal (8 * Real.pi * t * (((4 * (m : ℝ) - 2) ^ (4 * 2 ^ k) *
        (4 * 2 ^ k : ℝ) ^ (k + 2)) / (((2 * G + 1 : ℕ) : ℝ) * G * (H : ℝ) ^ k * η ^ 2)) ^ m) := by
  classical
  apply volume_survivingSum_le d (cubeWeight a) hG hH hX hm ht hη
  · intro x
    exact ⟨Finset.prod_nonneg fun _ _ => (ha _ _).1,
      Finset.prod_le_one₀ (fun _ _ => (ha _ _).1) (fun _ _ => (ha _ _).2)⟩
  · intro x _ hx v
    obtain ⟨s, e, b⟩ := v
    have hnz := Finset.prod_ne_zero_iff.mp hx s (Finset.mem_univ s)
    have hb := haX x.2.1 ((x.1.val : ℤ) + subsetShift x.2.2 s) hnz
    refine le_trans ?_ hb
    apply Int.cast_le.mpr
    cases e <;> cases b <;> simp [labelVertex, vertex] <;> omega

end Masullo.SignedCubeShell
