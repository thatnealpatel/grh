module

public import Lemmas.SignedCubeShell
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Data.Fin.Tuple.Basic

/-!
# The deleted cyclic gap-phase average is the integer cube sum

Source: `dcc11ec5:.godel/bob/signed-gap-cube-screen.md:34–48`.
Owning check session: `01a20d4e-3533-70d0-b28a-ab27fa9217cc`.

We identify the statistic obtained by differencing the actual cyclic gap-pair
phase and then deleting repeated vertices. The ordered draws and gap indices
are unchanged, and the denominator is `(2G+1) G H^(2k)`. On nonzero terms the
integer lift preserves the four prime endpoints and the phase at each corner.
The dense-gap and present-pair masks remain zeros of the original amplitude.
This is an identity, not a slow-variation, measure, or asymptotic estimate.
-/

open scoped BigOperators ComplexConjugate

namespace Masullo.DeletedCubePhaseAverage

open TriangularGapDifferencing TriangularCubeDeletion TriangularCubeCoefficients
open SignedCubeShell (cubeFrequency cubeWeight survivingSum)
open SignedBlockIntervalMoment (phase)

variable {G H k : ℕ}

/-- The angular gap-pair frequency on the integers, using the gap `g.val + 1`. -/
@[expose] public noncomputable def gapPairFrequency (d : ℤ) (g : Fin G) (p : ℤ) : ℝ :=
  Real.log (((p + d : ℤ) : ℝ) / (p : ℝ)) -
    Real.log (((p + ((g.val : ℤ) + 1) + d : ℤ) : ℝ) / ((p + ((g.val : ℤ) + 1) : ℤ) : ℝ))

/-- The original gap-pair amplitude with its phase at the cyclic representative.
The gap is `g.val + 1`, added in the integers, not modulo the start order. -/
@[expose] public noncomputable def gapPhase (d : ℤ) (a : Fin G → ℤ → ℝ) (u : ℝ)
    (g : Fin G) (p : Start G) : ℂ :=
  (a g p.val : ℂ) * phase (u * gapPairFrequency d g p.val)

private theorem phase_ne_zero (t : ℝ) : phase t ≠ 0 := Complex.exp_ne_zero _

private theorem gapPhase_ne_zero (d : ℤ) (a : Fin G → ℤ → ℝ) (u : ℝ)
    (g : Fin G) (p : Start G) : gapPhase d a u g p ≠ 0 ↔ a g p.val ≠ 0 := by
  rw [gapPhase, mul_ne_zero_iff, Complex.ofReal_ne_zero]
  exact and_iff_left (phase_ne_zero _)

private theorem phase_neg (t : ℝ) : phase (-t) = conj (phase t) := by
  rw [phase, phase, ← Complex.exp_conj]
  simp

private theorem phase_sum {ι : Type*} (s : Finset ι) (L : ι → ℝ) :
    phase (∑ j ∈ s, L j) = ∏ j ∈ s, phase (L j) := by
  simp only [phase, Complex.ofReal_sum, Finset.sum_mul, Complex.exp_sum]

private def unshifted (s : Fin k → Bool) : ℕ :=
  (Finset.univ.filter (fun i => s i = false)).card

private theorem unshifted_snoc (s : Fin k → Bool) (b : Bool) :
    unshifted (Fin.snoc s b) = unshifted s + (if b = false then 1 else 0) := by
  simp only [unshifted, Finset.card_filter]
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last]

private theorem subsetShift_snoc (a : Draws H (k + 1)) (s : Fin k → Bool) (b : Bool) :
    subsetShift a (Fin.snoc s b) =
      subsetShift (Fin.init a) s + if b then intShift (a (Fin.last k)) else 0 := by
  simp only [subsetShift, Fin.sum_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last, Fin.init_def]

private abbrev cyclicCorner (a : Draws H k) (p : Start G) (s : Fin k → Bool) : Start G :=
  p + (subsetShift a s : Start G)

private theorem iteratedDifference_eq_prod (A L : Start G → ℝ) (a : Draws H k) (p : Start G) :
    iteratedDifference (intervalDraw (2 * G + 1) H) (fun q => (A q : ℂ) * phase (L q)) k a p =
      ∏ s : Fin k → Bool, (A (cyclicCorner a p s) : ℂ) *
        phase ((-1 : ℝ) ^ unshifted s * L (cyclicCorner a p s)) := by
  classical
  induction k generalizing p with
  | zero => simp [iteratedDifference, cyclicCorner, subsetShift, unshifted]
  | succ k ih =>
    let h : Start G := (intShift (a (Fin.last k)) : Start G)
    have hshift : h = intervalDraw (2 * G + 1) H (a (Fin.last k)).1 -
        intervalDraw (2 * G + 1) H (a (Fin.last k)).2 := by simp [h, intShift, intervalDraw]
    simp only [iteratedDifference, difference, ← hshift, ih, map_prod]
    let e := Fin.snocEquiv (fun _ : Fin (k + 1) => Bool)
    rw [← Fintype.prod_equiv e _ _ (fun _ => rfl), Fintype.prod_prod_type, Fintype.prod_bool]
    congr 1
    · refine Finset.prod_congr rfl fun s _ => ?_
      simp only [e, Fin.snocEquiv, Equiv.coe_fn_mk, unshifted_snoc, cyclicCorner, subsetShift_snoc,
        Bool.true_eq_false, ↓reduceIte, Nat.add_zero, Int.cast_add]
      rw [show p + h + (subsetShift (Fin.init a) s : Start G) =
         p + ((subsetShift (Fin.init a) s : Start G) + (intShift (a (Fin.last k)) : Start G)) by
         dsimp [h]; ac_rfl]
    · refine Finset.prod_congr rfl fun s _ => ?_
      simp only [e, Fin.snocEquiv, Equiv.coe_fn_mk, unshifted_snoc, cyclicCorner, subsetShift_snoc,
        Bool.false_eq_true, ↓reduceIte, add_zero, pow_succ, mul_neg_one, neg_mul, phase_neg,
        map_mul, Complex.conj_ofReal]

private theorem iteratedGapPhase_eq (d : ℤ) (a : Fin G → ℤ → ℝ) (u : ℝ) (g : Fin G)
    (b : Draws H k) (p : Start G) :
    iteratedDifference (intervalDraw (2 * G + 1) H) (gapPhase d a u g) k b p =
      ((∏ s : Fin k → Bool, a g (cyclicCorner b p s).val : ℝ) : ℂ) *
        phase (u * ∑ s : Fin k → Bool, (-1 : ℝ) ^ unshifted s *
          gapPairFrequency d g (cyclicCorner b p s).val) := by
  unfold gapPhase
  rw [iteratedDifference_eq_prod]
  simp only [Complex.ofReal_prod, Finset.mul_sum, phase_sum, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun s _ => ?_
  rw [mul_left_comm ((-1 : ℝ) ^ unshifted s) u]

private theorem cubeFrequency_eq (d : ℤ) (x : Label G H k) :
    cubeFrequency d x = ∑ s : Fin k → Bool, (-1 : ℝ) ^ unshifted s *
      gapPairFrequency d x.2.1 ((x.1.val : ℤ) + subsetShift x.2.2 s) := by
  unfold cubeFrequency
  refine Finset.sum_congr rfl fun s _ => ?_
  simp [unshifted, gapPairFrequency, labelVertex, vertex]

private theorem subsetShift_bound (hH : 0 < H) (a : Draws H k) (s : Fin k → Bool) :
    |subsetShift a s| ≤ (k : ℤ) * ((H : ℤ) - 1) := by
  have h i : |if s i then intShift (a i) else 0| ≤ (H : ℤ) - 1 := by
    have hi := (a i).1.isLt
    have hj := (a i).2.isLt
    cases s i <;> simp only [Bool.false_eq_true, ↓reduceIte, abs_zero, abs_le, intShift] <;> omega
  exact (Finset.abs_sum_le_sum_abs _ _).trans <| by
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using
      Finset.sum_le_sum (s := Finset.univ) (fun i _ => h i)

/-- The converse support check starts from a nonzero *integer* product, so the
cyclic term is not yet known to be nonzero. Its root amplitude is nonzero and
supplies both margins for reducing each integer corner back to the cycle. -/
private theorem corner_val_of_root_band (hH : 0 < H) (b : Draws H k) (p : Start G)
    (hlo : (k : ℤ) * ((H : ℤ) - 1) ≤ (p.val : ℤ))
    (hhi : (p.val : ℤ) + (k : ℤ) * ((H : ℤ) - 1) < ((2 * G + 1 : ℕ) : ℤ))
    (s : Fin k → Bool) :
    ((cyclicCorner b p s).val : ℤ) = (p.val : ℤ) + subsetShift b s := by
  have hs := abs_le.mp (subsetShift_bound hH b s)
  have hc : (((p.val : ℤ) + subsetShift b s : ℤ) : Start G) = cyclicCorner b p s := by
    simp only [Int.cast_add, Int.cast_natCast, ZMod.natCast_zmod_val]
  rw [← hc, ZMod.val_intCast, Int.emod_eq_of_lt (by omega) (by omega)]

private theorem expect_prod {α β : Type*} [Fintype α] [Fintype β] (F : α × β → ℂ) :
    (𝔼 x, F x) = 𝔼 a, 𝔼 b, F (a, b) := by
  rw [← Finset.expect_product', Finset.univ_product_univ]

private theorem expect_labels (F : Label G H k → ℂ) :
    (𝔼 g, 𝔼 b, 𝔼 p, F (p, g, b)) = (∑ x, F x) / (normalizer G H k : ℂ) := by
  let e : Fin G × Draws H k × Start G ≃ Label G H k :=
    ⟨fun x => (x.2.2, x.1, x.2.1), fun x => (x.2.1, x.2.2, x.1), fun _ => rfl, fun _ => rfl⟩
  calc
    _ = 𝔼 x, F (e x) := by simp only [expect_prod, e, Equiv.coe_fn_mk]
    _ = 𝔼 x, F x := Fintype.expect_equiv e _ _ fun _ => rfl
    _ = _ := by
      simp [Finset.expect_eq_sum_div_card, Label, Start, Draws, ZMod.card, normalizer,
        mul_pow, pow_add, two_mul, mul_assoc]

/-- With the source's no-wrap margins and four prime endpoints on the
nonzero gap-pair amplitudes, deleting repeated vertices after cyclic
differencing gives exactly the normalized signed sum on integer prime cubes.
The hypotheses are on the integer amplitude at representatives of the start
cycle. Values outside that range cannot affect either sum: a nonzero root
amplitude forces every contributing integer corner into the range. The identity
holds without an amplitude bound or a sign restriction on `a`. -/
public theorem survivingAverage_eq_survivingSum (hH : 0 < H) (d : ℤ) (hd : 0 ≤ d)
    (a : Fin G → ℤ → ℝ)
    (hband : ∀ (g : Fin G) (p : ℤ), 0 ≤ p → p < ((2 * G + 1 : ℕ) : ℤ) → a g p ≠ 0 →
      (k : ℤ) * ((H : ℤ) - 1) ≤ p ∧
      p + (k : ℤ) * ((H : ℤ) - 1) < ((2 * G + 1 : ℕ) : ℤ) ∧
      p + (g.val : ℤ) + 1 + d < ((2 * G + 1 : ℕ) : ℤ))
    (hprime : ∀ (g : Fin G) (p : ℤ), 0 ≤ p → p < ((2 * G + 1 : ℕ) : ℤ) → a g p ≠ 0 →
      ∀ e b : Bool, (p + (if e then (g.val : ℤ) + 1 else 0) + (if b then d else 0)).toNat.Prime)
    (u : ℝ) :
    survivingAverage (H := H) d (gapPhase d a u) k =
      survivingSum d (cubeWeight (H := H) (k := k) a) u := by
  classical
  have hrep (q : Start G) : (q.val : ℤ) < ((2 * G + 1 : ℕ) : ℤ) := by
    exact_mod_cast ZMod.val_lt q
  let F (x : Label G H k) : ℂ :=
    if Function.Injective (labelVertex d x) then
      iteratedDifference (intervalDraw (2 * G + 1) H) (gapPhase d a u x.2.1) k x.2.2 x.1
    else 0
  change (𝔼 g, 𝔼 b, 𝔼 p, F (p, g, b)) = _
  rw [expect_labels F, survivingSum, survivors, Finset.sum_filter]
  congr 1
  refine Finset.sum_congr rfl fun x _ => ?_
  obtain ⟨p, g, b⟩ := x
  let x : Label G H k := (p, g, b)
  let T := iteratedDifference (intervalDraw (2 * G + 1) H) (gapPhase d a u g) k b p
  change (if Function.Injective (labelVertex d x) then T else 0) =
    if Survives d x then (cubeWeight a x : ℂ) * phase (u * cubeFrequency d x) else 0
  by_cases hn : T ≠ 0
  · have hvertex (v : VertexLabel k) := vertex_on_support hn hd
      (fun q hq => hband g q.val (Int.natCast_nonneg _) (hrep q)
        ((gapPhase_ne_zero d a u g q).mp hq)) v
    have hpr (v : VertexLabel k) : (labelVertex d x v).toNat.Prime := by
      let q := cyclicCorner b p v.1
      have hv : labelVertex d x v = (q.val : ℤ) +
          (if v.2.1 then (g.val : ℤ) + 1 else 0) + (if v.2.2 then d else 0) := (hvertex v).2.1
      rw [hv]
      exact hprime g q.val (Int.natCast_nonneg _) (hrep q)
        ((gapPhase_ne_zero d a u g q).mp (hvertex v).1) v.2.1 v.2.2
    have hval (s : Fin k → Bool) :
        ((cyclicCorner b p s).val : ℤ) = (p.val : ℤ) + subsetShift b s := by
      simpa [vertex] using (hvertex (s, false, false)).2.1.symm
    have hsurv : Survives d x ↔ Function.Injective (labelVertex d x) :=
      ⟨And.left, fun hi => ⟨hi, hpr⟩⟩
    rw [hsurv]
    split
    · simp only [T, x, iteratedGapPhase_eq, cubeWeight, cubeFrequency_eq, hval]
    · rfl
  · have hzero : cubeWeight a x = 0 := by
      by_contra hw
      have ha (s : Fin k → Bool) : a g ((p.val : ℤ) + subsetShift b s) ≠ 0 :=
        Finset.prod_ne_zero_iff.mp hw s (Finset.mem_univ _)
      have hroot : a g p.val ≠ 0 := by simpa [subsetShift] using ha (fun _ => false)
      have hb := hband g p.val (Int.natCast_nonneg _) (hrep p) hroot
      have hval := corner_val_of_root_band hH b p hb.1 hb.2.1
      apply hn
      dsimp only [T]
      rw [iteratedGapPhase_eq]
      refine mul_ne_zero (Complex.ofReal_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr ?_))
        (phase_ne_zero _)
      intro s _
      rw [hval]
      exact ha s
    simp [not_ne_iff.mp hn, hzero]

end Masullo.DeletedCubePhaseAverage
