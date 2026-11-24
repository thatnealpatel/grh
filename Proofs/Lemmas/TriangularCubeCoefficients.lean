module

public import Lemmas.TriangularCubeDeletion
public import Mathlib.Data.Nat.Factorization.Defs
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Tactic.Ring

/-!
# Coalesced coefficients of the surviving triangular cube

Source: `dcc11ec5:.godel/bob/signed-gap-cube-screen.md:34–48,52–56`.
Consumers: the mass in line 48 and the square budget inserted in the torus
moment and shell argument at lines 62–64 of the same note.
Owning check session: `01a20bcd-0340-73f5-9604-3b5724a0ee86`.

This is the finite coefficient estimate on the integer lift of the deletion
module. The cyclic starts, full gap interval and ordered interval draws are
unchanged. Only distinct prime vertices contribute; zero weights are allowed
also on these labels. The weights are real amplitudes in `[0,1]`, with the
original denominator `(2G+1) G H^(2k)`, not the number of survivors or keys.
The signs use the ratio `(p+d)/p`, the gap subtraction and the convention that
the unshifted factor is conjugated at each difference. No phase expansion,
torus moment inequality or analytic shell screen is asserted here.
-/

open scoped BigOperators

namespace Masullo.TriangularCubeCoefficients

open TriangularCubeDeletion

/-- Cyclic start, gap index (value plus one), and ordered interval draws. -/
public abbrev Label (G H k : ℕ) := Start G × Fin G × Draws H k

/-- The integer-lift vertex from the deletion module, with the inputs bundled. -/
@[expose] public def labelVertex {G H k : ℕ} (d : ℤ) (x : Label G H k)
    (v : VertexLabel k) : ℤ := vertex d x.2.1 x.2.2 x.1 v

/-- Repeated vertices are deleted, and every retained integer vertex is prime.
The latter condition also rules out negative vertices, since their `toNat` is zero. -/
@[expose] public def Survives {G H k : ℕ} (d : ℤ) (x : Label G H k) : Prop :=
  Function.Injective (labelVertex d x) ∧ ∀ v, (labelVertex d x v).toNat.Prime

/-- The parity counts the conjugated cube slots, the subtracted gap and the
base of the ratio `(p+d)/p`. -/
@[expose] public def cornerSign {k : ℕ} (v : VertexLabel k) : ℤ :=
  (-1) ^ ((Finset.univ.filter (fun i => v.1 i = false)).card +
    (if v.2.1 then 1 else 0) + (if v.2.2 then 0 else 1))

/-- The signed sum of the vertex prime factorizations. The key coordinates are
integers, so the two directions of a rational prime valuation stay distinct. -/
@[expose] public noncomputable def valuationKey {G H k : ℕ} (d : ℤ) (x : Label G H k) :
    ℕ →₀ ℤ :=
  ∑ v, cornerSign v • Finsupp.mapRange Int.ofNat rfl (labelVertex d x v).toNat.factorization

private theorem vertex_nonneg {G H k : ℕ} {d : ℤ} {x : Label G H k}
    (hx : Survives d x) (v : VertexLabel k) : 0 ≤ labelVertex d x v := by
  by_contra! h
  exact (hx.2 v).ne_zero (Int.toNat_of_nonpos h.le)

private theorem vertexNat_injective {G H k : ℕ} {d : ℤ} {x : Label G H k}
    (hx : Survives d x) : Function.Injective (fun v => (labelVertex d x v).toNat) := by
  intro u v huv
  apply hx.1
  have h : ((labelVertex d x u).toNat : ℤ) = ((labelVertex d x v).toNat : ℤ) :=
    congrArg Int.ofNat huv
  rwa [Int.toNat_of_nonneg (vertex_nonneg hx u), Int.toNat_of_nonneg (vertex_nonneg hx v)] at h

private theorem valuationKey_eq_sum_single {G H k : ℕ} {d : ℤ} {x : Label G H k}
    (hx : Survives d x) :
    valuationKey d x = ∑ v, Finsupp.single (labelVertex d x v).toNat (cornerSign v) := by
  classical
  unfold valuationKey
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [(hx.2 v).factorization, Finsupp.mapRange_single]
  simp

/-- At a retained vertex its own sign is the full valuation: all other
vertices contribute zero at this prime. -/
public theorem valuationKey_apply_vertex {G H k : ℕ} {d : ℤ} {x : Label G H k}
    (hx : Survives d x) (v : VertexLabel k) :
    valuationKey d x (labelVertex d x v).toNat = cornerSign v := by
  classical
  rw [valuationKey_eq_sum_single hx, Finsupp.finsetSum_apply, Finset.sum_eq_single v]
  · exact Finsupp.single_eq_same
  · intro u _ huv
    exact Finsupp.single_eq_of_ne (fun h => huv (vertexNat_injective hx h.symm))
  · simp

/-- The key recovers the entire set of distinct prime vertices. -/
public theorem valuationKey_support {G H k : ℕ} {d : ℤ} {x : Label G H k}
    (hx : Survives d x) : (valuationKey d x).support =
      Finset.univ.image (fun v => (labelVertex d x v).toNat) := by
  classical
  ext q
  rw [Finsupp.mem_support_iff, Finset.mem_image]
  constructor
  · intro h
    by_contra! hq
    apply h
    rw [valuationKey_eq_sum_single hx, Finsupp.finsetSum_apply]
    exact Finset.sum_eq_zero fun v hv => Finsupp.single_eq_of_ne (Ne.symm (hq v hv))
  · rintro ⟨v, -, rfl⟩
    rw [valuationKey_apply_vertex hx v]
    exact pow_ne_zero _ (by norm_num)

/-- Every surviving key has exactly `4 * 2^k` nonzero prime coordinates. -/
public theorem valuationKey_support_card {G H k : ℕ} {d : ℤ} {x : Label G H k}
    (hx : Survives d x) : (valuationKey d x).support.card = 4 * 2 ^ k := by
  classical
  rw [valuationKey_support hx, Finset.card_image_of_injective _ (vertexNat_injective hx)]
  simp [VertexLabel, mul_comm]

private theorem draw_eq_of_shift_eq_of_second_eq {H : ℕ} {a b : Fin H × Fin H}
    (h : intShift a = intShift b) (hs : a.2 = b.2) : a = b := by
  refine Prod.ext (Fin.ext ?_) hs
  have hv := congrArg Fin.val hs
  simp only [intShift] at h
  omega

/-- A prescribed vector of signed differences has at most `H^k` ordered draw
tuples. The second draw in each coordinate determines the first. -/
public theorem orderedDrawFiber_card_le {H k : ℕ} (h : Fin k → ℤ) :
    (Finset.univ.filter (fun a : Draws H k => ∀ i, intShift (a i) = h i)).card ≤ H ^ k := by
  classical
  let T := Finset.univ.filter (fun a : Draws H k => ∀ i, intShift (a i) = h i)
  let code (a : T) (i : Fin k) : Fin H := (a.val i).2
  have hinj : Function.Injective code := by
    intro a b hab
    apply Subtype.ext
    funext i
    have ha : ∀ j, intShift (a.val j) = h j := (Finset.mem_filter.mp a.property).2
    have hb : ∀ j, intShift (b.val j) = h j := (Finset.mem_filter.mp b.property).2
    exact draw_eq_of_shift_eq_of_second_eq ((ha i).trans (hb i).symm) (congrFun hab i)
  have hc := Fintype.card_le_of_injective code hinj
  simpa only [Fintype.card_coe, Fintype.card_fun, Fintype.card_fin] using hc

/-- All prime, collision-free labels in the original domain. -/
@[expose] public noncomputable def survivors {G H k : ℕ} (d : ℤ) : Finset (Label G H k) := by
  classical
  exact Finset.univ.filter (Survives d)

/-- The original labels contributing to one signed valuation key. -/
@[expose] public noncomputable def keyFiber {G H k : ℕ} (d : ℤ) (v : ℕ →₀ ℤ) :
    Finset (Label G H k) := by
  classical
  exact (survivors d).filter (fun x => valuationKey d x = v)

/-- The finite key set over which the coefficients are summed. -/
@[expose] public noncomputable def keys (G H k : ℕ) (d : ℤ) : Finset (ℕ →₀ ℤ) := by
  classical
  exact (survivors (G := G) (H := H) (k := k) d).image (valuationKey d)

private theorem mem_keyFiber {G H k : ℕ} {d : ℤ} {v : ℕ →₀ ℤ} {x : Label G H k}
    (hx : x ∈ keyFiber d v) : Survives d x ∧ valuationKey d x = v := by
  classical
  simpa [survivors, keyFiber] using hx

private def startCorner (k : ℕ) : VertexLabel k := (fun _ => false, false, false)
private def gapCorner (k : ℕ) : VertexLabel k := (fun _ => false, true, false)
private def shiftCorner {k : ℕ} (i : Fin k) : VertexLabel k :=
  (fun j => decide (j = i), false, false)

private theorem startCorner_vertex {G H k : ℕ} (d : ℤ) (x : Label G H k) :
    labelVertex d x (startCorner k) = (x.1.val : ℤ) := by
  simp [labelVertex, vertex, subsetShift, startCorner]

private theorem gapCorner_vertex {G H k : ℕ} (d : ℤ) (x : Label G H k) :
    labelVertex d x (gapCorner k) = (x.1.val : ℤ) + ((x.2.1.val : ℤ) + 1) := by
  simp [labelVertex, vertex, subsetShift, gapCorner]

private theorem shiftCorner_vertex {G H k : ℕ} (d : ℤ) (x : Label G H k) (i : Fin k) :
    labelVertex d x (shiftCorner i) = (x.1.val : ℤ) + intShift (x.2.2 i) := by
  simp [labelVertex, vertex, subsetShift, shiftCorner]

private def supportChoice {G H k : ℕ} {d : ℤ} {v : ℕ →₀ ℤ} (x : keyFiber (G := G)
    (H := H) (k := k) d v) (u : VertexLabel k) : v.support :=
  ⟨(labelVertex d x.val u).toNat, by
    obtain ⟨hx, hv⟩ := mem_keyFiber x.property
    have hu : (labelVertex d x.val u).toNat ∈ (valuationKey d x.val).support := by
      rw [valuationKey_support hx]
      exact Finset.mem_image.mpr ⟨u, Finset.mem_univ u, rfl⟩
    rwa [hv] at hu⟩

private theorem vertex_eq_of_choice_eq {G H k : ℕ} {d : ℤ} {v : ℕ →₀ ℤ}
    {x y : keyFiber (G := G) (H := H) (k := k) d v} {u : VertexLabel k}
    (h : supportChoice x u = supportChoice y u) : labelVertex d x.val u = labelVertex d y.val u := by
  have heq := congrArg (fun q : v.support => (q.val : ℤ)) h
  change ((labelVertex d x.val u).toNat : ℤ) = ((labelVertex d y.val u).toNat : ℤ) at heq
  rwa [Int.toNat_of_nonneg (vertex_nonneg (mem_keyFiber x.property).1 u),
    Int.toNat_of_nonneg (vertex_nonneg (mem_keyFiber y.property).1 u)] at heq

/-- A fixed key fiber injects into the ordered support choices for `p`, `p+g`
and all `p+hᵢ`, paired with the second draw in each coordinate. The choices
recover signed differences using integer subtraction, not cyclic subtraction. -/
public theorem keyFiber_card_le {G H k : ℕ} (d : ℤ) (v : ℕ →₀ ℤ) :
    (keyFiber (G := G) (H := H) (k := k) d v).card ≤ (4 * 2 ^ k) ^ (k + 2) * H ^ k := by
  classical
  let T := keyFiber (G := G) (H := H) (k := k) d v
  let code (x : T) : (v.support × v.support × (Fin k → v.support)) × (Fin k → Fin H) :=
    ((supportChoice x (startCorner k), supportChoice x (gapCorner k),
      fun i => supportChoice x (shiftCorner i)), fun i => (x.val.2.2 i).2)
  have hinj : Function.Injective code := by
    intro x y h
    have hp := vertex_eq_of_choice_eq (congrArg (fun z => z.1.1) h)
    have hg := vertex_eq_of_choice_eq (congrArg (fun z => z.1.2.1) h)
    simp only [startCorner_vertex] at hp
    simp only [gapCorner_vertex] at hg
    have hshift (i : Fin k) : intShift (x.val.2.2 i) = intShift (y.val.2.2 i) := by
      have hi := vertex_eq_of_choice_eq (congrArg (fun z => z.1.2.2 i) h)
      simp only [shiftCorner_vertex] at hi
      omega
    apply Subtype.ext
    refine Prod.ext (ZMod.val_injective _ (by exact_mod_cast hp)) (Prod.ext (Fin.ext ?_) ?_)
    · omega
    · funext i
      exact draw_eq_of_shift_eq_of_second_eq (hshift i) (congrArg (fun z => z.2 i) h)
  by_cases hT : T.Nonempty
  · obtain ⟨x, hx⟩ := hT
    have hcard : v.support.card = 4 * 2 ^ k := by
      obtain ⟨hs, hv⟩ := mem_keyFiber hx
      rw [← hv, valuationKey_support_card hs]
    have hc := Fintype.card_le_of_injective code hinj
    simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin, Fintype.card_coe, hcard] at hc
    rw [pow_add, pow_two]
    convert hc using 1
    ring
  · change T.card ≤ _
    rw [Finset.not_nonempty_iff_eq_empty.mp hT, Finset.card_empty]
    exact Nat.zero_le _

/-- The original normalization, including the original number of ordered draws. -/
@[expose] public def normalizer (G H k : ℕ) : ℝ :=
  ((2 * G + 1 : ℕ) : ℝ) * G * (H : ℝ) ^ (2 * k)

/-- The coalesced amplitude for a signed key; there is no renormalization. -/
@[expose] public noncomputable def coefficient {G H k : ℕ} (d : ℤ)
    (w : Label G H k → ℝ) (v : ℕ →₀ ℤ) : ℝ :=
  (∑ x ∈ keyFiber d v, w x) / normalizer G H k

private theorem normalizer_pos {G H k : ℕ} (hG : 0 < G) (hH : 0 < H) :
    0 < normalizer G H k := by
  unfold normalizer
  positivity

private theorem card_labels {G H k : ℕ} :
    (Fintype.card (Label G H k) : ℝ) = normalizer G H k := by
  simp [Label, Start, Draws, ZMod.card, normalizer, mul_pow, pow_add, two_mul, mul_assoc]

/-- Summing the coalesced coefficients gives exactly the original normalized
surviving mass: the key fibers partition the surviving labels. -/
public theorem sum_coefficient_eq {G H k : ℕ} (d : ℤ) (w : Label G H k → ℝ) :
    (∑ v ∈ keys G H k d, coefficient d w v) =
      (∑ x ∈ survivors d, w x) / normalizer G H k := by
  classical
  simp only [coefficient, ← Finset.sum_div, keyFiber, keys]
  congr 1
  exact Finset.sum_fiberwise_of_maps_to (fun x hx => Finset.mem_image_of_mem _ hx) w

/-- Original weights bounded by one give surviving total mass at most one. -/
public theorem sum_coefficient_le_one {G H k : ℕ} (hG : 0 < G) (hH : 0 < H)
    (d : ℤ) (w : Label G H k → ℝ) (hw : ∀ x, w x ≤ 1) :
    (∑ v ∈ keys G H k d, coefficient d w v) ≤ 1 := by
  rw [sum_coefficient_eq, div_le_iff₀ (normalizer_pos hG hH), one_mul, ← card_labels]
  calc
    (∑ x ∈ survivors d, w x) ≤ ∑ _x ∈ survivors d, (1 : ℝ) :=
      Finset.sum_le_sum fun x _ => hw x
    _ ≤ (Fintype.card (Label G H k) : ℝ) := by
      simpa only [Finset.sum_const, nsmul_eq_mul, mul_one, Nat.cast_le] using
        Finset.card_le_univ (survivors (G := G) (H := H) (k := k) d)

/-- Uniform coefficient bound from the actual prime support and ordered draws. -/
public theorem coefficient_le {G H k : ℕ} (hG : 0 < G) (hH : 0 < H)
    (d : ℤ) (w : Label G H k → ℝ) (hw : ∀ x, w x ≤ 1) (v : ℕ →₀ ℤ) :
    coefficient d w v ≤
      (4 * 2 ^ k : ℝ) ^ (k + 2) / (((2 * G + 1 : ℕ) : ℝ) * G * (H : ℝ) ^ k) := by
  have hHk : 0 < (H : ℝ) ^ k := by positivity
  calc
    coefficient d w v ≤ (∑ _x ∈ keyFiber d v, (1 : ℝ)) / normalizer G H k :=
      div_le_div_of_nonneg_right (Finset.sum_le_sum fun x _ => hw x) (normalizer_pos hG hH).le
    _ ≤ ((4 * 2 ^ k : ℝ) ^ (k + 2) * (H : ℝ) ^ k) / normalizer G H k := by
      apply div_le_div_of_nonneg_right _ (normalizer_pos hG hH).le
      simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
      exact_mod_cast keyFiber_card_le (G := G) (H := H) (k := k) d v
    _ = _ := by
      rw [normalizer, show 2 * k = k + k by omega, pow_add (H : ℝ) k k, ← mul_assoc]
      exact mul_div_mul_right _ _ hHk.ne'

/-- Finite square budget on the coalesced signed valuation coefficients.
It uses the uniform fiber-based cap times the original total mass, and does
not assert any estimate for a phase sum or shell integral. -/
public theorem sum_coefficient_sq_le {G H k : ℕ} (hG : 0 < G) (hH : 0 < H)
    (d : ℤ) (w : Label G H k → ℝ) (hw : ∀ x, 0 ≤ w x ∧ w x ≤ 1) :
    (∑ v ∈ keys G H k d, coefficient d w v ^ 2) ≤
      (4 * 2 ^ k : ℝ) ^ (k + 2) / (((2 * G + 1 : ℕ) : ℝ) * G * (H : ℝ) ^ k) := by
  let C := (4 * 2 ^ k : ℝ) ^ (k + 2) / (((2 * G + 1 : ℕ) : ℝ) * G * (H : ℝ) ^ k)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hc (v : ℕ →₀ ℤ) : 0 ≤ coefficient d w v :=
    div_nonneg (Finset.sum_nonneg fun x _ => (hw x).1) (normalizer_pos hG hH).le
  calc
    (∑ v ∈ keys G H k d, coefficient d w v ^ 2) ≤
        ∑ v ∈ keys G H k d, coefficient d w v * C := by
      refine Finset.sum_le_sum fun v _ => ?_
      rw [pow_two]
      exact mul_le_mul_of_nonneg_left (coefficient_le hG hH d w (fun x => (hw x).2) v) (hc v)
    _ = (∑ v ∈ keys G H k d, coefficient d w v) * C := (Finset.sum_mul ..).symm
    _ ≤ 1 * C := mul_le_mul_of_nonneg_right (sum_coefficient_le_one hG hH d w fun x => (hw x).2) hC
    _ = C := one_mul _

end Masullo.TriangularCubeCoefficients
