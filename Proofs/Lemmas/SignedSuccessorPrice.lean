module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Order.ToIntervalMod
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Nat.Prime.Basic

/-!
# Signed successor prices from overlapping triples

Source: `ac8b771857b16d36dcc380c4ca3990f33a4f5e1d:.godel/bob/finite-successor-cap.md`,
lines 14–30 and 51–57. Consumer: `selected-cell-comparison.md` at the same revision,
lines 23–33. Lean base: `b3723e8a43baefe5b5795e39005ed92872c52b99`.

The allocation first bounds the modulus for arbitrary real coefficients in `[-1,1]`,
charging all unallocated mass (including below the clip) at full price. The transfer
then sums local score bounds with the actual half-edge multiplicities and the signed
rank-two term. This is the finite input to intercept calibration; it does not certify
a numerical slab, a cutoff intercept, or a whole-cell enclosure.

Owning check session: `01a20b48-5cad-74c3-865b-b625005166b3`.
-/

open Finset
open scoped BigOperators

namespace Masullo.SignedSuccessorPrice

noncomputable section

/-- The unit complex phase at a real angle. -/
@[expose] public def phase (x : ℝ) : ℂ := Complex.exp ((x : ℂ) * Complex.I)

private theorem norm_phase (x : ℝ) : ‖phase x‖ = 1 := by
  simp [phase, Complex.norm_exp, Complex.mul_re]

/-- Either endpoint is allowed when the angle is congruent to `π/2` modulo `π`. -/
@[expose] public def IsReduction (x a : ℝ) : Prop :=
  |a| ≤ Real.pi / 2 ∧ ∃ m : ℤ, x = a + (m : ℝ) * Real.pi

public theorem exists_reduction (x : ℝ) : ∃ a, IsReduction x a := by
  let a := toIocMod Real.pi_pos (-(Real.pi / 2)) x
  have ha := toIocMod_mem_Ioc Real.pi_pos (-(Real.pi / 2)) x
  refine ⟨a, abs_le.mpr ⟨ha.1.le, ?_⟩, toIocDiv Real.pi_pos (-(Real.pi / 2)) x, ?_⟩
  · change a ≤ _
    exact ha.2.trans_eq (by ring)
  · simpa only [a, zsmul_eq_mul] using
      (toIocMod_add_toIocDiv_zsmul Real.pi_pos (-(Real.pi / 2)) x).symm

private theorem phase_add_pi_mul (x a : ℝ) (m : ℤ)
    (h : x = a + (m : ℝ) * Real.pi) :
    ∃ e : ℝ, (e = 1 ∨ e = -1) ∧ phase x = phase a * (e : ℂ) := by
  have hexp : phase x = phase a * (-1 : ℂ) ^ m := by
    rw [h, phase, phase]
    push_cast
    rw [add_mul, Complex.exp_add, mul_assoc, Complex.exp_int_mul, Complex.exp_pi_mul_I]
  rcases Int.even_or_odd m with he | ho
  · exact ⟨1, Or.inl rfl, by simpa only [he.neg_one_zpow, Complex.ofReal_one] using hexp⟩
  · exact ⟨-1, Or.inr rfl, by simpa only [ho.neg_one_zpow, Complex.ofReal_neg,
      Complex.ofReal_one] using hexp⟩

private theorem phase_add (x y : ℝ) : phase (x + y) = phase x * phase y := by
  simp only [phase, Complex.ofReal_add, add_mul, Complex.exp_add]

private def triple (x y z : ℂ) : ℂ := (3 / 10) * x + (4 / 10) * y + (3 / 10) * z

/-- The exact signed-corner envelope. Simultaneous negation of the three coefficients
allows the middle coefficient to be fixed at `1` at the corners. -/
@[expose] public def U (a b : ℝ) : ℝ :=
  let x := (3 / 10 : ℂ) * phase (-a)
  let y := (4 / 10 : ℂ)
  let z := (3 / 10 : ℂ) * phase b
  max (max ‖x + y + z‖ ‖x + y - z‖) (max ‖-x + y + z‖ ‖-x + y - z‖)

private theorem norm_segment_le (x y : ℂ) (r : ℝ) {K : ℝ} (hr : |r| ≤ 1)
    (h₁ : ‖x + y‖ ≤ K) (h₂ : ‖-x + y‖ ≤ K) : ‖(r : ℂ) * x + y‖ ≤ K := by
  let u := (1 + r) / 2
  let v := (1 - r) / 2
  have hu : 0 ≤ u := by dsimp [u]; linarith [(abs_le.mp hr).1]
  have hv : 0 ≤ v := by dsimp [v]; linarith [(abs_le.mp hr).2]
  have heq : (r : ℂ) * x + y = (u : ℂ) * (x + y) + (v : ℂ) * (-x + y) := by
    dsimp [u, v]
    push_cast
    ring
  rw [heq]
  calc
    _ ≤ ‖(u : ℂ) * (x + y)‖ + ‖(v : ℂ) * (-x + y)‖ := norm_add_le _ _
    _ = u * ‖x + y‖ + v * ‖-x + y‖ := by
      rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
        Real.norm_of_nonneg hu, Real.norm_of_nonneg hv]
    _ ≤ u * K + v * K := add_le_add (mul_le_mul_of_nonneg_left h₁ hu)
      (mul_le_mul_of_nonneg_left h₂ hv)
    _ = K := by dsimp [u, v]; ring

private theorem norm_box_le (x y z : ℂ) {K : ℝ}
    (hcorners : ∀ e f : ℝ, (e = 1 ∨ e = -1) → (f = 1 ∨ f = -1) →
      ‖(e : ℂ) * x + y + (f : ℂ) * z‖ ≤ K)
    (r s t : ℝ) (hr : |r| ≤ 1) (hs : |s| ≤ 1) (ht : |t| ≤ 1) :
    ‖(r : ℂ) * x + (s : ℂ) * y + (t : ℂ) * z‖ ≤ K := by
  have hside (e : ℝ) (he : e = 1 ∨ e = -1) (u : ℝ) (hu : |u| ≤ 1) :
      ‖(e : ℂ) * x + y + (u : ℂ) * z‖ ≤ K := by
    have h₁ : ‖z + ((e : ℂ) * x + y)‖ ≤ K := by
      simpa only [Complex.ofReal_one, one_mul, add_comm z] using hcorners e 1 he (Or.inl rfl)
    have h₂ : ‖-z + ((e : ℂ) * x + y)‖ ≤ K := by
      simpa only [Complex.ofReal_neg, Complex.ofReal_one, neg_one_mul, add_comm (-z)] using
        hcorners e (-1) he (Or.inr rfl)
    simpa only [add_comm ((u : ℂ) * z)] using norm_segment_le z ((e : ℂ) * x + y) u hu h₁ h₂
  have hmid (v u : ℝ) (hv : |v| ≤ 1) (hu : |u| ≤ 1) :
      ‖(v : ℂ) * x + y + (u : ℂ) * z‖ ≤ K := by
    have h₁ := hside 1 (Or.inl rfl) u hu
    have h₂ := hside (-1) (Or.inr rfl) u hu
    simp only [Complex.ofReal_neg, Complex.ofReal_one, one_mul, neg_one_mul, add_assoc] at h₁ h₂
    simpa only [add_assoc] using norm_segment_le x (y + (u : ℂ) * z) v hv h₁ h₂
  have h₁ : ‖y + ((r : ℂ) * x + (t : ℂ) * z)‖ ≤ K := by
    convert hmid r t hr ht using 2; ring
  have h₂ : ‖-y + ((r : ℂ) * x + (t : ℂ) * z)‖ ≤ K := by
    have hn := hmid (-r) (-t) (by rwa [abs_neg]) (by rwa [abs_neg])
    rw [← norm_neg] at hn
    push_cast at hn
    convert hn using 2; ring
  convert norm_segment_le y ((r : ℂ) * x + (t : ℂ) * z) s hs h₁ h₂ using 2; ring

private theorem norm_triple_reduced_le (a b r s t : ℝ)
    (hr : |r| ≤ 1) (hs : |s| ≤ 1) (ht : |t| ≤ 1) :
    ‖triple ((r : ℂ) * phase (-a)) (s : ℂ) ((t : ℂ) * phase b)‖ ≤ U a b := by
  let x := (3 / 10 : ℂ) * phase (-a)
  let y := (4 / 10 : ℂ)
  let z := (3 / 10 : ℂ) * phase b
  have hc (e f : ℝ) (he : e = 1 ∨ e = -1) (hf : f = 1 ∨ f = -1) :
      ‖(e : ℂ) * x + y + (f : ℂ) * z‖ ≤ U a b := by
    change ‖(e : ℂ) * x + y + (f : ℂ) * z‖ ≤
      max (max ‖x + y + z‖ ‖x + y - z‖) (max ‖-x + y + z‖ ‖-x + y - z‖)
    rcases he with rfl | rfl <;> rcases hf with rfl | rfl <;>
      simp only [Complex.ofReal_neg, Complex.ofReal_one, one_mul, neg_one_mul, ← sub_eq_add_neg]
    · exact (le_max_left _ _).trans (le_max_left _ _)
    · exact (le_max_right _ _).trans (le_max_left _ _)
    · exact (le_max_left _ _).trans (le_max_right _ _)
    · exact (le_max_right _ _).trans (le_max_right _ _)
  convert norm_box_le x y z hc r s t hr hs ht using 2
  dsimp [triple, x, y, z]
  ring

private theorem norm_triple_le {a b l m r s₀ s₁ s₂ : ℝ}
    (ha : IsReduction (m - l) a) (hb : IsReduction (r - m) b)
    (h₀ : |s₀| ≤ 1) (h₁ : |s₁| ≤ 1) (h₂ : |s₂| ≤ 1) :
    ‖triple ((s₀ : ℂ) * phase l) ((s₁ : ℂ) * phase m) ((s₂ : ℂ) * phase r)‖ ≤ U a b := by
  obtain ⟨j, hj⟩ := ha.2
  obtain ⟨k, hk⟩ := hb.2
  obtain ⟨e, he, hl⟩ := phase_add_pi_mul (l - m) (-a) (-j) (by push_cast; linarith)
  obtain ⟨f, hf, hr⟩ := phase_add_pi_mul (r - m) b k hk
  have hl' : phase l = phase m * (phase (-a) * (e : ℂ)) := by
    rw [← hl, ← phase_add, show m + (l - m) = l by ring]
  have hr' : phase r = phase m * (phase b * (f : ℂ)) := by
    rw [← hr, ← phase_add, show m + (r - m) = r by ring]
  have hrot : triple ((s₀ : ℂ) * phase l) ((s₁ : ℂ) * phase m) ((s₂ : ℂ) * phase r) =
      phase m * triple (((s₀ * e : ℝ) : ℂ) * phase (-a)) (s₁ : ℂ)
        (((s₂ * f : ℝ) : ℂ) * phase b) := by
    rw [hl', hr']
    simp only [triple, Complex.ofReal_mul]
    ring
  rw [hrot, norm_mul, norm_phase, one_mul]
  have hsign (u : ℝ) (hu : u = 1 ∨ u = -1) : |u| = 1 := by rcases hu with rfl | rfl <;> norm_num
  exact norm_triple_reduced_le a b _ _ _ (by rwa [abs_mul, hsign e he, mul_one]) h₁
    (by rwa [abs_mul, hsign f hf, mul_one])

section Allocation

variable {ι : Type*} [DecidableEq ι]

/-- Index triples by their left vertex `j`; the source's center is `i = j+1`. -/
@[expose] public def tripleMass (p : ℕ → ι) (w : ι → ℝ) (j : ℕ) : ℝ :=
  min (w (p j)) (min (w (p (j + 1))) (w (p (j + 2))))

private def roleMass (k : ℕ) (p : ℕ → ι) (w : ι → ℝ) (d : ℕ) (q : ι) : ℝ :=
  ∑ j ∈ range (k - 2), if p (j + d) = q then tripleMass p w j else 0

private def allocated (k : ℕ) (p : ℕ → ι) (w : ι → ℝ) (q : ι) : ℝ :=
  (3 / 10) * roleMass k p w 0 q + (4 / 10) * roleMass k p w 1 q +
    (3 / 10) * roleMass k p w 2 q

private theorem mem_clip_of_triple {k j d : ℕ} (hj : j ∈ range (k - 2)) (hd : d ≤ 2) :
    j + d ∈ range k := by
  simp only [mem_range] at hj ⊢
  omega

private theorem roleMass_le {A : Finset ι} {k : ℕ} {p : ℕ → ι} {w : ι → ℝ} {q : ι}
    (hq : q ∈ A) (hw : ∀ x ∈ A, 0 ≤ w x) (hinj : Set.InjOn p (↑(range k) : Set ℕ))
    {d : ℕ} (hd : d ≤ 2) : roleMass k p w d q ≤ w q := by
  let J := (range (k - 2)).filter fun j ↦ p (j + d) = q
  have hjcard : J.card ≤ 1 := by
    refine card_le_one.mpr fun j hj i hi ↦ ?_
    obtain ⟨hj, hjq⟩ := mem_filter.mp hj
    obtain ⟨hi, hiq⟩ := mem_filter.mp hi
    have hh := hinj (mem_clip_of_triple hj hd) (mem_clip_of_triple hi hd) (hjq.trans hiq.symm)
    omega
  rw [roleMass, ← sum_filter]
  change ∑ j ∈ J, tripleMass p w j ≤ w q
  calc
    _ ≤ ∑ _j ∈ J, w q := by
      refine sum_le_sum fun j hj ↦ ?_
      rw [← (mem_filter.mp hj).2]
      have hd' : d = 0 ∨ d = 1 ∨ d = 2 := by omega
      rcases hd' with rfl | rfl | rfl
      · exact min_le_left _ _
      · exact (min_le_right _ _).trans (min_le_left _ _)
      · exact (min_le_right _ _).trans (min_le_right _ _)
    _ = (J.card : ℝ) * w q := by rw [sum_const, nsmul_eq_mul]
    _ ≤ w q := by
      simpa only [Nat.cast_one, one_mul] using
        mul_le_mul_of_nonneg_right (Nat.cast_le (α := ℝ).mpr hjcard) (hw q hq)

private theorem allocated_le {A : Finset ι} {k : ℕ} {p : ℕ → ι} {w : ι → ℝ} {q : ι}
    (hq : q ∈ A) (hw : ∀ x ∈ A, 0 ≤ w x) (hinj : Set.InjOn p (↑(range k) : Set ℕ)) :
    allocated k p w q ≤ w q := by
  unfold allocated
  linarith [roleMass_le hq hw hinj (d := 0) (by decide),
    roleMass_le hq hw hinj (d := 1) (by decide), roleMass_le hq hw hinj (d := 2) (by decide)]

private theorem sum_roleMass_mul {R : Type*} [CommSemiring R] (f : ℝ →+* R)
    {A : Finset ι} {k : ℕ} {p : ℕ → ι} (w : ι → ℝ) (v : ι → R)
    (hclip : ∀ j ∈ range k, p j ∈ A) {d : ℕ} (hd : d ≤ 2) :
    ∑ q ∈ A, f (roleMass k p w d q) * v q =
      ∑ j ∈ range (k - 2), f (tripleMass p w j) * v (p (j + d)) := by
  simp only [roleMass, map_sum, Finset.sum_mul, apply_ite f, map_zero, ite_mul, zero_mul]
  rw [sum_comm]
  refine sum_congr rfl fun j hj ↦ ?_
  rw [Finset.sum_ite_eq, ite_eq_left (hclip _ (mem_clip_of_triple hj hd))]

private theorem sum_allocated_mul {R : Type*} [CommSemiring R] (f : ℝ →+* R)
    {A : Finset ι} {k : ℕ} {p : ℕ → ι} (w : ι → ℝ) (v : ι → R)
    (hclip : ∀ j ∈ range k, p j ∈ A) :
    ∑ q ∈ A, f (allocated k p w q) * v q =
      ∑ j ∈ range (k - 2), f (tripleMass p w j) *
        (f (3 / 10) * v (p j) + f (4 / 10) * v (p (j + 1)) + f (3 / 10) * v (p (j + 2))) := by
  simp only [allocated, map_add, map_mul, add_mul, mul_assoc, sum_add_distrib, ← mul_sum]
  rw [sum_roleMass_mul f w v hclip (d := 0) (by decide),
    sum_roleMass_mul f w v hclip (d := 1) (by decide),
    sum_roleMass_mul f w v hclip (d := 2) (by decide)]
  simp only [Nat.add_zero, mul_sum, ← sum_add_distrib]
  apply sum_congr rfl
  intro j _
  ring

private theorem sum_allocated {A : Finset ι} {k : ℕ} {p : ℕ → ι} (w : ι → ℝ)
    (hclip : ∀ j ∈ range k, p j ∈ A) :
    ∑ q ∈ A, allocated k p w q = ∑ j ∈ range (k - 2), tripleMass p w j := by
  simpa only [RingHom.id_apply, mul_one, show (3 / 10 + 4 / 10 + 3 / 10 : ℝ) = 1 by norm_num]
    using sum_allocated_mul (RingHom.id ℝ) w (fun _ ↦ 1) hclip

/-- The overlapping allocation inequality on the *full* support, for real coefficients
of absolute value at most one. The ordered clip is indexed by `range k`; edge `i` ends
at `p i`. The bound also applies when the clip has fewer than three vertices. -/
public theorem norm_le_overlapping_triples (A : Finset ι) (k : ℕ) (p : ℕ → ι)
    (w θ s : ι → ℝ) (a : ℕ → ℝ) (hclip : ∀ i ∈ range k, p i ∈ A)
    (hinj : Set.InjOn p (↑(range k) : Set ℕ)) (hw : ∀ q ∈ A, 0 ≤ w q)
    (hs : ∀ q ∈ A, |s q| ≤ 1)
    (ha : ∀ j ∈ range (k - 1), IsReduction (θ (p (j + 1)) - θ (p j)) (a (j + 1))) :
    ‖∑ q ∈ A, (w q : ℂ) * (s q : ℂ) * phase (θ q)‖ ≤
      (∑ q ∈ A, w q) + ∑ j ∈ range (k - 2),
        tripleMass p w j * (U (a (j + 1)) (a (j + 2)) - 1) := by
  let v (q : ι) := (s q : ℂ) * phase (θ q)
  let rem (q : ι) := w q - allocated k p w q
  let cv (j : ℕ) := (tripleMass p w j : ℂ) * triple (v (p j)) (v (p (j + 1))) (v (p (j + 2)))
  have htotal : ∑ q ∈ A, (allocated k p w q : ℂ) * v q = ∑ j ∈ range (k - 2), cv j := by
    simpa only [cv, triple, Complex.ofRealHom_eq_coe, Complex.ofReal_div, Complex.ofReal_ofNat]
      using sum_allocated_mul Complex.ofRealHom w v hclip
  -- The residue is summed over all of `A`. At vertices outside the clip the indicators
  -- defining every role vanish, so the residue there is the entire original weight.
  have hdecomp : (∑ q ∈ A, (w q : ℂ) * (s q : ℂ) * phase (θ q)) =
      (∑ q ∈ A, (rem q : ℂ) * v q) + ∑ j ∈ range (k - 2), cv j := by
    rw [← htotal, ← sum_add_distrib]
    refine sum_congr rfl fun q _ ↦ ?_
    simp only [rem, v, Complex.ofReal_sub]
    ring
  have hrem (q : ι) (hq : q ∈ A) : ‖(rem q : ℂ) * v q‖ ≤ rem q := by
    have hnonneg : 0 ≤ rem q := sub_nonneg.mpr (allocated_le hq hw hinj)
    have hv : ‖v q‖ ≤ 1 := by
      simpa only [v, norm_mul, norm_phase, Complex.norm_real, Real.norm_eq_abs, mul_one] using hs q hq
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hnonneg]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hv hnonneg
  have htr (j : ℕ) (hj : j ∈ range (k - 2)) :
      ‖cv j‖ ≤ tripleMass p w j * U (a (j + 1)) (a (j + 2)) := by
    have hmem (d : ℕ) (hd : d ≤ 2) := hclip _ (mem_clip_of_triple hj hd)
    have hc : 0 ≤ tripleMass p w j :=
      le_min (hw _ (hmem 0 (by decide))) (le_min (hw _ (hmem 1 (by decide))) (hw _ (hmem 2 (by decide))))
    have hj' : j ∈ range (k - 1) := by simp only [mem_range] at hj ⊢; omega
    have hj'' : j + 1 ∈ range (k - 1) := by simp only [mem_range] at hj ⊢; omega
    dsimp only [cv]
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hc]
    exact mul_le_mul_of_nonneg_left
      (norm_triple_le (ha j hj') (ha (j + 1) hj'')
        (hs _ (hmem 0 (by decide))) (hs _ (hmem 1 (by decide))) (hs _ (hmem 2 (by decide)))) hc
  rw [hdecomp]
  calc
    _ ≤ ‖∑ q ∈ A, (rem q : ℂ) * v q‖ + ‖∑ j ∈ range (k - 2), cv j‖ := norm_add_le _ _
    _ ≤ (∑ q ∈ A, rem q) + ∑ j ∈ range (k - 2), tripleMass p w j * U (a (j + 1)) (a (j + 2)) :=
      add_le_add ((norm_sum_le _ _).trans (sum_le_sum hrem))
        ((norm_sum_le _ _).trans (sum_le_sum htr))
    _ = _ := by
      simp only [rem, sum_sub_distrib, sum_allocated w hclip, mul_sub, mul_one]
      ring

end Allocation

/-- Loss on a reduced chord. -/
@[expose] public def deficit (a : ℝ) : ℝ := 1 - Real.cos (a / 2)

/-- `Z`, including the first clipped vertex even though it has no incoming chord. -/
@[expose] public def chordMass (k : ℕ) (z : ℕ → ℝ) : ℝ := ∑ j ∈ range k, z j

/-- `F`: each chord is weighted by `z` at its right vertex. -/
@[expose] public def chordMean (k : ℕ) (z a : ℕ → ℝ) : ℝ :=
  (∑ j ∈ range (k - 1), z (j + 1) * Real.cos (a (j + 1) / 2)) / chordMass k z

/-- The missing first weight and the two unpaired half-deficits. With two vertices
both end terms refer to the same chord; with just one vertex there are no chords. -/
@[expose] public def endpointAllowance (k : ℕ) (z : ℕ → ℝ) : ℝ :=
  z 0 / chordMass k z + if 2 ≤ k then
    (z 1 + z (k - 1)) * (1 - 1 / Real.sqrt 2) / (2 * chordMass k z) else 0

/-- The total normalized chord deficit charged by the triples. -/
@[expose] public def halfEdgeDeficit (k : ℕ) (z a : ℕ → ℝ) : ℝ :=
  ∑ j ∈ range (k - 2),
    (z (j + 1) * deficit (a (j + 1)) + z (j + 2) * deficit (a (j + 2))) / (2 * chordMass k z)

private theorem sum_adjacent (m : ℕ) (g : ℕ → ℝ) :
    ∑ j ∈ range m, (g j + g (j + 1)) = 2 * (∑ j ∈ range (m + 1), g j) - g 0 - g m := by
  rw [sum_add_distrib]
  linarith only [sum_range_succ g m, sum_range_succ' g m]

/-- Every interior chord occurs twice and each terminal chord loses one half.
For `m = 0`, the identical terminal indices subtract two halves of the only chord. -/
public theorem halfEdgeDeficit_eq (m : ℕ) (z a : ℕ → ℝ) (hZ : chordMass (m + 2) z ≠ 0) :
    halfEdgeDeficit (m + 2) z a = 1 - chordMean (m + 2) z a - z 0 / chordMass (m + 2) z -
      (z 1 * deficit (a 1) + z (m + 1) * deficit (a (m + 1))) / (2 * chordMass (m + 2) z) := by
  let Z := chordMass (m + 2) z
  let g (j : ℕ) := z (j + 1) * deficit (a (j + 1))
  let N : ℝ := ∑ j ∈ range (m + 1), z (j + 1) * Real.cos (a (j + 1) / 2)
  have hg : ∑ j ∈ range (m + 1), g j = Z - z 0 - N := by
    simp only [g, deficit, mul_sub, mul_one, sum_sub_distrib, Z, chordMass, N]
    rw [sum_range_succ' z (m + 1)]
    ring
  change (∑ j ∈ range m, (g j + g (j + 1)) / (2 * Z)) =
    1 - N / Z - z 0 / Z - (g 0 + g m) / (2 * Z)
  calc
    _ = (∑ j ∈ range m, (g j + g (j + 1))) / (2 * Z) := by
      simp only [div_eq_mul_inv, sum_mul]
    _ = _ := by
      rw [sum_adjacent, hg]
      have hZ' : Z ≠ 0 := hZ
      field_simp
      ring

private theorem deficit_le {a : ℝ} (ha : |a| ≤ Real.pi / 2) :
    deficit a ≤ 1 - 1 / Real.sqrt 2 := by
  have hsign : 0 ≤ |a| / 2 := by positivity
  have hcos := Real.cos_le_cos_of_nonneg_of_le_pi hsign
    (show Real.pi / 4 ≤ Real.pi by linarith [Real.pi_pos]) (show |a| / 2 ≤ Real.pi / 4 by linarith)
  have harg : |a| / 2 = |a / 2| := by rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  rw [Real.cos_pi_div_four, harg, Real.cos_abs] at hcos
  have hs : Real.sqrt 2 / 2 = 1 / Real.sqrt 2 := by
    apply (eq_div_iff (by positivity : Real.sqrt 2 ≠ 0)).2
    nlinarith only [Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  rw [hs] at hcos
  exact sub_le_sub_left hcos 1

/-- Bound the two lost halves at the source's endpoint allowance, without
approximating the interior chord weights. -/
public theorem halfEdgeDeficit_ge (k : ℕ) (z a : ℕ → ℝ)
    (hz : ∀ j ∈ range k, 0 ≤ z j) (hZ : 0 < chordMass k z)
    (ha : ∀ j ∈ range (k - 1), |a (j + 1)| ≤ Real.pi / 2) :
    1 - chordMean k z a - endpointAllowance k z ≤ halfEdgeDeficit k z a := by
  cases k with
  | zero => simp [chordMass] at hZ
  | succ k =>
    cases k with
    | zero =>
      have hz₀ : z 0 ≠ 0 := by simpa [chordMass] using hZ.ne'
      simp [chordMean, endpointAllowance, halfEdgeDeficit, chordMass, hz₀]
    | succ m =>
      rw [halfEdgeDeficit_eq m z a hZ.ne']
      have he₁ := deficit_le (ha 0 (mem_range.mpr (by omega)))
      have he₂ := deficit_le (ha m (mem_range.mpr (by omega)))
      have hw₁ := hz 1 (mem_range.mpr (by omega))
      have hw₂ := hz (m + 1) (mem_range.mpr (by omega))
      have hnum : z 1 * deficit (a 1) + z (m + 1) * deficit (a (m + 1)) ≤
          (z 1 + z (m + 1)) * (1 - 1 / Real.sqrt 2) := by
        rw [add_mul]
        exact add_le_add (mul_le_mul_of_nonneg_left he₁ hw₁) (mul_le_mul_of_nonneg_left he₂ hw₂)
      have hlast := div_le_div_of_nonneg_right hnum (show 0 ≤ 2 * chordMass (m + 2) z by positivity)
      simp only [endpointAllowance, ite_eq_left (show 2 ≤ m + 2 by omega),
        show m + 2 - 1 = m + 1 by omega]
      linarith only [hlast]

/-- The signed tapered rank-two statistic `S`, before gap pooling or a positive part. -/
@[expose] public def signedSum (k : ℕ) (t a : ℕ → ℝ) : ℝ :=
  ∑ j ∈ range (k - 2), t j * Real.cos (2 * (a (j + 1) + a (j + 2)))

/-- Local score at trial angles `u,v`, using this triple's own coefficients. -/
@[expose] public def localScore (c z t : ℕ → ℝ) (Z : ℝ) (j : ℕ) (u v : ℝ) : ℝ :=
  c j * (U u v - 1) + (873 / 1000) *
    ((z (j + 1) * deficit u + z (j + 2) * deficit v) / (2 * Z)) -
    (956 / 1000) * (t j * Real.cos (2 * (u + v)))

/-- Global price with `L` the sum of the local upper bounds. -/
@[expose] public def affinePrice (M F E S L : ℝ) : ℝ :=
  M - (873 / 1000) * (1 - F - E) + (956 / 1000) * S + L

/-- From separate upper certificates of the local envelopes, bound the full signed
modulus. Neither the actual chord mean nor the signed sum has a threshold premise. -/
public theorem norm_le_signed_price {ι : Type*} [DecidableEq ι]
    (A : Finset ι) (k : ℕ) (p : ℕ → ι) (w θ s : ι → ℝ) (z t a L : ℕ → ℝ)
    (hclip : ∀ i ∈ range k, p i ∈ A) (hinj : Set.InjOn p (↑(range k) : Set ℕ))
    (hw : ∀ q ∈ A, 0 ≤ w q) (hs : ∀ q ∈ A, |s q| ≤ 1)
    (hz : ∀ j ∈ range k, 0 ≤ z j) (hZ : 0 < chordMass k z)
    (ha : ∀ j ∈ range (k - 1), IsReduction (θ (p (j + 1)) - θ (p j)) (a (j + 1)))
    (hL : ∀ j ∈ range (k - 2), ∀ u v : ℝ, |u| ≤ Real.pi / 2 → |v| ≤ Real.pi / 2 →
      localScore (tripleMass p w) z t (chordMass k z) j u v ≤ L j) :
    ‖∑ q ∈ A, (w q : ℂ) * (s q : ℂ) * phase (θ q)‖ ≤
      affinePrice (∑ q ∈ A, w q) (chordMean k z a) (endpointAllowance k z) (signedSum k t a)
        (∑ j ∈ range (k - 2), L j) := by
  have halloc := norm_le_overlapping_triples A k p w θ s a hclip hinj hw hs ha
  have hhalf := halfEdgeDeficit_ge k z a hz hZ (fun j hj ↦ (ha j hj).1)
  have hlocal : ∑ j ∈ range (k - 2), localScore (tripleMass p w) z t (chordMass k z) j
      (a (j + 1)) (a (j + 2)) ≤ ∑ j ∈ range (k - 2), L j := by
    refine sum_le_sum fun j hj ↦ hL j hj _ _ (ha j ?_).1 (ha (j + 1) ?_).1 <;>
      simp only [mem_range] at hj ⊢ <;> omega
  simp only [localScore, sum_sub_distrib, sum_add_distrib, ← mul_sum] at hlocal
  change (∑ j ∈ range (k - 2), tripleMass p w j * (U (a (j + 1)) (a (j + 2)) - 1)) +
    (873 / 1000) * halfEdgeDeficit k z a - (956 / 1000) * signedSum k t a ≤
      ∑ j ∈ range (k - 2), L j at hlocal
  unfold affinePrice
  linarith only [halloc, hhalf, hlocal]

/-- A reference intercept is a bound on the affine *majorant* at `F₀,S₀`.
The same local certificates can then be used without restricting the actual data
by those reference values. -/
public theorem affinePrice_lt_of_calibration {M F E S L F₀ S₀ C : ℝ}
    (h : affinePrice M F₀ E S₀ L < C) :
    affinePrice M F E S L < C + (873 / 1000) * (F - F₀) + (956 / 1000) * (S - S₀) := by
  unfold affinePrice at h ⊢
  linarith only [h]

/-- Full prime support below the real cutoff `X` (not the clip). -/
@[expose] public def primeSupport (X : ℝ) : Finset ℕ := (range ⌈X⌉₊).filter Nat.Prime

public theorem mem_primeSupport {X : ℝ} {q : ℕ} :
    q ∈ primeSupport X ↔ q.Prime ∧ (q : ℝ) < X := by
  simp only [primeSupport, mem_filter, mem_range, Nat.lt_ceil, and_comm]

/-- The full ramp weight, used for both the total mass and the triple allocation. -/
@[expose] public def primeWeight (X : ℝ) (q : ℕ) : ℝ := Real.log q * Real.log (X / q) / X

/-- The exact `z` at the clipped vertices; do not replace it by the ramp weight. -/
@[expose] public def logWeight (X : ℝ) (p : ℕ → ℕ) (j : ℕ) : ℝ := Real.log (X / p j)

/-- The exact rank-two taper coefficient `tᵢ`, for `i = j+1`. -/
@[expose] public def taperWeight (X : ℝ) (p : ℕ → ℕ) (j : ℕ) : ℝ :=
  let H := 40 * Real.log X
  let d := (p (j + 2) : ℝ) - (p j : ℝ)
  (2 / H) * max (1 - d / H) 0 * logWeight X p (j + 2) * Real.log (p j) * Real.log (p (j + 2)) / X

private theorem log_ratio_pos {X : ℝ} {q : ℕ} (hq : q ∈ primeSupport X) :
    0 < Real.log (X / q) := by
  obtain ⟨hp, hX⟩ := mem_primeSupport.mp hq
  apply Real.log_pos
  rw [lt_div_iff₀ (Nat.cast_pos.mpr hp.pos), one_mul]
  exact hX

/-- The signed successor bound with the source's cutoff, clip, and weights. The
nonempty ordered enumeration is `p` on `range k`; only the chord statistics use
this clip. The certificates bound the score for each triple on the whole angular box. -/
public theorem norm_le_prime_signed_price (X : ℝ) (k : ℕ) (p : ℕ → ℕ) (θ s : ℕ → ℝ)
    (a L : ℕ → ℝ) (hk : 0 < k) (horder : StrictMonoOn p (↑(range k) : Set ℕ))
    (hclip : (range k).image p = (primeSupport X).filter (fun q : ℕ ↦ Real.exp (-8) * X ≤ (q : ℝ)))
    (hs : ∀ q ∈ primeSupport X, |s q| ≤ 1)
    (ha : ∀ j ∈ range (k - 1), IsReduction (θ (p (j + 1)) - θ (p j)) (a (j + 1)))
    (hL : ∀ j ∈ range (k - 2), ∀ u v : ℝ, |u| ≤ Real.pi / 2 → |v| ≤ Real.pi / 2 →
      localScore (tripleMass p (primeWeight X)) (logWeight X p) (taperWeight X p)
        (chordMass k (logWeight X p)) j u v ≤ L j) :
    ‖∑ q ∈ primeSupport X, (primeWeight X q : ℂ) * (s q : ℂ) * phase (θ q)‖ ≤
      affinePrice (∑ q ∈ primeSupport X, primeWeight X q) (chordMean k (logWeight X p) a)
        (endpointAllowance k (logWeight X p)) (signedSum k (taperWeight X p) a)
        (∑ j ∈ range (k - 2), L j) := by
  have hmem (j : ℕ) (hj : j ∈ range k) : p j ∈ primeSupport X := by
    have hm := mem_image_of_mem p hj
    rw [hclip] at hm
    exact (mem_filter.mp hm).1
  have hw (q : ℕ) (hq : q ∈ primeSupport X) : 0 ≤ primeWeight X q := by
    obtain ⟨hp, hqX⟩ := mem_primeSupport.mp hq
    have hqpos : (0 : ℝ) < q := Nat.cast_pos.mpr hp.pos
    have hlog : 0 < Real.log q := Real.log_pos (by exact_mod_cast hp.one_lt)
    exact (div_pos (mul_pos hlog (log_ratio_pos hq)) (hqpos.trans hqX)).le
  have hz (j : ℕ) (hj : j ∈ range k) : 0 < logWeight X p j := log_ratio_pos (hmem j hj)
  have hZ : 0 < chordMass k (logWeight X p) := sum_pos hz ⟨0, mem_range.mpr hk⟩
  exact norm_le_signed_price _ _ _ _ _ _ _ _ _ _ hmem horder.injOn hw hs
    (fun j hj ↦ (hz j hj).le) hZ ha hL

/-- Given an independently certified intercept at `F₀,S₀`, retain the signed
statistic in the strict cap for the actual phases. This does not certify an
intercept at any cutoff. -/
public theorem norm_lt_prime_signed_price_of_calibration
    (X : ℝ) (k : ℕ) (p : ℕ → ℕ) (θ s : ℕ → ℝ) (a L : ℕ → ℝ) (F₀ S₀ C : ℝ)
    (hk : 0 < k) (horder : StrictMonoOn p (↑(range k) : Set ℕ))
    (hclip : (range k).image p = (primeSupport X).filter (fun q : ℕ ↦ Real.exp (-8) * X ≤ (q : ℝ)))
    (hs : ∀ q ∈ primeSupport X, |s q| ≤ 1)
    (ha : ∀ j ∈ range (k - 1), IsReduction (θ (p (j + 1)) - θ (p j)) (a (j + 1)))
    (hL : ∀ j ∈ range (k - 2), ∀ u v : ℝ, |u| ≤ Real.pi / 2 → |v| ≤ Real.pi / 2 →
      localScore (tripleMass p (primeWeight X)) (logWeight X p) (taperWeight X p)
        (chordMass k (logWeight X p)) j u v ≤ L j)
    (hcal : affinePrice (∑ q ∈ primeSupport X, primeWeight X q) F₀
      (endpointAllowance k (logWeight X p)) S₀ (∑ j ∈ range (k - 2), L j) < C) :
    ‖∑ q ∈ primeSupport X, (primeWeight X q : ℂ) * (s q : ℂ) * phase (θ q)‖ <
      C + (873 / 1000) * (chordMean k (logWeight X p) a - F₀) +
        (956 / 1000) * (signedSum k (taperWeight X p) a - S₀) :=
  (norm_le_prime_signed_price X k p θ s a L hk horder hclip hs ha hL).trans_lt
    (affinePrice_lt_of_calibration hcal)

end

end Masullo.SignedSuccessorPrice
