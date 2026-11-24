module

public import Mathlib.Data.ZMod.QuotientGroup
public import Mathlib.GroupTheory.Index
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Denominator-pair mask indices

Sources: `e6b43a82d74c:.godel/alice/denominator-pair-gap-regions.md:19–29`
(index calculation on line 23), used in the widened count at
`1d036a89b046:.godel/alice/denominator-pair-gap-regions.md:37–53`.
Source pin: `f8c831a3e7afbcdd3488a3ad51afa8cea6e9fc99`, unchanged through
`c3cb30e1ffe1d586f95676e2f10b6ed29634ec97`.

Scope: the full additive gap and triple lattices in the integer coordinates
`(x,y)` and `(m,(x,y))`, the CRT projection, and its vertical fibers. There are
no box, primitivity, rank, or counting restrictions. The factor `G = gcd(d,e)`
is already accounted for by `G ∣ l` and `lcm(d,e) = de/G`.

Owning check session: `01a20e06-2914-72b5-a0f3-35d7c4cdf9e8`.
-/

namespace DenominatorPairMaskIndex

private def rectangle (s t : ℕ) : AddSubgroup (ℤ × ℤ) :=
  (AddSubgroup.zmultiples (s : ℤ)).prod (AddSubgroup.zmultiples (t : ℤ))

private theorem mem_rectangle {s t : ℕ} {b : ℤ × ℤ} :
    b ∈ rectangle s t ↔ ((s : ℤ) ∣ b.1) ∧ ((t : ℤ) ∣ b.2) := by
  rw [rectangle, AddSubgroup.mem_prod, Int.mem_zmultiples_iff, Int.mem_zmultiples_iff]

private def differenceResidue (l : ℕ) : (ℤ × ℤ) →+ ZMod l where
  toFun b := ((b.1 - b.2 : ℤ) : ZMod l)
  map_zero' := by simp
  map_add' b c := by
    simp only [Prod.fst_add, Prod.snd_add, Int.cast_add, Int.cast_sub]
    ring

/-- The gap lattice `M`, with all three divisibility conditions in the original coordinates. -/
public def gapMask (s t l : ℕ) : AddSubgroup (ℤ × ℤ) :=
  rectangle s t ⊓ (differenceResidue l).ker

public theorem mem_gapMask {s t l : ℕ} {b : ℤ × ℤ} :
    b ∈ gapMask s t l ↔ ((s : ℤ) ∣ b.1) ∧ ((t : ℤ) ∣ b.2) ∧
      ((l : ℤ) ∣ b.1 - b.2) := by
  change b ∈ rectangle s t ∧ ((b.1 - b.2 : ℤ) : ZMod l) = 0 ↔ _
  rw [mem_rectangle, ZMod.intCast_zmod_eq_zero_iff_dvd, and_assoc]

private theorem gcd_three_bezout (s t l : ℕ) :
    ∃ a b c : ℤ, (↑((s.gcd t).gcd l) : ℤ) = (s : ℤ) * a + (t : ℤ) * b + (l : ℤ) * c := by
  let u := Int.gcdA (s.gcd t : ℤ) (l : ℤ)
  refine ⟨Int.gcdA (s : ℤ) (t : ℤ) * u, Int.gcdB (s : ℤ) (t : ℤ) * u,
    Int.gcdB (s.gcd t : ℤ) (l : ℤ), ?_⟩
  calc
    (↑((s.gcd t).gcd l) : ℤ) = (s.gcd t : ℤ) * u +
        (l : ℤ) * Int.gcdB (s.gcd t : ℤ) (l : ℤ) := by
      simpa only [Int.gcd_natCast_natCast] using Int.gcd_eq_gcd_ab (s.gcd t : ℤ) (l : ℤ)
    _ = _ := by
      have h := Int.gcd_eq_gcd_ab (s : ℤ) (t : ℤ)
      rw [Int.gcd_natCast_natCast] at h
      rw [h]
      ring

private theorem difference_image_card (s t : ℕ) {l : ℕ} (hl : 0 < l) :
    Nat.card ↥((rectangle s t).map (differenceResidue l)) = l / (s.gcd t).gcd l := by
  let g := (s.gcd t).gcd l
  have hgl : g ∣ l := Nat.gcd_dvd_right _ _
  let f : ZMod l →+* ZMod g := ZMod.castHom hgl _
  have hs : (g : ℤ) ∣ (s : ℤ) := Int.ofNat_dvd.mpr
    ((Nat.gcd_dvd_left (s.gcd t) l).trans (Nat.gcd_dvd_left s t))
  have ht : (g : ℤ) ∣ (t : ℤ) := Int.ofNat_dvd.mpr
    ((Nat.gcd_dvd_left (s.gcd t) l).trans (Nat.gcd_dvd_right s t))
  -- The image is precisely the multiples of `g` modulo `l`.
  have himage : (rectangle s t).map (differenceResidue l) = f.toAddMonoidHom.ker := by
    ext z
    rw [AddSubgroup.mem_map, AddMonoidHom.mem_ker]
    change (∃ b ∈ rectangle s t, ((b.1 - b.2 : ℤ) : ZMod l) = z) ↔ f z = 0
    constructor
    · rintro ⟨b, hb, rfl⟩
      rw [map_intCast, ZMod.intCast_zmod_eq_zero_iff_dvd]
      obtain ⟨hb₁, hb₂⟩ := mem_rectangle.mp hb
      exact dvd_sub (hs.trans hb₁) (ht.trans hb₂)
    · obtain ⟨w, rfl⟩ := ZMod.intCast_surjective z
      rw [map_intCast, ZMod.intCast_zmod_eq_zero_iff_dvd]
      rintro ⟨k, rfl⟩
      obtain ⟨a, b, c, habc⟩ := gcd_three_bezout s t l
      refine ⟨((s : ℤ) * (a * k), (t : ℤ) * (-(b * k))),
        mem_rectangle.mpr ⟨dvd_mul_right _ _, dvd_mul_right _ _⟩, ?_⟩
      apply (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ l).mpr
      refine ⟨c * k, ?_⟩
      change (g : ℤ) * k - ((s : ℤ) * (a * k) - (t : ℤ) * (-(b * k))) = (l : ℤ) * (c * k)
      linear_combination k * habc
  have hf : Function.Surjective f.toAddMonoidHom := by
    intro z
    obtain ⟨w, rfl⟩ := ZMod.intCast_surjective z
    exact ⟨(w : ZMod l), map_intCast f w⟩
  have hindex : f.toAddMonoidHom.ker.index = g :=
    (Nat.card_congr (QuotientAddGroup.quotientKerEquivOfSurjective _ hf).toEquiv).trans
      (Nat.card_zmod g)
  apply (Nat.div_eq_of_eq_mul_left (Nat.pos_of_dvd_of_pos hgl hl) ?_).symm
  rw [himage]
  calc
    l = Nat.card (ZMod l) := (Nat.card_zmod l).symm
    _ = Nat.card ↥f.toAddMonoidHom.ker * f.toAddMonoidHom.ker.index :=
      (AddSubgroup.card_mul_index _).symm
    _ = Nat.card ↥f.toAddMonoidHom.ker * g :=
      congrArg (Nat.card ↥f.toAddMonoidHom.ker * ·) hindex

/-- The full gap lattice has index `D = s*t*l/gcd(gcd(s,t),l)` in `ℤ²`. -/
public theorem gapMask_index {s t l : ℕ} (_hs : 0 < s) (_ht : 0 < t) (hl : 0 < l) :
    (gapMask s t l).index = s * t * l / ((s.gcd t).gcd l) := by
  have hle : gapMask s t l ≤ rectangle s t := inf_le_left
  have hR : (rectangle s t).index = s * t := by
    rw [rectangle, AddSubgroup.index_prod, Int.index_zmultiples, Int.index_zmultiples]
    simp
  have hrel : (gapMask s t l).relIndex (rectangle s t) = l / (s.gcd t).gcd l := by
    rw [gapMask, AddSubgroup.inf_relIndex_left, AddSubgroup.relIndex_ker, difference_image_card s t hl]
  rw [← AddSubgroup.relIndex_mul_index hle, hrel, hR, mul_comm]
  exact (Nat.mul_div_assoc _ (Nat.gcd_dvd_right (s.gcd t) l)).symm

private def rowDifferences (F₁ q : ℤ) : (ℤ × ℤ × ℤ) →+ (ℤ × ℤ) where
  toFun p := (F₁ * p.1 - q * p.2.1, F₁ * p.1 - q * p.2.2)
  map_zero' := by simp
  map_add' p p' := by
    apply Prod.ext <;> simp only [Prod.fst_add, Prod.snd_add] <;> ring

/-- The masked triple lattice `Λ` in the coordinates `(m,(x,y))`. -/
public def maskedLattice (d e s t l : ℕ) (F₁ q : ℤ) : AddSubgroup (ℤ × ℤ × ℤ) :=
  (gapMask s t l).comap (AddMonoidHom.snd ℤ (ℤ × ℤ)) ⊓
    (rectangle d e).comap (rowDifferences F₁ q)

public theorem mem_maskedLattice {d e s t l : ℕ} {F₁ q : ℤ} {m : ℤ} {b : ℤ × ℤ} :
    (m,b) ∈ maskedLattice d e s t l F₁ q ↔ b ∈ gapMask s t l ∧
      ((d : ℤ) ∣ F₁ * m - q * b.1) ∧ ((e : ℤ) ∣ F₁ * m - q * b.2) := by
  change b ∈ gapMask s t l ∧ (F₁ * m - q * b.1, F₁ * m - q * b.2) ∈ rectangle d e ↔ _
  rw [mem_rectangle]

/-- The unmasked congruences are soluble exactly on the compatible gaps `x = y (mod G)`. -/
public theorem congruences_soluble_iff {d e : ℕ} {F₁ q x y : ℤ}
    (hc : Int.gcd (F₁ * q) ((d : ℤ) * (e : ℤ)) = 1) :
    (∃ m : ℤ, ((d : ℤ) ∣ F₁ * m - q * x) ∧ ((e : ℤ) ∣ F₁ * m - q * y)) ↔
      ((d.gcd e : ℤ) ∣ x - y) := by
  have hcop := Int.isCoprime_iff_gcd_eq_one.mpr hc
  have hGd : (d.gcd e : ℤ) ∣ (d : ℤ) := Int.ofNat_dvd.mpr (Nat.gcd_dvd_left d e)
  have hGe : (d.gcd e : ℤ) ∣ (e : ℤ) := Int.ofNat_dvd.mpr (Nat.gcd_dvd_right d e)
  constructor
  · rintro ⟨m, hmx, hmy⟩
    have hqx : (d.gcd e : ℤ) ∣ q * (x - y) := by
      convert dvd_sub (hGe.trans hmy) (hGd.trans hmx) using 1; ring
    have hq := hcop.of_mul_left_right.of_isCoprime_of_dvd_right
      (hGd.trans (dvd_mul_right (d : ℤ) (e : ℤ)))
    exact hq.symm.dvd_of_dvd_mul_left hqx
  · intro hxy
    obtain ⟨k, hk⟩ := (dvd_sub_comm.mp hxy).mul_left q
    let a := Int.gcdA (d : ℤ) (e : ℤ)
    let b := Int.gcdB (d : ℤ) (e : ℤ)
    have hBez : (d.gcd e : ℤ) = (d : ℤ) * a + (e : ℤ) * b := by
      simpa only [Int.gcd_natCast_natCast] using Int.gcd_eq_gcd_ab (d : ℤ) (e : ℤ)
    -- Generalized CRT: `r` solves the two congruences for the common value `F₁*m`.
    let r := q * x + (d : ℤ) * a * k
    have hrd : (d : ℤ) ∣ r - q * x := ⟨a * k, by dsimp [r]; ring⟩
    have hre : (e : ℤ) ∣ r - q * y := by
      refine ⟨-b * k, ?_⟩
      change q * x + (d : ℤ) * a * k - q * y = (e : ℤ) * (-b * k)
      linear_combination -hk - k * hBez
    -- Invert `F₁` modulo `d*e`, hence simultaneously modulo `d` and `e`.
    obtain ⟨u, v, huv⟩ := hcop.of_mul_left_left
    have hu : (d : ℤ) * (e : ℤ) ∣ F₁ * (u * r) - r :=
      ⟨-v * r, by linear_combination r * huv⟩
    refine ⟨u * r, ?_, ?_⟩
    · simpa only [sub_add_sub_cancel] using dvd_add ((dvd_mul_right _ _).trans hu) hrd
    · simpa only [sub_add_sub_cancel] using dvd_add ((dvd_mul_left _ _).trans hu) hre

variable {d e s t l : ℕ} {F₁ q : ℤ}

/-- Projection onto the gap lattice is onto all of `M`, not a proper sublattice. -/
public theorem maskedLattice_map_snd (hGl : d.gcd e ∣ l)
    (hc : Int.gcd (F₁ * q) ((d : ℤ) * (e : ℤ)) = 1) :
    (maskedLattice d e s t l F₁ q).map (AddMonoidHom.snd ℤ (ℤ × ℤ)) = gapMask s t l := by
  ext b
  rw [AddSubgroup.mem_map]
  constructor
  · rintro ⟨⟨m, b'⟩, hm, rfl⟩
    exact (mem_maskedLattice.mp hm).1
  · intro hb
    have hxy := (Int.ofNat_dvd.mpr hGl).trans (mem_gapMask.mp hb).2.2
    obtain ⟨m, hmd, hme⟩ := (congruences_soluble_iff hc).mpr hxy
    exact ⟨(m,b), mem_maskedLattice.mpr ⟨hb, hmd, hme⟩, rfl⟩

private theorem axis_mem_iff (hc : Int.gcd (F₁ * q) ((d : ℤ) * (e : ℤ)) = 1) {m : ℤ} :
    (m, (0 : ℤ × ℤ)) ∈ maskedLattice d e s t l F₁ q ↔ ((d.lcm e : ℤ) ∣ m) := by
  have hcop := (Int.isCoprime_iff_gcd_eq_one.mpr hc).of_mul_left_left
  rw [mem_maskedLattice, ← Int.lcm_natCast_natCast, Int.coe_lcm_dvd_iff]
  simp only [Prod.fst_zero, Prod.snd_zero, mul_zero, sub_zero, zero_mem, true_and]
  exact ⟨fun h => ⟨hcop.of_mul_right_left.symm.dvd_of_dvd_mul_left h.1,
      hcop.of_mul_right_right.symm.dvd_of_dvd_mul_left h.2⟩,
    fun h => ⟨h.1.mul_left _, h.2.mul_left _⟩⟩

/-- Each nonempty fiber is exactly one translate of the `lcm(d,e)`-multiples. -/
public theorem maskedLattice_mem_fiber_iff (hc : Int.gcd (F₁ * q) ((d : ℤ) * (e : ℤ)) = 1)
    {m m₀ : ℤ} {b : ℤ × ℤ} (h₀ : (m₀,b) ∈ maskedLattice d e s t l F₁ q) :
    (m,b) ∈ maskedLattice d e s t l F₁ q ↔ ((d.lcm e : ℤ) ∣ m - m₀) := by
  rw [← axis_mem_iff (s := s) (t := t) (l := l) hc]
  constructor
  · intro h
    simpa using sub_mem h h₀
  · intro h
    simpa using add_mem h h₀

/-- The full triple lattice has index `lcm(d,e)*D` in `ℤ³`, with no extra factor of `G`. -/
public theorem maskedLattice_index (_hd : 0 < d) (_he : 0 < e) (hs : 0 < s) (ht : 0 < t)
    (hl : 0 < l) (hGl : d.gcd e ∣ l) (hc : Int.gcd (F₁ * q) ((d : ℤ) * (e : ℤ)) = 1) :
    (maskedLattice d e s t l F₁ q).index = d.lcm e * (s * t * l / ((s.gcd t).gcd l)) := by
  let M := gapMask s t l
  let Λ := maskedLattice d e s t l F₁ q
  let π := AddMonoidHom.snd ℤ (ℤ × ℤ)
  let A := AddMonoidHom.inl ℤ (ℤ × ℤ)
  let K := M.comap π
  have hle : Λ ≤ K := inf_le_left
  -- Subtract a lift of the gap to represent every class in `K/Λ` on the `m`-axis.
  have hK : A.range ⊔ Λ = K := by
    apply le_antisymm
    · refine sup_le ?_ hle
      rintro _ ⟨m, rfl⟩
      exact M.zero_mem
    · intro p hp
      have hb : p.2 ∈ Λ.map π := by
        change p.2 ∈ (maskedLattice d e s t l F₁ q).map (AddMonoidHom.snd ℤ (ℤ × ℤ))
        rw [maskedLattice_map_snd hGl hc]
        exact hp
      obtain ⟨⟨m, b⟩, hm, hbp⟩ := AddSubgroup.mem_map.mp hb
      change b = p.2 at hbp
      subst b
      exact AddSubgroup.mem_sup.mpr ⟨A (p.1 - m), ⟨_, rfl⟩, (m,p.2), hm,
        Prod.ext (sub_add_cancel _ _) (zero_add _)⟩
  have haxis : Λ.comap A = AddSubgroup.zmultiples (d.lcm e : ℤ) := by
    ext m
    exact (axis_mem_iff hc).trans Int.mem_zmultiples_iff.symm
  have hrel : Λ.relIndex K = d.lcm e := by
    rw [← hK, AddSubgroup.relIndex_sup_right, ← AddSubgroup.index_comap, haxis,
      Int.index_zmultiples, Int.natAbs_natCast]
  have hπ : Function.Surjective π := fun b => ⟨(0,b), rfl⟩
  rw [← AddSubgroup.relIndex_mul_index hle, hrel, AddSubgroup.index_comap_of_surjective M hπ,
    gapMask_index hs ht hl]

end DenominatorPairMaskIndex
