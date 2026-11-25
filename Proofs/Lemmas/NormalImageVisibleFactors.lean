module

public import Mathlib.Data.Int.Basic
public import Mathlib.Data.Nat.GCD.Basic

/-!
# Visible factors of a normal image

Source: `df36e0b4e122:.godel/alice/effective-gap-normals.md:46–54,90–108`.
Consumer: the expensive-plane divisor crossing in the same note, lines 117–126.
This module starts at the four test divisibilities; it does not establish the lattice index
or count planes. The denominators need not be coprime.

Owning check session: `01a21064-e15a-7bed-9349-0a50688b4367`.
-/

namespace NormalImageVisibleFactors

private theorem quotient_dvd_coord {g t : ℕ} (hg : 0 < g) {z : ℤ}
    (hz : (g : ℤ) ∣ z * (t : ℤ)) : ((g / g.gcd t : ℕ) : ℤ) ∣ z := by
  apply Int.natCast_dvd.mpr
  apply (Nat.div_dvd_iff_dvd_mul (Nat.gcd_dvd_left g t) (Nat.gcd_pos_of_pos_left t hg)).mpr
  apply Nat.dvd_gcd_mul_iff_dvd_mul.mpr
  simpa only [Int.natAbs_mul, Int.natAbs_natCast, Nat.mul_comm] using Int.natCast_dvd.mp hz

private theorem dvd_coord_of_coprime_mul {k t : ℕ} {z : ℤ} (hkt : k.Coprime t)
    (h : (k : ℤ) ∣ (t : ℤ) * z) : (k : ℤ) ∣ z := by
  apply Int.natCast_dvd.mpr
  apply hkt.dvd_of_dvd_mul_left
  simpa only [Int.natAbs_mul, Int.natAbs_natCast] using Int.natCast_dvd.mp h

private theorem dvd_left_of_dvd_add {k x y : ℤ} (hxy : k ∣ x + y) (hy : k ∣ y) : k ∣ x := by
  simpa only [Int.add_sub_cancel] using Int.dvd_sub hxy hy

private theorem dvd_right_of_dvd_add {k x y : ℤ} (hxy : k ∣ x + y) (hx : k ∣ x) : k ∣ y :=
  dvd_left_of_dvd_add (Int.add_comm x y ▸ hxy) hx

private theorem eq_one_of_dvd_coords {k : ℕ} {a b c : ℤ}
    (hprim : a.natAbs.gcd (b.natAbs.gcd c.natAbs) = 1)
    (ha : (k : ℤ) ∣ a) (hb : (k : ℤ) ∣ b) (hc : (k : ℤ) ∣ c) : k = 1 := by
  apply Nat.dvd_one.mp
  rw [← hprim]
  exact Nat.dvd_gcd (Int.natCast_dvd.mp ha) (Nat.dvd_gcd (Int.natCast_dvd.mp hb)
    (Int.natCast_dvd.mp hc))

/-- The arithmetic consequences of the normal-image tests for a signed primitive triple.
Here primitivity is the natural gcd of the three absolute coordinates being one.
The proof needs neither primality of `q` nor coprimality of `q` and `F`, and uses no
sign restriction on the coordinates. -/
public theorem visible_factors {d e q F g : ℕ} {a b c : ℤ}
    (hg : 0 < g) (hcop : (q * F).Coprime (d * e))
    (hprim : a.natAbs.gcd (b.natAbs.gcd c.natAbs) = 1)
    (hgd : g ∣ d * e)
    (hN : (g : ℤ) ∣ (q : ℤ) * a + (F : ℤ) * (b + c))
    (hbd : (g : ℤ) ∣ b * (d : ℤ)) (hce : (g : ℤ) ∣ c * (e : ℤ)) :
    let G := d.gcd e
    let ell := d * e / g
    let A := g / g.gcd e
    let B := g / g.gcd d
    g ∣ d.lcm e ∧ G ∣ ell ∧ A * B = g / g.gcd G ∧ A.gcd B = 1 ∧
      ((A : ℤ) ∣ c) ∧ ((B : ℤ) ∣ b) ∧ a.natAbs.gcd (A * B) = 1 := by
  intro G ell A B
  have hAc : (A : ℤ) ∣ c := quotient_dvd_coord hg hce
  have hBb : (B : ℤ) ∣ b := quotient_dvd_coord hg hbd
  have hAg : A ∣ g := Nat.div_dvd_of_dvd (Nat.gcd_dvd_left g e)
  have hBg : B ∣ g := Nat.div_dvd_of_dvd (Nat.gcd_dvd_left g d)
  obtain ⟨hq, hF⟩ := Nat.coprime_mul_iff_right.mp (hcop.symm.coprime_dvd_left hgd)
  have hdvdN {k : ℕ} (hk : k ∣ g) : (k : ℤ) ∣ (q : ℤ) * a + (F : ℤ) * (b + c) :=
    Int.dvd_trans (Int.natCast_dvd_natCast.mpr hk) hN
  -- A shared factor of A and B divides both coordinates, and the normal test forces it into a.
  have hAB : A.Coprime B := by
    let k := A.gcd B
    have hkA : k ∣ A := Nat.gcd_dvd_left A B
    have hkB : k ∣ B := Nat.gcd_dvd_right A B
    have hkg : k ∣ g := hkA.trans hAg
    have hkb : (k : ℤ) ∣ b := Int.dvd_trans (Int.natCast_dvd_natCast.mpr hkB) hBb
    have hkc : (k : ℤ) ∣ c := Int.dvd_trans (Int.natCast_dvd_natCast.mpr hkA) hAc
    have hka : (k : ℤ) ∣ a := by
      apply dvd_coord_of_coprime_mul (hq.coprime_dvd_left hkg)
      exact dvd_left_of_dvd_add (hdvdN hkg) (Int.dvd_mul_of_dvd_right (Int.dvd_add hkb hkc))
    exact eq_one_of_dvd_coords hprim hka hkb hkc
  -- The part of g left after its gcd with the lcm divides both A and B, so it is one.
  have hgL : g ∣ d.lcm e := by
    let L := d.lcm e
    let K := g / g.gcd L
    have hKd {t : ℕ} (ht : t ∣ L) : K ∣ g / g.gcd t :=
      (Nat.div_dvd_div_iff_left hg (Nat.gcd_dvd_left g L) (Nat.gcd_dvd_left g t)).mpr
        (Nat.gcd_dvd_gcd_of_dvd_right g ht)
    have hK : K = 1 := Nat.eq_one_of_dvd_coprimes hAB (hKd (Nat.dvd_lcm_right d e))
      (hKd (Nat.dvd_lcm_left d e))
    have hexact : K * g.gcd L = g := Nat.div_mul_cancel (Nat.gcd_dvd_left g L)
    rw [hK, one_mul] at hexact
    exact Nat.gcd_eq_left_iff_dvd.mp hexact
  have hGell : G ∣ ell := by
    apply (Nat.dvd_div_iff_mul_dvd hgd).mpr
    rw [Nat.mul_comm g G, ← Nat.gcd_mul_lcm d e]
    exact Nat.mul_dvd_mul_left G hgL
  have hprod : A * B = g / g.gcd G := calc
    A * B = A.lcm B := hAB.lcm_eq_mul.symm
    _ = g / ((g.gcd e).gcd (g.gcd d)) :=
      Nat.div_lcm_eq_div_gcd (Nat.gcd_dvd_left g e) (Nat.gcd_dvd_left g d)
    _ = g / g.gcd G := by rw [Nat.gcd_gcd_gcd_left, Nat.gcd_comm e d]
  -- A factor of |a| and either visible factor divides b+c by cancelling F in the test.
  have hsum {k : ℕ} (hkg : k ∣ g) (hka : (k : ℤ) ∣ a) : (k : ℤ) ∣ b + c := by
    apply dvd_coord_of_coprime_mul (hF.coprime_dvd_left hkg)
    exact dvd_right_of_dvd_add (hdvdN hkg) (Int.dvd_mul_of_dvd_right hka)
  have haA : a.natAbs.Coprime A := by
    let k := a.natAbs.gcd A
    have hkA : k ∣ A := Nat.gcd_dvd_right _ _
    have hka : (k : ℤ) ∣ a := Int.natCast_dvd.mpr (Nat.gcd_dvd_left _ _)
    have hkc : (k : ℤ) ∣ c := Int.dvd_trans (Int.natCast_dvd_natCast.mpr hkA) hAc
    have hkb : (k : ℤ) ∣ b := dvd_left_of_dvd_add (hsum (hkA.trans hAg) hka) hkc
    exact eq_one_of_dvd_coords hprim hka hkb hkc
  have haB : a.natAbs.Coprime B := by
    let k := a.natAbs.gcd B
    have hkB : k ∣ B := Nat.gcd_dvd_right _ _
    have hka : (k : ℤ) ∣ a := Int.natCast_dvd.mpr (Nat.gcd_dvd_left _ _)
    have hkb : (k : ℤ) ∣ b := Int.dvd_trans (Int.natCast_dvd_natCast.mpr hkB) hBb
    have hkc : (k : ℤ) ∣ c := dvd_right_of_dvd_add (hsum (hkB.trans hBg) hka) hkb
    exact eq_one_of_dvd_coords hprim hka hkb hkc
  exact ⟨hgL, hGell, hprod, hAB.gcd_eq_one, hAc, hBb, (haA.mul_right haB).gcd_eq_one⟩

end NormalImageVisibleFactors
