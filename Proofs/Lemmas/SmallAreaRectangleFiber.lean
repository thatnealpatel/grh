module

public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.NumberTheory.Divisors
import Mathlib.Data.Int.Interval
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Small-area rectangle fibers at a fixed denominator pair

Source: `e98751e2:.godel/alice/gap-area-rectangles.md:9–21`, used in the
small-area deletion before the quarter-root estimate at lines 23–32. The
shared inputs can already have been thinned by the reciprocal tests of
`62cb33e1:.godel/alice/same-input-second-bracket.md:23–27,49–55`.

Only the nonzero determinant level is counted here, with the reference at
smaller output gcd. We do not estimate the zero level or the large-area
remainder. The finset consists of the complete inputs, not list realizations.
When the output window is given by positive real endpoints, `lo` and `hi`
are their ceiling and floor: the outputs themselves are positive integers.

Owning check session: `01a20bcd-0340-73f5-9604-3b5724a0ee86` (rectangle writer).
-/

public section

open Finset

namespace SmallAreaRectangleFiber

/-- Fixed denominators, modulus, input label, gap cutoff, and output window. -/
structure Parameters where
  d : ℕ
  e : ℕ
  q : ℕ
  F : ℕ
  H : ℕ
  lo : ℕ
  hi : ℕ
  d_pos : 0 < d
  e_pos : 0 < e
  distinct : d ≠ e
  q_pos : 0 < q
  q_unit_e : q.Coprime e
  gap_width : 2 * H < F
  lo_pos : 0 < lo
  lo_le_hi : lo ≤ hi

/-- The specified first-output data on the two incidences of an input. -/
structure Rows where
  yd : ℕ → ℕ
  ye : ℕ → ℕ
  bd : ℕ → ℤ
  be : ℕ → ℤ

/-- The two row identities at a complete shared input and the relevant unit
and size conditions. No condition is imposed on the data off the input set. -/
structure Valid (P : Parameters) (R : Rows) (v : ℕ) : Prop where
  input_pos : 0 < v
  row_d : (v : ℤ) = (P.d : ℤ) * R.yd v + (P.q : ℤ) * R.bd v
  row_e : (v : ℤ) = (P.e : ℤ) * R.ye v + (P.q : ℤ) * R.be v
  label_dvd : P.F ∣ v
  unit_q : v.Coprime P.q
  unit_d : v.Coprime P.d
  unit_e : v.Coprime P.e
  bd_le : (R.bd v).natAbs ≤ P.H
  be_le : (R.be v).natAbs ≤ P.H
  yd_lo : P.lo ≤ R.yd v
  yd_hi : R.yd v ≤ P.hi
  ye_lo : P.lo ≤ R.ye v
  ye_hi : R.ye v ≤ P.hi

@[expose] def Rows.outputGcd (R : Rows) (v : ℕ) : ℕ := (R.yd v).gcd (R.ye v)

@[expose] def Rows.gapGcd (R : Rows) (v : ℕ) : ℕ := (R.bd v).gcd (R.be v)

@[expose] def Rows.area (R : Rows) (r v : ℕ) : ℤ := R.bd r * R.be v - R.be r * R.bd v

@[expose] def Rows.outputDet (R : Rows) (r v : ℕ) : ℤ :=
  (R.yd r : ℤ) * R.ye v - (R.ye r : ℤ) * R.yd v

@[expose] def Rows.level (R : Rows) (P : Parameters) (r v : ℕ) : ℤ :=
  R.outputDet r v / (P.q : ℤ)

@[expose] def areaStep (P : Parameters) (R : Rows) (r : ℕ) : ℕ :=
  P.d.gcd P.e * R.gapGcd r

private theorem cancel_unit {a b : ℕ} {c : ℤ} (hab : a.Coprime b)
    (h : (a : ℤ) ∣ (b : ℤ) * c) : (a : ℤ) ∣ c := by
  rw [Int.ofNat_dvd_left, Int.natAbs_mul, Int.natAbs_natCast] at h
  exact Int.ofNat_dvd_left.mpr (hab.dvd_of_dvd_mul_left h)

variable {P : Parameters} {R : Rows} {r v w : ℕ}

private theorem row_difference (h : Valid P R v) :
    (P.q : ℤ) * (R.bd v - R.be v) = (P.e : ℤ) * R.ye v - (P.d : ℤ) * R.yd v := by
  linear_combination h.row_e - h.row_d

/-- The level is the exact integer quotient at two actual shared inputs. -/
theorem level_mul (hr : Valid P R r) (hv : Valid P R v) :
    R.level P r v * (P.q : ℤ) = R.outputDet r v := by
  apply Int.ediv_mul_cancel
  apply cancel_unit P.q_unit_e
  refine ⟨(R.yd r : ℤ) * (R.bd v - R.be v) - (R.yd v : ℤ) * (R.bd r - R.be r), ?_⟩
  unfold Rows.outputDet
  linear_combination (R.yd v : ℤ) * row_difference hr - (R.yd r : ℤ) * row_difference hv

/-- The determinant identity controlling the residue of the level. -/
theorem area_level_identity (hr : Valid P R r) (hv : Valid P R v) :
    (P.d : ℤ) * P.e * R.level P r v =
      (r : ℤ) * (R.bd v - R.be v) - (v : ℤ) * (R.bd r - R.be r) +
        (P.q : ℤ) * R.area r v := by
  have hq : (P.q : ℤ) ≠ 0 := by exact_mod_cast P.q_pos.ne'
  apply Int.eq_of_mul_eq_mul_right hq
  unfold Rows.area
  have hl := level_mul hr hv
  unfold Rows.outputDet at hl
  linear_combination (P.d : ℤ) * P.e * hl -
    ((P.e : ℤ) * R.ye v) * hr.row_d + ((P.e : ℤ) * R.ye r) * hv.row_d -
    ((r : ℤ) - (P.q : ℤ) * R.bd r) * hv.row_e +
    ((v : ℤ) - (P.q : ℤ) * R.bd v) * hr.row_e

/-- An explicit level cutoff supplied by the two rows and the output and gap
windows. It is independent of the gap label `F`. -/
theorem level_natAbs_le (hr : Valid P R r) (hv : Valid P R v) :
    (R.level P r v).natAbs ≤ 4 * P.H * P.hi / P.e := by
  have hq : (P.q : ℤ) ≠ 0 := by exact_mod_cast P.q_pos.ne'
  have h : (P.e : ℤ) * R.level P r v =
      (R.yd r : ℤ) * (R.bd v - R.be v) - (R.yd v : ℤ) * (R.bd r - R.be r) := by
    apply Int.eq_of_mul_eq_mul_right hq
    have hl := level_mul hr hv
    unfold Rows.outputDet at hl
    linear_combination (P.e : ℤ) * hl +
      (R.yd v : ℤ) * row_difference hr - (R.yd r : ℤ) * row_difference hv
  have hAbs := congrArg Int.natAbs h
  simp only [Int.natAbs_mul, Int.natAbs_natCast] at hAbs
  apply (Nat.le_div_iff_mul_le P.e_pos).mpr
  rw [Nat.mul_comm (R.level P r v).natAbs, hAbs]
  have hgap {x : ℕ} (hx : Valid P R x) : (R.bd x - R.be x).natAbs ≤ P.H + P.H :=
    (Int.natAbs_sub_le _ _).trans (Nat.add_le_add hx.bd_le hx.be_le)
  calc
    _ ≤ R.yd r * (R.bd v - R.be v).natAbs + R.yd v * (R.bd r - R.be r).natAbs := by
      simpa only [Int.natAbs_mul, Int.natAbs_natCast] using
        Int.natAbs_sub_le ((R.yd r : ℤ) * (R.bd v - R.be v))
          ((R.yd v : ℤ) * (R.bd r - R.be r))
    _ ≤ P.hi * (P.H + P.H) + P.hi * (P.H + P.H) :=
      Nat.add_le_add (Nat.mul_le_mul hr.yd_hi (hgap hv)) (Nat.mul_le_mul hv.yd_hi (hgap hr))
    _ = _ := by ring

/-- A fixed signed area fixes a single residue class modulo the input label. -/
theorem label_dvd_level_sub (hr : Valid P R r) (hv : Valid P R v) (hw : Valid P R w)
    (hA : R.area r v = R.area r w) : (P.F : ℤ) ∣ R.level P r v - R.level P r w := by
  have hunit : P.F.Coprime (P.d * P.e) :=
    (hr.unit_d.mul_right hr.unit_e).of_dvd_left hr.label_dvd
  apply cancel_unit hunit
  rw [Nat.cast_mul, mul_sub, area_level_identity hr hv, area_level_identity hr hw, hA]
  have hrF : (P.F : ℤ) ∣ (r : ℤ) := by exact_mod_cast hr.label_dvd
  have hvF : (P.F : ℤ) ∣ (v : ℤ) := by exact_mod_cast hv.label_dvd
  have hwF : (P.F : ℤ) ∣ (w : ℤ) := by exact_mod_cast hw.label_dvd
  rw [add_sub_add_right_eq_sub]
  exact dvd_sub (dvd_sub (dvd_mul_of_dvd_left hrF _) (dvd_mul_of_dvd_left hvF _))
    (dvd_sub (dvd_mul_of_dvd_left hrF _) (dvd_mul_of_dvd_left hwF _))

private theorem gap_difference_dvd (hv : Valid P R v) :
    (P.d.gcd P.e : ℤ) ∣ R.bd v - R.be v := by
  apply cancel_unit (P.q_unit_e.of_dvd_right (Nat.gcd_dvd_right P.d P.e)).symm
  rw [row_difference hv]
  have hd : (P.d.gcd P.e : ℤ) ∣ (P.d : ℤ) := by exact_mod_cast Nat.gcd_dvd_left P.d P.e
  have he : (P.d.gcd P.e : ℤ) ∣ (P.e : ℤ) := by exact_mod_cast Nat.gcd_dvd_right P.d P.e
  exact dvd_sub (dvd_mul_of_dvd_left he _) (dvd_mul_of_dvd_left hd _)

/-- Area divisibility uses both rows and the reference's input/denominator
primitivity. The two gcd factors are coprime, not merely independent divisors. -/
theorem areaStep_dvd_area (hr : Valid P R r) (hv : Valid P R v) :
    (areaStep P R r : ℤ) ∣ R.area r v := by
  let g := P.d.gcd P.e
  let k := R.gapGcd r
  have hbd : (k : ℤ) ∣ R.bd r := Int.gcd_dvd_left ..
  have hbe : (k : ℤ) ∣ R.be r := Int.gcd_dvd_right ..
  have hk : (k : ℤ) ∣ R.area r v :=
    dvd_sub (dvd_mul_of_dvd_left hbd _) (dvd_mul_of_dvd_left hbe _)
  have hg : (g : ℤ) ∣ R.area r v := by
    rw [Rows.area, show R.bd r * R.be v - R.be r * R.bd v =
      (R.bd r - R.be r) * R.bd v - R.bd r * (R.bd v - R.be v) by ring]
    exact dvd_sub (dvd_mul_of_dvd_left (gap_difference_dvd hr) _)
      (dvd_mul_of_dvd_right (gap_difference_dvd hv) _)
  have hcop : g.Coprime k := by
    let c := g.gcd k
    have hcd : c ∣ P.d := (Nat.gcd_dvd_left g k).trans (Nat.gcd_dvd_left P.d P.e)
    have hck : (c : ℤ) ∣ (k : ℤ) := by exact_mod_cast Nat.gcd_dvd_right g k
    have hcd' : (c : ℤ) ∣ (P.d : ℤ) := by exact_mod_cast hcd
    have hcr' : (c : ℤ) ∣ (r : ℤ) := by
      rw [hr.row_d]
      exact dvd_add (dvd_mul_of_dvd_left hcd' _) (dvd_mul_of_dvd_right (hck.trans hbd) _)
    have hcr : c ∣ r := by exact_mod_cast hcr'
    have hc1 : c ∣ 1 := by simpa only [hr.unit_d.gcd_eq_one] using Nat.dvd_gcd hcr hcd
    exact Nat.dvd_one.mp hc1
  exact Int.ofNat_dvd_left.mpr <|
    hcop.mul_dvd_of_dvd_of_dvd (Int.ofNat_dvd_left.mp hg) (Int.ofNat_dvd_left.mp hk)

private theorem outputGcd_pos (hv : Valid P R v) : 0 < R.outputGcd v :=
  Nat.gcd_pos_of_pos_left _ (P.lo_pos.trans_le hv.yd_lo)

private theorem outputGcd_coprime_q (hv : Valid P R v) : (R.outputGcd v).Coprime P.q := by
  let m := R.outputGcd v
  let c := m.gcd P.q
  have hcq := Nat.gcd_dvd_right m P.q
  have hcy : c ∣ R.yd v := (Nat.gcd_dvd_left m P.q).trans (Nat.gcd_dvd_left _ _)
  have hcq' : (c : ℤ) ∣ (P.q : ℤ) := by exact_mod_cast hcq
  have hcy' : (c : ℤ) ∣ (R.yd v : ℤ) := by exact_mod_cast hcy
  have hcv' : (c : ℤ) ∣ (v : ℤ) := by
    rw [hv.row_d]
    exact dvd_add (dvd_mul_of_dvd_right hcy' _) (dvd_mul_of_dvd_left hcq' _)
  have hcv : c ∣ v := by exact_mod_cast hcv'
  have hc1 : c ∣ 1 := by simpa only [hv.unit_q.gcd_eq_one] using Nat.dvd_gcd hcv hcq
  exact Nat.dvd_one.mp hc1

/-- The actual candidate gcd divides the signed level after removing `q`. -/
theorem outputGcd_dvd_level (hr : Valid P R r) (hv : Valid P R v) :
    R.outputGcd v ∣ (R.level P r v).natAbs := by
  apply Int.ofNat_dvd_left.mp
  apply cancel_unit (outputGcd_coprime_q hv)
  rw [mul_comm, level_mul hr hv, Rows.outputDet]
  have hd : (R.outputGcd v : ℤ) ∣ (R.yd v : ℤ) := by exact_mod_cast Nat.gcd_dvd_left _ _
  have he : (R.outputGcd v : ℤ) ∣ (R.ye v : ℤ) := by exact_mod_cast Nat.gcd_dvd_right _ _
  exact dvd_sub (dvd_mul_of_dvd_right he _) (dvd_mul_of_dvd_right hd _)

/-- In a fixed level and output-gcd fiber the first output coordinates are
congruent modulo `G' * (y_d / G)`, where `y_d` is the reference coordinate. -/
theorem output_spacing (hr : Valid P R r) (hv : Valid P R v) (hw : Valid P R w)
    (hL : R.level P r v = R.level P r w) (hG : R.outputGcd v = R.outputGcd w) :
    ((R.outputGcd v * (R.yd r / R.outputGcd r) : ℕ) : ℤ) ∣
      (R.yd v : ℤ) - R.yd w := by
  let G := R.outputGcd r
  let m := R.outputGcd v
  let a := R.yd r / G
  let b := R.ye r / G
  have ha : (G : ℤ) * (a : ℤ) = (R.yd r : ℤ) := by
    exact_mod_cast Nat.mul_div_cancel' (Nat.gcd_dvd_left (R.yd r) (R.ye r))
  have hb : (G : ℤ) * (b : ℤ) = (R.ye r : ℤ) := by
    exact_mod_cast Nat.mul_div_cancel' (Nat.gcd_dvd_right (R.yd r) (R.ye r))
  have hpair (x : ℕ) (hx : R.outputGcd x = m) :
      ((m : ℤ) ∣ (R.yd x : ℤ)) ∧ ((m : ℤ) ∣ (R.ye x : ℤ)) := by
    rw [← hx]
    exact ⟨by exact_mod_cast Nat.gcd_dvd_left (R.yd x) (R.ye x),
      by exact_mod_cast Nat.gcd_dvd_right (R.yd x) (R.ye x)⟩
  obtain ⟨u, hu⟩ := dvd_sub (hpair v rfl).1 (hpair w hG.symm).1
  obtain ⟨z, hz⟩ := dvd_sub (hpair v rfl).2 (hpair w hG.symm).2
  have hrel : (R.yd r : ℤ) * ((R.ye v : ℤ) - R.ye w) =
      (R.ye r : ℤ) * ((R.yd v : ℤ) - R.yd w) := by
    have hv' := level_mul hr hv
    have hw' := level_mul hr hw
    rw [hL] at hv'
    unfold Rows.outputDet at hv' hw'
    linear_combination hw' - hv'
  rw [← ha, ← hb, hu, hz] at hrel
  have hGm : (G : ℤ) * (m : ℤ) ≠ 0 := mul_ne_zero
    (by exact_mod_cast (outputGcd_pos hr).ne') (by exact_mod_cast (outputGcd_pos hv).ne')
  have hnorm : (a : ℤ) * z = (b : ℤ) * u := by
    apply Int.eq_of_mul_eq_mul_left hGm
    linear_combination hrel
  have hab : a.Coprime b := Nat.coprime_div_gcd_div_gcd (outputGcd_pos hr)
  obtain ⟨t, ht⟩ := cancel_unit hab (hnorm ▸ dvd_mul_right (a : ℤ) z)
  refine ⟨t, ?_⟩
  change (R.yd v : ℤ) - R.yd w = ((m * a : ℕ) : ℤ) * t
  rw [hu, ht, Nat.cast_mul, mul_assoc]

/-- A first output coordinate determines the actual input. Recovery uses the
first row and the full signed gap width. -/
theorem input_eq_of_yd_eq (hv : Valid P R v) (hw : Valid P R w)
    (hy : R.yd v = R.yd w) : v = w := by
  have hunit : P.F.Coprime P.q := hv.unit_q.of_dvd_left hv.label_dvd
  have hvF : (P.F : ℤ) ∣ (v : ℤ) := by exact_mod_cast hv.label_dvd
  have hwF : (P.F : ℤ) ∣ (w : ℤ) := by exact_mod_cast hw.label_dvd
  have heq : (v : ℤ) - w = (P.q : ℤ) * (R.bd v - R.bd w) := by
    rw [hv.row_d, hw.row_d, hy]
    ring
  have hdiv := dvd_sub hvF hwF
  rw [heq] at hdiv
  have hlt : (R.bd v - R.bd w).natAbs < (P.F : ℤ).natAbs := by
    rw [Int.natAbs_natCast]
    exact (Int.natAbs_sub_le _ _).trans_lt ((Nat.add_le_add hv.bd_le hw.bd_le).trans_lt
      (by simpa only [two_mul] using P.gap_width))
  have hb := Int.eq_zero_of_dvd_of_natAbs_lt_natAbs (cancel_unit hunit hdiv) hlt
  have hvw : (v : ℤ) = w := by simpa [hb, sub_eq_zero] using heq
  exact_mod_cast hvw

private theorem card_of_spaced {α : Type*} {s : Finset α} {f : α → ℤ} {lo : ℤ}
    {width step : ℕ} (hp : 0 < step)
    (hbox : ∀ x ∈ s, lo ≤ f x ∧ f x ≤ lo + width)
    (hspace : ∀ x ∈ s, ∀ y ∈ s, (step : ℤ) ∣ f x - f y)
    (hinj : Set.InjOn f (s : Set α)) : s.card ≤ 1 + width / step := by
  have hpZ : 0 < (step : ℤ) := by exact_mod_cast hp
  calc
    s.card ≤ (Icc (0 : ℤ) ((width / step : ℕ) : ℤ)).card := by
      apply card_le_card_of_injOn (fun x => (f x - lo) / (step : ℤ))
      · intro x hx
        obtain ⟨hl, hu⟩ := hbox x hx
        apply mem_Icc.mpr
        refine ⟨Int.ediv_nonneg (sub_nonneg.mpr hl) hpZ.le, ?_⟩
        rw [Int.natCast_ediv]
        exact Int.ediv_le_ediv hpZ (by omega)
      · intro x hx y hy hxy
        change (f x - lo) / (step : ℤ) = (f y - lo) / (step : ℤ) at hxy
        have hs := Int.add_ediv_of_dvd_right (a := f y - lo) (hspace x hx y hy)
        rw [show f y - lo + (f x - f y) = f x - lo by ring, hxy] at hs
        have hz : (f x - f y) / (step : ℤ) = 0 := by omega
        have hc := Int.ediv_mul_cancel (hspace x hx y hy)
        rw [hz, zero_mul] at hc
        exact hinj hx hy (by omega)
    _ = 1 + width / step := by
      have hn : 0 ≤ ((width / step : ℕ) : ℤ) := Int.natCast_nonneg _
      rw [Int.card_Icc]
      omega

/-- With a fixed level and candidate gcd `m`, the oriented spacing is at least
`lo`. This counts complete inputs, not possible representations of an input. -/
theorem card_le_of_level_of_gcd {s : Finset ℕ} {L : ℤ} {m : ℕ} (hr : Valid P R r)
    (hs : ∀ v ∈ s, Valid P R v ∧ R.level P r v = L ∧ R.outputGcd v = m)
    (horient : R.outputGcd r ≤ m) : s.card ≤ 1 + (P.hi - P.lo) / P.lo := by
  let a := R.yd r / R.outputGcd r
  have hy : R.outputGcd r * a = R.yd r := Nat.mul_div_cancel' (Nat.gcd_dvd_left _ _)
  have hstep : P.lo ≤ m * a := hr.yd_lo.trans (hy ▸ Nat.mul_le_mul_right a horient)
  have hlo : ((P.hi - P.lo : ℕ) : ℤ) = (P.hi : ℤ) - P.lo := Int.natCast_sub P.lo_le_hi
  calc
    s.card ≤ 1 + (P.hi - P.lo) / (m * a) := by
      apply card_of_spaced (f := fun v => (R.yd v : ℤ)) (lo := (P.lo : ℤ))
        (P.lo_pos.trans_le hstep)
      · intro v hv
        obtain ⟨h, _, _⟩ := hs v hv
        rw [hlo]
        exact ⟨by exact_mod_cast h.yd_lo, by simpa using (show (R.yd v : ℤ) ≤ (P.hi : ℤ) by
          exact_mod_cast h.yd_hi)⟩
      · intro v hv w hw
        obtain ⟨hv', hvL, hvG⟩ := hs v hv
        obtain ⟨hw', hwL, hwG⟩ := hs w hw
        rw [← hvG]
        exact output_spacing hr hv' hw' (hvL.trans hwL.symm) (hvG.trans hwG.symm)
      · intro v hv w hw h
        change (R.yd v : ℤ) = (R.yd w : ℤ) at h
        exact input_eq_of_yd_eq (hs v hv).1 (hs w hw).1 (by exact_mod_cast h)
    _ ≤ _ := Nat.add_le_add_left (Nat.div_le_div_left hstep P.lo_pos) 1

/-- Nonzero fixed-level fiber bound (in particular at any fixed signed area).
The output gcd is charged as a divisor of `|L|`; its fibers are counted using
`card_le_of_level_of_gcd`. -/
theorem card_le_of_level {s : Finset ℕ} {L : ℤ} (hr : Valid P R r) (hL : L ≠ 0)
    (hs : ∀ v ∈ s, Valid P R v ∧ R.level P r v = L ∧ R.outputGcd r ≤ R.outputGcd v) :
    s.card ≤ L.natAbs.divisors.card * (1 + (P.hi - P.lo) / P.lo) := by
  have himage : (s.image R.outputGcd) ⊆ L.natAbs.divisors := by
    intro m hm
    obtain ⟨v, hv, rfl⟩ := mem_image.mp hm
    obtain ⟨hv', hvL, _⟩ := hs v hv
    have hd := outputGcd_dvd_level hr hv'
    rw [hvL] at hd
    exact Nat.mem_divisors.mpr ⟨hd, Int.natAbs_eq_zero.not.mpr hL⟩
  have hf := card_le_mul_card_image (f := R.outputGcd) s (1 + (P.hi - P.lo) / P.lo) (by
    intro m hm
    obtain ⟨w, hw, rfl⟩ := mem_image.mp hm
    apply card_le_of_level_of_gcd (L := L) hr _ (hs w hw).2.2
    intro v hv
    obtain ⟨hv', hvG⟩ := mem_filter.mp hv
    exact ⟨(hs v hv').1, (hs v hv').2.1, hvG⟩)
  rw [mul_comm] at hf
  exact hf.trans (Nat.mul_le_mul_right _ (card_le_card himage))

private theorem mem_symmetric_interval {z : ℤ} {N : ℕ} (h : z.natAbs ≤ N) :
    z ∈ Icc (-(N : ℤ)) (N : ℤ) := by
  apply mem_Icc.mpr (abs_le.mp ?_)
  rw [Int.abs_eq_natAbs]
  exact_mod_cast h

private theorem card_area_image {s : Finset ℕ} {T : ℕ} (hr : Valid P R r)
    (hs : ∀ v ∈ s, Valid P R v ∧ (R.area r v).natAbs ≤ T * areaStep P R r) :
    (s.image (R.area r)).card ≤ 2 * T + 1 := by
  let a := areaStep P R r
  have hmem {z : ℤ} (hz : z ∈ s.image (R.area r)) :
      ((a : ℤ) ∣ z) ∧ z.natAbs ≤ T * a := by
    obtain ⟨v, hv, rfl⟩ := mem_image.mp hz
    exact ⟨areaStep_dvd_area hr (hs v hv).1, (hs v hv).2⟩
  calc
    (s.image (R.area r)).card ≤ (Icc (-(T : ℤ)) (T : ℤ)).card := by
      apply card_le_card_of_injOn (fun z : ℤ => z / (a : ℤ))
      · intro z hz
        obtain ⟨hd, hb⟩ := hmem hz
        apply mem_symmetric_interval
        by_cases ha : a = 0
        · simp [ha]
        · have hcancel := Int.ediv_mul_cancel hd
          rw [← hcancel, Int.natAbs_mul, Int.natAbs_natCast] at hb
          exact Nat.le_of_mul_le_mul_right hb (Nat.pos_of_ne_zero ha)
      · intro z hz w hw heq
        exact (Int.ediv_mul_cancel (hmem hz).1).symm.trans
          ((congrArg (fun x : ℤ => x * (a : ℤ)) heq).trans
            (Int.ediv_mul_cancel (hmem hw).1))
    _ = 2 * T + 1 := by rw [Int.card_Icc]; omega

private theorem card_level_image {s : Finset ℕ} {M : ℕ} {A : ℤ} (hr : Valid P R r)
    (hs : ∀ v ∈ s, Valid P R v ∧ (R.level P r v).natAbs ≤ M ∧ R.area r v = A) :
    (s.image (R.level P r)).card ≤ 1 + 2 * M / P.F := by
  have hF : 0 < P.F := (Nat.zero_le _).trans_lt P.gap_width
  apply card_of_spaced (f := id) (lo := -(M : ℤ)) hF
  · intro z hz
    obtain ⟨v, hv, rfl⟩ := mem_image.mp hz
    obtain ⟨hl, hu⟩ := mem_Icc.mp (mem_symmetric_interval (hs v hv).2.1)
    refine ⟨hl, ?_⟩
    change R.level P r v ≤ -(M : ℤ) + ((2 * M : ℕ) : ℤ)
    push_cast
    omega
  · intro z hz w hw
    obtain ⟨v, hv, rfl⟩ := mem_image.mp hz
    obtain ⟨u, hu, rfl⟩ := mem_image.mp hw
    obtain ⟨hv', _, hAv⟩ := hs v hv
    obtain ⟨hu', _, hAu⟩ := hs u hu
    exact label_dvd_level_sub hr hv' hu' (hAv.trans hAu.symm)
  · intro x hx y hy h
    exact h

/-- Maximum divisor count on the positive integers at most `M`. At `M = 0`
the interval is empty and this is zero. -/
@[expose] def maxDivisorCount (M : ℕ) : ℕ := (Icc 1 M).sup fun n => n.divisors.card

/-- The nonzero-level candidates in the smaller-output-gcd orientation for
one reference. `T` is the integer cutoff: the normalized signed area charge
is integral, so a nonnegative real cutoff uses its floor here. -/
@[expose] def smallCandidates (P : Parameters) (R : Rows) (s : Finset ℕ) (r T M : ℕ) :
    Finset ℕ := s.filter fun v => R.level P r v ≠ 0 ∧ (R.level P r v).natAbs ≤ M ∧
      R.outputGcd r ≤ R.outputGcd v ∧ (R.area r v).natAbs ≤ T * areaStep P R r

/-- The small-area nonzero-level deletion count for one fixed shared input.
There is no premise comparing the determinant height `M` with `F`. -/
theorem card_smallCandidates {s : Finset ℕ} {T M : ℕ} (hr : Valid P R r)
    (hs : ∀ v ∈ s, Valid P R v) :
    (smallCandidates P R s r T M).card ≤
      (2 * T + 1) * (1 + 2 * M / P.F) * maxDivisorCount M * (1 + (P.hi - P.lo) / P.lo) := by
  let t := smallCandidates P R s r T M
  let D := maxDivisorCount M * (1 + (P.hi - P.lo) / P.lo)
  let K := 1 + 2 * M / P.F
  have ht {v : ℕ} (hv : v ∈ t) : Valid P R v ∧ R.level P r v ≠ 0 ∧
      (R.level P r v).natAbs ≤ M ∧ R.outputGcd r ≤ R.outputGcd v ∧
      (R.area r v).natAbs ≤ T * areaStep P R r := by
    obtain ⟨hv', hc⟩ := mem_filter.mp hv
    exact ⟨hs v hv', hc⟩
  have hArea := card_area_image hr (s := t) (T := T) (fun v hv => ⟨(ht hv).1, (ht hv).2.2.2.2⟩)
  have hEach (A : ℤ) : (t.filter fun v => R.area r v = A).card ≤ D * K := by
    let u := t.filter fun v => R.area r v = A
    have hu {v : ℕ} (hv : v ∈ u) := mem_filter.mp hv
    have hImage : (u.image (R.level P r)).card ≤ K :=
      card_level_image hr (M := M) (A := A) (fun v hv =>
        ⟨(ht (hu hv).1).1, (ht (hu hv).1).2.2.1, (hu hv).2⟩)
    refine (card_le_mul_card_image (f := R.level P r) u D ?_).trans
      (Nat.mul_le_mul_left D hImage)
    intro L hL
    obtain ⟨w, hw, hwL⟩ := mem_image.mp hL
    have hne : L ≠ 0 := hwL ▸ (ht (hu hw).1).2.1
    have hM : L.natAbs ≤ M := hwL ▸ (ht (hu hw).1).2.2.1
    have hpos : 0 < L.natAbs := Nat.pos_of_ne_zero (Int.natAbs_eq_zero.not.mpr hne)
    have hmax : L.natAbs.divisors.card ≤ maxDivisorCount M :=
      Finset.le_sup (f := fun n : ℕ => n.divisors.card) (mem_Icc.mpr ⟨hpos, hM⟩)
    refine (card_le_of_level hr hne ?_).trans (Nat.mul_le_mul_right _ hmax)
    intro v hv
    obtain ⟨hv', hvL⟩ := mem_filter.mp hv
    have hh := ht (hu hv').1
    exact ⟨hh.1, hvL, hh.2.2.2.1⟩
  have h := (card_le_mul_card_image (f := R.area r) t (D * K) (fun A _ => hEach A)).trans
    (Nat.mul_le_mul_left (D * K) hArea)
  simpa only [D, K, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using h

/-- The real area test is exactly the integral test at `⌊T⌋₊`, including
when the gap gcd vanishes and the only area is zero. -/
theorem area_cutoff_iff (hr : Valid P R r) (hv : Valid P R v) {T : ℝ} (hT : 0 ≤ T) :
    ((R.area r v).natAbs : ℝ) ≤ T * (areaStep P R r : ℝ) ↔
      (R.area r v).natAbs ≤ Nat.floor T * areaStep P R r := by
  let a := areaStep P R r
  obtain ⟨j, hj⟩ := areaStep_dvd_area hr hv
  have hAbs : (R.area r v).natAbs = a * j.natAbs := by
    rw [hj, Int.natAbs_mul, Int.natAbs_natCast]
  change ((R.area r v).natAbs : ℝ) ≤ T * (a : ℝ) ↔
    (R.area r v).natAbs ≤ Nat.floor T * a
  by_cases ha : a = 0
  · simp [hAbs, ha]
  have hp : 0 < a := Nat.pos_of_ne_zero ha
  have hp' : 0 < (a : ℝ) := by exact_mod_cast hp
  rw [hAbs, mul_comm a j.natAbs, Nat.cast_mul, mul_le_mul_iff_of_pos_right hp']
  exact (Nat.le_floor_iff hT).symm.trans ⟨fun h => Nat.mul_le_mul_right _ h,
    fun h => Nat.le_of_mul_le_mul_right h hp⟩

/-- The complete small-area deletion count with the height cutoff derived from
both rows. The test uses the gap gcd of this reference and only charges it
when its output gcd is no larger than the candidate's. -/
theorem card_smallAreaInputs {s : Finset ℕ} {T : ℝ} (hT : 0 ≤ T) (hr : Valid P R r)
    (hs : ∀ v ∈ s, Valid P R v) :
    let M := 4 * P.H * P.hi / P.e
    (s.filter fun v => R.level P r v ≠ 0 ∧ R.outputGcd r ≤ R.outputGcd v ∧
      ((R.area r v).natAbs : ℝ) ≤ T * (areaStep P R r : ℝ)).card ≤
      (2 * Nat.floor T + 1) * (1 + 2 * M / P.F) * maxDivisorCount M *
        (1 + (P.hi - P.lo) / P.lo) := by
  dsimp only
  refine (card_le_card (t := smallCandidates P R s r (Nat.floor T) _) ?_).trans
    (card_smallCandidates hr hs)
  intro v hv
  obtain ⟨hv', hL, hG, hA⟩ := mem_filter.mp hv
  have h := hs v hv'
  exact mem_filter.mpr ⟨hv', hL, level_natAbs_le hr h, hG, (area_cutoff_iff hr h hT).mp hA⟩

/-- In a real output window one may use the original ratio in the last
factor, without losing the count for the exact integer window. In particular,
the window hypotheses hold for `lo = ⌈Aminus⌉₊`, `hi = ⌊Aplus⌋₊`. -/
theorem card_smallAreaInputs_realWindow {s : Finset ℕ} {T Aminus Aplus : ℝ}
    (hT : 0 ≤ T) (hminus : 0 < Aminus) (hlo : Aminus ≤ (P.lo : ℝ))
    (hhi : (P.hi : ℝ) ≤ Aplus) (hr : Valid P R r) (hs : ∀ v ∈ s, Valid P R v) :
    let M := 4 * P.H * P.hi / P.e
    (s.filter fun v => R.level P r v ≠ 0 ∧ R.outputGcd r ≤ R.outputGcd v ∧
      ((R.area r v).natAbs : ℝ) ≤ T * (areaStep P R r : ℝ)).card ≤
      (2 * Nat.floor T + 1) * (1 + 2 * M / P.F) * maxDivisorCount M *
        (1 + Nat.floor ((Aplus - Aminus) / Aminus)) := by
  dsimp only
  refine (card_smallAreaInputs hT hr hs).trans (Nat.mul_le_mul_left _ (Nat.add_le_add_left ?_ 1))
  let k := (P.hi - P.lo) / P.lo
  change k ≤ Nat.floor ((Aplus - Aminus) / Aminus)
  apply Nat.le_floor
  apply (le_div_iff₀ hminus).mpr
  calc
    (k : ℝ) * Aminus ≤ (k : ℝ) * (P.lo : ℝ) :=
      mul_le_mul_of_nonneg_left hlo (Nat.cast_nonneg _)
    _ ≤ ((P.hi - P.lo : ℕ) : ℝ) := by
      exact_mod_cast Nat.div_mul_le_self (P.hi - P.lo) P.lo
    _ = (P.hi : ℝ) - (P.lo : ℝ) := Nat.cast_sub P.lo_le_hi
    _ ≤ Aplus - Aminus := sub_le_sub hhi hlo

end SmallAreaRectangleFiber
