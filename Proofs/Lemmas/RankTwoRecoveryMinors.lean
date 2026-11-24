module

public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Nonvanishing of the rank-two recovery minors

Source: `3d2886df:.godel/alice/normal-factor-minors.md:17–39` (introduced in
`25765be8`, unchanged at `1de21475`), specifically the nonvanishing argument
at lines 33–37. The two small vectors are arbitrary in the transformed lattice
box; they need not be represented normals or generate the full plane lattice.
The plane hypothesis only uses that a represented point has nonzero `b` and
`c` coordinates; a coordinate that vanishes on the spanning pair vanishes on
the whole rational plane. The source unit conditions give `q` coprime to `F'`
and `d`, and `F'` coprime to `d`; `fA,fB` inherit coprimality from `P,Q`.
No saturated-basis divisibility or counting is used.

Owning check session: `01a20c3b-0de7-75d0-b4f0-194be0854305`.
-/

public section

namespace RankTwoRecoveryMinors

/-- Transformed integer coordinates in the order `(a', b, c)`. -/
abbrev Vector := Fin 3 → ℤ

/-- The numerator of the recovery coordinate `K`. -/
@[expose] def numerator (q F' : ℕ) (w : Vector) : ℤ :=
  (q : ℤ) * w 0 + (F' : ℤ) * (w 1 + w 2)

/-- The transformed lattice `L_d`, with `d = fA * fB`. -/
@[expose] def lattice (q F' fA fB : ℕ) : Set Vector :=
  {w | (fB : ℤ) ∣ w 1 ∧ (fA : ℤ) ∣ w 2 ∧ ((fA * fB : ℕ) : ℤ) ∣ numerator q F' w}

/-- The two equal transverse radii are allowed to be real, as in the source. -/
@[expose] def InBox (X Y : ℝ) (w : Vector) : Prop :=
  |(w 0 : ℝ)| ≤ X ∧ |(w 1 : ℝ)| ≤ Y ∧ |(w 2 : ℝ)| ≤ Y

/-- The exact quotient on `lattice q F' fA fB` by `d = fA * fB`. -/
@[expose] def K (q F' fA fB : ℕ) (w : Vector) : ℤ :=
  numerator q F' w / ((fA * fB : ℕ) : ℤ)

/-- The exact quotient of the third coordinate on the lattice. -/
@[expose] def C₀ (fA : ℕ) (w : Vector) : ℤ := w 2 / (fA : ℤ)

/-- The exact quotient of the second coordinate on the lattice. -/
@[expose] def B₀ (fB : ℕ) (w : Vector) : ℤ := w 1 / (fB : ℤ)

/-- Values of a form on the two vectors, in row order. -/
@[expose] def values (form : Vector → ℤ) (u v : Vector) : Fin 2 → ℤ := ![form u, form v]

/-- A two-column minor, with `u` in the first row and `v` in the second row. -/
@[expose] def minor (a b : Fin 2 → ℤ) : ℤ := a 0 * b 1 - a 1 * b 0

@[expose] def rationalize (w : Vector) : Fin 3 → ℚ := fun j ↦ (w j : ℚ)

/-- The rational plane spanned by the given pair when it is independent. -/
@[expose] def plane (u v : Vector) : Submodule ℚ (Fin 3 → ℚ) :=
  Submodule.span ℚ {rationalize u, rationalize v}

private def column (u v : Vector) (j : Fin 3) : Fin 2 → ℤ := values (fun w ↦ w j) u v

private theorem column_ne_zero_of_mem_plane {u v w : Vector}
    (hw : rationalize w ∈ plane u v) {j : Fin 3} (hj : w j ≠ 0) : column u v j ≠ 0 := by
  intro h
  have hu : u j = 0 := congrFun h 0
  have hv : v j = 0 := congrFun h 1
  obtain ⟨s, t, hst⟩ := Submodule.mem_span_pair.mp hw
  have hj' := congrFun hst j
  simp [rationalize, Pi.add_apply, Pi.smul_apply, hu, hv] at hj'
  exact hj (by exact_mod_cast hj'.symm)

private theorem false_of_zero_minors {u v : Vector}
    (hind : LinearIndependent ℚ ![rationalize u, rationalize v]) {j : Fin 3}
    (hj : column u v j ≠ 0) (h : ∀ i, minor (column u v i) (column u v j) = 0) : False := by
  -- The relation uses the two entries of the last column as coefficients.
  have hrel : (v j : ℚ) • rationalize u + (-(u j : ℚ)) • rationalize v = 0 := by
    funext i
    change (v j : ℚ) * (u i : ℚ) + (-(u j : ℚ)) * (v i : ℚ) = 0
    have hi : u i * v j - v i * u j = 0 := h i
    have hiQ : (u i : ℚ) * (v j : ℚ) - (v i : ℚ) * (u j : ℚ) = 0 := by exact_mod_cast hi
    linear_combination hiQ
  obtain ⟨hv, hu⟩ := LinearIndependent.pair_iff.mp hind _ _ hrel
  have hu' : u j = 0 := by exact_mod_cast (neg_eq_zero.mp hu)
  have hv' : v j = 0 := by exact_mod_cast hv
  apply hj
  funext i
  fin_cases i
  · exact hu'
  · exact hv'

private theorem minor_self (a : Fin 2 → ℤ) : minor a a = 0 := by
  rw [minor, mul_comm (a 0), sub_self]

private theorem minor_abs_le {a c : Fin 2 → ℤ} {X Y : ℝ}
    (ha : ∀ i, |(a i : ℝ)| ≤ X) (hc : ∀ i, |(c i : ℝ)| ≤ Y) :
    |(minor a c : ℝ)| ≤ 2 * X * Y := by
  have hX : 0 ≤ X := (abs_nonneg _).trans (ha 0)
  simp only [minor, Int.cast_sub, Int.cast_mul]
  calc
    _ ≤ |(a 0 : ℝ) * (c 1 : ℝ)| + |(a 1 : ℝ) * (c 0 : ℝ)| := abs_sub _ _
    _ ≤ X * Y + X * Y := by
      simp only [abs_mul]
      exact add_le_add (mul_le_mul (ha 0) (hc 1) (abs_nonneg _) hX)
        (mul_le_mul (ha 1) (hc 0) (abs_nonneg _) hX)
    _ = 2 * X * Y := by ring

private theorem cancel_factor {m n : ℕ} {z : ℤ} (h : m.Coprime n)
    (hz : (m : ℤ) ∣ (n : ℤ) * z) : (m : ℤ) ∣ z := by
  rw [Int.ofNat_dvd_left, Int.natAbs_mul, Int.natAbs_natCast] at hz
  exact Int.ofNat_dvd_left.mpr (h.dvd_of_dvd_mul_left hz)

private theorem minor_dvd_right {f : ℕ} {a c : Fin 2 → ℤ}
    (hc : ∀ i, (f : ℤ) ∣ c i) : (f : ℤ) ∣ minor a c :=
  dvd_sub (dvd_mul_of_dvd_right (hc 1) _) (dvd_mul_of_dvd_right (hc 0) _)

private theorem minor_dvd_left {g : ℕ} {b c : Fin 2 → ℤ}
    (hb : ∀ i, (g : ℤ) ∣ b i) : (g : ℤ) ∣ minor b c :=
  dvd_sub (dvd_mul_of_dvd_left (hb 0) _) (dvd_mul_of_dvd_left (hb 1) _)

private theorem zero_of_dvd_of_abs_lt {m : ℕ} {z : ℤ}
    (hd : (m : ℤ) ∣ z) (hlt : |(z : ℝ)| < (m : ℝ)) : z = 0 := by
  by_contra hne
  have hle := Nat.le_of_dvd (Int.natAbs_pos.mpr hne) (Int.ofNat_dvd_left.mp hd)
  have hleR : (m : ℝ) ≤ (z.natAbs : ℝ) := by exact_mod_cast hle
  exact (not_le_of_gt hlt) (by simpa only [Nat.cast_natAbs, Int.cast_abs] using hleR)

private theorem scaled_minor {d f : ℕ} {n c : Fin 2 → ℤ}
    (hn : ∀ i, (d : ℤ) ∣ n i) (hc : ∀ i, (f : ℤ) ∣ c i) :
    (d : ℤ) * (f : ℤ) * minor (fun i ↦ n i / (d : ℤ)) (fun i ↦ c i / (f : ℤ)) = minor n c := by
  calc
    _ = (n 0 / (d : ℤ) * (d : ℤ)) * (c 1 / (f : ℤ) * (f : ℤ)) -
        (n 1 / (d : ℤ) * (d : ℤ)) * (c 0 / (f : ℤ) * (f : ℤ)) := by unfold minor; ring
    _ = _ := by
      rw [Int.ediv_mul_cancel (hn 0), Int.ediv_mul_cancel (hn 1),
        Int.ediv_mul_cancel (hc 0), Int.ediv_mul_cancel (hc 1)]
      rfl

private theorem scaled_recovery_minor {q F' fA fB f : ℕ} {u v : Vector} {j : Fin 3}
    (hu : u ∈ lattice q F' fA fB) (hv : v ∈ lattice q F' fA fB)
    (huj : (f : ℤ) ∣ u j) (hvj : (f : ℤ) ∣ v j) :
    ((fA * fB : ℕ) : ℤ) * (f : ℤ) *
        minor (values (K q F' fA fB) u v) (values (fun w ↦ w j / (f : ℤ)) u v) =
      (q : ℤ) * minor (column u v 0) (column u v j) +
        (F' : ℤ) * (minor (column u v 1) (column u v j) + minor (column u v 2) (column u v j)) := by
  have hn : ∀ i, ((fA * fB : ℕ) : ℤ) ∣ values (numerator q F') u v i := by
    intro i
    fin_cases i
    · exact hu.2.2
    · exact hv.2.2
  have hc : ∀ i, (f : ℤ) ∣ column u v j i := by
    intro i
    fin_cases i
    · exact huj
    · exact hvj
  calc
    _ = minor (values (numerator q F') u v) (column u v j) := by
      change ((fA * fB : ℕ) : ℤ) * (f : ℤ) *
        minor (fun i ↦ values (numerator q F') u v i / ((fA * fB : ℕ) : ℤ))
          (fun i ↦ column u v j i / (f : ℤ)) = _
      exact scaled_minor hn hc
    _ = _ := by
      simp only [minor, column, values, Matrix.cons_val_zero, Matrix.cons_val_one, numerator]
      ring

private theorem two_minors_zero {q F' f g : ℕ} {X Y : ℝ} {a b c : Fin 2 → ℤ}
    (hqF : q.Coprime F') (hqg : q.Coprime g) (hfg : f.Coprime g)
    (hFfg : F'.Coprime (f * g)) (hlarge : 2 * X * Y < ((f * g * F' : ℕ) : ℝ))
    (ha : ∀ i, |(a i : ℝ)| ≤ X) (hc : ∀ i, |(c i : ℝ)| ≤ Y)
    (hbd : ∀ i, (g : ℤ) ∣ b i) (hcd : ∀ i, (f : ℤ) ∣ c i)
    (hz : (q : ℤ) * minor a c + (F' : ℤ) * minor b c = 0) :
    minor a c = 0 ∧ minor b c = 0 := by
  have heq : (q : ℤ) * minor a c = -((F' : ℤ) * minor b c) := by linear_combination hz
  have hF : (F' : ℤ) ∣ minor a c := by
    apply cancel_factor hqF.symm
    rw [heq, dvd_neg]
    exact dvd_mul_right _ _
  have hg : (g : ℤ) ∣ minor a c := by
    apply cancel_factor hqg.symm
    rw [heq, dvd_neg]
    exact dvd_mul_of_dvd_right (minor_dvd_left hbd) _
  have hf : (f : ℤ) ∣ minor a c := minor_dvd_right hcd
  -- The coprimalities first join `f` and `g`, then join their product with `F'`.
  have hd := hfg.mul_dvd_of_dvd_of_dvd (Int.ofNat_dvd_left.mp hf) (Int.ofNat_dvd_left.mp hg)
  have hprod : ((f * g * F' : ℕ) : ℤ) ∣ minor a c :=
    Int.ofNat_dvd_left.mpr (hFfg.symm.mul_dvd_of_dvd_of_dvd hd (Int.ofNat_dvd_left.mp hF))
  have hac := zero_of_dvd_of_abs_lt hprod ((minor_abs_le ha hc).trans_lt hlarge)
  have hFne : (F' : ℤ) ≠ 0 := by
    intro h
    have hFzero : F' = 0 := by exact_mod_cast h
    have hX : 0 ≤ X := (abs_nonneg _).trans (ha 0)
    have hY : 0 ≤ Y := (abs_nonneg _).trans (hc 0)
    have hXY : 0 ≤ 2 * X * Y := mul_nonneg (mul_nonneg zero_le_two hX) hY
    exact (not_lt_of_ge hXY) (by simpa [hFzero] using hlarge)
  refine ⟨hac, (mul_eq_zero.mp ?_).resolve_left hFne⟩
  simpa only [hac, mul_zero, zero_add] using hz

private theorem column_forall {P : ℤ → Prop} {u v : Vector} {j : Fin 3}
    (hu : P (u j)) (hv : P (v j)) : ∀ i, P (column u v j i) := by
  intro i
  fin_cases i
  · exact hu
  · exact hv

/-- On any independent pair of transformed lattice box vectors, both recovery minors
are nonzero if the spanned plane contains a represented point with `b,c ≠ 0`.
Only membership in the rational plane and the two nonzero coordinates of that
point are needed. -/
theorem recovery_minors_ne_zero {q F' fA fB : ℕ} {X Y : ℝ} {u v w : Vector}
    (hqF : q.Coprime F') (hqd : q.Coprime (fA * fB)) (hfAB : fA.Coprime fB)
    (hFd : F'.Coprime (fA * fB)) (hlarge : 2 * X * Y < ((fA * fB * F' : ℕ) : ℝ))
    (hu : u ∈ lattice q F' fA fB) (hv : v ∈ lattice q F' fA fB)
    (hubox : InBox X Y u) (hvbox : InBox X Y v)
    (hind : LinearIndependent ℚ ![rationalize u, rationalize v])
    (hw : rationalize w ∈ plane u v) (hwb : w 1 ≠ 0) (hwc : w 2 ≠ 0) :
    minor (values (K q F' fA fB) u v) (values (C₀ fA) u v) ≠ 0 ∧
      minor (values (K q F' fA fB) u v) (values (B₀ fB) u v) ≠ 0 := by
  have ha := column_forall (P := fun z ↦ |(z : ℝ)| ≤ X) hubox.1 hvbox.1
  have hb := column_forall (P := fun z ↦ |(z : ℝ)| ≤ Y) hubox.2.1 hvbox.2.1
  have hc := column_forall (P := fun z ↦ |(z : ℝ)| ≤ Y) hubox.2.2 hvbox.2.2
  have hbd := column_forall (P := fun z ↦ (fB : ℤ) ∣ z) hu.1 hv.1
  have hcd := column_forall (P := fun z ↦ (fA : ℤ) ∣ z) hu.2.1 hv.2.1
  constructor
  · intro hzero
    have hh := scaled_recovery_minor (j := 2) hu hv hu.2.1 hv.2.1
    change _ * _ * minor (values (K q F' fA fB) u v) (values (C₀ fA) u v) = _ at hh
    rw [hzero, mul_zero, minor_self, add_zero] at hh
    obtain ⟨hac, hbc⟩ := two_minors_zero hqF (hqd.of_dvd_right (Nat.dvd_mul_left fB fA))
      hfAB hFd hlarge ha hc hbd hcd hh.symm
    apply false_of_zero_minors hind (column_ne_zero_of_mem_plane hw hwc)
    intro i
    fin_cases i
    · exact hac
    · exact hbc
    · exact minor_self _
  · intro hzero
    have hh := scaled_recovery_minor (j := 1) hu hv hu.1 hv.1
    change _ * _ * minor (values (K q F' fA fB) u v) (values (B₀ fB) u v) = _ at hh
    rw [hzero, mul_zero, minor_self, zero_add] at hh
    have hFd' : F'.Coprime (fB * fA) := by simpa only [mul_comm fB fA] using hFd
    have hlarge' : 2 * X * Y < ((fB * fA * F' : ℕ) : ℝ) := by
      simpa only [mul_comm fB fA] using hlarge
    obtain ⟨hab, hcb⟩ := two_minors_zero hqF (hqd.of_dvd_right (Nat.dvd_mul_right fA fB))
      hfAB.symm hFd' hlarge' ha hb hcd hbd hh.symm
    apply false_of_zero_minors hind (column_ne_zero_of_mem_plane hw hwb)
    intro i
    fin_cases i
    · exact hab
    · exact minor_self _
    · exact hcb

end RankTwoRecoveryMinors
