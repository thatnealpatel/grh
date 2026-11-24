module

public import Lemmas.OrderedTwoKnotPrice
import Lemmas.MeasurableBernsteinCell
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Whole-slab two-knot price

Source: `a585cb27:.godel/bob/eight-piece-deletion-33.md:213–237`.
Consumer: `a585cb27:.godel/bob/check-refined-frontier-33.py:24–50`,
`double_costs`. Discovery pin: `b6b5fe8`; writer base: `87780093`.
Owning check session: `01a20efe-657a-74fc-9a09-f6e32d4cc146`.

Scope: the real two-knot price on a finite partition of one slab, with branch
changes at cell ends. The knots may coincide, including at a partition node.
The two primitive remainders pair separately with consecutive differences of
atom moments. The increment subtracts a lower bound on the unsplit support.
No numerical curvature bound, interval evaluation or exclusion is claimed.
-/

@[expose] public section

namespace Masullo.WholeSlabTwoKnotPrice

open Set OrderedTwoKnotPrice SharedKnotCell
open SplitAtomBernstein (Atom Moment Score)
open scoped BigOperators

noncomputable section

/-- The atom moment vector in the signed primitive convention. -/
def atomMoment (u : Atom) : Primitive := (-Moment.x.eval u, -Moment.t.eval u, u)

/-- The coordinate pairing of a primitive vector and a signed moment vector. -/
def pairing (p m : Primitive) : ℝ := p.1 * m.1 + p.2.1 * m.2.1 + p.2.2 * m.2.2

/-- The Bernstein interpolant of the true primitive's three nodal values. -/
def cellQuadratic (p : ℝ → Primitive) (a b z : ℝ) : Primitive :=
  quadratic (control p a b) ((z - a) / (b - a))

/-- The pointwise cubic remainder allowance at a real knot. -/
def nodalError (a b R z : ℝ) : ℝ :=
  (R / 6) * |(z - a) * (z - (a + b) / 2) * (z - b)|

/-- The sharp uniform-in-position bound for the nodal allowance on one cell. -/
def cellError (a b R : ℝ) : ℝ := R * (b - a) ^ 3 / (72 * Real.sqrt 3)

private def scalarQuadratic (f : ℝ → ℝ) (a b z : ℝ) : ℝ :=
  let s := (z - a) / (b - a)
  (1 - s) ^ 2 * f a + 2 * s * (1 - s) * (2 * f ((a + b) / 2) - (f a + f b) / 2) +
    s ^ 2 * f b

private theorem scalarQuadratic_nodes {a b : ℝ} (hab : a < b) (f : ℝ → ℝ) :
    scalarQuadratic f a b a = f a ∧ scalarQuadratic f a b ((a + b) / 2) = f ((a + b) / 2) ∧
      scalarQuadratic f a b b = f b := by
  have hn := sub_ne_zero.mpr hab.ne'
  have hm : ((a + b) / 2 - a) / (b - a) = 1 / 2 := by
    apply (div_eq_iff hn).2
    ring
  refine ⟨by simp [scalarQuadratic], ?_, by simp [scalarQuadratic, hn]⟩
  simp only [scalarQuadratic, hm]
  ring

private theorem scalarQuadratic_contDiff (f : ℝ → ℝ) (a b : ℝ) :
    ContDiff ℝ 3 (scalarQuadratic f a b) := by
  unfold scalarQuadratic
  fun_prop

private theorem scalarQuadratic_third {a b : ℝ} (hab : a < b) (f : ℝ → ℝ) (z : ℝ) :
    iteratedDeriv 3 (scalarQuadratic f a b) z = 0 := by
  let L := f a
  let M := 2 * f ((a + b) / 2) - (f a + f b) / 2
  let U := f b
  let D := (b - a) ^ 2
  have heq : scalarQuadratic f a b = fun t ↦
      ((L - 2 * M + U) / D) * t ^ 2 + ((-2 * b * L + 2 * (a + b) * M - 2 * a * U) / D) * t ^ 1 +
        (b ^ 2 * L - 2 * a * b * M + a ^ 2 * U) / D := by
    funext t
    change (1 - (t - a) / (b - a)) ^ 2 * L +
      2 * ((t - a) / (b - a)) * (1 - (t - a) / (b - a)) * M + ((t - a) / (b - a)) ^ 2 * U = _
    dsimp only [D]
    field_simp [sub_ne_zero.mpr hab.ne']
    ring
  rw [heq]
  repeat rw [iteratedDeriv_fun_add (by fun_prop) (by fun_prop)]
  simp only [iteratedDeriv_const_mul_field, iteratedDeriv_pow, iteratedDeriv_const]
  norm_num [Nat.descFactorial]

-- Subtract the interpolating polynomial before invoking the Bernstein cap.
-- Both signs of the residual have zero control values and the same derivative bound.
private theorem abs_scalarQuadratic_error_le {a b R z : ℝ} {f : ℝ → ℝ} (hab : a < b)
    (hz : z ∈ Icc a b) (hf : ContDiffOn ℝ 3 f (Icc a b))
    (hR : ∀ t ∈ Ioo a b, |iteratedDeriv 3 f t| ≤ R) :
    |f z - scalarQuadratic f a b z| ≤ nodalError a b R z := by
  let q := scalarQuadratic f a b
  have hq : ContDiff ℝ 3 q := scalarQuadratic_contDiff f a b
  obtain ⟨ha, hm, hb⟩ := scalarQuadratic_nodes hab f
  have cap {g : ℝ → ℝ} (hg : ContDiffOn ℝ 3 g (Icc a b))
      (hgR : ∀ t ∈ Ioo a b, |iteratedDeriv 3 g t| ≤ R)
      (ga : g a = 0) (gm : g ((a + b) / 2) = 0) (gb : g b = 0) : g z ≤ nodalError a b R z := by
    have hmid : 2 * g ((a + b) / 2) - (g a + g b) / 2 ≤ 0 := by simp [ga, gm, gb]
    simpa [nodalError] using MeasurableBernsteinCell.le_cap_add_nodal_error hab hg hgR
      ga.le hmid gb.le hz
  have hfAt (t : ℝ) (ht : t ∈ Ioo a b) : ContDiffAt ℝ 3 f t :=
    (hf.mono Ioo_subset_Icc_self).contDiffAt (isOpen_Ioo.mem_nhds ht)
  have hup : f z - q z ≤ nodalError a b R z := by
    refine cap (g := fun t ↦ f t - q t) (hf.sub hq.contDiffOn) ?_
      (sub_eq_zero.mpr ha.symm) (sub_eq_zero.mpr hm.symm) (sub_eq_zero.mpr hb.symm)
    intro t ht
    rw [iteratedDeriv_fun_sub (hfAt t ht) hq.contDiffAt, scalarQuadratic_third hab f t, sub_zero]
    exact hR t ht
  have hlo : q z - f z ≤ nodalError a b R z := by
    refine cap (g := fun t ↦ q t - f t) (hq.contDiffOn.sub hf) ?_
      (sub_eq_zero.mpr ha) (sub_eq_zero.mpr hm) (sub_eq_zero.mpr hb)
    intro t ht
    rw [iteratedDeriv_fun_sub hq.contDiffAt (hfAt t ht), scalarQuadratic_third hab f t, zero_sub, abs_neg]
    exact hR t ht
  exact abs_le.mpr ⟨by linarith only [hlo], hup⟩

private theorem pairing_sub (p q m : Primitive) :
    pairing (p - q) m = pairing p m - pairing q m := by
  simp [pairing]
  ring

private theorem pairing_cellQuadratic (p : ℝ → Primitive) (a b z : ℝ) (m : Primitive) :
    pairing (cellQuadratic p a b z) m = scalarQuadratic (fun t ↦ pairing (p t) m) a b z := by
  simp [pairing, cellQuadratic, quadratic, quadraticWeight, SharedKnotCell.control, Fin.sum_univ_succ,
    scalarQuadratic, smul_eq_mul]
  ring

/-- The true primitive remainder, paired against any two consecutive atom moments,
is bounded by the cubic nodal error. This also covers all three interpolation nodes. -/
theorem abs_pairing_cellError_le_nodal {p : ℝ → Primitive} {a b R z : ℝ} (hab : a < b)
    (hz : z ∈ Icc a b) (u v : Atom)
    (hSmooth : ContDiffOn ℝ 3 (fun t ↦ pairing (p t) (atomMoment v - atomMoment u)) (Icc a b))
    (hThird : ∀ t ∈ Ioo a b,
      |iteratedDeriv 3 (fun t ↦ pairing (p t) (atomMoment v - atomMoment u)) t| ≤ R) :
    |pairing (p z - cellQuadratic p a b z) (atomMoment v - atomMoment u)| ≤ nodalError a b R z := by
  let m := atomMoment v - atomMoment u
  change |pairing (p z - cellQuadratic p a b z) m| ≤ _
  rw [pairing_sub (p z) (cellQuadratic p a b z) m, pairing_cellQuadratic p a b z m]
  exact abs_scalarQuadratic_error_le (f := fun t ↦ pairing (p t) m) hab hz hSmooth hThird

private theorem abs_nodal_product_eq {a b z : ℝ} (hz : z ∈ Icc a b) :
    |(z - a) * (z - (a + b) / 2) * (z - b)| =
      |z - (a + b) / 2| * (((b - a) / 2) ^ 2 - |z - (a + b) / 2| ^ 2) := by
  rw [abs_mul, abs_mul, abs_of_nonneg (sub_nonneg.mpr hz.1), abs_of_nonpos (sub_nonpos.mpr hz.2), sq_abs]
  ring

/-- The maximum of the nodal product has the sharp coefficient `1 / (12 * √3)`,
so the scalar third-derivative allowance is `R * (b - a)^3 / (72 * √3)`. -/
theorem nodalError_le_cellError {a b R z : ℝ} (hz : z ∈ Icc a b) (hR : 0 ≤ R) :
    nodalError a b R z ≤ cellError a b R := by
  let d := (b - a) / 2
  let y := |z - (a + b) / 2|
  let q := Real.sqrt 3
  have hd : 0 ≤ d := div_nonneg (sub_nonneg.mpr (hz.1.trans hz.2)) (by norm_num)
  have hy : 0 ≤ y := abs_nonneg _
  have hq : 0 < q := Real.sqrt_pos.2 (by norm_num)
  have hq2 : q ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hn : |(z - a) * (z - (a + b) / 2) * (z - b)| = y * (d ^ 2 - y ^ 2) := abs_nodal_product_eq hz
  have hfactor : 0 ≤ (q * y - d) ^ 2 * (q * y + 2 * d) := by positivity
  have hpoly : (q * y - d) ^ 2 * (q * y + 2 * d) =
      2 * d ^ 3 - 3 * q * (y * (d ^ 2 - y ^ 2)) := by
    calc
      _ = q ^ 2 * (q * y ^ 3) - 3 * d ^ 2 * q * y + 2 * d ^ 3 := by ring
      _ = _ := by rw [hq2]; ring
  rw [hpoly] at hfactor
  have hmax : |(z - a) * (z - (a + b) / 2) * (z - b)| ≤ (b - a) ^ 3 / (12 * q) := by
    rw [hn, le_div_iff₀ (by positivity : 0 < 12 * q)]
    dsimp only [d] at hfactor ⊢
    linarith only [hfactor]
  calc
    nodalError a b R z ≤ (R / 6) * ((b - a) ^ 3 / (12 * q)) :=
      mul_le_mul_of_nonneg_left hmax (by positivity)
    _ = cellError a b R := by unfold cellError; change _ = R * (b - a) ^ 3 / (72 * q); ring

/-- The allowance is attained at the midpoint plus the half-width divided by `√3`. -/
theorem exists_nodalError_eq_cellError {a b : ℝ} (hab : a ≤ b) (R : ℝ) :
    ∃ z ∈ Icc a b, nodalError a b R z = cellError a b R := by
  let q := Real.sqrt 3
  let d := (b - a) / 2
  let m := (a + b) / 2
  have hd : 0 ≤ d := by dsimp [d]; linarith
  have hq : 1 ≤ q := Real.one_le_sqrt.mpr (by norm_num)
  have hq2 : q ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hdiv : 0 ≤ d / q := div_nonneg hd (zero_le_one.trans hq)
  have hz : m + d / q ∈ Icc a b := by
    have hb := div_le_self hd hq
    dsimp only [d, m] at hd hb hdiv ⊢
    exact ⟨by linarith, by linarith⟩
  refine ⟨m + d / q, hz, ?_⟩
  rw [nodalError, abs_nodal_product_eq hz]
  change (R / 6) * (|m + d / q - m| * (d ^ 2 - |m + d / q - m| ^ 2)) = _
  have hsq : (d / q) ^ 2 = d ^ 2 / 3 := by rw [div_pow, hq2]
  rw [add_sub_cancel_left, abs_of_nonneg hdiv, hsq]
  change _ = R * (b - a) ^ 3 / (72 * q)
  dsimp only [d]
  ring

abbrev Mesh (n : ℕ) := Fin (n + 2) → ℝ

abbrev ControlIndex (n : ℕ) := Fin (n + 1) × Fin 3

def cellLeft {n : ℕ} (mesh : Mesh n) (i : Fin (n + 1)) : ℝ := mesh i.castSucc

def cellRight {n : ℕ} (mesh : Mesh n) (i : Fin (n + 1)) : ℝ := mesh i.succ

/-- Regularity on one branch cell, tested against every adjacent pair of atoms.
The derivatives are ordinary derivatives on the open branch interior. -/
def CellRegular (p : ℝ → Primitive) (a b R : ℝ) : Prop :=
  ∀ u v : Atom,
    ContDiffOn ℝ 3 (fun t ↦ pairing (p t) (atomMoment v - atomMoment u)) (Icc a b) ∧
    ∀ t ∈ Ioo a b, |iteratedDeriv 3 (fun s ↦ pairing (p s) (atomMoment v - atomMoment u)) t| ≤ R

/-- The global control order. The right control of one cell and the left control
of the next have the same rank and the same primitive value. -/
def controlRank {n : ℕ} (i : ControlIndex n) : ℕ := 2 * i.1.val + i.2.val

def controlAt {n : ℕ} (p : ℝ → Primitive) (mesh : Mesh n) (i : ControlIndex n) : Primitive :=
  SharedKnotCell.control p (cellLeft mesh i.1) (cellRight mesh i.1) i.2

def orderedControlPairs (n : ℕ) : Finset (ControlIndex n × ControlIndex n) :=
  Finset.univ.filter fun ij ↦ controlRank ij.1 ≤ controlRank ij.2

def controlPairPrice {n : ℕ} (p : ℝ → Primitive) (mesh : Mesh n)
    (ij : ControlIndex n × ControlIndex n) : ℝ :=
  price atomSupport (p (mesh 0)) (p (mesh (Fin.last (n + 1)))) (controlAt p mesh ij.1) (controlAt p mesh ij.2)

/-- The maximum of the actual three-support price over globally ordered pairs
of controls, including diagonal pairs. -/
def orderedCap {n : ℕ} (p : ℝ → Primitive) (mesh : Mesh n) : ℝ :=
  (orderedControlPairs n).sup' ⟨((0, 0), (0, 0)), by simp [orderedControlPairs]⟩ (controlPairPrice p mesh)

/-- Certified upper bounds on the individual ordered pairs give an upper bound
on the exact cap; no attainment by real knots is needed. -/
theorem orderedCap_le_of_pair_bounds {n : ℕ} (p : ℝ → Primitive) (mesh : Mesh n) {B : ℝ}
    (hB : ∀ ij ∈ orderedControlPairs n, controlPairPrice p mesh ij ≤ B) : orderedCap p mesh ≤ B :=
  Finset.sup'_le _ _ hB

private theorem control_price_le {n : ℕ} (p : ℝ → Primitive) (mesh : Mesh n)
    {i j : ControlIndex n} (hij : controlRank i ≤ controlRank j) :
    price atomSupport (p (mesh 0)) (p (mesh (Fin.last (n + 1)))) (controlAt p mesh i)
      (controlAt p mesh j) ≤ orderedCap p mesh := by
  have hm : (i, j) ∈ orderedControlPairs n := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hij⟩
  exact Finset.le_sup' (controlPairPrice p mesh) hm

private theorem left_lt_right {n : ℕ} {mesh : Mesh n} (hm : StrictMono mesh) (i : Fin (n + 1)) :
    cellLeft mesh i < cellRight mesh i := hm (Fin.lt_def.mpr (Nat.lt_succ_self _))

private theorem quadraticWeight_nonneg {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (i : Fin 3) :
    0 ≤ quadraticWeight s i := by
  have hs0 := hs.1
  have hs1 : 0 ≤ 1 - s := sub_nonneg.mpr hs.2
  fin_cases i <;> simp [quadraticWeight] <;> positivity

private theorem sum_quadraticWeight (s : ℝ) : ∑ i, quadraticWeight s i = 1 := by
  simp [quadraticWeight, Fin.sum_univ_succ]
  ring

-- Different cells use the product of their Bernstein laws. Every point of
-- this product grid is admissible in the global order, unlike in one cell.
private theorem price_le_of_cross_bounds (C D : Fin 3 → Primitive) (L U : Primitive) {s t B : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1)
    (hB : ∀ i j, price atomSupport L U (C i) (D j) ≤ B) :
    price atomSupport L U (quadratic C s) (quadratic D t) ≤ B := by
  let w (k : Fin 3 × Fin 3) := quadraticWeight s k.1 * quadraticWeight t k.2
  let x (k : Fin 3 × Fin 3) := C k.1
  let y (k : Fin 3 × Fin 3) := D k.2
  have hw (k : Fin 3 × Fin 3) : 0 ≤ w k :=
    mul_nonneg (quadraticWeight_nonneg hs k.1) (quadraticWeight_nonneg ht k.2)
  have hw1 : ∑ k, w k = 1 := by
    rw [Fintype.sum_prod_type]
    simp only [w, ← Finset.mul_sum, sum_quadraticWeight, mul_one]
  have hx : (∑ k, w k • x k) = quadratic C s := by
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    simp only [w, x, ← Finset.sum_smul, ← Finset.mul_sum, sum_quadraticWeight, mul_one]
  have hy : (∑ k, w k • y k) = quadratic D t := by
    rw [Fintype.sum_prod_type_right]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    simp only [w, y, ← Finset.sum_smul, ← Finset.sum_mul, sum_quadraticWeight, one_mul]
  have hL : (∑ k, w k • (L - x k)) = L - quadratic C s := by
    simp only [smul_sub, Finset.sum_sub_distrib]
    rw [← Finset.sum_smul, hw1, one_smul, hx]
  have hM : (∑ k, w k • (x k - y k)) = quadratic C s - quadratic D t := by
    simp only [smul_sub, Finset.sum_sub_distrib, hx, hy]
  have hU : (∑ k, w k • (y k - U)) = quadratic D t - U := by
    simp only [smul_sub, Finset.sum_sub_distrib]
    rw [← Finset.sum_smul, hw1, one_smul, hy]
  have hJ (v : Fin 3 × Fin 3 → Primitive) :
      atomSupport (∑ k, w k • v k) ≤ ∑ k, w k * atomSupport (v k) := by
    simpa only [smul_eq_mul] using
      convexOn_atomSupport.map_sum_le (fun k _ ↦ hw k) hw1 (fun k _ ↦ mem_univ (v k))
  unfold price
  rw [← hL, ← hM, ← hU]
  calc
    _ ≤ (∑ k, w k * atomSupport (L - x k)) + (∑ k, w k * atomSupport (x k - y k)) +
        (∑ k, w k * atomSupport (y k - U)) :=
      add_le_add (add_le_add (hJ fun k ↦ L - x k) (hJ fun k ↦ x k - y k)) (hJ fun k ↦ y k - U)
    _ = ∑ k, w k * price atomSupport L U (x k) (y k) := by
      simp only [price, mul_add, Finset.sum_add_distrib]
    _ ≤ ∑ k, w k * B :=
      Finset.sum_le_sum fun k _ ↦ mul_le_mul_of_nonneg_left (hB k.1 k.2) (hw k)
    _ = B := by rw [← Finset.sum_mul, hw1, one_mul]

private theorem normalized_mem {a b z : ℝ} (hab : a < b) (hz : z ∈ Icc a b) :
    (z - a) / (b - a) ∈ Icc (0 : ℝ) 1 := by
  refine ⟨div_nonneg (sub_nonneg.mpr hz.1) (sub_nonneg.mpr hab.le), ?_⟩
  rw [div_le_iff₀ (sub_pos.mpr hab), one_mul]
  exact sub_le_sub_right hz.2 a

private theorem interpolated_price_le {n : ℕ} (p : ℝ → Primitive) {mesh : Mesh n}
    (hmesh : StrictMono mesh) {i j : Fin (n + 1)} {x y : ℝ} (hij : i ≤ j) (hxy : x ≤ y)
    (hx : x ∈ Icc (cellLeft mesh i) (cellRight mesh i))
    (hy : y ∈ Icc (cellLeft mesh j) (cellRight mesh j)) :
    price atomSupport (p (mesh 0)) (p (mesh (Fin.last (n + 1))))
      (cellQuadratic p (cellLeft mesh i) (cellRight mesh i) x)
      (cellQuadratic p (cellLeft mesh j) (cellRight mesh j) y) ≤ orderedCap p mesh := by
  have hni := normalized_mem (left_lt_right hmesh i) hx
  have hnj := normalized_mem (left_lt_right hmesh j) hy
  rcases hij.eq_or_lt with rfl | hij
  · unfold cellQuadratic
    refine price_le_of_pair_bounds atomSupport convexOn_atomSupport _ _ _ hni.1 ?_ hnj.2 ?_
    · exact div_le_div_of_nonneg_right (sub_le_sub_right hxy _)
        (sub_nonneg.mpr (left_lt_right hmesh i).le)
    · intro k l hkl
      apply control_price_le (i := (i, k)) (j := (i, l))
      exact Nat.add_le_add_left (Fin.le_iff_val_le_val.mp hkl) _
  · unfold cellQuadratic
    apply price_le_of_cross_bounds _ _ _ _ hni hnj
    intro k l
    apply control_price_le (i := (i, k)) (j := (j, l))
    have h := Fin.lt_def.mp hij
    have hk := k.isLt
    change 2 * i.val + k.val ≤ 2 * j.val + l.val
    omega

private theorem halfScore_eval_eq_pairing (p q : Primitive) (u : Atom) :
    (halfScore p q).eval u = pairing (p - q) (atomMoment u) := by
  simp [halfScore, Score.eval, pairing, atomMoment, Moment.eval]
  ring

private theorem continuous_atom_eval (v : Primitive) : Continuous (halfScore v 0).eval := by
  unfold Score.eval Moment.eval
  fun_prop

private theorem pairing_le_atomSupport (v : Primitive) (u : Atom) :
    pairing v (atomMoment u) ≤ atomSupport v := by
  have he := halfScore_eval_eq_pairing v 0 u
  rw [sub_zero] at he
  rw [← he]
  exact le_csSup (isCompact_Icc.image (continuous_atom_eval v)).bddAbove ⟨u, u.property, rfl⟩

private theorem atomSupport_attained (v : Primitive) :
    ∃ u : Atom, atomSupport v = pairing v (atomMoment u) := by
  have hn : (Icc (0 : ℝ) 1).Nonempty := nonempty_Icc.mpr zero_le_one
  obtain ⟨u, hu, hmax⟩ := isCompact_Icc.exists_isMaxOn hn (continuous_atom_eval v).continuousOn
  refine ⟨⟨u, hu⟩, (le_antisymm ?_ (pairing_le_atomSupport v ⟨u, hu⟩))⟩
  have he := halfScore_eval_eq_pairing v 0 (⟨u, hu⟩ : Atom)
  rw [sub_zero] at he
  rw [← he]
  apply csSup_le (hn.image _)
  rintro _ ⟨w, hw, rfl⟩
  exact hmax hw

private def jointAtomScore (L U x y : Primitive) (u v w : Atom) : ℝ :=
  pairing (L - x) (atomMoment u) + pairing (x - y) (atomMoment v) + pairing (y - U) (atomMoment w)

-- Each interior primitive occurs twice, with opposite signs. Take the
-- difference of moments *before* estimating either interpolation error.
private theorem jointAtomScore_sub (L U x y qx qy : Primitive) (u v w : Atom) :
    jointAtomScore L U x y u v w = jointAtomScore L U qx qy u v w +
      pairing (x - qx) (atomMoment v - atomMoment u) + pairing (y - qy) (atomMoment w - atomMoment v) := by
  simp [jointAtomScore, pairing]
  ring

/-- The actual three-support price, evaluated at real knots in the original slab. -/
def slabPrice (p : ℝ → Primitive) (l r x y : ℝ) : ℝ :=
  price atomSupport (p l) (p r) (p x) (p y)

/-- For any ordered pair of cells containing the ordered real knots, the true
price is bounded by the ordered finite cap plus its two pointwise errors. -/
theorem price_le_orderedCap_add_nodalErrors {n : ℕ} (p : ℝ → Primitive) {mesh : Mesh n}
    (hmesh : StrictMono mesh) {i j : Fin (n + 1)} {x y Ri Rj : ℝ} (hij : i ≤ j) (hxy : x ≤ y)
    (hx : x ∈ Icc (cellLeft mesh i) (cellRight mesh i))
    (hy : y ∈ Icc (cellLeft mesh j) (cellRight mesh j))
    (hi : CellRegular p (cellLeft mesh i) (cellRight mesh i) Ri)
    (hj : CellRegular p (cellLeft mesh j) (cellRight mesh j) Rj) :
    slabPrice p (mesh 0) (mesh (Fin.last (n + 1))) x y ≤ orderedCap p mesh +
      nodalError (cellLeft mesh i) (cellRight mesh i) Ri x + nodalError (cellLeft mesh j) (cellRight mesh j) Rj y := by
  let L := p (mesh 0)
  let U := p (mesh (Fin.last (n + 1)))
  let qx := cellQuadratic p (cellLeft mesh i) (cellRight mesh i) x
  let qy := cellQuadratic p (cellLeft mesh j) (cellRight mesh j) y
  obtain ⟨u, hu⟩ := atomSupport_attained (L - p x)
  obtain ⟨v, hv⟩ := atomSupport_attained (p x - p y)
  obtain ⟨w, hw⟩ := atomSupport_attained (p y - U)
  have hqx := abs_pairing_cellError_le_nodal (left_lt_right hmesh i) hx u v (hi u v).1 (hi u v).2
  have hqy := abs_pairing_cellError_le_nodal (left_lt_right hmesh j) hy v w (hj v w).1 (hj v w).2
  have hcap : jointAtomScore L U qx qy u v w ≤ orderedCap p mesh :=
    (add_le_add (add_le_add (pairing_le_atomSupport (L - qx) u) (pairing_le_atomSupport (qx - qy) v))
      (pairing_le_atomSupport (qy - U) w)).trans (interpolated_price_le p hmesh hij hxy hx hy)
  change atomSupport (L - p x) + atomSupport (p x - p y) + atomSupport (p y - U) ≤ _
  rw [hu, hv, hw]
  change jointAtomScore L U (p x) (p y) u v w ≤ _
  rw [jointAtomScore_sub L U (p x) (p y) qx qy u v w]
  exact add_le_add (add_le_add hcap ((le_abs_self _).trans hqx)) ((le_abs_self _).trans hqy)

private theorem exists_cell {n : ℕ} (mesh : Mesh n) {z : ℝ}
    (hz : z ∈ Icc (mesh 0) (mesh (Fin.last (n + 1)))) :
    ∃ i, z ∈ Icc (cellLeft mesh i) (cellRight mesh i) := by
  let S := Finset.univ.filter fun i : Fin (n + 1) ↦ cellLeft mesh i ≤ z
  have hS : S.Nonempty := ⟨0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hz.1⟩⟩
  let i := S.max' hS
  have hi : cellLeft mesh i ≤ z := (Finset.mem_filter.mp (Finset.max'_mem S hS)).2
  refine ⟨i, hi, ?_⟩
  by_contra! h
  have hn : i.val < n := by
    by_contra! hn
    have hlast : i.succ = Fin.last (n + 1) := Fin.ext (by simp; omega)
    exact (h.not_ge) (by simpa only [cellRight, hlast] using hz.2)
  let j : Fin (n + 1) := ⟨i.val + 1, by omega⟩
  have he : j.castSucc = i.succ := Fin.ext rfl
  have hj : j ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
    change mesh j.castSucc ≤ z
    exact he ▸ h.le⟩
  have hji : j ≤ i := Finset.le_max' S j hj
  exact (Nat.not_succ_le_self _) (Fin.le_iff_val_le_val.mp hji)

private theorem exists_ordered_cells {n : ℕ} {mesh : Mesh n} (hmesh : StrictMono mesh)
    {x y : ℝ} (hlx : mesh 0 ≤ x) (hxy : x ≤ y) (hyr : y ≤ mesh (Fin.last (n + 1))) :
    ∃ i j : Fin (n + 1), i ≤ j ∧ x ∈ Icc (cellLeft mesh i) (cellRight mesh i) ∧
      y ∈ Icc (cellLeft mesh j) (cellRight mesh j) := by
  obtain ⟨i, hi⟩ := exists_cell mesh ⟨hlx, hxy.trans hyr⟩
  rcases hxy.lt_or_eq with hxy | rfl
  · obtain ⟨j, hj⟩ := exists_cell mesh ⟨hlx.trans hxy.le, hyr⟩
    refine ⟨i, j, ?_, hi, hj⟩
    by_contra! hji
    have hnodes : j.succ ≤ i.castSucc := Fin.le_iff_val_le_val.mpr (Fin.lt_def.mp hji)
    exact hxy.not_ge (hj.2.trans ((hmesh.monotone hnodes).trans hi.1))
  · exact ⟨i, i, le_rfl, hi, hi⟩

private theorem CellRegular.nonneg {p : ℝ → Primitive} {a b R : ℝ}
    (h : CellRegular p a b R) (hab : a < b) : 0 ≤ R := by
  let u : Atom := ⟨0, le_rfl, zero_le_one⟩
  have hm : (a + b) / 2 ∈ Ioo a b := ⟨by linarith, by linarith⟩
  exact (abs_nonneg _).trans ((h u u).2 _ hm)

/-- Whole-slab pricing for all closed-slab ordered knot positions, including
coincidences. In addition to the two pointwise bounds this gives the two sharp
cell-width allowances, which need not be the same on a nonuniform mesh. -/
theorem wholeSlab_price_le_orderedCap_add_errors {n : ℕ} (p : ℝ → Primitive) {mesh : Mesh n}
    (hmesh : StrictMono mesh) (R : Fin (n + 1) → ℝ)
    (hreg : ∀ i, CellRegular p (cellLeft mesh i) (cellRight mesh i) (R i))
    {x y : ℝ} (hlx : mesh 0 ≤ x) (hxy : x ≤ y) (hyr : y ≤ mesh (Fin.last (n + 1))) :
    ∃ i j : Fin (n + 1), i ≤ j ∧ x ∈ Icc (cellLeft mesh i) (cellRight mesh i) ∧
      y ∈ Icc (cellLeft mesh j) (cellRight mesh j) ∧
      slabPrice p (mesh 0) (mesh (Fin.last (n + 1))) x y ≤ orderedCap p mesh +
        nodalError (cellLeft mesh i) (cellRight mesh i) (R i) x +
        nodalError (cellLeft mesh j) (cellRight mesh j) (R j) y ∧
      slabPrice p (mesh 0) (mesh (Fin.last (n + 1))) x y ≤ orderedCap p mesh +
        cellError (cellLeft mesh i) (cellRight mesh i) (R i) + cellError (cellLeft mesh j) (cellRight mesh j) (R j) := by
  obtain ⟨i, j, hij, hx, hy⟩ := exists_ordered_cells hmesh hlx hxy hyr
  have hb := price_le_orderedCap_add_nodalErrors p hmesh hij hxy hx hy (hreg i) (hreg j)
  have hei := nodalError_le_cellError hx ((hreg i).nonneg (left_lt_right hmesh i))
  have hej := nodalError_le_cellError hy ((hreg j).nonneg (left_lt_right hmesh j))
  exact ⟨i, j, hij, hx, hy, hb, hb.trans (add_le_add (add_le_add le_rfl hei) hej)⟩

/-- With a common allowance for the individual cells, the whole-slab cap pays
it twice. -/
theorem wholeSlab_price_le_orderedCap_add_twice {n : ℕ} (p : ℝ → Primitive) {mesh : Mesh n}
    (hmesh : StrictMono mesh) (R : Fin (n + 1) → ℝ)
    (hreg : ∀ i, CellRegular p (cellLeft mesh i) (cellRight mesh i) (R i))
    {ε x y : ℝ} (hε : ∀ i, cellError (cellLeft mesh i) (cellRight mesh i) (R i) ≤ ε)
    (hlx : mesh 0 ≤ x) (hxy : x ≤ y) (hyr : y ≤ mesh (Fin.last (n + 1))) :
    slabPrice p (mesh 0) (mesh (Fin.last (n + 1))) x y ≤ orderedCap p mesh + 2 * ε := by
  obtain ⟨i, j, _, _, _, _, h⟩ := wholeSlab_price_le_orderedCap_add_errors p hmesh R hreg hlx hxy hyr
  linarith only [h, hε i, hε j]

/-- The unsplit support is in the same start-minus-stop orientation. -/
def unsplitSupport (p : ℝ → Primitive) (l r : ℝ) : ℝ := atomSupport (p l - p r)

/-- Subtracting a certified *lower* unsplit support bound gives an upper bound
on the actual excess over the unsplit support. The finite cap may itself be
replaced by any certified upper bound `B`. -/
theorem wholeSlab_excess_le_cap_sub_lower {n : ℕ} (p : ℝ → Primitive) {mesh : Mesh n}
    (hmesh : StrictMono mesh) (R : Fin (n + 1) → ℝ)
    (hreg : ∀ i, CellRegular p (cellLeft mesh i) (cellRight mesh i) (R i))
    {B ε x y lower : ℝ} (hB : orderedCap p mesh ≤ B)
    (hε : ∀ i, cellError (cellLeft mesh i) (cellRight mesh i) (R i) ≤ ε)
    (hlx : mesh 0 ≤ x) (hxy : x ≤ y) (hyr : y ≤ mesh (Fin.last (n + 1)))
    (hlower : lower ≤ unsplitSupport p (mesh 0) (mesh (Fin.last (n + 1)))) :
    slabPrice p (mesh 0) (mesh (Fin.last (n + 1))) x y -
      unsplitSupport p (mesh 0) (mesh (Fin.last (n + 1))) ≤ B + 2 * ε - lower := by
  have h := wholeSlab_price_le_orderedCap_add_twice p hmesh R hreg hε hlx hxy hyr
  linarith only [h, hB, hlower]

/-- A stored upper bound for the unsplit price can be retained: add the
nonnegative increment computed by subtracting a **lower** bound on the unsplit
support from the refined two-knot cap plus both errors. -/
theorem wholeSlab_price_le_stored_add_increment {n : ℕ} (p : ℝ → Primitive) {mesh : Mesh n}
    (hmesh : StrictMono mesh) (R : Fin (n + 1) → ℝ)
    (hreg : ∀ i, CellRegular p (cellLeft mesh i) (cellRight mesh i) (R i))
    {B ε x y lower stored : ℝ} (hB : orderedCap p mesh ≤ B)
    (hε : ∀ i, cellError (cellLeft mesh i) (cellRight mesh i) (R i) ≤ ε)
    (hlx : mesh 0 ≤ x) (hxy : x ≤ y) (hyr : y ≤ mesh (Fin.last (n + 1)))
    (hlower : lower ≤ unsplitSupport p (mesh 0) (mesh (Fin.last (n + 1))))
    (hstored : unsplitSupport p (mesh 0) (mesh (Fin.last (n + 1))) ≤ stored) :
    slabPrice p (mesh 0) (mesh (Fin.last (n + 1))) x y ≤
      stored + max 0 (B + 2 * ε - lower) := by
  have h := wholeSlab_excess_le_cap_sub_lower p hmesh R hreg hB hε hlx hxy hyr hlower
  have hincr := le_max_right 0 (B + 2 * ε - lower)
  linarith only [h, hstored, hincr]

end

end Masullo.WholeSlabTwoKnotPrice
