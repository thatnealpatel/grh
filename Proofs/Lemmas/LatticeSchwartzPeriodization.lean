module

public import Mathlib.Algebra.Module.ZLattice.Basic
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.Topology.Instances.AddCircle.Real
import Mathlib.Algebra.Module.ZLattice.Summable
import Mathlib.Analysis.Normed.Group.FunctionSeries

/-! # Periodization of Schwartz functions on real lattices

A summable majorant on each bounded set gives local uniform absolute convergence.
The resulting continuous sum is invariant under translation by the lattice, so it
is a continuous function on the torus in lattice basis coordinates.
-/

open Filter Topology
open scoped SchwartzMap

namespace Masullo

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable (L : Submodule ℤ E) [DiscreteTopology L]

private theorem summable_lattice_one_add_norm_inv_pow (n : ℕ) (hn : Module.finrank ℤ L < n) :
    Summable (fun u : L ↦ (1 + ‖u‖)⁻¹ ^ n) := by
  apply (ZLattice.summable_norm_pow_inv L n hn).of_norm_bounded_eventually
  filter_upwards [(Set.finite_singleton (0 : L)).compl_mem_cofinite] with u hu
  have hu0 : 0 < ‖u‖ := norm_pos_iff.mpr (by simpa using hu)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact pow_le_pow_left₀ (by positivity) (inv_anti₀ hu0 (by linarith)) _

/-- On every norm-bounded set of shifts the absolute lattice samples admit a
single summable majorant. -/
public theorem exists_summable_norm_schwartz_lattice_add_majorant
    (φ : 𝓢(E, ℂ)) (R : ℝ) (hR : 0 ≤ R) :
    ∃ a : L → ℝ, Summable a ∧ ∀ (u : L) (x : E), ‖x‖ ≤ R → ‖φ (x + u)‖ ≤ a u := by
  let n := Module.finrank ℤ L + 1
  let C := 2 ^ n * (Finset.Iic (n, 0)).sup (fun m ↦ SchwartzMap.seminorm ℝ m.1 m.2) φ
  refine ⟨fun u ↦ (C * (1 + R) ^ n) * (1 + ‖u‖)⁻¹ ^ n,
    (summable_lattice_one_add_norm_inv_pow L n (Nat.lt_succ_self _)).mul_left _, ?_⟩
  intro u x hx
  have hφ : (1 + ‖x + (u : E)‖) ^ n * ‖φ (x + u)‖ ≤ C := by
    simpa only [C, norm_iteratedFDeriv_zero] using
      (SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (n, 0))
        (k := n) (n := 0) le_rfl le_rfl φ (x + u))
  have hu : ‖u‖ ≤ ‖x + (u : E)‖ + ‖x‖ := by
    simpa only [add_sub_cancel_left, Submodule.norm_coe] using norm_sub_le (x + (u : E)) x
  have hshift : 1 + ‖u‖ ≤ (1 + R) * (1 + ‖x + (u : E)‖) := by
    nlinarith only [hu, hx, mul_nonneg hR (norm_nonneg (x + (u : E)))]
  change ‖φ (x + u)‖ ≤ (C * (1 + R) ^ n) * (1 + ‖u‖)⁻¹ ^ n
  rw [inv_pow, ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
  calc
    _ ≤ ((1 + R) * (1 + ‖x + (u : E)‖)) ^ n * ‖φ (x + u)‖ := by
      rw [mul_comm ‖φ (x + u)‖]
      gcongr
    _ = ((1 + ‖x + (u : E)‖) ^ n * ‖φ (x + u)‖) * (1 + R) ^ n := by
      rw [mul_pow]
      ring
    _ ≤ C * (1 + R) ^ n := mul_le_mul_of_nonneg_right hφ (by positivity)

/-- Absolute convergence at an arbitrary shift (even for a non-full lattice). -/
public theorem summable_norm_schwartz_lattice_add (φ : 𝓢(E, ℂ)) (x : E) :
    Summable (fun u : L ↦ ‖φ (x + u)‖) := by
  obtain ⟨a, ha, hle⟩ :=
    exists_summable_norm_schwartz_lattice_add_majorant L φ ‖x‖ (norm_nonneg _)
  exact ha.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun u ↦ hle u x le_rfl)

private theorem continuous_tsum_schwartz_lattice_add (φ : 𝓢(E, ℂ)) :
    Continuous (fun x : E ↦ ∑' u : L, φ (x + u)) := by
  rw [continuous_iff_continuousAt]
  intro x
  let R := ‖x‖ + 1
  obtain ⟨a, ha, hle⟩ :=
    exists_summable_norm_schwartz_lattice_add_majorant L φ R (by dsimp [R]; positivity)
  have h : ContinuousOn (fun y : E ↦ ∑' u : L, φ (y + u)) (Metric.ball 0 R) :=
    continuousOn_tsum (fun _ ↦ (φ.continuous.comp (continuous_id.add continuous_const)).continuousOn)
      ha (fun u y hy ↦ hle u y (mem_ball_zero_iff.mp hy).le)
  exact h.continuousAt (Metric.isOpen_ball.mem_nhds (by simp [R]))

-- Translation in the summation index is the permutation `u ↦ v + u` of `L`.
omit [FiniteDimensional ℝ E] [DiscreteTopology L] in
private theorem tsum_schwartz_lattice_add_translate (φ : 𝓢(E, ℂ)) (x : E) (v : L) :
    (∑' u : L, φ ((x + (v : E)) + u)) = ∑' u : L, φ (x + u) := by
  simpa only [Function.comp_apply, Equiv.coe_addLeft, Submodule.coe_add, add_assoc] using
    (Equiv.addLeft v).tsum_eq (fun u : L ↦ φ (x + u))

variable [IsZLattice ℝ L] {ι : Type*} [Fintype ι] (b : Module.Basis ι ℤ L)

private noncomputable def latticeTorusQuot (x : E) : UnitAddTorus ι :=
  fun i ↦ ((b.ofZLatticeBasis ℝ).repr x i : UnitAddCircle)

private theorem latticeTorusQuot_isOpenQuotientMap : IsOpenQuotientMap (latticeTorusQuot L b) := by
  have hCircle : IsOpenQuotientMap (fun t : ℝ ↦ (t : UnitAddCircle)) :=
    QuotientAddGroup.isOpenQuotientMap_mk
  exact (IsOpenQuotientMap.piMap (fun _ : ι ↦ hCircle)).comp
    (b.ofZLatticeBasis ℝ).equivFunL.toHomeomorph.isOpenQuotientMap

-- Equal torus coordinates give an integer coordinate difference, which is
-- realized by an actual lattice vector via the integral basis.
private theorem exists_lattice_add_of_latticeTorusQuot_eq {x y : E}
    (hxy : latticeTorusQuot L b x = latticeTorusQuot L b y) : ∃ v : L, x = y + v := by
  classical
  let B := b.ofZLatticeBasis ℝ
  have h : ∀ i : ι, ∃ m : ℤ, (m : ℝ) = B.repr x i - B.repr y i := by
    intro i
    have hi : (B.repr x i : UnitAddCircle) = (B.repr y i : UnitAddCircle) := congrFun hxy i
    have hz : ((B.repr x i - B.repr y i : ℝ) : UnitAddCircle) = 0 := by
      rw [AddCircle.coe_sub, hi, sub_self]
    simpa only [zsmul_eq_mul, mul_one] using (AddCircle.coe_eq_zero_iff 1).mp hz
  choose m hm using h
  let v : L := b.equivFun.symm m
  refine ⟨v, ?_⟩
  have hv (i : ι) : b.repr v i = m i :=
    congrFun (b.equivFun.apply_symm_apply m) i
  apply B.repr.injective
  ext i
  rw [map_add, Finsupp.add_apply]
  change B.repr x i = B.repr y i + (b.ofZLatticeBasis ℝ).repr (v : E) i
  rw [b.ofZLatticeBasis_repr_apply ℝ L v i, hv i, hm i]
  ring

private theorem tsum_schwartz_lattice_add_eq_of_quot_eq (φ : 𝓢(E, ℂ)) {x y : E}
    (h : latticeTorusQuot L b x = latticeTorusQuot L b y) :
    (∑' u : L, φ (x + u)) = ∑' u : L, φ (y + u) := by
  obtain ⟨v, rfl⟩ := exists_lattice_add_of_latticeTorusQuot_eq L b h
  exact tsum_schwartz_lattice_add_translate L φ y v

/-- Continuous periodization on the torus in the given lattice basis. -/
public noncomputable def latticeSchwartzPeriodization (φ : 𝓢(E, ℂ)) : C(UnitAddTorus ι, ℂ) where
  toFun t := ∑' u : L, φ (Function.surjInv (latticeTorusQuot_isOpenQuotientMap L b).surjective t + u)
  continuous_toFun := by
    let h := latticeTorusQuot_isOpenQuotientMap L b
    apply h.isQuotientMap.continuous_iff.mpr
    convert continuous_tsum_schwartz_lattice_add L φ using 1
    funext x
    exact tsum_schwartz_lattice_add_eq_of_quot_eq L b φ (Function.surjInv_eq h.surjective _)

/-- Evaluate periodization on the torus class of an arbitrary real shift. -/
public theorem latticeSchwartzPeriodization_apply (φ : 𝓢(E, ℂ)) (x : E) :
    latticeSchwartzPeriodization L b φ (fun i ↦ ((b.ofZLatticeBasis ℝ).repr x i : UnitAddCircle)) =
      ∑' u : L, φ (x + u) :=
  tsum_schwartz_lattice_add_eq_of_quot_eq L b φ
    (Function.surjInv_eq (latticeTorusQuot_isOpenQuotientMap L b).surjective (latticeTorusQuot L b x))

end Masullo
