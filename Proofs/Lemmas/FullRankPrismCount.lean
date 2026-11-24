module

public import Mathlib.Algebra.Module.ZLattice.Covolume
import Mathlib.Analysis.Convex.Combination
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Full-rank convex-window lattice count

Source: `e6b43a82:.godel/alice/denominator-pair-gap-regions.md:19–29`, especially
line 25, and the widening `1d036a89:.godel/alice/denominator-pair-gap-regions.md:37–47`.
The source is unchanged between discovery pin `50cd94de` and writing base `8b1b2fc2`.
Owning check session: `01a20e58-ec66-7c2b-94b4-741e4461cd8a`.

The points in the window give a real basis and generate an integral sublattice, not
necessarily the entire lattice. Half-open cells give exact disjointness within each
coset. Summing over the cosets cancels the index in the sublattice covolume.
-/

open Module MeasureTheory Set
open scoped Pointwise

namespace FullRankPrismCount

private theorem add_cell_mem_dilate {n : ℕ} {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (b : Basis (Fin n) ℝ E) {K : Set E} (hK : Convex ℝ K)
    (h0 : 0 ∈ K) (hb : ∀ i, b i ∈ K) {x p : E} (hx : x ∈ K)
    (hp : p ∈ ZSpan.fundamentalDomain b) : x + p ∈ ((n : ℝ) + 1) • K := by
  let c : ℝ := (n : ℝ) + 1
  have hc : 0 < c := by dsimp [c]; positivity
  let z : Option (Fin n) → E := fun i ↦ i.elim x (fun j ↦ b.repr p j • b j)
  have hz (i : Option (Fin n)) : z i ∈ K := by
    cases i with
    | none => exact hx
    | some j =>
      exact hK.smul_mem_of_zero_mem h0 (hb j)
        ⟨(hp j).1, (hp j).2.le⟩
  have hw : ∑ _i : Option (Fin n), c⁻¹ = 1 := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_option, Fintype.card_fin,
      nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
    exact mul_inv_cancel₀ hc.ne'
  have hm := hK.sum_mem (w := fun _ : Option (Fin n) ↦ c⁻¹)
    (fun _ _ ↦ inv_nonneg.mpr hc.le) hw (fun i _ ↦ hz i)
  have hsum : ∑ i, z i = x + p := by
    rw [Fintype.sum_option]
    exact congrArg (x + ·) (b.sum_repr p)
  rw [← Finset.smul_sum, hsum] at hm
  exact Set.mem_smul_set.mpr ⟨_, hm, smul_inv_smul₀ hc.ne' _⟩

/-- A compact convex window containing zero and `n` real-linearly independent points of a
full lattice in `ℝⁿ` contains at most `(n+1)^n * vol(K) / covol(L)` lattice points, in
cross-multiplied form. Central symmetry is not needed once `0 ∈ K` is given. -/
public theorem card_mul_covolume_le {n : ℕ} (L : Submodule ℤ (Fin n → ℝ))
    [DiscreteTopology L] [IsZLattice ℝ L] {K : Set (Fin n → ℝ)}
    (hcompact : IsCompact K) (hconvex : Convex ℝ K) (hzero : 0 ∈ K)
    {v : Fin n → (Fin n → ℝ)} (hv : LinearIndependent ℝ v)
    (hvL : ∀ i, v i ∈ L) (hvK : ∀ i, v i ∈ K) :
    (Nat.card ↥(K ∩ (L : Set (Fin n → ℝ))) : ℝ) * ZLattice.covolume L ≤
      ((n : ℝ) + 1)^n * volume.real K := by
  classical
  let E := Fin n → ℝ
  have hdim : finrank ℝ E = n := by simp [E]
  have hspan : Submodule.span ℝ (Set.range v) = ⊤ := by
    by_cases hn : n = 0
    · subst n
      exact Subsingleton.elim _ _
    · let : NeZero n := ⟨hn⟩
      exact hv.span_eq_top_of_card_eq_finrank (by rw [Fintype.card_fin, hdim])
  let b : Basis (Fin n) ℝ E := Basis.mk hv hspan.ge
  have hb (i : Fin n) : b i = v i := Basis.mk_apply _ _ i
  let L₀ : Submodule ℤ E := Submodule.span ℤ (Set.range b)
  have hle : L₀ ≤ L := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact hb i ▸ hvL i
  let P := ZSpan.fundamentalDomain b
  let H := L₀.toAddSubgroup.addSubgroupOf L.toAddSubgroup
  let Q := L.toAddSubgroup ⧸ H
  have hLpos := ZLattice.covolume_pos L volume
  have hcovol : ZLattice.covolume L₀ = (Nat.card Q : ℝ) * ZLattice.covolume L :=
    (div_eq_iff hLpos.ne').mp (ZLattice.covolume_div_covolume_eq_relIndex L₀ L hle)
  have hQ : Nat.card Q ≠ 0 := by
    intro h
    have hp := ZLattice.covolume_pos L₀ volume
    rw [hcovol, h, Nat.cast_zero, zero_mul] at hp
    exact (lt_irrefl 0) hp
  let : Finite Q := Nat.finite_of_card_ne_zero hQ
  let : Fintype Q := Fintype.ofFinite Q
  have hPvol : volume.real P = ZLattice.covolume L₀ :=
    (ZLattice.covolume_eq_measure_fundamentalDomain L₀ volume
      (ZSpan.isAddFundamentalDomain b volume)).symm
  have hPfinite : volume P ≠ ⊤ := (ZSpan.fundamentalDomain_isBounded b).measure_lt_top.ne
  let S : Set E := K ∩ (L : Set E)
  have hS : S.Finite := by
    change (K ∩ (L : Set E)).Finite
    rw [← (Free.chooseBasis ℤ L).ofZLatticeBasis_span ℝ]
    exact ZSpan.setFinite_inter _ hcompact.isBounded
  let : Fintype S := hS.fintype
  let toL (x : S) : L.toAddSubgroup := ⟨x.1, x.2.2⟩
  let f (x : S) : Q := QuotientAddGroup.mk (toL x)
  let F (q : Q) := {x : S // f x = q}
  let A (x : S) : Set E := (x : E) +ᵥ P
  let W : Set E := ((n : ℝ) + 1) • K
  have hW : volume W ≠ ⊤ := (hcompact.smul ((n : ℝ) + 1)).measure_ne_top
  have hsub (x : S) : A x ⊆ W := by
    intro z hz
    obtain ⟨p, hp, rfl⟩ := Set.mem_vadd_set.mp hz
    exact add_cell_mem_dilate b hconvex hzero (fun i ↦ hb i ▸ hvK i) x.2.1 hp
  have hdisj (q : Q) : Pairwise (Function.onFun Disjoint (fun x : F q ↦ A x.1)) := by
    intro x y hxy
    rw [Function.onFun, Set.disjoint_left]
    intro z hzx hzy
    have heq : f x.1 = f y.1 := x.2.trans y.2.symm
    have hd : (x.1 : E) - (y.1 : E) ∈ L₀ :=
      QuotientAddGroup.eq_iff_sub_mem.mp heq
    obtain ⟨p, hp, hpz⟩ := Set.mem_vadd_set.mp hzx
    obtain ⟨r, hr, hrz⟩ := Set.mem_vadd_set.mp hzy
    change (x.1 : E) + p = z at hpz
    change (y.1 : E) + r = z at hrz
    have hh : -p + r = (x.1 : E) - (y.1 : E) := by
      calc
        -p + r = ((y.1 : E) + r) - ((x.1 : E) + p) + ((x.1 : E) - (y.1 : E)) := by abel
        _ = _ := by rw [hpz, hrz, sub_self, zero_add]
    have hpr : p = r := by
      have h := (ZSpan.fract_eq_fract b p r).mpr (hh ▸ hd)
      rwa [ZSpan.fract_eq_self.mpr hp, ZSpan.fract_eq_self.mpr hr] at h
    apply hxy
    exact Subtype.ext (Subtype.ext (add_right_cancel (hpr ▸ hpz.trans hrz.symm)))
  have hA (x : S) : volume (A x) = volume P := measure_vadd volume (x : E) P
  have hAr (x : S) : volume.real (A x) = ZLattice.covolume L₀ :=
    (congrArg ENNReal.toReal (hA x)).trans hPvol
  have hbound (q : Q) : (Fintype.card (F q) : ℝ) * ZLattice.covolume L₀ ≤ volume.real W := by
    have hu : (⋃ x : F q, A x.1) ⊆ W := iUnion_subset fun x ↦ hsub x.1
    calc
      _ = ∑ _x : F q, ZLattice.covolume L₀ := by simp [nsmul_eq_mul]
      _ = volume.real (⋃ x : F q, A x.1) := by
        rw [measureReal_iUnion_fintype (hdisj q)
          (fun x ↦ (ZSpan.fundamentalDomain_measurableSet b).const_vadd (x.1 : E))
          (fun x ↦ (hA x.1).trans_ne hPfinite)]
        simp only [hAr]
      _ ≤ _ := measureReal_mono hu hW
  have hcard : ∑ q : Q, Fintype.card (F q) = Nat.card S := by
    rw [← Fintype.card_sigma]
    exact (Fintype.card_congr (Equiv.sigmaFiberEquiv f)).trans Nat.card_eq_fintype_card.symm
  have htotal : (Nat.card S : ℝ) * ZLattice.covolume L₀ ≤ (Nat.card Q : ℝ) * volume.real W := by
    have hQcard : Fintype.card Q = Nat.card Q := Nat.card_eq_fintype_card.symm
    simpa only [← Finset.sum_mul, ← Nat.cast_sum, hcard, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, hQcard] using
      (Finset.sum_le_sum (s := Finset.univ) (fun q _ ↦ hbound q))
  rw [hcovol, ← mul_left_comm] at htotal
  have hcount := le_of_mul_le_mul_left htotal (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hQ) :
    (0 : ℝ) < Nat.card Q)
  have hscale : volume.real W = ((n : ℝ) + 1)^n * volume.real K := by
    have hnonneg : 0 ≤ ((n : ℝ) + 1)^n := by positivity
    simp only [W, measureReal_def, Measure.addHaar_smul, hdim, abs_of_nonneg hnonneg,
      ENNReal.toReal_mul, ENNReal.toReal_ofReal hnonneg]
  exact hcount.trans_eq hscale

/-- Rank-three prism bound at either width in the source. The inputs are the prism's
volume (half-height `V` over gap area `8*D*T`) and the covolume of the whole masked
lattice, not the covolume of the sublattice generated by the points in the prism. -/
public theorem prism_card_le (L : Submodule ℤ (Fin 3 → ℝ))
    [DiscreteTopology L] [IsZLattice ℝ L] {K : Set (Fin 3 → ℝ)}
    (hcompact : IsCompact K) (hconvex : Convex ℝ K) (hzero : 0 ∈ K)
    {v : Fin 3 → (Fin 3 → ℝ)} (hv : LinearIndependent ℝ v)
    (hvL : ∀ i, v i ∈ L) (hvK : ∀ i, v i ∈ K)
    {V D T d e G : ℝ} (hG : 0 < G) (hD : 0 < D) (hde : 0 < d * e)
    (hvolume : volume.real K = 16 * V * D * T)
    (hcovol : ZLattice.covolume L = (d * e / G) * D) :
    (Nat.card ↥(K ∩ (L : Set (Fin 3 → ℝ))) : ℝ) ≤ 1024 * V * G * T / (d * e) := by
  have h := card_mul_covolume_le L hcompact hconvex hzero hv hvL hvK
  have hscale : ((↑(3 : ℕ) : ℝ) + 1)^3 = 64 := by norm_num
  rw [hvolume, hcovol, hscale] at h
  apply (le_div_iff₀ hde).mpr
  apply (mul_le_mul_iff_of_pos_right (div_pos hD hG)).mp
  convert h using 1
  · field_simp
  · field_simp
    ring

end FullRankPrismCount
