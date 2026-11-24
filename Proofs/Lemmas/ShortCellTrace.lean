module

public import Lemmas.ShortCellCrossing
public import Mathlib.Data.Nat.Prime.Basic
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Finite short-cell prime crossing trace

Source: `db84b3c3:.godel/bob/short-cell-weil-list.md:39–55`, eq. (4),
unchanged at writing pin `4fc0c11e`. This is the finite trace estimate from the
cell budget (2), before the source uses the PNT. It applies to the continuous
smeared crossing kernel and its symmetric form on unit window inputs, not to
replacement of the discrete shifts.

Integration uses disjoint open interiors. Prime ownership instead uses closed
cells and assigns every prime in the closed window exactly once. The cell
budget is written with the width cleared; it is equivalent to the density
bound on a positive-width cell and requires only nonnegative available budget
on a zero-width cell. In particular the source's nonnegative budget constant
works also when the window degenerates.

Owning check session: `01a20f51-211d-73b8-9726-8aa026238fa2`.
-/

open MeasureTheory Set

namespace ShortCellTrace

public section

/-- Closed cells lie in the window and cover its interior. Only their open
interiors are required to be disjoint. -/
structure Partition (J : Type*) (L Y h : ℝ) where
  left : J → ℝ
  right : J → ℝ
  left_le (j : J) : L ≤ left j
  ordered (j : J) : left j ≤ right j
  le_right (j : J) : right j ≤ Y
  width_le (j : J) : right j - left j ≤ h
  disjoint : Pairwise (fun j k ↦ Disjoint (Ioo (left j) (right j)) (Ioo (left k) (right k)))
  cover : Ioo L Y ⊆ ⋃ j, Icc (left j) (right j)

/-- The actual primes in the closed window, including primes at either end. -/
@[expose] noncomputable def primes (L Y : ℝ) : Finset ℕ :=
  (Finset.range (⌊Y⌋₊ + 1)).filter fun p ↦ p.Prime ∧ L ≤ (p : ℝ) ∧ (p : ℝ) ≤ Y

@[simp] theorem mem_primes {L Y : ℝ} {p : ℕ} :
    p ∈ primes L Y ↔ p.Prime ∧ L ≤ (p : ℝ) ∧ (p : ℝ) ≤ Y := by
  simp only [primes, Finset.mem_filter, Finset.mem_range]
  exact ⟨And.right, fun hp ↦ ⟨Nat.lt_succ_of_le (Nat.le_floor hp.2.2), hp⟩⟩

/-- One owner for each prime; a shared boundary can be assigned to either
adjacent cell that contains it. -/
structure PrimeAssignment {J : Type*} {L Y h : ℝ} (P : Partition J L Y h) where
  owner : ↥(primes L Y) → J
  in_cell (p : ↥(primes L Y)) : (p.val : ℝ) ∈ Icc (P.left (owner p)) (P.right (owner p))

/-- The fibre of the owner map over a cell. -/
@[expose] noncomputable def PrimeAssignment.cellPrimes {J : Type*} {L Y h : ℝ}
    {P : Partition J L Y h} (A : PrimeAssignment P) (j : J) : Finset ↥(primes L Y) := by
  classical
  exact Finset.univ.filter (fun p ↦ A.owner p = j)

/-- The prime-log mass actually assigned to the cell. -/
@[expose] noncomputable def PrimeAssignment.mass {J : Type*} {L Y h : ℝ}
    {P : Partition J L Y h} (A : PrimeAssignment P) (j : J) : ℝ :=
  ∑ p ∈ A.cellPrimes j, Real.log (p.val : ℝ)

variable {J ι : Type*} [Fintype J] [Fintype ι] {L Y h C : ℝ}
  {P : Partition J L Y h} (A : PrimeAssignment P)

omit [Fintype J] in
private theorem prime_in_cell {j : J} {p : ↥(primes L Y)} (hp : p ∈ A.cellPrimes j) :
    (p.val : ℝ) ∈ Icc (P.left j) (P.right j) := by
  classical
  have ho := (Finset.mem_filter.mp hp).2
  simpa only [ho] using A.in_cell p

private theorem log_prime_pos (p : ↥(primes L Y)) : 0 < Real.log (p.val : ℝ) :=
  Real.log_pos (by exact_mod_cast (mem_primes.mp p.property).1.one_lt)

private theorem sum_cellPrimes (w : ℕ → ℝ) :
    (∑ j, ∑ p ∈ A.cellPrimes j, w p.val) = ∑ p ∈ primes L Y, w p := by
  classical
  calc
    _ = ∑ p : ↥(primes L Y), w p.val :=
      Finset.sum_fiberwise Finset.univ A.owner (fun p ↦ w p.val)
    _ = _ := by rw [Finset.univ_eq_attach, Finset.sum_attach]

private theorem restrict_eq_sum (P : Partition J L Y h) :
    volume.restrict (Icc L Y) = Measure.sum fun j ↦ volume.restrict (Ioo (P.left j) (P.right j)) := by
  have hcell : ∀ᵐ v ∂(volume : Measure ℝ), ∀ j,
      (v ∈ Ioo (P.left j) (P.right j)) ↔ (v ∈ Icc (P.left j) (P.right j)) :=
    ae_all_iff.mpr fun _ ↦ Ioo_ae_eq_Icc
  have hcover : Icc L Y =ᵐ[(volume : Measure ℝ)] ⋃ j, Ioo (P.left j) (P.right j) := by
    filter_upwards [Ioo_ae_eq_Icc (μ := (volume : Measure ℝ)) (a := L) (b := Y), hcell]
      with v hv hc
    constructor
    · intro hv'
      obtain ⟨j, hj⟩ := mem_iUnion.mp (P.cover (hv.mpr hv'))
      exact mem_iUnion.mpr ⟨j, (hc j).mpr hj⟩
    · intro hv'
      obtain ⟨j, hj⟩ := mem_iUnion.mp hv'
      exact ⟨(P.left_le j).trans hj.1.le, hj.2.le.trans (P.le_right j)⟩
  exact (Measure.restrict_congr_set hcover).trans
    (Measure.restrict_iUnion P.disjoint fun _ ↦ measurableSet_Ioo)

private theorem step_regular (P : Partition J L Y h) {m : ℝ → ℂ} {c : J → ℂ}
    (hm : ∀ j, m =ᵐ[volume.restrict (Ioo (P.left j) (P.right j))] fun _ ↦ c j) :
    AEStronglyMeasurable m (volume.restrict (Icc L Y)) ∧
      IntegrableOn (fun v ↦ ‖m v‖ ^ 2) (Icc L Y) := by
  rw [IntegrableOn, restrict_eq_sum P]
  refine ⟨aestronglyMeasurable_sum_measure_iff.mpr (fun j ↦ ?_),
    integrable_sum_measure (fun j ↦ ?_) (Summable.of_finite)⟩
  · exact aestronglyMeasurable_const.congr (hm j).symm
  · refine (integrable_const (‖c j‖ ^ 2)).congr ?_
    filter_upwards [hm j] with v hv
    rw [hv]

private theorem symmetric_sq_le_trace {D L : ℝ} {m f : ℝ → ℂ}
    (hD : 0 < D) (hL : 0 < L) (hLY : L ≤ Real.exp D) (hhalf : D / 2 ≤ Real.log L)
    (hm : AEStronglyMeasurable m (volume.restrict (Icc L (Real.exp D))))
    (hmi : IntegrableOn (fun v ↦ ‖m v‖ ^ 2) (Icc L (Real.exp D)))
    (hf : MemLp f 2 (volume.restrict (Icc 0 D)))
    (hunit : (∫ x in Icc 0 D, ‖f x‖ ^ 2) = 1) :
    (ShortCellCrossing.symmetricForm D L m f) ^ 2 ≤
      ∫ v in Icc L (Real.exp D), ShortCellCrossing.weightedSquare D m v := by
  let T := ∫ v in Icc L (Real.exp D), ShortCellCrossing.weightedSquare D m v
  have hT : 0 ≤ T := by
    dsimp only [T]
    rw [← (ShortCellCrossing.integral_sq_kernel hD hL hLY hhalf hmi).2]
    exact integral_nonneg fun _ ↦ integral_nonneg fun _ ↦ sq_nonneg _
  have hb := (ShortCellCrossing.abs_symmetricForm_le hD hL hLY hhalf hm hmi hf hunit).2
  change _ ≤ Real.sqrt T at hb
  calc
    _ = |ShortCellCrossing.symmetricForm D L m f| ^ 2 := (sq_abs _).symm
    _ ≤ (Real.sqrt T) ^ 2 := (sq_le_sq₀ (abs_nonneg _) (Real.sqrt_nonneg _)).2 hb
    _ = T := Real.sq_sqrt hT

omit [Fintype J] in
private theorem weight_le_of_same_cell (hL : 0 < L) (P : Partition J L Y h) (j : J)
    {v p : ℝ} (hv : v ∈ Icc (P.left j) (P.right j))
    (hp : p ∈ Icc (P.left j) (P.right j)) :
    Real.log (Y / v) ≤ Real.log (Y / p) + h / L := by
  have hLv := (P.left_le j).trans hv.1
  have hv₀ := hL.trans_le hLv
  have hp₀ := hL.trans_le ((P.left_le j).trans hp.1)
  have hY₀ := hv₀.trans_le (hv.2.trans (P.le_right j))
  have hh₀ := (sub_nonneg.mpr (P.ordered j)).trans (P.width_le j)
  have hdist : p - v ≤ h := (sub_le_sub hp.2 hv.1).trans (P.width_le j)
  have hlog := Real.log_le_sub_one_of_pos (div_pos hp₀ hv₀)
  rw [Real.log_div hp₀.ne' hv₀.ne', show p / v - 1 = (p - v) / v by
    rw [sub_div, div_self hv₀.ne']] at hlog
  have hb : Real.log p - Real.log v ≤ h / L :=
    hlog.trans ((div_le_div_of_nonneg_right hdist hv₀.le).trans
      (div_le_div_of_nonneg_left hh₀ hL hLv))
  rw [Real.log_div hY₀.ne' hv₀.ne', Real.log_div hY₀.ne' hp₀.ne']
  linarith only [hb]

omit [Fintype J] in
/-- Convert the quotient cell budget into the width-cleared budget. The second
hypothesis is vacuous on a positive-width partition, and automatic for a
nonnegative `C` even if a zero-width cell owns a prime. -/
theorem mul_cellBudget_of_div {c : ι → J → ℂ}
    (hcell : ∀ j, (∑ i, ‖c i j‖ ^ 2) ≤ C * (A.mass j / (P.right j - P.left j)))
    (hzero : ∀ j, P.right j = P.left j → 0 ≤ C * A.mass j) (j : J) :
    (P.right j - P.left j) * (∑ i, ‖c i j‖ ^ 2) ≤ C * A.mass j := by
  rcases (P.ordered j).eq_or_lt with hj | hj
  · simpa only [← hj, sub_self, zero_mul] using hzero j hj.symm
  · have hs := (le_div_iff₀ (sub_pos.mpr hj)).1
        (by simpa only [mul_div_assoc] using hcell j :
          (∑ i, ‖c i j‖ ^ 2) ≤ (C * A.mass j) / (P.right j - P.left j))
    simpa only [mul_comm (P.right j - P.left j)] using hs

/-- Finite trace inequality before any prime number theorem input. The
positive-width cell budget is exactly the source's density bound after
clearing the denominator. The width-cleared statement does not require a
separate sign assumption on `C`. -/
theorem integral_trace_le (hL : 0 < L) {m : ι → ℝ → ℂ} {c : ι → J → ℂ}
    (hconst : ∀ i j, m i =ᵐ[volume.restrict (Ioo (P.left j) (P.right j))] fun _ ↦ c i j)
    (hcell : ∀ j, (P.right j - P.left j) * (∑ i, ‖c i j‖ ^ 2) ≤ C * A.mass j) :
    (∑ i, ∫ v in Icc L Y, Real.log (Y / v) * ‖m i v‖ ^ 2) ≤
      C * ((∑ p ∈ primes L Y, Real.log (p : ℝ) * Real.log (Y / p)) +
        (h / L) * ∑ p ∈ primes L Y, Real.log (p : ℝ)) := by
  let w : ℝ → ℝ := fun v ↦ Real.log (Y / v)
  let energy : J → ℝ := fun j ↦ ∑ i, ‖c i j‖ ^ 2
  let cost : J → ℝ := fun j ↦ ∑ p ∈ A.cellPrimes j, Real.log (p.val : ℝ) * (w (p.val : ℝ) + h / L)
  have hwin (j : J) : Ioo (P.left j) (P.right j) ⊆ Icc L Y := fun _ hv ↦
    ⟨(P.left_le j).trans hv.1.le, hv.2.le.trans (P.le_right j)⟩
  have hw₀ {v : ℝ} (hv : v ∈ Icc L Y) : 0 ≤ w v :=
    Real.log_nonneg ((one_le_div (hL.trans_le hv.1)).2 hv.2)
  have hdiv : ContinuousOn (fun v : ℝ ↦ Y / v) (Icc L Y) :=
    continuousOn_const.div continuousOn_id (fun _ hv ↦ (hL.trans_le hv.1).ne')
  have hw : IntegrableOn w (Icc L Y) := ContinuousOn.integrableOn_compact isCompact_Icc
    (hdiv.log (fun _ hv ↦ (div_pos (hL.trans_le (hv.1.trans hv.2)) (hL.trans_le hv.1)).ne'))
  have hsplit (i : ι) : (∫ v in Icc L Y, w v * ‖m i v‖ ^ 2) =
      ∑ j, (∫ v in Ioo (P.left j) (P.right j), w v) * ‖c i j‖ ^ 2 := by
    have heq (j : J) : (fun v ↦ w v * ‖m i v‖ ^ 2)
        =ᵐ[volume.restrict (Ioo (P.left j) (P.right j))] fun v ↦ w v * ‖c i j‖ ^ 2 := by
      filter_upwards [hconst i j] with v hv
      rw [hv]
    have hi (j : J) : IntegrableOn (fun v ↦ w v * ‖m i v‖ ^ 2) (Ioo (P.left j) (P.right j)) :=
      ((hw.mono_set (hwin j)).mul_const _).congr (heq j).symm
    rw [restrict_eq_sum P, integral_sum_measure (integrable_sum_measure hi Summable.of_finite),
      tsum_fintype]
    exact Finset.sum_congr rfl fun j _ ↦ (integral_congr_ae (heq j)).trans (integral_mul_const _ _)
  have hlocal (j : J) :
      (∫ v in Ioo (P.left j) (P.right j), w v) * energy j ≤ C * cost j := by
    have hcoeff {p : ↥(primes L Y)} (hp : p ∈ A.cellPrimes j) :
        0 ≤ C * Real.log (p.val : ℝ) := by
      have hm : 0 < A.mass j := Finset.sum_pos' (fun q _ ↦ (log_prime_pos q).le)
        ⟨p, hp, log_prime_pos p⟩
      have he : 0 ≤ energy j := Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
      have ha : 0 ≤ C * A.mass j := (mul_nonneg (sub_nonneg.mpr (P.ordered j)) he).trans (hcell j)
      exact mul_nonneg (nonneg_of_mul_nonneg_left ha hm) (log_prime_pos p).le
    rcases (P.ordered j).eq_or_lt with hj | hj
    · rw [← hj, Ioo_self, setIntegral_empty, zero_mul]
      dsimp only [cost]
      rw [Finset.mul_sum]
      refine Finset.sum_nonneg fun p hp ↦ ?_
      rw [← mul_assoc]
      have hpp := mem_primes.mp p.property
      exact mul_nonneg (hcoeff hp) (add_nonneg (hw₀ ⟨hpp.2.1, hpp.2.2⟩)
        (div_nonneg ((sub_nonneg.mpr (P.ordered j)).trans (P.width_le j)) hL.le))
    · have hd : 0 < P.right j - P.left j := sub_pos.mpr hj
      have hvbound (v : ℝ) (hv : v ∈ Ioo (P.left j) (P.right j)) :
          w v * energy j ≤ (C * cost j) / (P.right j - P.left j) := by
        apply (le_div_iff₀ hd).2
        calc
          (w v * energy j) * (P.right j - P.left j) =
              w v * ((P.right j - P.left j) * energy j) := by ring
          _ ≤ w v * (C * A.mass j) := mul_le_mul_of_nonneg_left (hcell j) (hw₀ (hwin j hv))
          _ = ∑ p ∈ A.cellPrimes j, (C * Real.log (p.val : ℝ)) * w v := by
            simp only [PrimeAssignment.mass, Finset.mul_sum]
            exact Finset.sum_congr rfl fun p _ ↦ by ring
          _ ≤ ∑ p ∈ A.cellPrimes j, (C * Real.log (p.val : ℝ)) * (w (p.val : ℝ) + h / L) :=
            Finset.sum_le_sum fun p hp ↦ mul_le_mul_of_nonneg_left
              (weight_le_of_same_cell hL P j (Ioo_subset_Icc_self hv) (prime_in_cell A hp)) (hcoeff hp)
          _ = C * cost j := by simp only [cost, Finset.mul_sum, mul_assoc]
      rw [← integral_mul_const]
      calc
        _ ≤ ∫ _ in Ioo (P.left j) (P.right j), (C * cost j) / (P.right j - P.left j) :=
          setIntegral_mono_on ((hw.mono_set (hwin j)).mul_const _) (integrable_const _)
            measurableSet_Ioo hvbound
        _ = C * cost j := by
          rw [integral_const, measureReal_restrict_apply MeasurableSet.univ, univ_inter,
            Real.volume_real_Ioo, max_eq_left hd.le, smul_eq_mul, mul_div_cancel₀ _ hd.ne']
  change (∑ i, ∫ v in Icc L Y, w v * ‖m i v‖ ^ 2) ≤ _
  calc
    _ = ∑ j, (∫ v in Ioo (P.left j) (P.right j), w v) * energy j := by
      simp_rw [hsplit, Finset.sum_comm (s := (Finset.univ : Finset ι)), energy, Finset.mul_sum]
    _ ≤ ∑ j, C * cost j := Finset.sum_le_sum fun j _ ↦ hlocal j
    _ = _ := by
      rw [← Finset.mul_sum]
      congr 1
      rw [show (∑ j, cost j) = ∑ p ∈ primes L Y, Real.log (p : ℝ) * (w p + h / L) from
        sum_cellPrimes A (fun p ↦ Real.log (p : ℝ) * (w p + h / L))]
      simp_rw [mul_add, Finset.sum_add_distrib, mul_comm (Real.log (_ : ℝ)) (h / L), ← Finset.mul_sum, w]

/-- The source's quotient budget on positive-width cells, with no separate
sign hypothesis on `C`. -/
theorem integral_trace_le_of_div (hL : 0 < L) (hwidth : ∀ j, P.left j < P.right j)
    {m : ι → ℝ → ℂ} {c : ι → J → ℂ}
    (hconst : ∀ i j, m i =ᵐ[volume.restrict (Ioo (P.left j) (P.right j))] fun _ ↦ c i j)
    (hcell : ∀ j, (∑ i, ‖c i j‖ ^ 2) ≤ C * (A.mass j / (P.right j - P.left j))) :
    (∑ i, ∫ v in Icc L Y, Real.log (Y / v) * ‖m i v‖ ^ 2) ≤
      C * ((∑ p ∈ primes L Y, Real.log (p : ℝ) * Real.log (Y / p)) +
        (h / L) * ∑ p ∈ primes L Y, Real.log (p : ℝ)) :=
  integral_trace_le A hL hconst (mul_cellBudget_of_div A hcell fun j hj ↦
    ((hwidth j).ne hj.symm).elim)

/-- Extend the quotient form to zero-width cells when the budget constant is
nonnegative as in the source. -/
theorem integral_trace_le_of_div_nonneg (hL : 0 < L) (hC : 0 ≤ C)
    {m : ι → ℝ → ℂ} {c : ι → J → ℂ}
    (hconst : ∀ i j, m i =ᵐ[volume.restrict (Ioo (P.left j) (P.right j))] fun _ ↦ c i j)
    (hcell : ∀ j, (∑ i, ‖c i j‖ ^ 2) ≤ C * (A.mass j / (P.right j - P.left j))) :
    (∑ i, ∫ v in Icc L Y, Real.log (Y / v) * ‖m i v‖ ^ 2) ≤
      C * ((∑ p ∈ primes L Y, Real.log (p : ℝ) * Real.log (Y / p)) +
        (h / L) * ∑ p ∈ primes L Y, Real.log (p : ℝ)) :=
  integral_trace_le A hL hconst (mul_cellBudget_of_div A hcell fun _ _ ↦
    mul_nonneg hC (Finset.sum_nonneg fun p _ ↦ (log_prime_pos p).le))

/-- The trace bound for the actual forward crossing kernels. The integration
rectangle is left times right, with no additional adjoint copy. -/
theorem kernel_trace_le {D : ℝ} {P : Partition J L (Real.exp D) h} (A : PrimeAssignment P)
    (hD : 0 < D) (hL : 0 < L) (hLY : L ≤ Real.exp D) (hhalf : D / 2 ≤ Real.log L)
    {m : ι → ℝ → ℂ} {c : ι → J → ℂ}
    (hconst : ∀ i j, m i =ᵐ[volume.restrict (Ioo (P.left j) (P.right j))] fun _ ↦ c i j)
    (hcell : ∀ j, (P.right j - P.left j) * (∑ i, ‖c i j‖ ^ 2) ≤ C * A.mass j) :
    (∑ i, ∫ x in ShortCellCrossing.leftHalf D, ∫ y in ShortCellCrossing.rightHalf D,
      ‖ShortCellCrossing.kernel D L (m i) x y‖ ^ 2) ≤
      C * ((∑ p ∈ primes L (Real.exp D), Real.log (p : ℝ) * Real.log (Real.exp D / p)) +
        (h / L) * ∑ p ∈ primes L (Real.exp D), Real.log (p : ℝ)) := by
  have heq (i : ι) := (ShortCellCrossing.integral_sq_kernel hD hL hLY hhalf
    (step_regular P (hconst i)).2).2
  simp_rw [heq, ShortCellCrossing.weightedSquare]
  exact integral_trace_le A hL hconst hcell

/-- The same budget bounds the sum of squared absolute symmetric crossing
values for arbitrary, possibly different, unit window inputs. No factor of
two is lost on passing from the one forward kernel to the symmetric form. -/
theorem symmetricForm_trace_le {D : ℝ} {P : Partition J L (Real.exp D) h} (A : PrimeAssignment P)
    (hD : 0 < D) (hL : 0 < L) (hLY : L ≤ Real.exp D) (hhalf : D / 2 ≤ Real.log L)
    {m f : ι → ℝ → ℂ} {c : ι → J → ℂ}
    (hconst : ∀ i j, m i =ᵐ[volume.restrict (Ioo (P.left j) (P.right j))] fun _ ↦ c i j)
    (hcell : ∀ j, (P.right j - P.left j) * (∑ i, ‖c i j‖ ^ 2) ≤ C * A.mass j)
    (hf : ∀ i, MemLp (f i) 2 (volume.restrict (Icc 0 D)))
    (hunit : ∀ i, (∫ x in Icc 0 D, ‖f i x‖ ^ 2) = 1) :
    (∑ i, (ShortCellCrossing.symmetricForm D L (m i) (f i)) ^ 2) ≤
      C * ((∑ p ∈ primes L (Real.exp D), Real.log (p : ℝ) * Real.log (Real.exp D / p)) +
        (h / L) * ∑ p ∈ primes L (Real.exp D), Real.log (p : ℝ)) := by
  refine (Finset.sum_le_sum fun i _ ↦ ?_).trans (integral_trace_le A hL hconst hcell)
  obtain ⟨hm, hmi⟩ := step_regular P (hconst i)
  exact symmetric_sq_le_trace hD hL hLY hhalf hm hmi (hf i) (hunit i)

end

end ShortCellTrace
