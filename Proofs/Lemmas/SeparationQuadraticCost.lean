module

public import Mathlib.Algebra.Polynomial.Coeff
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Data.Nat.Prime.Defs

/-!
# The quadratic cost of excluding close starts

Source: `6fe747e1:.godel/bob/detection-radius.md`, “The quadratic coefficient
pays the whole nonvanishing cost” (the quadratic input to (3)); the polynomial
is from `0e672a90:.godel/bob/separated-signed-tuples.md`, “Excluding close
starts in a real projection”. Owning check session:
`01a208fa-736c-75e9-a336-a5cd6d3b0490`.

A start is a natural number, with distance computed after casting to `ℝ`.
The finite identity holds for arbitrary real activities on any finite set of
starts. For the source's fixed shift, the specialization uses both prime
endpoints in the frozen band and the original, unnormalized weights. Close
pairs are ordered and include ties at the cutoff and the entire diagonal.
The module does not treat the formal logarithm, higher coefficients, or the
ratio induction and detector that use the quadratic estimate.
-/

open scoped BigOperators

namespace SeparationQuadraticCost

/-- Distance of starts on the real line (not truncated natural subtraction). -/
@[expose] public noncomputable def startDistance (p q : ℕ) : ℝ := |(p : ℝ) - (q : ℝ)|

private theorem startDistance_comm (p q : ℕ) : startDistance p q = startDistance q p :=
  abs_sub_comm _ _

@[simp] private theorem startDistance_self (p : ℕ) : startDistance p p = 0 := by
  simp [startDistance]

/-- The independent subsets for the graph joining distinct starts at distance at most `r`. -/
@[expose] public noncomputable def independentSets (starts : Finset ℕ) (r : ℝ) :
    Finset (Finset ℕ) := by
  classical
  exact starts.powerset.filter fun I ↦
    ∀ p ∈ I, ∀ q ∈ I, p ≠ q → r < startDistance p q

/-- The source's independence polynomial: one weighted monomial per separated subset. -/
@[expose] public noncomputable def independencePolynomial (starts : Finset ℕ) (r : ℝ)
    (x : ℕ → ℝ) : Polynomial ℝ :=
  ∑ I ∈ independentSets starts r, Polynomial.monomial I.card (∏ p ∈ I, x p)

/-- The expression `2[z²]P - S²`, where `S` is the sum of the activities. -/
@[expose] public noncomputable def b2 (starts : Finset ℕ) (r : ℝ) (x : ℕ → ℝ) : ℝ :=
  2 * (independencePolynomial starts r x).coeff 2 - (∑ p ∈ starts, x p) ^ 2

/-- All ordered close pairs; there is no distinctness condition. -/
@[expose] public noncomputable def closePairs (starts : Finset ℕ) (r : ℝ) : Finset (ℕ × ℕ) := by
  classical
  exact (starts ×ˢ starts).filter fun a ↦ startDistance a.1 a.2 ≤ r

/-- The non-strict cutoff includes equality, and admits `(p,p)` whenever `p` is a start
and `0 ≤ r`. -/
public theorem mem_closePairs {starts : Finset ℕ} {r : ℝ} {p q : ℕ} :
    (p, q) ∈ closePairs starts r ↔ p ∈ starts ∧ q ∈ starts ∧ |(p : ℝ) - (q : ℝ)| ≤ r := by
  classical
  rw [closePairs, Finset.mem_filter, Finset.mem_product, and_assoc]
  rfl

private noncomputable def farPairs (starts : Finset ℕ) (r : ℝ) : Finset (ℕ × ℕ) := by
  classical
  exact (starts ×ˢ starts).filter fun a ↦ r < startDistance a.1 a.2

/-- In degree two each independent two-element subset contributes its activity product once. -/
private theorem coeff_two_eq_sum (starts : Finset ℕ) (r : ℝ) (x : ℕ → ℝ) :
    (independencePolynomial starts r x).coeff 2 =
      ∑ I ∈ (independentSets starts r).filter (fun I ↦ I.card = 2), ∏ p ∈ I, x p := by
  rw [independencePolynomial, Polynomial.finsetSum_coeff, Finset.sum_filter]
  simp only [Polynomial.coeff_monomial, Finsupp.single_apply]

private theorem mem_independent_pair {starts : Finset ℕ} {r : ℝ} {p q : ℕ} (hne : p ≠ q) :
    {p, q} ∈ independentSets starts r ↔ p ∈ starts ∧ q ∈ starts ∧ r < startDistance p q := by
  classical
  simp only [independentSets, Finset.mem_filter, Finset.mem_powerset]
  constructor
  · rintro ⟨hsub, hsep⟩
    exact ⟨hsub (by simp), hsub (by simp), hsep p (by simp) q (by simp) hne⟩
  · rintro ⟨hp, hq, hfar⟩
    refine ⟨?_, ?_⟩
    · intro a ha
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha
      rcases ha with rfl | rfl <;> assumption
    · intro a ha b hb hab
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
      · exact (hab rfl).elim
      · exact hfar
      · rwa [startDistance_comm]
      · exact (hab rfl).elim

private theorem coeff_two_eq_forward (starts : Finset ℕ) (r : ℝ) (x : ℕ → ℝ) :
    (independencePolynomial starts r x).coeff 2 =
      ∑ a ∈ (farPairs starts r).filter (fun a ↦ a.1 < a.2), x a.1 * x a.2 := by
  classical
  rw [coeff_two_eq_sum]
  symm
  -- Orient each two-element subset by its unique smaller start.
  refine Finset.sum_nbij (fun a : ℕ × ℕ ↦ ({a.1, a.2} : Finset ℕ)) ?_ ?_ ?_ ?_
  · intro a ha
    simp only [farPairs, Finset.mem_filter, Finset.mem_product] at ha
    exact Finset.mem_filter.mpr
      ⟨(mem_independent_pair ha.2.ne).mpr ⟨ha.1.1.1, ha.1.1.2, ha.1.2⟩,
        Finset.card_eq_two.mpr ⟨a.1, a.2, ha.2.ne, rfl⟩⟩
  · intro a ha b hb hab
    change ({a.1, a.2} : Finset ℕ) = {b.1, b.2} at hab
    have ha' := (Finset.mem_filter.mp ha).2
    have hb' := (Finset.mem_filter.mp hb).2
    have h₁ : a.1 = b.1 ∨ a.1 = b.2 := by
      have hm : a.1 ∈ ({b.1, b.2} : Finset ℕ) := by rw [← hab]; simp
      simpa using hm
    have h₂ : a.2 = b.1 ∨ a.2 = b.2 := by
      have hm : a.2 ∈ ({b.1, b.2} : Finset ℕ) := by rw [← hab]; simp
      simpa using hm
    exact Prod.ext (by omega) (by omega)
  · intro I hI
    obtain ⟨hI, hcard⟩ := Finset.mem_filter.mp hI
    obtain ⟨p, q, hne, rfl⟩ := Finset.card_eq_two.mp hcard
    obtain ⟨hp, hq, hfar⟩ := (mem_independent_pair hne).mp hI
    rcases lt_or_gt_of_ne hne with h | h
    · exact ⟨(p, q), by simpa [farPairs] using ⟨⟨⟨hp, hq⟩, hfar⟩, h⟩, rfl⟩
    · refine ⟨(q, p), ?_, Finset.pair_comm _ _⟩
      rw [startDistance_comm] at hfar
      simpa [farPairs] using ⟨⟨⟨hq, hp⟩, hfar⟩, h⟩
  · intro a ha
    exact (Finset.prod_pair (Finset.mem_filter.mp ha).2.ne).symm

private theorem sum_far_eq_twice_coeff_two (starts : Finset ℕ) {r : ℝ} (hr : 0 ≤ r)
    (x : ℕ → ℝ) :
    ∑ a ∈ farPairs starts r, x a.1 * x a.2 =
      2 * (independencePolynomial starts r x).coeff 2 := by
  classical
  rw [coeff_two_eq_forward, two_mul, ← Finset.sum_filter_add_sum_filter_not
    (farPairs starts r) (fun a : ℕ × ℕ ↦ a.1 < a.2) (fun a ↦ x a.1 * x a.2)]
  congr 1
  -- Swapping the coordinates bijects the reverse and forward orientations.
  refine Finset.sum_nbij' Prod.swap Prod.swap ?_ ?_ (fun a _ ↦ Prod.swap_swap a)
    (fun a _ ↦ Prod.swap_swap a) (fun a _ ↦ mul_comm _ _)
  · intro a ha
    simp only [farPairs, Finset.mem_filter, Finset.mem_product] at ha ⊢
    obtain ⟨⟨⟨hp, hq⟩, hfar⟩, hnotlt⟩ := ha
    have hne : a.1 ≠ a.2 := by
      intro heq
      rw [heq, startDistance_self] at hfar
      exact (not_lt_of_ge hr) hfar
    exact ⟨⟨⟨hq, hp⟩, by rwa [startDistance_comm]⟩, lt_of_le_of_ne (le_of_not_gt hnotlt) hne.symm⟩
  · intro a ha
    simp only [farPairs, Finset.mem_filter, Finset.mem_product] at ha ⊢
    obtain ⟨⟨⟨hp, hq⟩, hfar⟩, hlt⟩ := ha
    exact ⟨⟨⟨hq, hp⟩, by rwa [startDistance_comm]⟩, not_lt_of_ge hlt.le⟩

/-- Subtracting `S²` from twice the degree-two coefficient leaves exactly the negative of the
ordered close-pair sum, with diagonal terms and equality at the cutoff. -/
public theorem b2_eq_neg_close_sum (starts : Finset ℕ) {r : ℝ} (hr : 0 ≤ r) (x : ℕ → ℝ) :
    b2 starts r x = -(∑ a ∈ closePairs starts r, x a.1 * x a.2) := by
  classical
  have hpartition :
      (∑ a ∈ closePairs starts r, x a.1 * x a.2) +
        (∑ a ∈ farPairs starts r, x a.1 * x a.2) = (∑ p ∈ starts, x p) ^ 2 := by
    rw [pow_two, Finset.sum_mul_sum, ← Finset.sum_product starts starts (fun a ↦ x a.1 * x a.2)]
    simpa only [closePairs, farPairs, not_le] using
      Finset.sum_filter_add_sum_filter_not (starts ×ˢ starts)
        (fun a : ℕ × ℕ ↦ startDistance a.1 a.2 ≤ r) (fun a ↦ x a.1 * x a.2)
  rw [b2, ← sum_far_eq_twice_coeff_two starts hr x, ← hpartition, add_comm, sub_add_eq_sub_sub,
    sub_self, zero_sub]

/-- The unnormalized weight of the ordered close pairs, including the diagonal. -/
@[expose] public noncomputable def closePairCost (starts : Finset ℕ) (r : ℝ)
    (w : ℕ → ℝ) : ℝ :=
  ∑ a ∈ closePairs starts r, w a.1 * w a.2

/-- The entire quadratic error is bounded by the actual weight of the ordered close pairs. -/
public theorem abs_b2_le_closePairCost (starts : Finset ℕ) {r : ℝ} (hr : 0 ≤ r)
    (x w : ℕ → ℝ) (hx : ∀ p ∈ starts, |x p| ≤ w p) :
    |b2 starts r x| ≤ closePairCost starts r w := by
  classical
  rw [b2_eq_neg_close_sum starts hr x, abs_neg]
  calc
    _ ≤ ∑ a ∈ closePairs starts r, |x a.1 * x a.2| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ closePairCost starts r w := by
      apply Finset.sum_le_sum
      intro a ha
      obtain ⟨hp, hq, _⟩ := mem_closePairs.mp ha
      rw [abs_mul]
      exact mul_le_mul (hx _ hp) (hx _ hq) (abs_nonneg _) ((abs_nonneg _).trans (hx _ hp))

/-- Starts of prime pairs at natural shift `d`, with both endpoints in `[exp(-8) X, X]`. -/
@[expose] public noncomputable def primeStarts (X : ℝ) (d : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range (⌊X⌋₊ + 1)).filter fun p ↦
    p.Prime ∧ (p + d).Prime ∧ Real.exp (-8) * X ≤ (p : ℝ) ∧ (↑(p + d) : ℝ) ≤ X

/-- The range used to define the finite set makes no further restriction on the source band. -/
public theorem mem_primeStarts {X : ℝ} {d p : ℕ} :
    p ∈ primeStarts X d ↔
      p.Prime ∧ (p + d).Prime ∧ (p : ℝ) ∈ Set.Icc (Real.exp (-8) * X) X ∧
        (↑(p + d) : ℝ) ∈ Set.Icc (Real.exp (-8) * X) X := by
  classical
  have hppd : (p : ℝ) ≤ (↑(p + d) : ℝ) := Nat.cast_le.mpr (Nat.le_add_right p d)
  simp only [primeStarts, Finset.mem_filter, Finset.mem_range, Nat.lt_succ_iff, Set.mem_Icc]
  constructor
  · rintro ⟨_, hp, hpd, hlo, hhi⟩
    exact ⟨hp, hpd, ⟨hlo, hppd.trans hhi⟩, ⟨hlo.trans hppd, hhi⟩⟩
  · rintro ⟨hp, hpd, ⟨hlo, hhi⟩, _, hpdhi⟩
    exact ⟨Nat.le_floor hhi, hp, hpd, hlo, hpdhi⟩

/-- The source weight, evaluated on `primeStarts X d`. -/
@[expose] public noncomputable def primePairWeight (X : ℝ) (d p : ℕ) : ℝ :=
  X⁻¹ * Real.log (X / (p : ℝ)) * Real.log (p : ℝ) * Real.log (↑(p + d) : ℝ)

/-- The source's `C_d(r)` at the frozen cutoff `X`. -/
@[expose] public noncomputable def primePairCost (X : ℝ) (d : ℕ) (r : ℝ) : ℝ :=
  closePairCost (primeStarts X d) r (primePairWeight X d)

/-- The quadratic bound at a fixed prime shift with the source normalization of `C_d(r)`. -/
public theorem abs_b2_le_primePairCost (X : ℝ) (d : ℕ) {r : ℝ} (hr : 0 ≤ r) (x : ℕ → ℝ)
    (hx : ∀ p ∈ primeStarts X d, |x p| ≤ primePairWeight X d p) :
    |b2 (primeStarts X d) r x| ≤ primePairCost X d r :=
  abs_b2_le_closePairCost (primeStarts X d) hr x (primePairWeight X d) hx

end SeparationQuadraticCost
