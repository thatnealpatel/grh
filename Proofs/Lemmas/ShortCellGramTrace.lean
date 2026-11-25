module

public import Lemmas.ShortCellGramAssembly
public import Lemmas.ShortCellTraceAsymptotic

/-!
# Short-cell Gram bounds imply an eventual crossing trace bound

Source: `8058479e:.godel/bob/short-cell-weil-list.md:17–21,39–53`, the elementary
prime-measure step (2) and the forward kernel trace used in (4), unchanged in
those ranges at `7f6ac23` and `aaf7e47`. The finite integer Gram bounds are inputs;
this file neither estimates them nor treats unsmeared shifts, operator norms, or
Weil values. The prime-ramp asymptotic is inherited from `ShortCellTrace`.

Owning check session: `01a20ff6-8a18-70ab-866d-9f5902b34d4c`.
-/

open Filter MeasureTheory Set
open scoped Topology

namespace ShortCellTrace

/-- Prime-log moment of an actual owner fibre, divided by the cell width.
The common twist is evaluated at the natural prime and each row at its integer cast. -/
@[expose] public noncomputable def PrimeAssignment.gramMoment {J ι : Type*} {L Y h : ℝ}
    {P : Partition J L Y h} (A : PrimeAssignment P) (ξ : ℕ → ℂ) (χ : ι → ℤ → ℂ)
    (i : ι) (j : J) : ℂ :=
  ShortCellGramAssembly.moment (A.cellPrimes j)
    ((Function.Embedding.subtype _).trans (Nat.castEmbedding : ℕ ↪ ℤ))
    (fun p ↦ Real.log (p.val : ℝ)) (fun p ↦ ξ p.val) χ (P.right j - P.left j) i

private theorem gramMoment_cellBudget {J ι : Type*} [Fintype ι] [Nonempty ι]
    {L Y h C : ℝ} {P : Partition J L Y h} (A : PrimeAssignment P) (j : J)
    {S : Finset ℤ} {W : ℤ → ℝ} {ξ : ℕ → ℂ} {χ : ι → ℤ → ℂ} {M B E : ℝ}
    (hwidth : 0 < P.right j - P.left j)
    (hS : ∀ p ∈ A.cellPrimes j, (p.val : ℤ) ∈ S)
    (hW : ∀ n ∈ S, 0 ≤ W n)
    (hone : ∀ p ∈ A.cellPrimes j, W (p.val : ℤ) = 1)
    (hξ : ∀ p : ↥(primes L Y), ‖ξ p.val‖ ≤ 1)
    (hlog : ∀ p ∈ A.cellPrimes j, Real.log (p.val : ℝ) ≤ M)
    (hE : 0 ≤ E)
    (hdiag : ∀ i, ∑ n ∈ S, W n * ‖χ i n‖ ^ 2 ≤ B)
    (hoff : ∀ i k, i ≠ k → ‖ShortCellGramAssembly.gram S W χ i k‖ ≤ E)
    (hcoef : (M / (P.right j - P.left j)) * (B + ((Fintype.card ι - 1 : ℕ) : ℝ) * E) ≤ C) :
    (∑ i, ‖A.gramMoment ξ χ i j‖ ^ 2) ≤ C * (A.mass j / (P.right j - P.left j)) := by
  let point : ↥(primes L Y) ↪ ℤ :=
    (Function.Embedding.subtype _).trans (Nat.castEmbedding : ℕ ↪ ℤ)
  have hsub : (A.cellPrimes j).map point ⊆ S := by
    intro n hn
    obtain ⟨p, hp, rfl⟩ := Finset.mem_map.mp hn
    exact hS p hp
  have hB : 0 ≤ B := by
    obtain ⟨i⟩ := ‹Nonempty ι›
    exact (Finset.sum_nonneg fun n hn ↦ mul_nonneg (hW n hn) (sq_nonneg _)).trans (hdiag i)
  have hgram := ShortCellGramAssembly.sum_norm_moment_sq_le S (A.cellPrimes j) point χ
    (w := fun p ↦ Real.log (p.val : ℝ)) (ξ := fun p ↦ ξ p.val) hwidth hsub
    (fun p hp ↦ ⟨Real.log_natCast_nonneg p.val, hlog p hp⟩) (fun p _ ↦ hξ p)
    hW hone hB hE hdiag hoff
  have hmass : 0 ≤ A.mass j := Finset.sum_nonneg fun p _ ↦ Real.log_natCast_nonneg p.val
  refine hgram.trans ?_
  rw [mul_assoc, mul_comm C]
  exact mul_le_mul_of_nonneg_left hcoef (div_nonneg hmass hwidth.le)

/-- Finite integer Gram inputs for the owner fibres give an eventual trace bound
for the smeared forward crossing kernels. Here `M` bounds the individual prime-log
weights, and `B` and `E` bound the diagonal and off-diagonal Gram entries, respectively.
The profiles need only agree with the normalized moments almost everywhere on
cell interiors. -/
public theorem eventually_kernel_trace_le_of_gram {α : Type*} {l : Filter α}
    {X D L h C : α → ℝ} {C₀ ε : ℝ} (hX : Tendsto X l atTop)
    (hY : Tendsto (fun a ↦ Real.exp (D a) / X a) l (𝓝 1))
    (hsmall : Tendsto (fun a ↦ h a / L a) l (𝓝 0))
    (hC : Tendsto C l (𝓝 C₀)) (hCnonneg : ∀ᶠ a in l, 0 ≤ C a) (hε : 0 < ε) :
    ∀ᶠ a in l, ∀ {J ι : Type*} [Fintype J] [Fintype ι] [Nonempty ι]
      {P : Partition J (L a) (Real.exp (D a)) (h a)} (A : PrimeAssignment P),
      0 < D a → 0 < L a → L a ≤ Real.exp (D a) → D a / 2 ≤ Real.log (L a) →
      ∀ {S : J → Finset ℤ} {W : J → ℤ → ℝ} {ξ : ℕ → ℂ} {χ : ι → ℤ → ℂ}
        {M B E : J → ℝ} {m : ι → ℝ → ℂ},
        (∀ j, 0 < P.right j - P.left j) →
        (∀ j, ∀ p ∈ A.cellPrimes j, (p.val : ℤ) ∈ S j) →
        (∀ j, ∀ n ∈ S j, 0 ≤ W j n) →
        (∀ j, ∀ p ∈ A.cellPrimes j, W j (p.val : ℤ) = 1) →
        (∀ p : ↥(primes (L a) (Real.exp (D a))), ‖ξ p.val‖ ≤ 1) →
        (∀ j, ∀ p ∈ A.cellPrimes j, Real.log (p.val : ℝ) ≤ M j) →
        (∀ j, 0 ≤ E j) →
        (∀ j i, ∑ n ∈ S j, W j n * ‖χ i n‖ ^ 2 ≤ B j) →
        (∀ j i k, i ≠ k → ‖ShortCellGramAssembly.gram (S j) (W j) χ i k‖ ≤ E j) →
        (∀ j, (M j / (P.right j - P.left j)) * (B j + ((Fintype.card ι - 1 : ℕ) : ℝ) * E j) ≤ C a) →
        (∀ i j, m i =ᵐ[volume.restrict (Ioo (P.left j) (P.right j))] fun _ ↦ A.gramMoment ξ χ i j) →
        (∑ i, ∫ x in ShortCellCrossing.leftHalf (D a), ∫ y in ShortCellCrossing.rightHalf (D a),
          ‖ShortCellCrossing.kernel (D a) (L a) (m i) x y‖ ^ 2) ≤ (C₀ + ε) * X a := by
  filter_upwards [eventually_kernel_trace_le_of_div hX hY hsmall hC hCnonneg hε] with a ha
  intro J ι _ _ _ P A hD hL hLY hhalf S W ξ χ M B E m hwidth hS hW hone hξ hlog hE hdiag hoff
    hcoef hconst
  exact ha A hD hL hLY hhalf (c := fun i j ↦ A.gramMoment ξ χ i j) hconst fun j ↦
    gramMoment_cellBudget A j (hwidth j) (hS j) (hW j) (hone j) hξ (hlog j) (hE j) (hdiag j)
      (hoff j) (hcoef j)

end ShortCellTrace
