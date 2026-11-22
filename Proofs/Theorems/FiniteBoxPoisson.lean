module

public import Theorems.ArchimedeanTracePoisson
public import Theorems.FiniteBoxDiagonalCoset
public import Theorems.FiniteBoxFourier

/-! # Translated finite-box Poisson summation

Masullo states adelic Riemann–Roch in Theorem 2.2.3.2 (PDF p. 82), with
separate zero-mode corrections, and uses a product of local Fourier integrals
in (2.2.4.32) (p. 92) for a differentiated tensor with compactly supported
infinite factor. The former invokes an adelic theorem and does not give this
lattice argument. For one translated finite box, we prove the equality
of the two full diagonal sums by reindexing the spatial sum on the ideal
lattice and the frequency sum on the trace dual. In place of importing adelic
Riemann–Roch, `archimedeanIdeal_tracePoisson` gives the shifted lattice identity,
and `finiteBox_fourier_finprod` supplies its phase and reciprocal covolume.
This does not identify the product with the global adelic integral.
Source reading: Provisional pinned Markdown and numbered PDF layout.
-/

open Function IsDedekindDomain MeasureTheory NumberField NumberField.InfinitePlace
open scoped Classical InnerProductSpace SchwartzMap nonZeroDivisors WithZero

namespace Masullo

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

local notation "V" => HeightOneSpectrum (𝓞 K)
local notation "F" => FiniteAdeleRing (𝓞 K) K
local notation "Eucl" => mixedEmbedding.euclidean.mixedSpace K
local notation "ι" => archimedeanEuclideanEmbedding K
local notation "K[" v "]" => HeightOneSpectrum.adicCompletion K v
local notation "w[" v "]" => (Valued.v : Valuation K[v] ℤᵐ⁰)
local notation "k[" v "]" => algebraMap K K[v]

omit [Field K] [NumberField K] in
private theorem diagonalSeries_on_support (S : Set K) (f : K → ℂ) (h : ∀ x ∉ S, f x = 0) :
    (Summable (fun x : S ↦ ‖f x‖) ↔ Summable (fun x : K ↦ ‖f x‖)) ∧
      ∑' x : S, f x = ∑' x : K, f x := by
  refine ⟨?_, tsum_subtype_eq_of_support_subset ?_⟩
  · exact Subtype.val_injective.summable_iff (g := (Subtype.val : S → K))
      (f := fun x ↦ ‖f x‖) (by simpa only [Subtype.range_coe, norm_eq_zero] using h)
  · intro x hx
    exact by_contra fun hn ↦ hx (h x hn)

/-- For a Schwartz input at infinity and a translated box at the finite places,
both full diagonal series converge absolutely and agree. On the frequency
side the factors are the local Fourier integrals, not a presupposed global
transform. Both sums range over all of `K`, including zero. -/
public theorem finiteBox_diagonal_poisson (a : F) (g : Fˣ) (φ : 𝓢(Eucl, ℂ)) :
    let S : Set K := {x | ∀ v : V, w[v] (k[v] x - a v) ≤ w[v] (g.val v)}
    let p (x : K) := S.indicator (φ ∘ ι) x
    let q (y : K) := archimedeanTraceFourier K φ (ι y) *
      ∏ᶠ v : V, finiteBoxLocalFourier a g y v
    Summable (fun x ↦ ‖p x‖) ∧ Summable (fun y ↦ ‖q y‖) ∧
      ∑' x, p x = ∑' y, q y := by
  intro S p q
  let I := finiteIdeleIdeal K g
  let L := archimedeanIdealLattice K I
  let D : Set K := FractionalIdeal.dual ℤ ℚ I.val
  obtain ⟨x₀, hcoset⟩ := exists_finiteBox_diagonalCoset a g
  have hx₀ : x₀ ∈ S := (hcoset x₀).2 (by rw [sub_self]; exact I.val.zero_mem)
  -- Subtract the chosen diagonal point and embed the resulting ideal in Euclidean space.
  let e₀ (x : S) : L := ⟨ι ((x : K) - x₀), (mem_archimedeanIdealLattice K I _).2
    ⟨_, (hcoset x).1 x.property, rfl⟩⟩
  have hι : Injective ι := (mixedEmbedding.euclidean.toMixed K).symm.injective.comp
    (mixedEmbedding_injective K)
  let e : S ≃ L := Equiv.ofBijective e₀ ⟨fun x y h ↦
    Subtype.ext (sub_left_inj.mp (hι (congrArg Subtype.val h))), fun u ↦ by
      obtain ⟨z, hz, he⟩ := (mem_archimedeanIdealLattice K I u).1 u.property
      have hsub : x₀ + z - x₀ = z := by abel
      exact ⟨⟨x₀ + z, (hcoset _).2 (hsub.symm ▸ hz)⟩,
        Subtype.ext (by simpa only [e₀, hsub])⟩⟩
  have hp (x : S) : p x = φ (ι x₀ + (e x : Eucl)) := by
    dsimp only [p]
    rw [Set.indicator_of_mem x.property]
    change φ (ι x) = φ (ι x₀ + ι ((x : K) - x₀))
    have hadd (x y : K) : ι (x + y) = ι x + ι y := by simp [archimedeanEuclideanEmbedding]
    rw [← hadd, show x₀ + ((x : K) - x₀) = x by abel]
  obtain ⟨hpL, hqD, hP⟩ := archimedeanIdeal_tracePoisson K I φ (ι x₀)
  dsimp only at hpL hqD hP
  -- The finite product is supported on the trace dual, with precisely the Poisson coefficient.
  let c : ℂ := ((↑(ZLattice.covolume L (archimedeanTraceMeasure K)) : ℂ)⁻¹)
  let r (y : D) :=
    let f := archimedeanTraceFrequency K (ι y)
    Complex.exp ((↑(2 * Real.pi * ⟪ι x₀, f⟫_ℝ) : ℂ) * Complex.I) *
      archimedeanTraceFourier K φ (ι y)
  change Summable (fun y : D ↦ ‖r y‖) at hqD
  change ∑' u : L, φ (ι x₀ + u) = c * ∑' y : D, r y at hP
  have hz (y : K) (hy : y ∉ D) : q y = 0 := by
    change y ∉ FractionalIdeal.dual ℤ ℚ I.val at hy
    dsimp only [q]
    rw [(finiteBox_fourier_finprod a g x₀ y hx₀).2, ite_eq_right hy, mul_zero]
  have hq (y : D) : q y = c * r y := by
    have hy : (y : K) ∈ FractionalIdeal.dual ℤ ℚ I.val := y.property
    dsimp only [q]
    rw [(finiteBox_fourier_finprod a g x₀ y hx₀).2, ite_eq_left hy]
    dsimp only [r, c, L, I]
    rw [inner_archimedeanEuclideanEmbedding_traceFrequency, Complex.ofReal_inv]
    push_cast
    ring_nf
  obtain ⟨hpNorm, hpSum⟩ := diagonalSeries_on_support S p (fun x hx ↦
    Set.indicator_of_notMem hx _)
  obtain ⟨hqNorm, hqSum⟩ := diagonalSeries_on_support D q hz
  refine ⟨hpNorm.1 ?_, hqNorm.1 ?_, ?_⟩
  · have he := (e.summable_iff (f := fun u : L ↦ ‖φ (ι x₀ + (u : Eucl))‖)).2 hpL
    change Summable (fun x : S ↦ ‖φ (ι x₀ + (e x : Eucl))‖) at he
    simpa only [hp] using he
  · simpa only [hq, norm_mul] using hqD.mul_left ‖c‖
  · calc
      ∑' x : K, p x = ∑' x : S, p x := hpSum.symm
      _ = ∑' u : L, φ (ι x₀ + u) := by
        simp_rw [hp]
        exact e.tsum_eq (fun u : L ↦ φ (ι x₀ + (u : Eucl)))
      _ = c * ∑' y : D, r y := hP
      _ = ∑' y : D, q y := by simp_rw [hq, tsum_mul_left]
      _ = ∑' y : K, q y := hqSum

end

end Masullo
