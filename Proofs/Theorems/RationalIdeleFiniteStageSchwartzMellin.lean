module

public import Theorems.IdeleFiniteStageIntegral
public import Theorems.RationalArchimedeanSchwartzMellin
public import Theorems.RationalFiniteCompactMellin
import Mathlib.Analysis.Calculus.Deriv.Mul

/-! # Entire raw zeta pairing on a rational idele stage

For the compact-away repair to Lemma 5.3.4.2(2), PDF pp. 259–261, the
raw pairing of one pure tensor on the exact stage factors with no
scalar. The full signed real pairing and every active finite pairing
are entire. This does not identify the stage with the global integral.
-/

open IsDedekindDomain MeasureTheory NumberField InfinitePlace.Completion Set
open scoped SchwartzMap

namespace Masullo

local notation "V" => HeightOneSpectrum (𝓞 ℚ)
local notation "Iℚ" => IdeleGroup (𝓞 ℚ) ℚ
local notation "F" v => HeightOneSpectrum.adicCompletion ℚ v
set_option quotPrecheck false in
local notation "A" => ((v : InfinitePlace ℚ) → v.Completionˣ)
local notation "w" => Rat.infinitePlace
local notation "μa" => (fun v : InfinitePlace ℚ ↦ archimedeanCompletionHaar v)
local notation "μf" => (fun v : V ↦ rationalLocalMultiplicativeHaar v)

set_option linter.concreteInstances false

variable [ma : ∀ v : InfinitePlace ℚ, MeasurableSpace v.Completionˣ]
  [mf : ∀ v : V, MeasurableSpace (F v)ˣ]
  [mu : ∀ v : V, MeasurableSpace (v.adicCompletionIntegers ℚ)ˣ]
  [ba : ∀ v : InfinitePlace ℚ, BorelSpace v.Completionˣ]
  [bf : ∀ v : V, BorelSpace (F v)ˣ]
  [bu : ∀ v : V, BorelSpace (v.adicCompletionIntegers ℚ)ˣ]
  [MeasurableSpace Iℚ] [BorelSpace Iℚ]

/-- A flat real Schwartz profile and continuous compactly supported active
finite profiles give an absolutely integrable raw zeta density on the exact
stage at every exponent. Its integral is the product of the full real pairing
and the active finite pairings, and is entire. -/
public theorem rationalIdeleFiniteStage_schwartzMellin (S : Finset V) (μ : Measure Iℚ)
    (hμ : μ.comap (ideleFiniteStageEmbedding ℚ S) = ideleFiniteStageProduct ℚ μa μf S)
    (χ : HeckeCharacter (𝓞 ℚ) ℚ) (hu : ∀ v ∉ S, χ.IsUnramifiedAt v)
    (hχ : ∀ x : IdeleClassGroup (𝓞 ℚ) ℚ, ‖χ x‖ = 1)
    (b : 𝓢(ℝ, ℂ)) (hflat : ∀ j : ℕ, iteratedDeriv j (b : ℝ → ℂ) 0 = 0)
    (f : (v : V) → (F v)ˣ → ℂ) (hf : ∀ v ∈ S, Continuous (f v))
    (hc : ∀ v ∈ S, HasCompactSupport (f v)) :
    let arch (x : A) := b (extensionEmbeddingOfIsReal Rat.isReal_infinitePlace (x w).val)
    let g (s : ℂ) (a : Iℚ) := ideleZetaTest ℚ S arch f a *
      χ (QuotientGroup.mk' (IdeleGroup.principalSubgroup (𝓞 ℚ) ℚ) a) *
      (‖(a : AdeleRing (𝓞 ℚ) ℚ)‖ : ℂ) ^ s
    let R (s : ℂ) := ∫ u : Rat.infinitePlace.Completionˣ,
      b (extensionEmbeddingOfIsReal Rat.isReal_infinitePlace u.val) *
        χ (IdeleClassGroup.ofCompletion (𝓞 ℚ) ℚ w u) *
        (((‖u.val‖ ^ Rat.infinitePlace.mult : ℝ) : ℂ) ^ s) ∂realCompletionHaar Rat.isReal_infinitePlace
    let L (v : {v // v ∈ S}) (s : ℂ) := ∫ u : (F v.val)ˣ,
      f v u * χ.restrict v (u : F v.val) * (‖(u : F v.val)‖ : ℂ) ^ s ∂μf v.val
    let T (s : ℂ) := ∫ a in range (ideleFiniteStageEmbedding ℚ S), g s a ∂μ
    (∀ s, IntegrableOn (g s) (range (ideleFiniteStageEmbedding ℚ S)) μ ∧
      T s = R s * ∏ v, L v s) ∧ Differentiable ℂ T := by
  intro arch g R L T
  have hFin (v : {v // v ∈ S}) := rationalFiniteCompactMellinPair v.val χ (f v)
    (hf v v.property) (hc v v.property)
  have hTest (v : {v // v ∈ S}) (x : (F v.val)ˣ) : ideleFiniteTest ℚ S f v x = f v x := by
    simp only [ideleFiniteTest, ite_eq_left v.property]
  have hFactor (s : ℂ) : IntegrableOn (g s) (range (ideleFiniteStageEmbedding ℚ S)) μ ∧
      T s = R s * ∏ v, L v s := by
    obtain ⟨hA, hRealValue⟩ := rationalArchimedeanSchwartzMellinPair χ hχ b hflat s
    obtain ⟨hi, hValue, _⟩ := ideleFiniteStage_zetaIntegral ℚ μa μf S S Subset.rfl
      (fun v _ ↦ rationalLocalMultiplicativeHaar_unitMass v) μ hμ χ hu s arch f hA (fun v ↦ by
        obtain ⟨⟨_, _, _, _, hs⟩, _⟩ := hFin v
        simpa only [hTest] using (hs s).1)
    rw [hRealValue] at hValue
    exact ⟨hi, by simpa only [hTest] using hValue⟩
  refine ⟨hFactor, ?_⟩
  -- The parity and radial frequency do not depend on the Mellin parameter.
  obtain ⟨ε, τ, _, _, hReal⟩ := realCompletionSchwartzMellinPair χ hχ Rat.isReal_infinitePlace b hflat
  have hR (s : ℂ) : R s =
      ∫ t : ℝ, realSchwartzParityLogProfile b ε t * Complex.exp ((s + (τ : ℂ) * Complex.I) * t) :=
    (hReal s).2
  have hdR : Differentiable ℂ R := by
    rw [funext hR]
    exact (differentiable_realSchwartzParityLog_mellin b hflat ε).comp
      (differentiable_id.add_const ((τ : ℂ) * Complex.I))
  rw [show T = (fun s ↦ R s * ∏ v, L v s) from funext fun s ↦ (hFactor s).2]
  exact hdR.mul (Differentiable.fun_finsetProd fun v _ ↦ (hFin v).2)

end Masullo
