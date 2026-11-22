module

public import Theorems.RationalIdeleFiniteStageSchwartzMellin
public import Theorems.IdeleZetaIntegral

/-! # Raw upstairs pairing of a repaired rational pure tensor

With exact product-Haar comaps on the cofinal stages, the entire stage pairing
for the compact-away repair of Lemma 5.3.4.2(2), PDF pp. 259–261, determines the
raw upstairs pairing above one after multiplication by the Euler tail off the
actual stage. This is not the printed modified-factor identity (3.4.1.6),
p. 143, or a continuation of the upstairs Lebesgue integral.
-/

open IsDedekindDomain MeasureTheory NumberField InfinitePlace.Completion Set
open scoped SchwartzMap Classical

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

/-- For one repaired rational pure tensor, the raw upstairs zeta integral is
absolutely convergent above one and is the integral on the exact stage times
the finite Euler tail off that stage. Both integrals use the same measure. -/
public theorem rationalIdeleZetaIntegral_schwartzMellin (S : Finset V) (μ : Measure Iℚ)
    (hμ : ∀ U : Finset V, S ⊆ U →
      μ.comap (ideleFiniteStageEmbedding ℚ U) = ideleFiniteStageProduct ℚ μa μf U)
    (χ : HeckeCharacter (𝓞 ℚ) ℚ) (hu : ∀ v ∉ S, χ.IsUnramifiedAt v)
    (hχ : ∀ x : IdeleClassGroup (𝓞 ℚ) ℚ, ‖χ x‖ = 1)
    (b : 𝓢(ℝ, ℂ)) (hflat : ∀ j : ℕ, iteratedDeriv j (b : ℝ → ℂ) 0 = 0)
    (f : (v : V) → (F v)ˣ → ℂ) (hf : ∀ v ∈ S, Continuous (f v))
    (hc : ∀ v ∈ S, HasCompactSupport (f v)) (s : ℂ) (hs : 1 < s.re) :
    let arch (x : A) := b (extensionEmbeddingOfIsReal Rat.isReal_infinitePlace (x w).val)
    let g (s : ℂ) (a : Iℚ) := ideleZetaTest ℚ S arch f a *
      χ (QuotientGroup.mk' (IdeleGroup.principalSubgroup (𝓞 ℚ) ℚ) a) *
      (‖(a : AdeleRing (𝓞 ℚ) ℚ)‖ : ℂ) ^ s
    let T := ∫ a in range (ideleFiniteStageEmbedding ℚ S), g s a ∂μ
    let z (v : V) := if v ∈ S then 0 else finiteHeckeCoefficient χ v
    Integrable (g s) μ ∧ (∫ a, g s a ∂μ) = T * finiteHeckeEulerProduct z s := by
  intro arch g T z
  obtain ⟨hA, hRealValue⟩ := rationalArchimedeanSchwartzMellinPair χ hχ b hflat s
  obtain ⟨hi, hVal, _⟩ := ideleZetaIntegral_rightHalfPlane ℚ μa μf S S Subset.rfl
    (fun v _ ↦ rationalLocalMultiplicativeHaar_unitMass v) μ hμ χ hu hχ s hs arch f hA
    (fun v hv ↦ by
      obtain ⟨⟨_, _, _, _, h⟩, _⟩ := rationalFiniteCompactMellinPair v χ (f v) (hf v hv) (hc v hv)
      simpa only [ideleFiniteTest, ite_eq_left hv] using (h s).1)
  have hStage := ((rationalIdeleFiniteStage_schwartzMellin S μ (hμ S Subset.rfl)
    χ hu hχ b hflat f hf hc).1 s).2
  refine ⟨hi, hVal.trans (congrArg (· * finiteHeckeEulerProduct z s) ?_)⟩
  symm
  rw [hRealValue]
  rw [← Finset.prod_coe_sort (s := S)]
  simpa only [ideleFiniteTest, ite_eq_left (Subtype.property _)] using hStage

end Masullo
