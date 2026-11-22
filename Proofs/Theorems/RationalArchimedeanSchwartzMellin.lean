module

public import Theorems.IdeleHeckeGaussian
public import Theorems.RealCompletionSchwartzMellin
import Mathlib.MeasureTheory.Constructions.Pi

/-! # The flat Schwartz pairing on the rational Archimedean block

The grouped infinite density of `ideleFiniteStage_zetaIntegral` over `ℚ`
is the pullback of the real completion density. Evaluation preserves the
full signed Haar measure, without a factor of two or a probability rescaling.
This supplies the real input for the compact-away repair of Lemma 5.3.4.2(2),
PDF pp. 259–261, not for its printed finite test space.
-/

open MeasureTheory NumberField InfinitePlace.Completion
open scoped SchwartzMap

namespace Masullo

set_option quotPrecheck false in
local notation "A" => ((v : InfinitePlace ℚ) → v.Completionˣ)
local notation "U" => Rat.infinitePlace.Completionˣ
local notation "ev" => (fun x : A ↦ x Rat.infinitePlace)
local notation "μa" => (fun v : InfinitePlace ℚ ↦ archimedeanCompletionHaar v)
local notation "μr" => (realCompletionHaar Rat.isReal_infinitePlace)

-- Match the Borel instances of the ambient stage theorem.
set_option linter.concreteInstances false

variable [ma : ∀ v : InfinitePlace ℚ, MeasurableSpace v.Completionˣ]
  [ba : ∀ v : InfinitePlace ℚ, BorelSpace v.Completionˣ]

/-- Evaluating at the sole Archimedean place preserves the full signed real
completion Haar measure. -/
public theorem rationalArchimedeanEval_measurePreserving : MeasurePreserving ev (Measure.pi μa) μr := by
  let : Unique (InfinitePlace ℚ) := ⟨⟨Rat.infinitePlace⟩, fun _ ↦ Subsingleton.elim _ _⟩
  have h : MeasurePreserving ev (Measure.pi μa) (μa Rat.infinitePlace) :=
    measurePreserving_piUnique (X := fun v : InfinitePlace ℚ ↦ v.Completionˣ) μa
  rw [show μa Rat.infinitePlace = μr by
    simp only [archimedeanCompletionHaar, dite_eq_left Rat.isReal_infinitePlace]] at h
  exact h

/-- The grouped rational Archimedean factor for a flat Schwartz profile is
absolutely integrable for every complex exponent and equals the raw real
completion pairing with the same character. -/
public theorem rationalArchimedeanSchwartzMellinPair
    (χ : HeckeCharacter (𝓞 ℚ) ℚ) (hχ : ∀ x : IdeleClassGroup (𝓞 ℚ) ℚ, ‖χ x‖ = 1)
    (b : 𝓢(ℝ, ℂ)) (hflat : ∀ j : ℕ, iteratedDeriv j (b : ℝ → ℂ) 0 = 0) (s : ℂ) :
    let arch (x : A) := b (extensionEmbeddingOfIsReal Rat.isReal_infinitePlace (ev x).val)
    let G (x : A) := arch x *
      (∏ v : InfinitePlace ℚ, χ (IdeleClassGroup.ofCompletion (𝓞 ℚ) ℚ v (x v))) *
      ((∏ v : InfinitePlace ℚ, ‖(x v : v.Completion)‖ ^ v.mult : ℝ) : ℂ) ^ s
    let F (u : U) := b (extensionEmbeddingOfIsReal Rat.isReal_infinitePlace u.val) *
      χ (IdeleClassGroup.ofCompletion (𝓞 ℚ) ℚ Rat.infinitePlace u) *
      (((‖u.val‖ ^ Rat.infinitePlace.mult : ℝ) : ℂ) ^ s)
    Integrable G (Measure.pi μa) ∧
      (∫ x, G x ∂Measure.pi μa) = ∫ u, F u ∂μr := by
  intro arch G F
  have hGF : G = F ∘ ev := by
    funext x
    simp only [G, F, arch, Function.comp_apply, Fintype.prod_subsingleton _ Rat.infinitePlace]
  rw [hGF]
  obtain ⟨_, _, _, _, h⟩ := realCompletionSchwartzMellinPair χ hχ Rat.isReal_infinitePlace b hflat
  have hi : Integrable F μr := (h s).1
  have he : MeasurableEmbedding ev := by
    let : Unique (InfinitePlace ℚ) := ⟨⟨Rat.infinitePlace⟩, fun _ ↦ Subsingleton.elim _ _⟩
    exact (MeasurableEquiv.piUnique (fun v : InfinitePlace ℚ ↦ v.Completionˣ)).measurableEmbedding
  exact ⟨rationalArchimedeanEval_measurePreserving.integrable_comp_of_integrable hi,
    rationalArchimedeanEval_measurePreserving.integral_comp he F⟩

end Masullo
