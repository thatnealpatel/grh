module

public import Lemmas.RationalAdeleThetaDerivative

/-! # Differentiating theta on rational idele classes

This is Lemma 2.2.4.3, (2.2.4.7), pp. 88–91, for the positive real
norm section and the rational Schwartz LF model. No zero-mode
conditions are needed.
-/

open NumberField

namespace Masullo

local notation "C" => IdeleClassGroup (𝓞 ℚ) ℚ
local notation "E" => RationalAdeleSchwartzLF
local notation "τ" => fun t : ℝ ↦ rationalIdeleClassLogSection (Multiplicative.ofAdd t)

/-- The theta function of every rational Schwartz LF test is continuous
on the idele class group, in particular for the derivative test `Df`. -/
public theorem continuous_rationalAdeleClassTheta_LF (f : E) :
    Continuous (rationalAdeleClassTheta f.toUnion.val) := by
  obtain ⟨_, b, a, g, hf⟩ := exists_rationalAdeleLF_eq_boxSum f
  rw [hf]
  exact continuous_rationalAdeleClassTheta_boxSum Finset.univ (fun _ ↦ 1) b a g

/-- Along the positive real norm section, the derivative of class theta
is class theta of the dilation generator, at every log scale. Together
with continuity for the derivative test, this gives (2.2.4.7). -/
public theorem hasDerivAt_rationalAdeleClassTheta_logDilation (f : E) (d : C) (s : ℝ) :
    HasDerivAt (fun t : ℝ ↦ rationalAdeleClassTheta f.toUnion.val (τ t * d))
      (rationalAdeleClassTheta (rationalAdeleLFDilationDeriv f).toUnion.val (τ s * d)) s := by
  obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective d
  simpa only [rationalIdeleClassLogSection_apply, ← QuotientGroup.mk_mul,
    rationalAdeleClassTheta_mk] using hasDerivAt_rationalAdeleTheta_logDilation f k s

end Masullo
