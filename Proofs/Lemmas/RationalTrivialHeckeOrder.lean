module

public import Lemmas.CompletedZetaOrders
public import Lemmas.IdeleClassStripDivisor
public import Lemmas.RationalTrivialFiniteEulerProduct
public import Lemmas.TrivialRealHeckeGamma

open Complex NumberField

namespace Masullo

local notation "χ₀" => (1 : HeckeCharacter (𝓞 ℚ) ℚ)

/-- On the Euler half-plane the completed trivial rational product is completed zeta. -/
public theorem completedHeckeEulerProduct_one_rat {s : ℂ} (hs : 1 < s.re) :
    completedHeckeEulerProduct χ₀ (fun _ ↦ norm_one) s = completedRiemannZeta s := by
  let : Unique (InfinitePlace ℚ) := ⟨⟨Rat.infinitePlace⟩, fun _ ↦ Subsingleton.elim _ _⟩
  rw [completedHeckeEulerProduct, Fintype.prod_unique, show (default : InfinitePlace ℚ) = Rat.infinitePlace from
    Subsingleton.elim _ _, finiteHeckeCharacterEulerProduct_one_rat hs,
    localHeckeGammaFactor_one_real_eq_Gammaℝ _ Rat.isReal_infinitePlace,
    riemannZeta_def_of_ne_zero (by rintro rfl; norm_num at hs),
    mul_div_cancel₀ _ (Gammaℝ_ne_zero_of_re_pos (zero_lt_one.trans hs))]

/-- The chosen continuation on the rational norm-power component has exactly the
signed orders of completed zeta, including at its poles. -/
public theorem ideleClassHeckeOrder_normPower_rat (s : ℂ) :
    ideleClassHeckeOrder (ideleClassNormPower (K := ℚ) s) =
      meromorphicOrderAt completedRiemannZeta s := by
  rw [ideleClassHeckeOrder_eq _ meromorphicAt_completedZeta, ideleClassNormExponent_normPower]
  intro z hz
  simpa only [ideleClassHeckeBase_normPower] using (completedHeckeEulerProduct_one_rat hz).symm

end Masullo
