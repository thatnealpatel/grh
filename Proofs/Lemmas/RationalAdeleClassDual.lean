module

public import Theorems.RationalAdeleClassFourierBasis
import Theorems.RationalAdelePoisson
import Mathlib.MeasureTheory.Group.Integral

/-! # Exhaustion of the adele class characters by rational frequencies -/

open NumberField MeasureTheory Topology
open scoped ComplexConjugate

namespace Masullo

local notation "A" => AdeleRing (𝓞 ℚ) ℚ
local notation "Cq" => A ⧸ rationalDiagonal

local instance : CompactSpace Cq := compactSpace_rationalAdeleClasses
local instance : T2Space Cq := t2Space_rationalAdeleClasses

/-- A continuous circle character of the additive adele classes is a rational
frequency: Otherwise every Fourier coefficient vanishes by Haar translation. -/
public theorem exists_rationalAdeleClassChar_eq (θ : Cq →+ Additive Circle)
    (hθ : Continuous θ) :
    ∃ r : ℚ, ∀ c : Cq, rationalAdeleClassChar r c = (θ c).toMul.val := by
  let : MeasurableSpace A := borel A
  let : BorelSpace A := ⟨rfl⟩
  let : MeasurableSpace Cq := borel Cq
  let : BorelSpace Cq := ⟨rfl⟩
  let g : C(Cq, ℂ) := ⟨fun c ↦ (θ c).toMul.val, continuous_subtype_val.comp hθ⟩
  have hg_add (c d : Cq) : g (c + d) = g c * g d := by
    change (↑(θ (c + d)).toMul : ℂ) = _
    rw [map_add]
    exact Circle.coe_mul _ _
  have hg_norm (c : Cq) : ‖g c‖ = 1 := Circle.norm_coe _
  change ∃ r : ℚ, ∀ c : Cq, rationalAdeleClassChar r c = g c
  by_contra! hn
  have hcoeff (r : ℚ) : rationalAdeleClassFourierCoeff g r = 0 := by
    let f (c : Cq) := g c * conj (rationalAdeleClassChar r c)
    obtain ⟨d, hd⟩ := hn r
    have hχ (c : Cq) : rationalAdeleClassChar r c ≠ 0 := by
      intro h
      simpa [h] using norm_rationalAdeleClassChar r c
    have hne : f d ≠ 1 := by
      rw [show f d = g d * (rationalAdeleClassChar r d)⁻¹ from
        congrArg (g d * ·) (Complex.inv_eq_conj (norm_rationalAdeleClassChar r d)).symm,
        ← div_eq_mul_inv]
      exact fun h ↦ hd (div_eq_one_iff_eq (hχ d) |>.mp h).symm
    have hshift (c : Cq) : f (d + c) = f d * f c := by
      dsimp [f]
      rw [hg_add, AddChar.map_add_eq_mul, map_mul]
      ring
    have ht := integral_add_left_eq_self (μ := rationalAdeleClassHaar) f d
    simp only [hshift, integral_const_mul] at ht
    change (∫ c, f c ∂rationalAdeleClassHaar) = 0
    by_contra hz
    apply hne
    exact mul_right_cancel₀ hz (ht.trans (one_mul _).symm)
  have hsum := hasSum_rationalAdeleClassFourier g (by simp [hcoeff])
  simp only [hcoeff, zero_smul] at hsum
  have hz := congrArg (fun h : C(Cq, ℂ) ↦ h 0) (hsum.unique hasSum_zero)
  exact one_ne_zero (by simpa [hz] using hg_norm 0 : (1 : ℝ) = 0)

end Masullo
