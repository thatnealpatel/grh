module

public import Props.BoundaryLogJet
public import Theorems.RationalThetaMellinLogMoments
public import Lemmas.RationalThetaWeightedLog

/-!
# Zeta jets annihilate the rational theta closure

This proves the closed-kernel inclusion for the log-line model of
(10.2.2.3)–(10.2.2.6), pp. 445–446. The theta profiles have been twisted
once, as in (10.1.1.3), p. 434. At the boundary we use the strict
integrability criterion. Neither the converse inclusion nor any
identification of adelic Haar measures is asserted.
-/

open MeasureTheory
open scoped FourierTransform SchwartzMap

namespace Masullo

/-- Every interior jet strictly below the open-strip zeta order vanishes
on the weighted log-line closure of the once-twisted rational theta inputs. -/
public theorem rationalThetaWeightedLog_closure_subset_ker (a : ℝ) {α s : ℝ}
    (hs : 0 ≤ s) {ρ : ℂ} (hpos : 0 < ρ.re) (hlt : ρ.re < 1)
    (hρ : |(ρ - (a : ℂ)).re| < α) {m : ℕ}
    (hm : (m : ℕ∞) < analyticOrderAt riemannZeta ρ) :
    closure (Set.range (rationalThetaWeightedLog a hs ((abs_nonneg _).trans hρ.le))) ⊆
      (interiorLogJet hs hρ m).ker := by
  apply closure_minimal _ (interiorLogJet hs hρ m).isClosed_ker
  rintro _ ⟨b, rfl⟩
  change interiorLogJet hs hρ m (rationalThetaWeightedLog a hs _ b) = 0
  rw [rationalThetaWeightedLog, (interiorLogJet_toLp hs hρ m _ _).2]
  exact (rationalTheta_twisted_logMoment_eq_zero b.val b.property.1 b.property.2 a hpos hlt hm).2

/-- A boundary jet below both the open-strip zeta order and the strict
Sobolev threshold vanishes on the weighted closure of the once-twisted
rational unramified theta inputs. This includes width zero. -/
public theorem rationalThetaWeightedLog_closure_subset_boundary_ker (a : ℝ) {α s : ℝ}
    (hs : 0 ≤ s) {ρ : ℂ} (hpos : 0 < ρ.re) (hlt : ρ.re < 1)
    (hρ : |(ρ - (a : ℂ)).re| = α) {m : ℕ}
    (hm : (m : ℕ∞) < analyticOrderAt riemannZeta ρ) (hcap : 2 * (m : ℝ) + 1 < s) :
    closure (Set.range (rationalThetaWeightedLog a hs (hρ ▸ abs_nonneg (ρ - (a : ℂ)).re))) ⊆
      (boundaryLogJet hs hρ hcap).ker := by
  apply closure_minimal _ (boundaryLogJet hs hρ hcap).isClosed_ker
  rintro _ ⟨b, rfl⟩
  change boundaryLogJet hs hρ hcap (rationalThetaWeightedLog a hs _ b) = 0
  rw [rationalThetaWeightedLog, (boundaryLogJet_toLp hs hρ hcap _ _).2]
  exact (rationalTheta_twisted_logMoment_eq_zero b.val b.property.1 b.property.2 a hpos hlt hm).2

end Masullo
