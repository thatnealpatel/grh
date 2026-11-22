module

public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace Masullo

section

variable {G : Type*} [Group G] [TopologicalSpace G]

/-- The log of a continuous positive multiplicative map, in multiplicative notation. -/
@[expose] public noncomputable def logPositiveHom (f : G →* ℝ)
    (hpos : ∀ g, 0 < f g) (hf : Continuous f) : G →ₜ* Multiplicative ℝ where
  toFun g := Multiplicative.ofAdd (Real.log (f g))
  map_one' := by rw [map_one, Real.log_one]; rfl
  map_mul' g k := by
    change Real.log (f (g * k)) = Real.log (f g) + Real.log (f k)
    rw [map_mul, Real.log_mul (hpos g).ne' (hpos k).ne']
  continuous_toFun := continuous_iff_continuousAt.mpr fun g ↦
    (Real.continuousAt_log (hpos g).ne').comp hf.continuousAt

public theorem mem_ker_logPositiveHom (f : G →* ℝ) (hpos : ∀ g, 0 < f g)
    (hf : Continuous f) (g : G) : g ∈ (logPositiveHom f hpos hf).toMonoidHom.ker ↔ f g = 1 := by
  change Real.log (f g) = 0 ↔ f g = 1
  constructor
  · intro h
    rw [← Real.exp_log (hpos g), h, Real.exp_zero]
  · intro h
    rw [h, Real.log_one]

end

variable {G H : Type*} [Group G] [Group H]
  [TopologicalSpace G] [TopologicalSpace H]

/-- The complementary kernel coordinate to a section of a group homomorphism. -/
@[expose] public def sectionKernelComponent (n : G →ₜ* H) (s : H →ₜ* G)
    (hs : ∀ x, n (s x) = x) (g : G) : n.toMonoidHom.ker :=
  ⟨(s (n g))⁻¹ * g, by
    change n ((s (n g))⁻¹ * g) = 1
    rw [map_mul, map_inv, hs, inv_mul_cancel]⟩

variable [IsTopologicalGroup G]

/-- A continuous homomorphic section with central image splits a continuous homomorphism. -/
@[expose] public def continuousMulEquivOfSection (n : G →ₜ* H) (s : H →ₜ* G)
    (hs : ∀ x, n (s x) = x) (hc : ∀ x g, Commute (s x) g) :
    (H × n.toMonoidHom.ker) ≃ₜ* G where
  toFun p := s p.1 * p.2
  invFun g := (n g, sectionKernelComponent n s hs g)
  map_mul' p q := by
    change s (p.1 * q.1) * ((p.2 : G) * q.2) = _
    rw [map_mul, mul_assoc, ← mul_assoc (s q.1), (hc q.1 p.2).eq]
    simp only [mul_assoc]
  left_inv p := by
    have hk : n (p.2 : G) = 1 := p.2.property
    have h : n (s p.1 * p.2) = p.1 := by rw [map_mul, hs, hk, mul_one]
    refine Prod.ext h (Subtype.ext ?_)
    change (s (n (s p.1 * p.2)))⁻¹ * (s p.1 * p.2) = (p.2 : G)
    rw [h, inv_mul_cancel_left]
  right_inv g := mul_inv_cancel_left _ _
  continuous_toFun := ((map_continuous s).comp continuous_fst).mul
    (continuous_subtype_val.comp continuous_snd)
  continuous_invFun := (map_continuous n).prodMk
    (((map_continuous s).comp (map_continuous n)).inv.mul continuous_id |>.subtype_mk
      (fun g ↦ (sectionKernelComponent n s hs g).property))

end Masullo
