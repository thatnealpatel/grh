module

public import Theorems.RationalAdeleLFFourierInversion
public import Theorems.RationalAdeleFourierParseval
import Theorems.RationalAdeleSchwartzDensity
import Lemmas.RationalAdeleStageNorm
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.MeasureTheory.Function.LpSpace.Complete

/-! # The rational adelic Plancherel extension

On the rational adelic frequency model, the normalized Fourier integral on
Schwartz functions extends uniquely to a complex-linear isometric equivalence of
`L²` with itself. This is a rational-model step toward (D.1.1.10), p. 747.
Agreement with the integral on every `L¹ ∩ L²` input and identification of the
full compact-open dual are separate obligations.
-/

open NumberField MeasureTheory
open scoped ENNReal

namespace Masullo

noncomputable section

local notation "A" => AdeleRing (𝓞 ℚ) ℚ
local notation "E" => RationalAdeleSchwartzLF
local notation "μA" => rationalAdeleAddHaar

set_option linter.concreteInstances false

variable [MeasurableSpace A] [BorelSpace A]

local notation "H" => Lp ℂ 2 μA

private theorem schwartz_memLp (f : E) : MemLp f.toUnion.val 2 μA := by
  obtain ⟨n, hn⟩ := mem_rationalAdeleSchwartzStageUnion.mp f.toUnion.property
  let b := rationalAdeleLFRead n f
  let hM := rationalAdeleFactorialLevel_pos n
  rw [← rationalAdeleLFAssembly_read n f hn, rationalAdeleLFAssembly_toUnion,
    rationalAdeleFactorialStageAssembly_val, rationalAdeleStageCoordinates_symm_eq_assembleProfiles hM]
  exact (rationalAdeleAssembleProfiles_norm_sq hM (fun j ↦ b j) fun j ↦ (b j).memLp 2 volume).1

/-- Take the almost-everywhere class of a rational adelic Schwartz function in
`L²` for normalized additive Haar. -/
public def rationalAdeleSchwartzToL2 : E →ₗ[ℂ] H where
  toFun f := (schwartz_memLp f).toLp f.toUnion.val
  map_add' f g := by
    simpa only [map_add, Submodule.coe_add] using (schwartz_memLp f).toLp_add (schwartz_memLp g)
  map_smul' c f := by
    simpa only [RingHom.id_apply, map_smul, Submodule.coe_smul] using
      (schwartz_memLp f).toLp_const_smul c

/-- The class of a Schwartz test is represented almost everywhere by the test. -/
public theorem rationalAdeleSchwartzToL2_ae_eq (f : E) :
    (rationalAdeleSchwartzToL2 f : A → ℂ) =ᵐ[μA] f.toUnion.val :=
  (schwartz_memLp f).coeFn_toLp

/-- The Schwartz classes are dense in `L²` for normalized additive Haar. -/
public theorem denseRange_rationalAdeleSchwartzToL2 :
    DenseRange (rationalAdeleSchwartzToL2 : E → H) := by
  intro u
  refine EMetric.mem_closure_iff.mpr fun ε hε ↦ ?_
  obtain ⟨f, _, hf⟩ := exists_rationalAdeleSchwartzLF_L2_approx (Lp.memLp u) hε
  refine ⟨rationalAdeleSchwartzToL2 f, ⟨f, rfl⟩, ?_⟩
  rw [Lp.edist_def, eLpNorm_congr_ae (Filter.EventuallyEq.rfl.sub (rationalAdeleSchwartzToL2_ae_eq f))]
  exact hf

private theorem norm_schwartzToL2 (f : E) :
    ‖rationalAdeleSchwartzToL2 f‖ = (∫ x, ‖f.toUnion.val x‖ ^ 2 ∂μA) ^ (2 : ℝ)⁻¹ := by
  change ‖(schwartz_memLp f).toLp f.toUnion.val‖ = _
  rw [Lp.norm_toLp, (schwartz_memLp f).eLpNorm_eq_integral_rpow_norm two_ne_zero ENNReal.ofNat_ne_top]
  simp only [ENNReal.toReal_ofNat, Real.rpow_two]
  exact ENNReal.toReal_ofReal (Real.rpow_nonneg (integral_nonneg fun _ ↦ sq_nonneg _) _)

private theorem norm_schwartzFourier (f : E) :
    ‖rationalAdeleSchwartzToL2 (rationalAdeleLFFourierEquiv f)‖ = ‖rationalAdeleSchwartzToL2 f‖ := by
  simp_rw [norm_schwartzToL2, rationalAdeleLFFourierEquiv_apply]
  rw [(rationalAdeleFourier_parseval f).2.2]

/-- The normalized rational adelic Fourier transform extends from the Schwartz
core to a unitary self-equivalence of `L²` on the rational adelic frequency model. -/
public def rationalAdeleL2Fourier : H ≃ₗᵢ[ℂ] H :=
  rationalAdeleLFFourierEquiv.toLinearEquiv.extendOfIsometry
    rationalAdeleSchwartzToL2 rationalAdeleSchwartzToL2
    denseRange_rationalAdeleSchwartzToL2 denseRange_rationalAdeleSchwartzToL2
    norm_schwartzFourier

/-- The `L²` transform sends each Schwartz class to its Fourier class. -/
public theorem rationalAdeleL2Fourier_onSchwartz (f : E) :
    rationalAdeleL2Fourier (rationalAdeleSchwartzToL2 f) =
      rationalAdeleSchwartzToL2 (rationalAdeleLFFourierEquiv f) :=
  LinearEquiv.extendOfIsometry_eq _ _ _ _ _ _ f

/-- On Schwartz inputs, the `L²` Fourier class is represented by the
normalized Fourier integral. -/
public theorem rationalAdeleL2Fourier_ae_eq_onSchwartz (f : E) :
    (rationalAdeleL2Fourier (rationalAdeleSchwartzToL2 f) : A → ℂ) =ᵐ[μA]
      rationalAdeleFourier f.toUnion.val := by
  rw [rationalAdeleL2Fourier_onSchwartz, ← funext (rationalAdeleLFFourierEquiv_apply f)]
  exact rationalAdeleSchwartzToL2_ae_eq _

/-- Agreement on the dense Schwartz core determines the `L²` transform
among all continuous maps. -/
public theorem rationalAdeleL2Fourier_unique {T : H → H} (hT : Continuous T)
    (h : ∀ f : E, T (rationalAdeleSchwartzToL2 f) =
      rationalAdeleSchwartzToL2 (rationalAdeleLFFourierEquiv f)) :
    T = (rationalAdeleL2Fourier : H → H) :=
  denseRange_rationalAdeleSchwartzToL2.equalizer hT rationalAdeleL2Fourier.continuous
    (funext fun f ↦ (h f).trans (rationalAdeleL2Fourier_onSchwartz f).symm)

end
end Masullo
