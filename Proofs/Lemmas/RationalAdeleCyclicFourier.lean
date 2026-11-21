module

public import Theorems.RationalAdeleStageFourier
public import Mathlib.Analysis.Fourier.ZMod

/-! # The cyclic Fourier matrix on a rational adelic stage

The normalized finite Fourier transform is `M` times Mathlib's inverse
DFT at modulus `M²`. The sign comes from triviality of the full adelic
character on rational diagonals, not from a choice of a finite pairing.
-/

open NumberField IsDedekindDomain
open scoped ComplexConjugate FourierTransform SchwartzMap

namespace Masullo

noncomputable section

local notation "F" => FiniteAdeleRing (𝓞 ℚ) ℚ
local notation "S" => 𝓢(ℝ, ℂ)
local notation "rep" => rationalAdeleStageRepresentative

private theorem finEquiv_eq_cast {N : ℕ} [NeZero N] (j : Fin N) :
    ZMod.finEquiv N j = (j.val : ZMod N) := by
  apply ZMod.val_injective N
  rw [ZMod.val_natCast_of_lt j.isLt]
  cases N with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ n => rfl

/-- After identifying the cells with cyclic residues, the conjugated finite
phase of the adelic Fourier matrix is Mathlib's positive cyclic phase. -/
public theorem rationalAdeleStageFourier_phase {M : ℕ} [NeZero M] (j k : Fin (M ^ 2)) :
    conj (rationalFiniteAdeleAddChar (rep M j * rep M k)) =
      ZMod.stdAddChar ((j.val : ZMod (M ^ 2)) * (k.val : ZMod (M ^ 2))) := by
  let r : ℚ := (j.val : ℚ) * (k.val : ℚ) / (M : ℚ) ^ 2
  have hrep : rep M j * rep M k = algebraMap ℚ F r := by
    rw [rationalAdeleStageRepresentative, rationalAdeleStageRepresentative, ← map_mul]
    congr 1
    simp only [r, div_mul_div_comm, pow_two]
  rw [hrep, conj_rationalFiniteAdeleAddChar_algebraMap, ← Nat.cast_mul,
    ← Int.cast_natCast (R := ZMod (M ^ 2)), ZMod.stdAddChar_coe]
  congr 1
  dsimp [r]
  push_cast
  ring

private def cyclicDFT {N : ℕ} [NeZero N] : (ZMod N → S) ≃L[ℂ] (ZMod N → S) where
  toLinearEquiv := ZMod.dft
  continuous_toFun := continuous_pi fun k ↦ by
    change Continuous (fun b : ZMod N → S ↦ ZMod.dft b k)
    simp only [ZMod.dft_apply]
    exact continuous_finsetSum _ fun j _ ↦ (continuous_apply j).const_smul
      (ZMod.stdAddChar (-(j * k)) : ℂ)
  continuous_invFun := continuous_pi fun k ↦ by
    change Continuous (fun b : ZMod N → S ↦ (ZMod.dft (E := S)).symm b k)
    simp only [ZMod.invDFT_apply]
    exact (continuous_finsetSum Finset.univ fun j _ ↦ (continuous_apply j).const_smul
      (ZMod.stdAddChar (j * k) : ℂ)).const_smul ((N : ℂ)⁻¹)

private def finiteScale {M : ℕ} [NeZero M] : (ZMod (M ^ 2) → S) ≃L[ℂ] (ZMod (M ^ 2) → S) where
  toLinearEquiv := LinearEquiv.smulOfNeZero ℂ _ (M : ℂ) (NeZero.ne (M : ℂ))
  continuous_toFun := continuous_id.const_smul (M : ℂ)
  continuous_invFun := continuous_id.const_smul (M : ℂ)⁻¹

private def residues {M : ℕ} [NeZero M] : (Fin (M ^ 2) → S) ≃L[ℂ] (ZMod (M ^ 2) → S) :=
  let e := (ZMod.finEquiv (M ^ 2)).toEquiv
  { toFun := fun b z ↦ b (e.symm z)
    invFun := fun b j ↦ b (e j)
    left_inv := fun b ↦ funext fun j ↦ congrArg b (e.symm_apply_apply j)
    right_inv := fun b ↦ funext fun z ↦ congrArg b (e.apply_symm_apply z)
    map_add' := fun _ _ ↦ rfl
    map_smul' := fun _ _ ↦ rfl
    continuous_toFun := continuous_pi fun z ↦ continuous_apply (e.symm z)
    continuous_invFun := continuous_pi fun j ↦ continuous_apply (e j) }

/-- The stage Fourier equivalence: Apply the real Schwartz transform to each
profile, and then the Haar-normalized inverse cyclic DFT to the tuple. -/
public def rationalAdeleStageFourierEquiv {M : ℕ} (hM : 0 < M) :
    (Fin (M ^ 2) → S) ≃L[ℂ] (Fin (M ^ 2) → S) :=
  letI : NeZero M := ⟨hM.ne'⟩
  (ContinuousLinearEquiv.piCongrRight fun _ ↦ FourierTransform.fourierCLE ℂ S).trans
    (residues.trans (cyclicDFT.symm.trans (finiteScale.trans residues.symm)))

/-- The equivalence has the same forward map as the adelic Fourier matrix. -/
public theorem rationalAdeleStageFourierEquiv_apply {M : ℕ} (hM : 0 < M) (b : Fin (M ^ 2) → S) :
    rationalAdeleStageFourierEquiv hM b = rationalAdeleStageFourier M b := by
  let : NeZero M := ⟨hM.ne'⟩
  let e := (ZMod.finEquiv (M ^ 2)).toEquiv
  funext k
  change ((M : ℂ) • (ZMod.dft (E := S)).symm (fun j ↦ 𝓕 (b (e.symm j)))) (e k) = _
  rw [Pi.smul_apply, ZMod.invDFT_apply, smul_smul, rationalAdeleStageFourier_apply]
  have hweight : (M : ℂ) * ((M ^ 2 : ℕ) : ℂ)⁻¹ = (M : ℂ)⁻¹ := by
    push_cast
    field_simp [NeZero.ne (M : ℂ)]
  rw [hweight, Finset.smul_sum]
  symm
  refine Fintype.sum_equiv e _ _ fun j ↦ ?_
  rw [e.symm_apply_apply, rationalAdeleStageFourier_phase, ← smul_smul]
  dsimp [e]
  rw [finEquiv_eq_cast, finEquiv_eq_cast]

end
end Masullo
