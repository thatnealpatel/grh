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

private theorem conj_stdAddChar {N : ℕ} [NeZero N] (z : ZMod N) :
    conj (ZMod.stdAddChar z) = ZMod.stdAddChar (-z) := by
  simp only [ZMod.stdAddChar_apply, ← Circle.coe_inv_eq_conj]
  exact congrArg ((↑) : Circle → ℂ) (ZMod.toCircle.map_neg_eq_inv z).symm

private theorem cyclic_orthogonality {N : ℕ} [NeZero N] (j l : ZMod N) :
    (∑ k : ZMod N, ZMod.stdAddChar (j * k) * conj (ZMod.stdAddChar (l * k))) =
      if j = l then (N : ℂ) else 0 := by
  simp_rw [conj_stdAddChar, ← AddChar.map_add_eq_mul, ← sub_eq_add_neg, ← sub_mul]
  split_ifs with h
  · simp [h, ZMod.card]
  · exact AddChar.sum_eq_zero_of_ne_one (ZMod.isPrimitive_stdAddChar N (sub_ne_zero.mpr h))

private theorem cyclic_sum_mul_conj {N : ℕ} [NeZero N] (b : ZMod N → ℂ) :
    let d := fun k : ZMod N ↦ ∑ j : ZMod N, ZMod.stdAddChar (j * k) * b j
    (∑ k, d k * conj (d k)) = (N : ℂ) * ∑ j, b j * conj (b j) := by
  classical
  dsimp only
  calc
    _ = ∑ k : ZMod N, ∑ j : ZMod N, ∑ l : ZMod N,
          (ZMod.stdAddChar (j * k) * conj (ZMod.stdAddChar (l * k))) * (b j * conj (b l)) := by
      refine Finset.sum_congr rfl fun k _ ↦ ?_
      rw [map_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun l _ ↦ by rw [map_mul (starRingEnd ℂ)]; ring
    _ = ∑ j : ZMod N, ∑ l : ZMod N,
          (∑ k : ZMod N, ZMod.stdAddChar (j * k) * conj (ZMod.stdAddChar (l * k))) *
            (b j * conj (b l)) := by
      simp only [Finset.sum_mul]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun _ _ ↦ Finset.sum_comm
    _ = _ := by
      simp only [cyclic_orthogonality, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ,
        ite_true, Finset.mul_sum]

private theorem normalized_cyclic_sum_norm_sq {M : ℕ} [NeZero M] (b : ZMod (M ^ 2) → ℂ) :
    (∑ k : ZMod (M ^ 2), ‖(M : ℂ)⁻¹ * ∑ j : ZMod (M ^ 2), ZMod.stdAddChar (j * k) * b j‖ ^ 2) =
      ∑ j, ‖b j‖ ^ 2 := by
  let d (k : ZMod (M ^ 2)) := ∑ j : ZMod (M ^ 2), ZMod.stdAddChar (j * k) * b j
  have h : (∑ k, ‖d k‖ ^ 2) = ((M ^ 2 : ℕ) : ℝ) * ∑ j, ‖b j‖ ^ 2 := by
    apply Complex.ofReal_injective
    simp only [Complex.ofReal_mul, Complex.ofReal_natCast, Complex.ofReal_sum, Complex.sq_norm,
      ← Complex.mul_conj]
    exact cyclic_sum_mul_conj b
  change (∑ k, ‖(M : ℂ)⁻¹ * d k‖ ^ 2) = _
  simp only [norm_mul, mul_pow, norm_inv, Complex.norm_natCast]
  rw [← Finset.mul_sum, h, Nat.cast_pow, ← mul_assoc, ← mul_pow,
    inv_mul_cancel₀ (NeZero.ne (M : ℝ)), one_pow, one_mul]

/-- At each real frequency the Haar-normalized finite matrix preserves the
sum of the squared magnitudes of the real Fourier profiles. -/
public theorem rationalAdeleStageFourier_sum_norm_sq {M : ℕ} (hM : 0 < M)
    (b : Fin (M ^ 2) → S) (t : ℝ) :
    (∑ k, ‖rationalAdeleStageFourier M b k t‖ ^ 2) = ∑ j, ‖𝓕 (b j) t‖ ^ 2 := by
  let : NeZero M := ⟨hM.ne'⟩
  let e := (ZMod.finEquiv (M ^ 2)).toEquiv
  let c : ZMod (M ^ 2) → ℂ := fun j ↦ 𝓕 (b (e.symm j)) t
  calc
    _ = ∑ k : ZMod (M ^ 2),
        ‖(M : ℂ)⁻¹ * ∑ j : ZMod (M ^ 2), ZMod.stdAddChar (j * k) * c j‖ ^ 2 := by
      refine Fintype.sum_equiv e _ _ fun k ↦ ?_
      rw [rationalAdeleStageFourier_apply, sum_apply, Finset.mul_sum]
      congr 2
      refine Fintype.sum_equiv e _ _ fun j ↦ ?_
      simp only [smul_apply, smul_eq_mul, rationalAdeleStageFourier_phase, c, e.symm_apply_apply]
      change _ = (M : ℂ)⁻¹ * (ZMod.stdAddChar (_ * _) * _)
      rw [show e j = _ from finEquiv_eq_cast j, show e k = _ from finEquiv_eq_cast k, mul_assoc]
    _ = ∑ j, ‖c j‖ ^ 2 := normalized_cyclic_sum_norm_sq c
    _ = _ := Fintype.sum_equiv e.symm _ _ fun _ ↦ rfl

end
end Masullo
